/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalGradedAlgebraBasic
public import WeilConjectures.RingTheory.AssociatedGradedRing
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.AlgebraicGeometry.Closed.ClosedImmersionGradedAlgebraDescent
import WeilConjectures.AlgebraicGeometry.Graded.GradedSheafAlgebraTotalization
import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalCoproductAffineAddEquiv
import WeilConjectures.AlgebraicGeometry.FormalAssociatedGradedAlgebraExists
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPowerQuotient
import WeilConjectures.AlgebraicGeometry.FormalAssociatedGradedAffineMultiplication
import WeilConjectures.AlgebraicGeometry.FormalPolynomialPowerLifts

/-! # The algebra obtained by descending the ideal-power quotients

Source: Stacks Project, Divisors, Tags 0630 and 0633.
(blueprint: lem-pur-conormal-graded-algebra-construction).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.ConormalGradedAlgebra
variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The algebra construction with its coproduct and normalized affine charts.
This record contains no stalk or finiteness assertion and no symmetric comparison
or augmentation. Source: Stacks Project, Divisors, Tags 0630 and 0633.
(blueprint: lem-pur-conormal-graded-algebra-construction). -/
structure AffineData where
  algebra : Z.CommAlgebraSheaf
  inclusion : ∀ n, piece i n ⟶ algebra.toModule
  coproduct : IsColimit (Cofan.mk algebra.toModule inclusion)
  multiplication : ∀ (m n : ℕ) (U : X.Opens)
    (a : (power i m).val.obj (op U)) (b : (power i n).val.obj (op U))
    (d : (power i (m + n)).val.obj (op U)),
    (powerInclusion i (m + n)).val.app (op U) d =
        (@id Γ(X, U) ((powerInclusion i m).val.app (op U) a)) *
          (@id Γ(X, U) ((powerInclusion i n).val.app (op U) b)) →
      homogeneousClass i algebra inclusion m U a * homogeneousClass i algebra inclusion n U b =
        homogeneousClass i algebra inclusion (m + n) U d
  constants : ∀ (U : X.Opens) (a : (power i 0).val.obj (op U)),
    homogeneousClass i algebra inclusion 0 U a =
      algebra.hom.hom.app (op (i ⁻¹ᵁ U)) (i.app U a)
  affineChart : ∀ U : X.affineOpens,
    ∃ e : algebra.right.obj.obj (op (i ⁻¹ᵁ U.1)) ≅
        CommRingCat.of (Ideal.associatedGraded (i.ker.ideal U)),
      ∀ (n : ℕ) (a : (power i n).val.obj (op U.1)),
        ∃ h : (powerInclusion i n).val.app (op U.1) a ∈ i.ker.ideal U ^ n,
          e.hom (homogeneousClass i algebra inclusion n U.1 a) =
            DirectSum.of (Ideal.associatedGradedPiece (i.ker.ideal U)) n
              (Submodule.Quotient.mk ⟨(powerInclusion i n).val.app (op U.1) a, h⟩)

private theorem quotient_comparison (n : ℕ) :
    ∃ e : (Scheme.Modules.pushforward i).obj (piece i n) ≅
        formalAssociatedGradedPiece i.ker n,
      ∀ (U : X.Opens) (a : (power i n).val.obj (op U)),
        e.hom.val.app (op U) (representative i n U a) =
          (formalAssociatedGradedπ i.ker n).val.app (op U) a := by
  let adj := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)
  obtain ⟨e, he⟩ := closedImmersion_power_quotient i.ker 1 i (by simp) adj (power i n)
  refine ⟨e.symm, ?_⟩
  intro U a
  have h : adj.unit.app (power i n) ≫ e.inv = formalAssociatedGradedπ i.ker n := by
    rw [← he, Category.assoc, e.hom_inv_id, Category.comp_id]
    rfl
  exact ConcreteCategory.congr_hom (congrArg (fun f ↦ f.val.app (op U)) h) a

omit [IsClosedImmersion i] in
private theorem power_lift (U : X.affineOpens) (n : ℕ)
    (x : (i.ker.ideal U ^ n : Ideal Γ(X, U.1))) :
    ∃ a : (power i n).val.obj (op U.1),
      (powerInclusion i n).val.app (op U.1) a = x.val := by
  have hx : x.val ∈ Set.range ((powerInclusion i n).app U.1) := by
    exact (power_affine_range i.ker U n).symm.subset x.property
  exact hx

omit [IsClosedImmersion i] in
private theorem additive_chart_induction
    (A : Z.CommAlgebraSheaf) (j : ∀ n, piece i n ⟶ A.toModule)
    (U : X.affineOpens)
    (E : A.right.obj.obj (op (i ⁻¹ᵁ U.1)) ≃+ Ideal.associatedGraded (i.ker.ideal U))
    (hE : ∀ (n : ℕ) (a : (power i n).val.obj (op U.1)),
      ∃ h : (powerInclusion i n).val.app (op U.1) a ∈ i.ker.ideal U ^ n,
        E (homogeneousClass i A j n U.1 a) =
          DirectSum.of (Ideal.associatedGradedPiece (i.ker.ideal U)) n
            (Submodule.Quotient.mk ⟨(powerInclusion i n).val.app (op U.1) a, h⟩))
    (P : A.right.obj.obj (op (i ⁻¹ᵁ U.1)) → Prop)
    (hzero : P 0)
    (hhom : ∀ (n : ℕ) (a : (power i n).val.obj (op U.1)),
      P (homogeneousClass i A j n U.1 a))
    (hadd : ∀ a b, P a → P b → P (a + b))
    (a : A.right.obj.obj (op (i ⁻¹ᵁ U.1))) : P a := by
  suffices hp : ∀ b : Ideal.associatedGraded (i.ker.ideal U), P (E.symm b) by
    simpa using hp (E a)
  intro b
  induction b using DirectSum.induction_on with
  | zero => simpa using hzero
  | add b c hb hc => simpa using hadd (E.symm b) (E.symm c) hb hc
  | of n x =>
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      obtain ⟨a, ha⟩ := power_lift i U n x
      obtain ⟨h, he⟩ := hE n a
      have he' : E (homogeneousClass i A j n U.1 a) =
          DirectSum.of (Ideal.associatedGradedPiece (i.ker.ideal U)) n
            (Submodule.Quotient.mk x) := by
        rw [he]
        congr 2
        exact Subtype.ext ha
      rw [← he', E.symm_apply_apply]
      exact hhom n a

omit [IsClosedImmersion i] in
private theorem additive_chart_mul
    (A : Z.CommAlgebraSheaf) (j : ∀ n, piece i n ⟶ A.toModule)
    (hmul : ∀ (m n : ℕ) (U : X.Opens)
      (a : (power i m).val.obj (op U)) (b : (power i n).val.obj (op U))
      (d : (power i (m + n)).val.obj (op U)),
      (powerInclusion i (m + n)).val.app (op U) d =
          (@id Γ(X, U) ((powerInclusion i m).val.app (op U) a)) *
            (@id Γ(X, U) ((powerInclusion i n).val.app (op U) b)) →
        homogeneousClass i A j m U a * homogeneousClass i A j n U b =
          homogeneousClass i A j (m + n) U d)
    (U : X.affineOpens)
    (E : A.right.obj.obj (op (i ⁻¹ᵁ U.1)) ≃+ Ideal.associatedGraded (i.ker.ideal U))
    (hE : ∀ (n : ℕ) (a : (power i n).val.obj (op U.1)),
      ∃ h : (powerInclusion i n).val.app (op U.1) a ∈ i.ker.ideal U ^ n,
        E (homogeneousClass i A j n U.1 a) =
          DirectSum.of (Ideal.associatedGradedPiece (i.ker.ideal U)) n
            (Submodule.Quotient.mk ⟨(powerInclusion i n).val.app (op U.1) a, h⟩)) :
    ∀ a b, E (a * b) = E a * E b := by
  intro a
  refine additive_chart_induction i A j U E hE
    (fun a ↦ ∀ b, E (a * b) = E a * E b) ?_ ?_ ?_ a
  · intro b
    simp only [zero_mul, map_zero]
  · intro m a b
    refine additive_chart_induction i A j U E hE
      (fun b ↦ E (homogeneousClass i A j m U.1 a * b) =
        E (homogeneousClass i A j m U.1 a) * E b) ?_ ?_ ?_ b
    · simp only [mul_zero, map_zero]
    · intro n b
      obtain ⟨d, hd⟩ := power_affine_product i.ker m n U a b
      rw [hmul m n U.1 a b d hd]
      obtain ⟨ha, hea⟩ := hE m a
      obtain ⟨hb, heb⟩ := hE n b
      obtain ⟨hd', hed⟩ := hE (m + n) d
      rw [hea, heb, hed, Ideal.associatedGraded_mul]
      congr 2
      exact Subtype.ext hd
    · intro b c hb hc
      simp only [mul_add, map_add, hb, hc]
  · intro a b ha hb c
    simp only [add_mul, map_add, ha c, hb c]

/-- The ideal-power quotient multiplication descends to the closed subscheme and
its total algebra has the expected normalized affine associated-graded charts.
Source: Stacks Project, Divisors, Tags 0630 and 0633.
(blueprint: lem-pur-conormal-graded-algebra-construction).

Proof: Form the quasi-coherent sheaf cokernels `B_n = I^n/I I^n` on the ambient
scheme. Their multiplication is the multiplication of ideal-power representatives:
changing either representative changes the product by `I^(m+n+1)`. The affine
quotient formula and sheaf separatedness glue the products and verify the ring
laws. Each `B_n` is annihilated by `I`. The normalized closed-immersion unit quotient
identifies it with the pushforward of the fixed module `i^*I^n`, including n=0.
Transport the products and unit through these identifications; fully faithful
pushforward makes their laws hold on the closed subscheme. Sheafify the presheaf
of finite sums of homogeneous sections with this convolution multiplication.
Its maps as a module sheaf are precisely families of maps from the homogeneous
pieces, proving the coproduct property. On an ambient affine `Spec R`, the quotient
pieces have sections `J^n/J^(n+1)` on `Spec(R/J)`. The affine tilde adjunction preserves
the coproduct and identifies its sections with the direct sum of these modules.
The representative multiplication and constant formulas make this identification
an isomorphism of rings with `gr_J(R)`. Every construction respects restriction.
The Lean reduction isolates homogeneous descent, totalization and the additive
coproduct comparison as separate lemmas. It proves the quotient normalization and
representative formulas from the ambient graded algebra. For the ring chart, double
additive induction reduces preservation of products to homogeneous representatives;
quotient induction and the affine power range provide such representatives. Both
products then have the same degree-(m+n) quotient class. A multiplicative additive
equivalence is a ring equivalence. No assertion about arbitrary sections commuting
with infinite sums is needed. The zero ring, n=0, and the empty closed subscheme
satisfy the same construction and formulas. -/
theorem exists_affineData : Nonempty (AffineData i) := by
  classical
  obtain ⟨B, hBunit, hBmul⟩ := formalAssociatedGraded_algebra_exists i.ker
  choose e he using quotient_comparison i
  obtain ⟨D, hDunit, hDmul⟩ := exists_gradedAlgebra_closed_descent i
    (formalAssociatedGradedPiece i.ker) (piece i) e B
  obtain ⟨A, j, ⟨hc⟩, hmul, hunit⟩ := exists_gradedSheafAlgebra_totalization (piece i) D
  have hrep (m n : ℕ) (U : X.Opens)
      (a : (power i m).val.obj (op U)) (b : (power i n).val.obj (op U))
      (d : (power i (m + n)).val.obj (op U))
      (hd : (powerInclusion i (m + n)).val.app (op U) d =
        (@id Γ(X, U) ((powerInclusion i m).val.app (op U) a)) *
          (@id Γ(X, U) ((powerInclusion i n).val.app (op U) b))) :
      homogeneousClass i A j m U a * homogeneousClass i A j n U b =
        homogeneousClass i A j (m + n) U d := by
    change (@id (A.right.obj.obj (op (i ⁻¹ᵁ U)))
      ((j m).val.app _ (representative i m U a))) *
      (@id (A.right.obj.obj (op (i ⁻¹ᵁ U)))
        ((j n).val.app _ (representative i n U b))) = _
    rw [hmul]
    apply congrArg ((j (m + n)).val.app (op (i ⁻¹ᵁ U)))
    have : Mono (e (m + n)).hom.val := (SheafOfModules.forget _).map_mono _
    apply (PresheafOfModules.injective_of_mono (e (m + n)).hom.val (op U))
    rw [hDmul, he, he, he]
    obtain ⟨c, hcprod, hcclass⟩ := hBmul m n U a b
    have hcd : c = d :=
      formalPolynomial_power_injective i.ker.toModulesι (m + n) U
        (hcprod.trans hd.symm)
    exact hcclass.trans (congrArg ((formalAssociatedGradedπ i.ker (m + n)).val.app
      (op U)) hcd)
  have hconst (U : X.Opens) (a : (power i 0).val.obj (op U)) :
      homogeneousClass i A j 0 U a = A.hom.hom.app (op (i ⁻¹ᵁ U)) (i.app U a) := by
    have ht := ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.val.app (op U)) hDunit) a
    change (e 0).hom.val.app (op U)
      (D.unit.val.app (op (i ⁻¹ᵁ U)) (i.app U a)) = B.unit.val.app (op U) a at ht
    rw [hBunit] at ht
    have hr : representative i 0 U a =
        D.unit.val.app (op (i ⁻¹ᵁ U)) (i.app U a) := by
      have : Mono (e 0).hom.val := (SheafOfModules.forget _).map_mono _
      apply (PresheafOfModules.injective_of_mono (e 0).hom.val (op U))
      exact (he 0 U a).trans ht.symm
    change (j 0).val.app _ (representative i 0 U a) = _
    rw [hr, hunit]
  refine ⟨⟨A, j, hc, hrep, hconst, ?_⟩⟩
  intro U
  obtain ⟨E, hE⟩ := exists_conormalCoproduct_affine_addEquiv i A.toModule j hc U
  have hE' : ∀ (n : ℕ) (a : (power i n).val.obj (op U.1)),
      ∃ h : (powerInclusion i n).val.app (op U.1) a ∈ i.ker.ideal U ^ n,
        E (homogeneousClass i A j n U.1 a) =
          DirectSum.of (Ideal.associatedGradedPiece (i.ker.ideal U)) n
            (Submodule.Quotient.mk ⟨(powerInclusion i n).val.app (op U.1) a, h⟩) := hE
  let R : A.right.obj.obj (op (i ⁻¹ᵁ U.1)) ≃+*
      Ideal.associatedGraded (i.ker.ideal U) :=
    { E with map_mul' := additive_chart_mul i A j hrep U E hE' }
  exact ⟨R.toCommRingCatIso, hE'⟩

end AlgebraicGeometry.ConormalGradedAlgebra
