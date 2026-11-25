/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalGradedAlgebraConstruction
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalGradedPieceStalk
import WeilConjectures.Topology.StalkDirectSums
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.AlgebraicGeometry.FormalAssociatedGradedAffineMultiplication

/-! # Stalk charts of the conormal algebra

Source: Stacks Project, Divisors, Tag 0633; Algebra, Tag 00CS.
(blueprint: lem-pur-conormal-graded-algebra-stalk).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped DirectSum
namespace AlgebraicGeometry.ConormalGradedAlgebra
variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

-- Keep the explicit tensor-pullback construction behind its module interface.
attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj

@[irreducible] private noncomputable def ring_stalk_add_equiv (A : Z.CommAlgebraSheaf) (z : Z) :
    TopCat.Presheaf.stalk (C := CommRingCat) A.right.obj z ≃+
      (RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj A.toModule :=
  (preservesColimitIso (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat Ab)
    ((OpenNhds.inclusion z).op ⋙ A.right.obj)).addCommGroupIsoToAddEquiv

private theorem ring_stalk_add_equiv_germ (A : Z.CommAlgebraSheaf) (z : Z)
    (U : Z.Opens) (hz : z ∈ U) (a : A.right.obj.obj (op U)) :
    ring_stalk_add_equiv A z (TopCat.Presheaf.germ A.right.obj U z hz a) =
      TopCat.Presheaf.germ A.toModule.val.presheaf U z hz a := by
  unfold ring_stalk_add_equiv
  exact ConcreteCategory.congr_hom (ι_preservesColimitIso_hom
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat Ab)
    ((OpenNhds.inclusion z).op ⋙ A.right.obj) (op (⟨U, hz⟩ : OpenNhds z))) a

private theorem stalk_map_germ (z : Z) {M N : Z.Modules} (f : M ⟶ N)
    (U : Z.Opens) (hz : z ∈ U) (a : M.val.obj (op U)) :
    (RingedSpace.moduleStalkFunctor Z.toRingedSpace z).map f
        (TopCat.Presheaf.germ M.val.presheaf U z hz a) =
      TopCat.Presheaf.germ N.val.presheaf U z hz (f.val.app (op U) a) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U z hz
    ((PresheafOfModules.toPresheaf _).map f.val) a

private theorem additive_stalk_chart (A : AffineData i) (z : Z) :
    ∃ e : TopCat.Presheaf.stalk (C := CommRingCat) A.algebra.right.obj z ≃+
        Ideal.associatedGraded (RingHom.ker (i.stalkMap z).hom),
      ∀ (n : ℕ) (U : X.Opens) (hz : i z ∈ U) (a : (power i n).val.obj (op U)),
        ∃ h : X.presheaf.germ U (i z) hz
            ((powerInclusion i n).val.app (op U) a) ∈
              RingHom.ker (i.stalkMap z).hom ^ n,
          e (TopCat.Presheaf.germ A.algebra.right.obj (i ⁻¹ᵁ U) z hz
            (homogeneousClass i A.algebra A.inclusion n U a)) =
              DirectSum.of (Ideal.associatedGradedPiece (RingHom.ker (i.stalkMap z).hom)) n
                (Submodule.Quotient.mk
                  ⟨X.presheaf.germ U (i z) hz ((powerInclusion i n).val.app (op U) a), h⟩) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  classical
  let : DecidableEq (ULift.{u} ℕ) := Classical.decEq _
  let S := RingedSpace.moduleStalkFunctor Z.toRingedSpace z
  let F : ULift.{u} ℕ → Z.Modules := fun n ↦ piece i n.down
  let t : (∐ F) ≅ A.algebra.toModule :=
    Sigma.reindex (Equiv.ulift : ULift.{u} ℕ ≃ ℕ) (piece i) ≪≫
      (coproductIsCoproduct (piece i)).coconePointUniqueUpToIso A.coproduct
  obtain ⟨es, hs⟩ := SheafOfModules.exists_stalk_directSum_linearEquiv Z.ringCatSheaf
    (ULift.{u} ℕ) F z
  let p : S.obj A.algebra.toModule ≃+ (⨁ n : ULift.{u} ℕ,
      TopCat.Presheaf.stalk (C := Ab.{u}) (F n).val.presheaf z) :=
    (S.mapIso t).symm.toLinearEquiv.toAddEquiv.trans es.toAddEquiv
  let r : (⨁ n : ULift.{u} ℕ,
      TopCat.Presheaf.stalk (C := Ab.{u}) (F n).val.presheaf z) ≃+
      (⨁ n : ℕ, TopCat.Presheaf.stalk (C := Ab.{u}) (piece i n).val.presheaf z) :=
    DirectSum.equivCongrLeft (Equiv.ulift : ULift.{u} ℕ ≃ ℕ)
  choose ec₀ hc using fun n ↦ graded_piece_stalk i n z
  let ec (n : ℕ) : TopCat.Presheaf.stalk (C := Ab.{u}) (piece i n).val.presheaf z ≃+
      Ideal.associatedGradedPiece (RingHom.ker (i.stalkMap z).hom) n := ec₀ n
  let e := (ring_stalk_add_equiv A.algebra z).trans
    (p.trans (r.trans (DirectSum.congrAddEquiv ec)))
  refine ⟨e, ?_⟩
  intro n U hz a
  obtain ⟨h, hec⟩ := hc n U hz a
  refine ⟨h, ?_⟩
  have hι : Sigma.ι F (ULift.up n) ≫ t.hom = A.inclusion n := by
    dsimp only [t, Iso.trans_hom]
    rw [← Category.assoc]
    exact (congrArg (fun k ↦ k ≫
      ((coproductIsCoproduct (piece i)).coconePointUniqueUpToIso A.coproduct).hom)
        (Sigma.ι_reindex_hom (Equiv.ulift : ULift.{u} ℕ ≃ ℕ) (piece i)
          (ULift.up n))).trans
      (IsColimit.comp_coconePointUniqueUpToIso_hom
        (coproductIsCoproduct (piece i)) A.coproduct ⟨n⟩)
  have hi : A.inclusion n ≫ t.inv = Sigma.ι F (ULift.up n) := by
    rw [← hι, Category.assoc, t.hom_inv_id, Category.comp_id]
  have ht : (S.mapIso t).inv (TopCat.Presheaf.germ A.algebra.toModule.val.presheaf
      (i ⁻¹ᵁ U) z hz (homogeneousClass i A.algebra A.inclusion n U a)) =
      TopCat.Presheaf.germ (∐ F).val.presheaf (i ⁻¹ᵁ U) z hz
        ((Sigma.ι F (ULift.up n)).val.app (op (i ⁻¹ᵁ U))
          (representative i n U a)) := by
    exact (stalk_map_germ z t.inv _ hz _).trans
      (congrArg (TopCat.Presheaf.germ (∐ F).val.presheaf (i ⁻¹ᵁ U) z hz)
        (ConcreteCategory.congr_hom (congrArg (fun f ↦ f.val.app (op (i ⁻¹ᵁ U))) hi)
          (representative i n U a)))
  change (DirectSum.congrAddEquiv ec) (r (es ((S.mapIso t).inv
    (ring_stalk_add_equiv A.algebra z
      (TopCat.Presheaf.germ A.algebra.right.obj (i ⁻¹ᵁ U) z hz
        (homogeneousClass i A.algebra A.inclusion n U a)))))) = _
  simp only [ring_stalk_add_equiv_germ]
  rw [ht]
  rw [hs]
  rw [DirectSum.lof_eq_of]
  have hr : r (DirectSum.of (fun k : ULift.{u} ℕ ↦
      TopCat.Presheaf.stalk (C := Ab.{u}) (F k).val.presheaf z) (ULift.up n)
      (TopCat.Presheaf.germ (piece i n).val.presheaf (i ⁻¹ᵁ U) z hz
        (representative i n U a))) = DirectSum.of
      (fun k : ℕ ↦ TopCat.Presheaf.stalk (C := Ab.{u}) (piece i k).val.presheaf z) n
      (TopCat.Presheaf.germ (piece i n).val.presheaf (i ⁻¹ᵁ U) z hz
        (representative i n U a)) :=
    DirectSum.equivCongrLeft_of
      (β := fun k : ULift.{u} ℕ ↦ TopCat.Presheaf.stalk (C := Ab.{u}) (F k).val.presheaf z)
      (Equiv.ulift : ULift.{u} ℕ ≃ ℕ) n
      (TopCat.Presheaf.germ (piece i n).val.presheaf (i ⁻¹ᵁ U) z hz
        (representative i n U a))
  apply (congrArg (DirectSum.congrAddEquiv ec) hr).trans
  change DirectSum.map (fun n ↦ (ec n).toAddMonoidHom) (DirectSum.of _ n _) = _
  exact (DirectSum.map_of (fun n ↦ (ec n).toAddMonoidHom) n
    (TopCat.Presheaf.germ (piece i n).val.presheaf (i ⁻¹ᵁ U) z hz
      (representative i n U a))).trans (congrArg (DirectSum.of _ n) hec)

private theorem ring_iso_inv_eq {R S : CommRingCat.{u}} (e : R ≅ S)
    {a : R} {b : S} (h : e.hom a = b) : e.inv b = a :=
  (congrArg e.inv h.symm).trans (CommRingCat.inv_hom_apply e a)

omit [IsClosedImmersion i] in
private theorem affineData_induction (A : AffineData i) (U : X.affineOpens)
    (P : A.algebra.right.obj.obj (op (i ⁻¹ᵁ U.1)) → Prop)
    (hz : P 0)
    (hrep : ∀ (n : ℕ) (a : (power i n).val.obj (op U.1)),
      P (homogeneousClass i A.algebra A.inclusion n U.1 a))
    (hadd : ∀ a b, P a → P b → P (a + b)) : ∀ a, P a := by
  obtain ⟨e, he⟩ := A.affineChart U
  have hh (y : Ideal.associatedGraded (i.ker.ideal U)) : P (e.inv y) := by
    induction y using DirectSum.induction_on with
    | zero => simpa only [map_zero] using hz
    | add a b ha hb => simpa only [map_add] using hadd _ _ ha hb
    | of n y =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
        have hy : y.val ∈ Set.range ((powerInclusion i n).val.app (op U.1)) := by
          change y.val ∈ Set.range ((Scheme.idealSheafPower i.ker.toModulesι n).2.app U.1)
          rw [power_affine_range i.ker U n]
          exact y.property
        obtain ⟨a, ha⟩ := hy
        obtain ⟨hm, heq⟩ := he n a
        have h : e.inv (DirectSum.of _ n (Submodule.Quotient.mk y)) =
            homogeneousClass i A.algebra A.inclusion n U.1 a := by
          apply ring_iso_inv_eq e
          exact heq.trans (congrArg (fun t : ↥(i.ker.ideal U ^ n) ↦
            DirectSum.of (Ideal.associatedGradedPiece (i.ker.ideal U)) n
              (Submodule.Quotient.mk t)) (Subtype.ext ha))
        rw [h]
        exact hrep n a
  intro a
  have hi : e.inv (e.hom a) = a := congrArg (fun k ↦ k a) e.hom_inv_id
  simpa only [hi] using hh (e.hom a)

private theorem addHom_mul_add {R S : Type*}
    [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
    (f : R →+ S) (a b c : R)
    (hb : f (a * b) = f a * f b) (hc : f (a * c) = f a * f c) :
    f (a * (b + c)) = f a * f (b + c) := by
  rw [mul_add, map_add, hb, hc, map_add, mul_add]

private theorem addHom_add_mul {R S : Type*}
    [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
    (f : R →+ S) (a b c : R)
    (ha : f (a * c) = f a * f c) (hb : f (b * c) = f b * f c) :
    f ((a + b) * c) = f (a + b) * f c := by
  rw [add_mul, map_add, ha, hb, map_add, add_mul]

/-- The affine associated-graded charts induce the associated-graded chart for the
actual ideal kernel at every point of the closed subscheme.
Source: Stacks Project, Divisors, Tag 0633; Algebra, Tag 00CS.
(blueprint: lem-pur-conormal-graded-algebra-stalk).

Proof: Apply the exact module stalk functor to the normalized unit quotients
`i_* i^*(I^n) = I^n/I I^n`. The stalk range of the ideal inclusion is the actual
kernel `K` of the structure-stalk map; the image-power calculation identifies the
stalk of `I^n` with `K^n`, including n=0. Exactness identifies each quotient stalk
with `K^n/K^(n+1)`, taking every representative germ to its quotient class.
Pushforward along the closed embedding has the same stalk on its image, so these
are the stalks of the fixed homogeneous pieces on the closed subscheme. Stalks
preserve the sheaf coproduct. Hence the coproduct property of `A` assembles the
piece isomorphisms to an additive isomorphism with the associated-graded direct
sum. Multiplication of representative germs is the product of their ambient
representatives; every finite set of germs has a common neighbourhood. The
multiplication and constants formulas of `A` therefore make this additive
isomorphism a ring isomorphism. Its restriction to each homogeneous summand is
the quotient-stalk comparison already constructed, proving the normalized formula.
No finite generation is used. A vanishing stalk or degree zero causes no exception. -/
theorem affineData_stalk_chart (A : AffineData i) : ∀ z : Z,
    ∃ e : TopCat.Presheaf.stalk A.algebra.right.obj z ≅
        CommRingCat.of (Ideal.associatedGraded (RingHom.ker (i.stalkMap z).hom)),
      ∀ (n : ℕ) (U : X.Opens) (hz : i z ∈ U) (a : (power i n).val.obj (op U)),
        ∃ h : X.presheaf.germ U (i z) hz
            ((powerInclusion i n).val.app (op U) a) ∈
              RingHom.ker (i.stalkMap z).hom ^ n,
          e.hom (TopCat.Presheaf.germ A.algebra.right.obj (i ⁻¹ᵁ U) z hz
            (homogeneousClass i A.algebra A.inclusion n U a)) =
              DirectSum.of (Ideal.associatedGradedPiece (RingHom.ker (i.stalkMap z).hom)) n
                (Submodule.Quotient.mk
                  ⟨X.presheaf.germ U (i z) hz ((powerInclusion i n).val.app (op U) a), h⟩) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  intro z
  classical
  obtain ⟨e, he⟩ := additive_stalk_chart i A z
  let K := RingHom.ker (i.stalkMap z).hom
  let f (U : X.Opens) (hz : i z ∈ U) :
      A.algebra.right.obj.obj (op (i ⁻¹ᵁ U)) →+ Ideal.associatedGraded K :=
    e.toAddMonoidHom.comp
      (TopCat.Presheaf.germ A.algebra.right.obj (i ⁻¹ᵁ U) z hz).hom.toAddMonoidHom
  have hmulU (U : X.affineOpens) (hz : i z ∈ U.1)
      (a b : A.algebra.right.obj.obj (op (i ⁻¹ᵁ U.1))) :
      f U.1 hz (a * b) = f U.1 hz a * f U.1 hz b := by
    apply affineData_induction i A U (fun a ↦ ∀ b, _ = _) ?_ ?_ ?_ a b
    · intro b
      simp only [zero_mul, map_zero]
    · intro m a
      apply affineData_induction i A U (fun b ↦ _ = _) ?_ ?_ ?_
      · simp only [mul_zero, map_zero]
      · intro n b
        obtain ⟨c, hc⟩ := power_affine_product i.ker m n U a b
        rw [A.multiplication m n U.1 a b c hc]
        obtain ⟨ha, hea⟩ := he m U.1 hz a
        obtain ⟨hb, heb⟩ := he n U.1 hz b
        obtain ⟨hd, hed⟩ := he (m + n) U.1 hz c
        let g : Γ(X, U.1) →+* X.presheaf.stalk (i z) :=
          (X.presheaf.germ U.1 (i z) hz).hom
        let aa : ↥(K ^ m) :=
          ⟨g ((powerInclusion i m).val.app (op U.1) a), ha⟩
        let bb : ↥(K ^ n) :=
          ⟨g ((powerInclusion i n).val.app (op U.1) b), hb⟩
        let dd : ↥(K ^ (m + n)) :=
          ⟨g ((powerInclusion i (m + n)).val.app (op U.1) c), hd⟩
        let ab : ↥(K ^ (m + n)) :=
          ⟨aa.val * bb.val, by simpa [pow_add] using Ideal.mul_mem_mul ha hb⟩
        have hdc : dd = ab := by
          apply Subtype.ext
          change g ((powerInclusion i (m + n)).val.app (op U.1) c) =
            g ((powerInclusion i m).val.app (op U.1) a) *
              g ((powerInclusion i n).val.app (op U.1) b)
          exact (congrArg g hc).trans (g.map_mul _ _)
        have hq := congrArg (fun t : ↥(K ^ (m + n)) ↦
          DirectSum.of (Ideal.associatedGradedPiece K) (m + n) (Submodule.Quotient.mk t))
            hdc
        exact hed.trans (hq.trans ((Ideal.associatedGraded_mul K m n aa bb).symm.trans
          (congrArg₂ (fun x y : Ideal.associatedGraded K ↦ x * y) hea.symm heb.symm)))
      · intro b c hb hc
        exact addHom_mul_add (f U.1 hz) _ b c hb hc
    · intro a c ha hc b
      exact addHom_add_mul (f U.1 hz) a c b (ha b) (hc b)
  have hmul (a b : TopCat.Presheaf.stalk (C := CommRingCat) A.algebra.right.obj z) :
      e (a * b) = e a * e b := by
    obtain ⟨U, hzU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq A.algebra.right.obj a
    obtain ⟨V, hzV, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq A.algebra.right.obj b
    have hb := X.isBasis_affineOpens.of_isInducing i.isClosedEmbedding.isInducing
    obtain ⟨W, ⟨_, ⟨T, hT, rfl⟩, rfl⟩, hzW, hWU⟩ :=
      hb.exists_subset_of_mem_open (show z ∈ U ⊓ V from ⟨hzU, hzV⟩) (U ⊓ V).2
    have hTU : i ⁻¹ᵁ T ≤ U := hWU.trans inf_le_left
    have hTV : i ⁻¹ᵁ T ≤ V := hWU.trans inf_le_right
    let aa := A.algebra.right.obj.map (homOfLE hTU).op a
    let bb := A.algebra.right.obj.map (homOfLE hTV).op b
    let g : A.algebra.right.obj.obj (op (i ⁻¹ᵁ T)) →+*
        TopCat.Presheaf.stalk (C := CommRingCat) A.algebra.right.obj z :=
      (TopCat.Presheaf.germ A.algebra.right.obj (i ⁻¹ᵁ T) z hzW).hom
    have ha : g aa = TopCat.Presheaf.germ A.algebra.right.obj U z hzU a :=
      TopCat.Presheaf.germ_res_apply A.algebra.right.obj (homOfLE hTU) z hzW a
    have hb : g bb = TopCat.Presheaf.germ A.algebra.right.obj V z hzV b :=
      TopCat.Presheaf.germ_res_apply A.algebra.right.obj (homOfLE hTV) z hzW b
    have hprod := congrArg₂
      (fun x y : TopCat.Presheaf.stalk (C := CommRingCat) A.algebra.right.obj z ↦ x * y)
      ha hb
    exact (congrArg e hprod.symm).trans
      ((congrArg e (g.map_mul aa bb).symm).trans
        ((hmulU ⟨T, hT⟩ hzW aa bb).trans
          (congrArg₂ (fun x y : Ideal.associatedGraded K ↦ x * y)
            (congrArg e ha) (congrArg e hb))))
  let q : TopCat.Presheaf.stalk (C := CommRingCat) A.algebra.right.obj z ≃+*
      Ideal.associatedGraded (RingHom.ker (i.stalkMap z).hom) :=
    { e with map_mul' := hmul }
  exact ⟨q.toCommRingCatIso, he⟩

end AlgebraicGeometry.ConormalGradedAlgebra
