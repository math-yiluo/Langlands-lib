import Langlands.BruhatTits.RationalPoints.BoundedSetOperations
import Langlands.GroupScheme.Rational.MatrixEntryBoundedness
import Langlands.GroupScheme.BoundedSubgroupStableLatticeStatement
import Langlands.GroupScheme.Rational.OrderedProductAlgebra
import Langlands.GroupScheme.AffineLinearEmbeddingProof

/-! # Products of algebraically bounded sets over an arbitrary valued field -/

noncomputable section

universe u

open CategoryTheory ValuativeRel
open _root_.AlgebraicGeometry
open scoped Pointwise CategoryTheory.MonObj Matrix
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

namespace MatrixRepresentation

variable {F : Type u} [Field F] [ValuativeRel F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {n : Type} [Fintype n] [DecidableEq n]

omit [ValuativeRel F] in
/-- Each entry and each inverse entry of an actual rational matrix is the value of one
regular function on `G`. -/
theorem exists_entry_regularFunction (ρ : MatrixRepresentation G n) (i j : n) :
    ∃ f g : AffineCoordinateRing F G.X, ∀ x : rationalPoints G,
      rationalPointAlgebraHom F G.X x f = ρ.rationalMatrix x i j ∧
        rationalPointAlgebraHom F G.X x g = (ρ.rationalMatrix x)⁻¹ i j := by
  let : IsAffine (Grp.toMon (GeneralLinear.groupScheme n (CommRingCat.of F))).X.left :=
    GeneralLinear.isAffine_groupScheme n (CommRingCat.of F)
  let π : MvPolynomial (GeneralLinear.Coordinate n) F →ₐ[F]
      AffineCoordinateRing F G.X :=
    (affineCoordinatePullback F ρ.hom.hom).comp
      ((spectrumCoordinateAlgEquiv F (GeneralLinear.CoordinateRing n F)).symm.toAlgHom.comp
        (GeneralLinear.quotient n F))
  refine ⟨π (MvPolynomial.X (.entry i j)), π (MvPolynomial.X (.inverseEntry i j)),
    fun x => ⟨?_, ?_⟩⟩
  · rw [rationalPointAlgebraHom_apply_appTop, rationalMatrix_apply_apply]
    change (Scheme.ΓSpecIso (CommRingCat.of F)).hom
      (x.left.appTop (ρ.hom.hom.left.appTop
        (GeneralLinear.entrySection n (CommRingCat.of F) i j))) =
      (Scheme.ΓSpecIso (CommRingCat.of F)).hom
        ((x.left ≫ ρ.hom.hom.left).appTop
          (GeneralLinear.entrySection n (CommRingCat.of F) i j))
    rw [Scheme.Hom.comp_appTop]
    rfl
  · rw [rationalPointAlgebraHom_apply_appTop, rationalMatrix_inv_apply_apply]
    change (Scheme.ΓSpecIso (CommRingCat.of F)).hom
      (x.left.appTop (ρ.hom.hom.left.appTop
        (GeneralLinear.inverseEntrySection n (CommRingCat.of F) i j))) =
      (Scheme.ΓSpecIso (CommRingCat.of F)).hom
        ((x.left ≫ ρ.hom.hom.left).appTop
          (GeneralLinear.inverseEntrySection n (CommRingCat.of F) i j))
    rw [Scheme.Hom.comp_appTop]
    rfl

/-- Algebraically bounded sets have bounded inverse matrix entries in every
representation. -/
theorem inverseEntries_bounded_of_isAlgebraicallyBounded (ρ : MatrixRepresentation G n)
    {B : Set (rationalPoints G)} (hB : IsAlgebraicallyBounded F G.X B) (i j : n) :
    ∃ b : F, b ≠ 0 ∧ ∀ x ∈ B, (ρ.rationalMatrix x)⁻¹ i j ≤ᵥ b := by
  obtain ⟨_, g, hg⟩ := ρ.exists_entry_regularFunction i j
  obtain ⟨b, hb, h⟩ := hB g
  exact ⟨b, hb, fun x hx => (hg x).2 ▸ h x hx⟩

omit [DecidableEq n] in
/-- Bounded families of matrices have bounded products: each entry of `M p * N p` is a
finite sum of products of bounded entries. -/
theorem matrix_mul_entries_bounded {I : Type*} (M N : I → Matrix n n F)
    (hM : ∀ i j : n, ∃ b : F, b ≠ 0 ∧ ∀ p, M p i j ≤ᵥ b)
    (hN : ∀ i j : n, ∃ b : F, b ≠ 0 ∧ ∀ p, N p i j ≤ᵥ b) (i j : n) :
    ∃ b : F, b ≠ 0 ∧ ∀ p, (M p * N p) i j ≤ᵥ b := by
  let e : I → (I → F) →ₐ[F] F := fun p => Pi.evalAlgHom F (fun _ => F) p
  have hmem : (fun p => (M p * N p) i j) ∈ boundedEvaluationSubalgebra e := by
    have heq : (fun p => (M p * N p) i j) =
        ∑ l : n, (fun p => M p i l) * (fun p => N p l j) := by
      funext p
      simp only [Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply]
    rw [heq]
    refine Subalgebra.sum_mem _ fun l _ => Subalgebra.mul_mem _ ?_ ?_
    · obtain ⟨b, hb, h⟩ := hM i l
      exact ⟨b, hb, fun p => h p⟩
    · obtain ⟨b, hb, h⟩ := hN l j
      exact ⟨b, hb, fun p => h p⟩
  obtain ⟨b, hb, h⟩ := hmem
  exact ⟨b, hb, fun p => h p⟩

/-- A closed matrix representation transports boundedness to products of subsets of the
rational points, over an arbitrary field with a valuative relation. -/
theorem isAlgebraicallyBounded_mul (ρ : MatrixRepresentation G n) (hρ : IsClosedSubgroup ρ)
    {S T : Set (rationalPoints G)} (hS : IsAlgebraicallyBounded F G.X S)
    (hT : IsAlgebraicallyBounded F G.X T) :
    IsAlgebraicallyBounded F G.X (S * T) := by
  apply ρ.isAlgebraicallyBounded_of_entries_and_inverse hρ
  · intro i j
    obtain ⟨b, hb, h⟩ := matrix_mul_entries_bounded
      (fun p : S × T => (ρ.rationalMatrix (p.1 : rationalPoints G) : Matrix n n F))
      (fun p : S × T => (ρ.rationalMatrix (p.2 : rationalPoints G) : Matrix n n F))
      (fun i j => by
        obtain ⟨b, hb, h⟩ := ρ.hasBoundedRationalEntries_of_isAlgebraicallyBounded _ hS i j
        exact ⟨b, hb, fun p => h p.1 p.1.2⟩)
      (fun i j => by
        obtain ⟨b, hb, h⟩ := ρ.hasBoundedRationalEntries_of_isAlgebraicallyBounded _ hT i j
        exact ⟨b, hb, fun p => h p.2 p.2.2⟩) i j
    refine ⟨b, hb, ?_⟩
    rintro _ ⟨s, hs, t, ht, rfl⟩
    have := h (⟨s, hs⟩, ⟨t, ht⟩)
    simpa only [map_mul, Units.val_mul] using this
  · intro i j
    obtain ⟨b, hb, h⟩ := matrix_mul_entries_bounded
      (fun p : S × T => (↑((ρ.rationalMatrix (p.2 : rationalPoints G))⁻¹) : Matrix n n F))
      (fun p : S × T => (↑((ρ.rationalMatrix (p.1 : rationalPoints G))⁻¹) : Matrix n n F))
      (fun i j => by
        obtain ⟨b, hb, h⟩ := ρ.inverseEntries_bounded_of_isAlgebraicallyBounded hT i j
        exact ⟨b, hb, fun p => h p.2 p.2.2⟩)
      (fun i j => by
        obtain ⟨b, hb, h⟩ := ρ.inverseEntries_bounded_of_isAlgebraicallyBounded hS i j
        exact ⟨b, hb, fun p => h p.1 p.1.2⟩) i j
    refine ⟨b, hb, ?_⟩
    rintro _ ⟨s, hs, t, ht, rfl⟩
    have := h (⟨s, hs⟩, ⟨t, ht⟩)
    simpa only [map_mul, mul_inv_rev, Units.val_mul] using this

end MatrixRepresentation

section Groups

variable {F : Type u} [Field F] [ValuativeRel F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

local instance valuedBoundedProductsAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

/-- KP Lemma 2.2.6 for products over an arbitrary field with a valuative relation: a
product of two algebraically bounded subsets of the rational points of an affine group
of finite type is algebraically bounded. No topology or completeness is used. -/
theorem isAlgebraicallyBounded_mul_of_finiteType {S T : Set (rationalPoints G)}
    (hS : IsAlgebraicallyBounded F G.X S) (hT : IsAlgebraicallyBounded F G.X T) :
    IsAlgebraicallyBounded F G.X (S * T) := by
  obtain ⟨N, ρ, hρ⟩ := affineLinearEmbeddingStatement F G inferInstance inferInstance
  exact ρ.isAlgebraicallyBounded_mul hρ hS hT

/-- Left translates of bounded subsets are bounded, over any valued field. -/
theorem isAlgebraicallyBounded_smul_set_of_finiteType {S : Set (rationalPoints G)}
    (hS : IsAlgebraicallyBounded F G.X S) (g : rationalPoints G) :
    IsAlgebraicallyBounded F G.X (g • S) := by
  refine (isAlgebraicallyBounded_mul_of_finiteType
    (isAlgebraicallyBounded_singleton g) hS).mono ?_
  rintro _ ⟨s, hs, rfl⟩
  exact Set.mul_mem_mul (Set.mem_singleton g) hs

/-- Conjugates of bounded subsets are bounded, over any valued field. -/
theorem isAlgebraicallyBounded_conj_of_finiteType {S : Set (rationalPoints G)}
    (hS : IsAlgebraicallyBounded F G.X S) (g : rationalPoints G) :
    IsAlgebraicallyBounded F G.X ({g} * S * {g⁻¹}) :=
  isAlgebraicallyBounded_mul_of_finiteType
    (isAlgebraicallyBounded_mul_of_finiteType (isAlgebraicallyBounded_singleton g) hS)
    (isAlgebraicallyBounded_singleton g⁻¹)

/-- The range of an ordered product of finitely many bounded subgroups is bounded. -/
theorem isAlgebraicallyBounded_range_orderedProduct_of_finiteType :
    ∀ {m : ℕ} (H : Fin m → Subgroup (rationalPoints G)),
      (∀ j, IsAlgebraicallyBounded F G.X (H j : Set (rationalPoints G))) →
      IsAlgebraicallyBounded F G.X (Set.range
        (RelativeRoot.CentralExtension.orderedProduct (fun j => (H j).subtype)))
  | 0, H, _ => by
      refine (isAlgebraicallyBounded_singleton (1 : rationalPoints G)).mono ?_
      rintro _ ⟨x, rfl⟩
      simp [RelativeRoot.CentralExtension.orderedProduct]
  | m + 1, H, hH => by
      refine (isAlgebraicallyBounded_mul_of_finiteType (hH 0)
        (isAlgebraicallyBounded_range_orderedProduct_of_finiteType
          (fun j : Fin m => H j.succ) (fun j => hH j.succ))).mono ?_
      rintro _ ⟨x, rfl⟩
      refine ⟨(x 0 : rationalPoints G), (x 0).property,
        RelativeRoot.CentralExtension.orderedProduct (fun j : Fin m => (H j.succ).subtype)
          (fun j => x j.succ), ⟨_, rfl⟩, ?_⟩
      simp only [RelativeRoot.CentralExtension.orderedProduct, List.ofFn_succ,
        List.prod_cons, Subgroup.coe_subtype]

end Groups

end Langlands.GroupScheme
