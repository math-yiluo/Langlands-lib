import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsInnerCocycle
import Langlands.GroupScheme.SimplyConnected.OuterTypeAQuadraticExtension
import Langlands.LinearAlgebra.SpecialLinearInverseTranspose

/-! # The actual quadratic star field lies in the special-linear cocycle cover -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SpecialLinearTitsCocycle

open Matrix
open Langlands.LinearAlgebra.SpecialLinearInverseTranspose

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {G : GroupScheme (Spec (CommRingCat.of K))} {n : ℕ}
  (E : LocalGroupIso (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) G
    (cover K L))

/-- An outer representative of the discrepancy, on every test and cover point. -/
def HasOuterDiscrepancy (σ : L ≃ₐ[K] L) (X : GeneralLinearGroup (Fin (n + 1)) L) : Prop :=
  ∀ (Z : Over (Spec (CommRingCat.of K))) (a : Z ⟶ cover K L)
    (g : SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)),
    SpecialLinearGroup.toGL (discrepancy E σ a g) =
      GeneralLinearGroup.map (coefficients a) X *
        SpecialLinearGroup.toGL (inverseTranspose g) *
        (GeneralLinearGroup.map (coefficients a) X)⁻¹

omit E in
/-- Inverse transpose commutes with any coefficient homomorphism. -/
theorem inverseTranspose_map {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (g : SpecialLinearGroup (Fin (n + 1)) A) :
    inverseTranspose (SpecialLinearGroup.map f g) =
      SpecialLinearGroup.map f (inverseTranspose g) := by
  apply Subtype.ext
  change (((SpecialLinearGroup.map f g)⁻¹ : SpecialLinearGroup (Fin (n + 1)) B) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) B).transpose = _
  rw [← map_inv]
  rfl

/-- In rank at least two, the identity discrepancy cannot have an outer representative. -/
theorem not_hasOuterDiscrepancy_one (hn : 2 ≤ n)
    (X : GeneralLinearGroup (Fin (n + 1)) L) : ¬ HasOuterDiscrepancy E 1 X := by
  intro hX
  apply not_inner_fin hn X
  intro g
  let f := (baseCoefficientsEquiv (K := K) (L := L)).toRingHom
  have h := hX _ (𝟙 _) (SpecialLinearGroup.map f g)
  rw [discrepancy_one, coefficients_id, inverseTranspose_map] at h
  have hm (z : SpecialLinearGroup (Fin (n + 1)) L) :
      SpecialLinearGroup.toGL (SpecialLinearGroup.map f z) =
        GeneralLinearGroup.map f (SpecialLinearGroup.toGL z) := Units.ext rfl
  rw [hm, hm, ← map_inv, ← map_mul, ← map_mul] at h
  apply Units.ext
  ext i j
  apply (baseCoefficientsEquiv (K := K) (L := L)).injective
  exact congrArg (fun z : GeneralLinearGroup (Fin (n + 1)) Γ((cover K L).left, ⊤) =>
    z i j) h.symm

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)

/-- The actual star action determines inner or outer all-test discrepancies for
every absolute Galois lift of an automorphism of the cover. -/
def HasStarDiscrepancy (ι₀ : L →ₐ[K] SeparableClosure K)
    (x : (L ≃ₐ[K] L) → GeneralLinearGroup (Fin (n + 1)) L) : Prop :=
  ∀ (σ : L ≃ₐ[K] L) (τ : SeparableClosure K ≃ₐ[K] SeparableClosure K),
    (∀ y, τ (ι₀ y) = ι₀ (σ y)) →
      ((∀ v, d.star τ v = v) → HasInnerDiscrepancy E σ (x σ)) ∧
      ((∃ v, d.star τ v ≠ v) → HasOuterDiscrepancy E σ (x σ))

/-- Every absolute Galois automorphism fixing the cocycle cover has trivial star action. -/
theorem HasStarDiscrepancy.star_trivial_of_fixes_cover
    {ι₀ : L →ₐ[K] SeparableClosure K}
    {x : (L ≃ₐ[K] L) → GeneralLinearGroup (Fin (n + 1)) L}
    (hshape : HasStarDiscrepancy E d ι₀ x) (hn : 2 ≤ n)
    (τ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (hτ : ∀ y, τ (ι₀ y) = ι₀ y) : ∀ v, d.star τ v = v := by
  by_contra hstar
  push Not at hstar
  exact not_hasOuterDiscrepancy_one E hn (x 1) ((hshape 1 τ hτ).2 hstar)

/-- The actual star field is a subfield of the image of the cocycle cover. -/
theorem HasStarDiscrepancy.starField_le_cover
    {ι₀ : L →ₐ[K] SeparableClosure K}
    {x : (L ≃ₐ[K] L) → GeneralLinearGroup (Fin (n + 1)) L}
    (hshape : HasStarDiscrepancy E d ι₀ x) (hn : 2 ≤ n) :
    d.starField ≤ ι₀.fieldRange := by
  have hle : ι₀.fieldRange.fixingSubgroup ≤ d.starKernel := by
    intro τ hτ
    apply hshape.star_trivial_of_fixes_cover E d hn τ
    intro y
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ (ι₀ y) ⟨y, rfl⟩
  rw [← InfiniteGalois.fixedField_fixingSubgroup ι₀.fieldRange]
  exact IntermediateField.fixedField_le hle

omit E in
/-- The canonical embedding of the actual star field into a cover containing it. -/
def starFieldToCover (ι₀ : L →ₐ[K] SeparableClosure K) (hle : d.starField ≤ ι₀.fieldRange) :
    d.starField →ₐ[K] L :=
  ι₀.equivFieldRange.symm.toAlgHom.comp (IntermediateField.inclusion hle)

omit E in
/-- The embedding into the cover retains the actual star-field inclusion in the separable closure. -/
theorem embedding_starFieldToCover (ι₀ : L →ₐ[K] SeparableClosure K)
    (hle : d.starField ≤ ι₀.fieldRange) (z : d.starField) :
    ι₀ (starFieldToCover d ι₀ hle z) = (z : SeparableClosure K) :=
  congrArg Subtype.val (ι₀.equivFieldRange.apply_symm_apply (IntermediateField.inclusion hle z))

omit E in
/-- A lifted cover automorphism has trivial star action exactly when it fixes
the embedded actual star field pointwise. -/
theorem star_trivial_iff_fixes_starField_cover
    (ι₀ : L →ₐ[K] SeparableClosure K) (hle : d.starField ≤ ι₀.fieldRange)
    (σ : L ≃ₐ[K] L) (τ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (hlift : ∀ y, τ (ι₀ y) = ι₀ (σ y)) :
    (∀ v, d.star τ v = v) ↔ ∀ z : d.starField,
      σ (starFieldToCover d ι₀ hle z) = starFieldToCover d ι₀ hle z := by
  rw [← d.fixes_starField_iff τ]
  constructor
  · intro h z
    apply ι₀.injective
    change ι₀ (σ (starFieldToCover d ι₀ hle z)) = ι₀ (starFieldToCover d ι₀ hle z)
    rw [← hlift, embedding_starFieldToCover]
    exact h z z.property
  · intro h z hz
    let w : d.starField := ⟨z, hz⟩
    change τ (w : SeparableClosure K) = (w : SeparableClosure K)
    rw [← embedding_starFieldToCover d ι₀ hle w, hlift, h]

end SpecialLinearTitsCocycle

namespace TitsIndexData

variable {K : Type u} [Field K] {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] {d : TitsIndexData G}

/-- A nontrivial reversal star image requires at least two simple vertices. -/
theorem StarImagePair.two_le {n : ℕ} {e : d.Vertex ≃ Fin n}
    (hstar : d.StarImagePair e Fin.revPerm) : 2 ≤ n := by
  by_contra hn
  apply hstar.1
  apply Equiv.ext
  intro i
  apply Fin.ext
  change n - (i.val + 1) = i.val
  have := i.isLt
  omega

end TitsIndexData

end Langlands.GroupScheme
