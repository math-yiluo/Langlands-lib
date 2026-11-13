import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleAlgebra
import Langlands.LinearAlgebra.SpecialLinearNormalizedCocycle

/-! # Inner representatives of the actual special-linear Galois discrepancy -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinearTitsCocycle

open Matrix

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {G : GroupScheme (Spec (CommRingCat.of K))} {n : ℕ}
  (E : LocalGroupIso (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) G
    (cover K L))

/-- An inner representative of the discrepancy, on every cover point of every test. -/
def HasInnerDiscrepancy (σ : L ≃ₐ[K] L) (X : GeneralLinearGroup (Fin (n + 1)) L) : Prop :=
  ∀ (Z : Over (Spec (CommRingCat.of K))) (a : Z ⟶ cover K L)
    (g : SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)),
    SpecialLinearGroup.toGL (discrepancy E σ a g) =
      GeneralLinearGroup.map (coefficients a) X * SpecialLinearGroup.toGL g *
        (GeneralLinearGroup.map (coefficients a) X)⁻¹

/-- The identity discrepancy is represented by the identity matrix. -/
theorem hasInnerDiscrepancy_one : HasInnerDiscrepancy E 1 1 := by
  intro Z a g
  simp

/-- Products of inner discrepancies are represented by the semilinear matrix product. -/
theorem HasInnerDiscrepancy.mul {σ τ : L ≃ₐ[K] L}
    {X Y : GeneralLinearGroup (Fin (n + 1)) L}
    (hX : HasInnerDiscrepancy E σ X) (hY : HasInnerDiscrepancy E τ Y) :
    HasInnerDiscrepancy E (σ * τ) (X * GeneralLinearGroup.map σ.toRingHom Y) := by
  intro Z a g
  rw [discrepancy_mul, hX, hY, coefficients_coverAut]
  have hmap : GeneralLinearGroup.map ((coefficients a).comp σ.toRingHom) Y =
      GeneralLinearGroup.map (coefficients a) (GeneralLinearGroup.map σ.toRingHom Y) := rfl
  rw [hmap, map_mul]
  group

/-- The coefficient homomorphism of the identity cover point is a ring equivalence. -/
def baseCoefficientsEquiv : L ≃+* Γ((cover K L).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of L)).symm.commRingCatIsoToRingEquiv

@[simp] theorem coefficients_id :
    coefficients (𝟙 (cover K L)) = (baseCoefficientsEquiv (K := K) (L := L)).toRingHom := by
  ext x
  simp [coefficients, baseCoefficientsEquiv]
  rfl

/-- Equal all-test inner discrepancies give the same conjugation on `SL(L)`. -/
theorem HasInnerDiscrepancy.conjugation_eq {σ : L ≃ₐ[K] L}
    {X Y : GeneralLinearGroup (Fin (n + 1)) L}
    (hX : HasInnerDiscrepancy E σ X) (hY : HasInnerDiscrepancy E σ Y)
    (g : SpecialLinearGroup (Fin (n + 1)) L) :
    X * SpecialLinearGroup.toGL g * X⁻¹ = Y * SpecialLinearGroup.toGL g * Y⁻¹ := by
  let f := (baseCoefficientsEquiv (K := K) (L := L)).toRingHom
  have h := (hX _ (𝟙 _) (SpecialLinearGroup.map f g)).symm.trans
    (hY _ (𝟙 _) (SpecialLinearGroup.map f g))
  rw [coefficients_id] at h
  have htoGL : SpecialLinearGroup.toGL (SpecialLinearGroup.map f g) =
      GeneralLinearGroup.map f (SpecialLinearGroup.toGL g) := Units.ext rfl
  rw [htoGL, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul] at h
  apply Units.ext
  ext i j
  apply (baseCoefficientsEquiv (K := K) (L := L)).injective
  exact congrArg (fun z : GeneralLinearGroup (Fin (n + 1)) Γ((cover K L).left, ⊤) =>
    z i j) h

/-- Inner representatives of a subgroup of discrepancies obey the projective cocycle law. -/
theorem projective_cocycle (H : Subgroup (L ≃ₐ[K] L))
    (x : H → GeneralLinearGroup (Fin (n + 1)) L)
    (hx : ∀ σ, HasInnerDiscrepancy E σ.val (x σ))
    (σ τ : H) (g : SpecialLinearGroup (Fin (n + 1)) L) :
    x (σ * τ) * SpecialLinearGroup.toGL g * (x (σ * τ))⁻¹ =
      (x σ * GeneralLinearGroup.map σ.val.toRingHom (x τ)) *
        SpecialLinearGroup.toGL g *
        (x σ * GeneralLinearGroup.map σ.val.toRingHom (x τ))⁻¹ :=
  (hx (σ * τ)).conjugation_eq E ((hx σ).mul E (hx τ)) g

/-- If the local coordinates of a point are independent of the cover point,
every discrepancy fixes those coordinates. -/
theorem discrepancy_fixes_of_coordinates {Z : Over (Spec (CommRingCat.of K))}
    (z : Z ⟶ G.X) (g : SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤))
    (hg : ∀ a : Z ⟶ cover K L,
      SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z ((E.toFun a).symm z) = g)
    (σ : L ≃ₐ[K] L) (a : Z ⟶ cover K L) : discrepancy E σ a g = g := by
  have hz : (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z).symm g =
      (E.toFun (a ≫ coverAut K L σ)).symm z := by
    rw [← hg (a ≫ coverAut K L σ), MulEquiv.symm_apply_apply]
  unfold discrepancy
  rw [hz, MulEquiv.apply_symm_apply, hg]

/-- An inner representative centralizes every cover-independent coordinate matrix. -/
theorem HasInnerDiscrepancy.commutes_of_coordinates {σ : L ≃ₐ[K] L}
    {X : GeneralLinearGroup (Fin (n + 1)) L} (hX : HasInnerDiscrepancy E σ X)
    {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K L)
    (z : Z ⟶ G.X) (g : SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤))
    (hg : ∀ b : Z ⟶ cover K L,
      SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z ((E.toFun b).symm z) = g) :
    GeneralLinearGroup.map (coefficients a) X * SpecialLinearGroup.toGL g =
      SpecialLinearGroup.toGL g * GeneralLinearGroup.map (coefficients a) X := by
  have h := hX Z a g
  rw [discrepancy_fixes_of_coordinates E z g hg σ a] at h
  exact mul_inv_eq_iff_eq_mul.mp h.symm


/-- The subgroup acts on coefficients through its actual field automorphisms. -/
def subgroupRingAction (H : Subgroup (L ≃ₐ[K] L)) : H →* (L ≃+* L) where
  toFun σ := σ.val.toRingEquiv
  map_one' := by ext a; rfl
  map_mul' σ τ := by ext a; rfl

open Langlands.LinearAlgebra.SpecialLinearNormalizedCocycle

/-- Dividing an inner representative by its coordinate eigenvalue preserves the
all-test discrepancy formula. -/
theorem HasInnerDiscrepancy.normalize {σ : L ≃ₐ[K] L}
    {X : GeneralLinearGroup (Fin (n + 1)) L} (hX : HasInnerDiscrepancy E σ X)
    (p : Fin (n + 1)) (hp : PreservesCoordinate p X) :
    HasInnerDiscrepancy E σ (normalize X p hp) := by
  intro Z a g
  rw [map_normalize_conjugate]
  exact hX Z a g

/-- A normalized representative of the identity discrepancy is the identity. -/
theorem normalized_identity {X : GeneralLinearGroup (Fin (n + 1)) L}
    (hX : HasInnerDiscrepancy E 1 X) (p : Fin (n + 1))
    (hp : PreservesCoordinate p X) : normalize X p hp = 1 := by
  apply Langlands.LinearAlgebra.SpecialLinearConjugation.eq_of_conjugation_eq_of_entry_eq_one
    _ _ p (normalize_entry _ _ _) (by simp)
  exact (hX.normalize E p hp).conjugation_eq E (hasInnerDiscrepancy_one E)

/-- The normalized inner representatives satisfy an honest semilinear matrix cocycle law. -/
theorem normalized_cocycle (H : Subgroup (L ≃ₐ[K] L))
    (x : H → GeneralLinearGroup (Fin (n + 1)) L)
    (hx : ∀ σ, HasInnerDiscrepancy E σ.val (x σ))
    (p : Fin (n + 1)) (hp : ∀ σ, PreservesCoordinate p (x σ))
    (σ τ : H) :
    normalize (x (σ * τ)) p (hp (σ * τ)) =
      normalize (x σ) p (hp σ) *
        GeneralLinearGroup.map σ.val.toRingHom (normalize (x τ) p (hp τ)) :=
  normalize_cocycle (subgroupRingAction H) x p hp (projective_cocycle E H x hx) σ τ

end Langlands.GroupScheme.SpecialLinearTitsCocycle
