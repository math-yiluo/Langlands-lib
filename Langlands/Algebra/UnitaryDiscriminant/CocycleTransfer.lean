import Langlands.Algebra.UnitaryDiscriminant.Class

/-! # Restricting a unitary determinant factor set and extending its coefficients -/

noncomputable section

universe u v

open Matrix

namespace Langlands.UnitaryDiscriminant

open LinearAlgebra.UnitaryTwistedDescent

section Transfer

variable {F M : Type u} {F' M' : Type v} [Field F] [Field M] [Algebra F M]
  [Field F'] [Field M'] [Algebra F' M']
  {I : Type} [Fintype I] [DecidableEq I]
  (f : M →+* M') (ρ : Gal(M'/F') →* Gal(M/F))
  (hcompat : ∀ (g : Gal(M'/F')) (x : M), g (f x) = f (ρ g x))

/-- Restrict the matrix lifts along `ρ` and extend their coefficients along `f`. -/
def transferredLift (P : Gal(M/F) → GL I M) (g : Gal(M'/F')) : GL I M' :=
  GeneralLinearGroup.map f (P (ρ g))

/-- Restrict both arguments of the scalar factor and extend its values to the new field. -/
def transferredFactor (c : Gal(M/F) → Gal(M/F) → Mˣ) (g h : Gal(M'/F')) : M'ˣ :=
  Units.map f.toMonoidHom (c (ρ g) (ρ h))

include hcompat

omit [Fintype I] [DecidableEq I] in
private theorem map_matrix_aut (g : Gal(M'/F')) (X : Matrix I I M) :
    (X.map f).map g = (X.map (ρ g)).map f := by
  ext i j
  exact hcompat g (X i j)

private theorem map_GL_aut (g : Gal(M'/F')) (X : GL I M) :
    GeneralLinearGroup.map (g : M' →+* M') (GeneralLinearGroup.map f X) =
      GeneralLinearGroup.map f (GeneralLinearGroup.map (ρ g : M →+* M) X) := by
  apply Units.ext
  exact map_matrix_aut f ρ hcompat g (X : Matrix I I M)

private theorem map_twistGL {H : Subgroup (M ≃ₐ[F] M)} (g : Gal(M'/F')) (X : GL I M) :
    twistGL (H.comap ρ) g (GeneralLinearGroup.map f X) =
      GeneralLinearGroup.map f (twistGL H (ρ g) X) := by
  by_cases hg : ρ g ∈ H
  · rw [twistGL_of_mem (show g ∈ H.comap ρ from hg), twistGL_of_mem hg, map_GL_aut f ρ hcompat]
  · rw [twistGL_of_not_mem (show g ∉ H.comap ρ from hg), twistGL_of_not_mem hg,
      map_GL_aut f ρ hcompat, invTranspose_map]

private theorem map_unit_smul (g : Gal(M'/F')) (a : Mˣ) :
    g • Units.map f.toMonoidHom a = Units.map f.toMonoidHom (ρ g • a) := by
  apply Units.ext
  exact hcompat g (a : M)

/-- The extended lifts satisfy the projective lift identity for the pulled-back center stabilizer. -/
theorem transferredLift_mul {H : Subgroup (M ≃ₐ[F] M)} (P : Gal(M/F) → GL I M)
    (c : Gal(M/F) → Gal(M/F) → Mˣ)
    (hc : ∀ g h, P g * twistGL H g (P h) = GeneralLinearGroup.scalar I (c g h) * P (g * h))
    (g h : Gal(M'/F')) :
    transferredLift f ρ P g * twistGL (H.comap ρ) g (transferredLift f ρ P h) =
      GeneralLinearGroup.scalar I (transferredFactor f ρ c g h) * transferredLift f ρ P (g * h) := by
  rw [transferredLift, transferredLift, map_twistGL f ρ hcompat, ← map_mul, hc,
    map_mul, GeneralLinearGroup.map_scalar, transferredLift, map_mul ρ]
  rfl

/-- Entrywise extension commutes with the restricted semilinear action of the lifts. -/
theorem twistedAct_transferredLift {H : Subgroup (M ≃ₐ[F] M)}
    (P : Gal(M/F) → GL I M) (g : Gal(M'/F')) (X : Matrix I I M) :
    twistedAct (H.comap ρ) (transferredLift f ρ P) g (X.map f) =
      (twistedAct H P (ρ g) X).map f := by
  rw [twistedAct_eq, twistedAct_eq]
  have hcoeff : coeffTwist (H.comap ρ) g (X.map f) = (coeffTwist H (ρ g) X).map f := by
    by_cases hg : ρ g ∈ H
    · rw [coeffTwist_of_mem (show g ∈ H.comap ρ from hg), coeffTwist_of_mem hg,
        map_matrix_aut f ρ hcompat]
    · rw [coeffTwist_of_not_mem (show g ∉ H.comap ρ from hg), coeffTwist_of_not_mem hg,
        map_matrix_aut f ρ hcompat]
      rfl
  rw [hcoeff, transferredLift, ← map_inv]
  change ((P (ρ g) : GL I M) : Matrix I I M).map f * (coeffTwist H (ρ g) X).map f *
      (((P (ρ g))⁻¹ : GL I M) : Matrix I I M).map f = _
  simp only [Matrix.map_mul]

/-- Restriction of the determinant formula commutes with compatible coefficient extension. -/
theorem detCocycle_transferredLift {H : Subgroup (M ≃ₐ[F] M)}
    (P : Gal(M/F) → GL I M) (c : Gal(M/F) → Gal(M/F) → Mˣ) (m : ℕ)
    (g h : Gal(M'/F')) :
    detCocycle (H.comap ρ) (transferredLift f ρ P) (transferredFactor f ρ c) m g h =
      transferredFactor f ρ (detCocycle H P c m) g h := by
  have hdet :
      g • GeneralLinearGroup.det (transferredLift f ρ P h) =
        Units.map f.toMonoidHom (ρ g • GeneralLinearGroup.det (P (ρ h))) := by
    rw [transferredLift, GeneralLinearGroup.map_det]
    exact map_unit_smul f ρ hcompat g _
  rw [transferredFactor]
  by_cases hg : ρ g ∈ H
  · rw [detCocycle_of_mem _ _ _ (show g ∈ H.comap ρ from hg), detCocycle_of_mem _ _ _ hg,
      transferredFactor, map_pow]
  · by_cases hh : ρ h ∈ H
    · rw [detCocycle_of_not_mem_of_mem _ _ _ (show g ∉ H.comap ρ from hg)
        (show h ∈ H.comap ρ from hh), detCocycle_of_not_mem_of_mem _ _ _ hg hh,
        transferredFactor, hdet, map_mul, map_pow]
    · rw [detCocycle_of_not_mem_of_not_mem _ _ _ (show g ∉ H.comap ρ from hg)
        (show h ∉ H.comap ρ from hh), detCocycle_of_not_mem_of_not_mem _ _ _ hg hh,
        transferredFactor, hdet, map_mul, map_mul, map_pow, map_pow]
      congr 1
      apply Units.ext
      simp

end Transfer

end Langlands.UnitaryDiscriminant
