/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius

/-!
# The Galois action on a base-changed group scheme preserves the group law

Let `A` be a group scheme over a field `K` and `A_{K̄} = A ×_K K̄` its base change to the
algebraic closure, with the base-changed group law. For a `K`-algebra endomorphism `σ` of `K̄`,
the map `σ_A = 𝟙 × Spec σ` of `A_{K̄}` (`AlgebraicGeometry.Scheme.Hom.geometricFiberGaloisMap`)
lies over `Spec σ` and is compatible with the group laws: it is a homomorphism of group schemes
semilinear over `Spec σ` (`AlgebraicGeometry.SemilinearGrpHom`).

## Main definitions

- `AlgebraicGeometry.Scheme.geometricFiberGaloisGrpHom`: `σ_A` as a semilinear homomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry.Scheme

variable {K : Type u} [Field K] (A : Over (Spec (.of K))) [GrpObj A]


/-- **The Galois action on a base-changed group scheme preserves the group law.** For a group
scheme `A` over `K` and `σ ∈ Gal(K̄ / K)` (or any `K`-endomorphism of `K̄`), the automorphism
`σ_A = 𝟙 × Spec σ` of `A_{K̄} = A ×_K K̄` lies over `Spec σ` and satisfies
`μ ∘ (σ_A ×_σ σ_A) = σ_A ∘ μ` for the base-changed group law `μ`. Applied to the Jacobian `J₀`
of `AlgebraicGeometry.exists_jacobian_galoisAction`, this is the clause of
`proposition-jacobian-over-ground-field--5` that `σ_J` preserves the group laws.
(blueprint: `proposition-jacobian-over-ground-field--5`) -/
noncomputable def geometricFiberGaloisGrpHom (σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) :
    SemilinearGrpHom (S := Spec (.of (AlgebraicClosure K)))
      (Scheme.specAlgebraicClosureMap σ).left (baseChangeAlgebraicClosure A)
      (baseChangeAlgebraicClosure A) where
  hom := A.hom.geometricFiberGaloisMap σ
  w := A.hom.geometricFiberGaloisMap_comp_geometricFiberToAlgebraicClosure σ
  mul_comp := by
    have ha : A.hom.geometricFiberGaloisMap σ ≫
        pullback.fst A.hom (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) =
          pullback.fst A.hom (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) :=
      A.hom.geometricFiberGaloisMap_comp_geometricFiberProj σ
    have hb : A.hom.geometricFiberGaloisMap σ ≫
        pullback.snd A.hom (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) =
          pullback.snd A.hom (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) ≫
            (Scheme.specAlgebraicClosureMap σ).left :=
      A.hom.geometricFiberGaloisMap_comp_geometricFiberToAlgebraicClosure σ
    have hμ : μ[baseChangeAlgebraicClosure A] = Functor.LaxMonoidal.μ (Over.pullback _) A A ≫
        (Over.pullback _).map μ[A] := rfl
    rw [hμ, Over.comp_left]
    apply pullback.hom_ext
    · simp only [Category.assoc, ha, Over.pullback_map_left, pullback.lift_fst]
      simp only [← Category.assoc]
      congr 1
      apply Over.tensorObj_ext
      · simp only [Category.assoc, Over.μ_pullback_left_fst_fst, pullback.map,
          pullback.lift_fst_assoc, ha]
      · simp only [Category.assoc, Over.μ_pullback_left_fst_snd, pullback.map,
          pullback.lift_snd_assoc, ha]
    · simp only [Category.assoc, hb, Over.pullback_map_left, pullback.lift_snd_assoc,
        pullback.lift_snd, reassoc_of% (Over.μ_pullback_left_snd A A), Over.μ_pullback_left_snd,
        pullback.map]

/-- The underlying morphism of `AlgebraicGeometry.Scheme.geometricFiberGaloisGrpHom` is
`σ_A = 𝟙 × Spec σ`. -/
@[simp]
theorem geometricFiberGaloisGrpHom_hom (σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) :
    (geometricFiberGaloisGrpHom A σ).hom = A.hom.geometricFiberGaloisMap σ :=
  rfl

end AlgebraicGeometry.Scheme
