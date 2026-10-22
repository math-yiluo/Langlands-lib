import Langlands.ClassFieldTheory.Local.Cohomology
import Langlands.Galois.ClosureRestriction

/-! # Actual absolute cohomology restriction along explicit closure embeddings -/

noncomputable section

open CategoryTheory

namespace Langlands.ClassFieldTheory.Local

open Langlands.GaloisRepresentation

universe u u₁ v₁

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- The actual closure-unit coefficient inclusion for an explicit closure embedding. -/
def absoluteRestrictionAlongClosureCoefficients
    (ι : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    TopRep.res (restrictionAlongClosure ι) (absoluteUnits K) ⟶ absoluteUnits L := by
  letI : Algebra (AlgebraicClosure K) (AlgebraicClosure L) := ι.toAlgebra
  exact absoluteRestrictionCoefficients K L

/-- The actual continuous cohomology map for an explicit compatible closure embedding. -/
def absoluteRestrictionAlongClosure
    (ι : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) (n : ℕ) :
    absoluteCohomology K n ⟶ absoluteCohomology L n :=
  ContinuousCohomology.map (restrictionAlongClosure ι)
    (absoluteRestrictionAlongClosureCoefficients ι) n

@[simp]
theorem absoluteRestrictionAlongClosureCoefficients_apply
    (ι : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (x : Additive (AlgebraicClosure K)ˣ) :
    ((absoluteRestrictionAlongClosureCoefficients ι) x).toMul.val = ι x.toMul.val := rfl

/-- On group restriction, precomposing the closure embedding with an automorphism
composes the corresponding contravariant group maps. -/
theorem restrictionAlongClosure_comp_automorphism
    (ι : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (c : Field.absoluteGaloisGroup K) :
    restrictionAlongClosure (ι.comp c.toAlgHom) =
      (restrictionAlongClosure c.toAlgHom).comp (restrictionAlongClosure ι) := by
  apply ContinuousMonoidHom.ext
  intro g
  apply AlgEquiv.ext
  intro x
  apply (ι.comp c.toAlgHom).injective
  change (ι.comp c.toAlgHom)
      (AlgEquiv.toRingEquiv (restrictionAlongClosure (ι.comp c.toAlgHom) g) x) =
    ι (AlgEquiv.toRingEquiv c
      (AlgEquiv.toRingEquiv (restrictionAlongClosure c.toAlgHom
        (restrictionAlongClosure ι g)) x))
  rw [restrictionAlongClosure_commutes]
  change AlgEquiv.toRingEquiv g (ι (AlgEquiv.toRingEquiv c x)) =
    ι (c.toAlgHom (AlgEquiv.toRingEquiv (restrictionAlongClosure c.toAlgHom
      (restrictionAlongClosure ι g)) x))
  rw [restrictionAlongClosure_commutes, restrictionAlongClosure_commutes]
  rfl

private theorem continuousMap_congr
    {k : Type u₁} {G H : Type v₁} [Ring k] [TopologicalSpace k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {X : TopRep k G} {Y : TopRep k H} {φ ψ : H →ₜ* G}
    (f : TopRep.res φ X ⟶ Y) (g : TopRep.res ψ X ⟶ Y)
    (h : φ = ψ) (hf : ∀ x : X, f x = g x) (n : ℕ) :
    ContinuousCohomology.map (X := X) φ f n =
      ContinuousCohomology.map (X := X) ψ g n := by
  subst ψ
  have hfg : f = g := by
    ext x
    exact hf x
  rw [hfg]

/-- Precomposing a closure embedding by a source automorphism factors the actual
cohomology map through that automorphism's actual map. -/
theorem absoluteRestrictionAlongClosure_comp_automorphism
    (ι : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (c : Field.absoluteGaloisGroup K) (n : ℕ) :
    absoluteRestrictionAlongClosure (ι.comp c.toAlgHom) n =
      absoluteRestrictionAlongClosure c.toAlgHom n ≫
        absoluteRestrictionAlongClosure ι n := by
  unfold absoluteRestrictionAlongClosure
  rw [← ContinuousCohomology.map_comp]
  apply continuousMap_congr _ _ (restrictionAlongClosure_comp_automorphism ι c)
  intro x
  apply Units.ext
  rfl

/-- The explicit embedding given by the comparison automorphism is the second embedding. -/
theorem closureChange_comp_embedding
    (ι κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    ι.comp (closureChange ι κ).toAlgHom = κ := by
  ext x
  exact closureChange_spec ι κ x

/-- The second closure embedding factors through the comparison automorphism
and the first embedding, on actual continuous cohomology in every degree. -/
theorem absoluteRestrictionAlongClosure_change
    (ι κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) (n : ℕ) :
    absoluteRestrictionAlongClosure κ n =
      absoluteRestrictionAlongClosure (closureChange ι κ).toAlgHom n ≫
        absoluteRestrictionAlongClosure ι n := by
  rw [← absoluteRestrictionAlongClosure_comp_automorphism, closureChange_comp_embedding]

end Langlands.ClassFieldTheory.Local
