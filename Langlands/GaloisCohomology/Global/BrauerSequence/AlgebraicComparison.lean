import Langlands.GaloisCohomology.Global.BrauerSequence.FiniteComparison

/-! # Algebraic Brauer classes and localization in the cochain model -/

noncomputable section

universe u

namespace Langlands.GaloisCohomology

open CategoryTheory ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

section Embedding

variable (K F S T : Type u) [Field K] [Field F] [Field S] [Field T]
  [Algebra K F] [Algebra K S] [Algebra F T] [Algebra K T] [IsScalarTower K F T]
  [IsSepClosure K S] [IsSepClosure F T]
  (j : S →ₐ[K] T)

/-- Restriction of the unit cohomology in the cochain model along a compatible
embedding of separable closures. -/
def unitsRestrictionForEmbedding (n : ℕ) :
    cohomology (unitsModule K S) n →+ cohomology (unitsModule F T) n := by
  let : Algebra S T := j.toRingHom.toAlgebra
  let : IsScalarTower K S T := IsScalarTower.of_algHom j
  exact (map (BrauerComparison.krullRestriction K F S T)
    (underlyingHom _ (BrauerComparison.continuousUnitRestrictionCoefficients K F S T)) n).hom.toAddMonoidHom

/-- The restriction of a degree-two unit class along `j` corresponds to algebraic Brauer scalar extension. -/
theorem unitsRestrictionForEmbedding_brauerEquiv (b : BrauerGroup.{u, u} K) :
    unitsRestrictionForEmbedding K F S T j 2 (brauerEquiv K S b) =
      brauerEquiv F T (Brauer.scalarExtension F b) := by
  let : Algebra S T := j.toRingHom.toAlgebra
  let : IsScalarTower K S T := IsScalarTower.of_algHom j
  have h := congrArg (fun f => f.hom (brauerEquiv K S b)) (isoContinuousCohomology_naturality
    (BrauerComparison.krullRestriction K F S T)
    (BrauerComparison.continuousUnitRestrictionCoefficients K F S T) 2)
  change unitsModuleContinuousEquiv F T 2 (unitsRestrictionForEmbedding K F S T j 2 (brauerEquiv K S b)) =
    BrauerComparison.continuousUnitRestriction K F S T 2
      (unitsModuleContinuousEquiv K S 2 (brauerEquiv K S b)) at h
  apply (unitsModuleContinuousEquiv F T 2).injective
  rw [h, unitsModuleContinuousEquiv_brauerEquiv, unitsModuleContinuousEquiv_brauerEquiv,
    BrauerComparison.brauerContinuousEquiv_scalarExtension K F S T]

private theorem unitsRestrictionForEmbedding_eq_map
    (f : Rep.res (decompositionHom F j : Gal(T/F) →* Gal(S/K)) (unitsModule K S) ⟶ unitsModule F T)
    (hf : ∀ x : Additive Sˣ, (f.hom x).toMul.val = j x.toMul.val)
    (n : ℕ) (a : cohomology (unitsModule K S) n) :
    unitsRestrictionForEmbedding K F S T j n a = (map (decompositionHom F j) f n).hom a := by
  let : Algebra S T := j.toRingHom.toAlgebra
  let : IsScalarTower K S T := IsScalarTower.of_algHom j
  have hg : BrauerComparison.krullRestriction K F S T = decompositionHom F j := by
    apply ContinuousMonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro x
    apply j.injective
    calc
      _ = σ (j x) := (σ.restrictScalars K).restrictNormal_commutes S x
      _ = _ := (decompositionHom_apply j σ x).symm
  exact congrArg (fun g => g.hom a) (map_congr
    (underlyingHom _ (BrauerComparison.continuousUnitRestrictionCoefficients K F S T)) f hg
    (fun x => Additive.toMul.injective (Units.ext (hf x).symm)) n)

end Embedding

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω)

/-- Finite localization of an algebraic Brauer class is extension to the actual completion. -/
theorem brauerLocalization_brauerEquiv (v : HeightOneSpectrum (𝓞 K)) (b : BrauerGroup.{u, u} K) :
    brauerLocalization ι v 2 (brauerEquiv K Ω b) =
      brauerEquiv (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))
        (Brauer.scalarExtension (v.adicCompletion K) b) := by
  rw [← unitsRestrictionForEmbedding_brauerEquiv K (v.adicCompletion K) Ω
    (AlgebraicClosure (v.adicCompletion K)) (ι.finite v),
    unitsRestrictionForEmbedding_eq_map _ _ _ _ _ (unitsLocalHom ι v)
      (unitsLocalHom_hom_apply ι v)]
  rfl

/-- Infinite localization of an algebraic Brauer class is extension to the actual completion. -/
theorem realBrauerLocalization_brauerEquiv (w : InfinitePlace K) (b : BrauerGroup.{u, u} K) :
    realBrauerLocalization ι w 2 (brauerEquiv K Ω b) =
      brauerEquiv w.Completion (AlgebraicClosure w.Completion) (Brauer.scalarExtension w.Completion b) := by
  rw [← unitsRestrictionForEmbedding_brauerEquiv K w.Completion Ω (AlgebraicClosure w.Completion)
    (ι.infinite w), unitsRestrictionForEmbedding_eq_map _ _ _ _ _ (realUnitsLocalHom ι w) (fun _ => rfl)]
  rfl

/-- The finite invariant of an algebraic Brauer class is the local Brauer invariant of its extension. -/
theorem localInvariant_brauerEquiv (v : HeightOneSpectrum (𝓞 K)) (b : BrauerGroup.{u, u} K) :
    letI := Langlands.Global.FiniteCompletion.valuativeRel v
    letI := Langlands.Global.FiniteCompletion.isNonarchimedeanLocalField v
    localInvariant ι v (brauerEquiv K Ω b) =
      ClassFieldTheory.Local.localBrauerInvariant (v.adicCompletion K)
        (Brauer.scalarExtension (v.adicCompletion K) b) := by
  rw [localInvariant_apply, brauerLocalization_brauerEquiv, finiteInvariant,
    Local.invariant_brauerEquiv]

end Langlands.GaloisCohomology
