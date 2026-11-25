import Langlands.GaloisCohomology.Global.BrauerSequence.Statement
import Langlands.GaloisCohomology.Field.RelativeInflation
import Langlands.ClassFieldTheory.Local.PadicBrauerInvariantComparison
import Langlands.Algebra.BrauerComparison.RegularClass
import Langlands.Global.CompletionPadic
import Langlands.ClassFieldTheory.Global.CohomologyMaps
import Langlands.ClassFieldTheory.Global.IdeleCohomology
import Langlands.ClassFieldTheory.Global.ReciprocityTower
import Langlands.Global.AdelicFunctoriality.LocalDegree

/-!
# Local invariants of inflated classes at the finite places

Let `K` be a number field, `Ω` a separable closure, `ι : PlaceEmbeddings K Ω`, `E ⊆ Ω` a finite Galois
extension of `K` and `v` a finite place of `K`. The embedding `ι.finite v` restricted to `E`
determines a place `w = localPlace ι E v` of `E` above `v` and an embedding `E_w → K̄_v` over `K_v`
(`completionAlgebra`, from `completionEmbeddingOfAlgHom` of
`Langlands/Galois/RestrictedRamification/Localization.lean`).

* `brauerLocalization_unitsInflation`: localizing at `v` a class inflated from
  `H²(Gal(E/K), Eˣ)` is inflating, from `H²(Gal(E_w/K_v), E_wˣ)`, the Library's local component
  `unitsLocalMap v w 2` of the class.
* `finiteInvariant_unitsTowerMap`: for a finite Galois
  extension `L` of `K_v` embedded in `K̄_v`, the local theory's invariant of the inflation of a class
  `b ∈ H²(Gal(L/K_v), Lˣ)` is the relative invariant `I.relative (padicField v) L b` of any local
  invariant family `I` with the arithmetic normalization and compatibility with inflation (the
  Library's `relativeInvariant_eq_localBrauerInvariant`, read through `Br(K_v) ≅ H²`).
* `localInvariant_unitsInflation`: hence the local invariant at `v` of the inflated class is the
  Library's `finiteLocalInvariant v w I`.
-/

namespace Langlands.GaloisCohomology
open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
open Langlands.ClassFieldTheory.Local Langlands.Global.CompletionPadic

universe u

/-- The local Brauer invariant depends on the topology and valuative relation only through their
equality. -/
theorem localBrauerInvariant_congr {F : Type u} [Field F] {T₁ T₂ : TopologicalSpace F}
    {V₁ V₂ : ValuativeRel F} (h₁ : @IsNonarchimedeanLocalField F _ V₁ T₁)
    (h₂ : @IsNonarchimedeanLocalField F _ V₂ T₂) (hT : T₁ = T₂) (hV : V₁ = V₂)
    (x : BrauerGroup.{u, u} F) :
    @localBrauerInvariant F _ V₁ T₁ h₁ x = @localBrauerInvariant F _ V₂ T₂ h₂ x := by
  subst hT hV
  rfl

variable {K : Type u} [Field K] [NumberField K]

/-- The local invariant at a finite place of a class inflated from a finite Galois extension
`L` of `K_v` (embedded in `K̄_v`) is its relative invariant for any local invariant family with the
arithmetic normalization and compatibility with inflation. -/
theorem finiteInvariant_unitsTowerMap (v : HeightOneSpectrum (𝓞 K))
    (L : Type u) [Field L] [Algebra (v.adicCompletion K) L] [FiniteDimensional (v.adicCompletion K) L]
    [IsGalois (v.adicCompletion K) L] [Algebra L (AlgebraicClosure (v.adicCompletion K))]
    [IsScalarTower (v.adicCompletion K) L (AlgebraicClosure (v.adicCompletion K))]
    (I : InvariantFamily.{u, u} (residuePrime v)) (hA : I.ArithmeticNormalization)
    (hInf : I.InflationCompatibility) (b : relativeCohomology (v.adicCompletion K) L 2) :
    finiteInvariant v ((unitsTowerMap (v.adicCompletion K) L
        (AlgebraicClosure (v.adicCompletion K)) 2).hom
      ((isoGroupCohomology (unitsModule (v.adicCompletion K) L) 2).inv.hom b)) =
      I.relative (padicField v) L b := by
  classical
  obtain ⟨A, e, rfl⟩ := BrauerComparison.exists_relativeClass_eq (K := v.adicCompletion K) (L := L) b
  rw [← unitsModuleContinuousEquiv_symm_relativeToContinuous,
    ← BrauerComparison.brauerContinuousEquiv_at_chart (v.adicCompletion K)
      (AlgebraicClosure (v.adicCompletion K)) A L e,
    relativeInvariant_eq_localBrauerInvariant (padicField v) I hA hInf L A e]
  change finiteInvariant v (brauerEquiv _ _ (Langlands.Brauer.classOf A)) = _
  unfold finiteInvariant
  rw [Local.invariant_brauerEquiv]
  exact localBrauerInvariant_congr _ _ (completion_topology_eq v)
    (Langlands.Global.FiniteCompletion.topologicalData_valuativeRel_eq v).symm _

section Inflation

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]

/-- Inflation from a finite Galois level `E ⊆ L` is `isoGroupCohomology⁻¹` followed by the map along
the restriction `Gal(L/K) → Gal(E/K)` (`unitsTowerMap`), for any Galois extension `L / K`. -/
theorem unitsInflation_apply_eq (E : IntermediateField K L) [FiniteDimensional K E]
    [IsGalois K E] (n : ℕ) (a : groupCohomology (unitsModule K E) n) :
    (unitsInflation E n).hom a =
      (unitsTowerMap K E L n).hom ((isoGroupCohomology (unitsModule K E) n).inv.hom a) := by
  apply (unitsModuleContinuousEquiv K L n).injective
  rw [unitsModuleContinuousEquiv_unitsInflation,
    ← unitsModuleContinuousEquiv_symm_relativeToContinuous, LinearEquiv.apply_symm_apply]

end Inflation

noncomputable section Compat

open Langlands.ClassFieldTheory.Global Langlands.Global.AdelicFunctoriality
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

attribute [local instance] Langlands.Global.AdelicFunctoriality.isGalois_adicCompletion
  Langlands.Global.AdelicFunctoriality.FiniteExtension.local_finite

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]
  [NumberField E] (v : HeightOneSpectrum (𝓞 K))

/-- The embedding `E → K̄_v` of `ι`. -/
abbrev placeEmbedding : E →ₐ[K] AlgebraicClosure (v.adicCompletion K) :=
  (ι.finite v).comp E.val

/-- The place of `E` above `v` determined by `ι`. -/
abbrev localPlace : HeightOneSpectrum (𝓞 E) := (placeOfAlgHom (placeEmbedding ι E v)).1

/-- The place of `ι` lies over `v`. -/
instance liesOver_localPlace : (localPlace ι E v).asIdeal.LiesOver v.asIdeal :=
  (placeOfAlgHom (placeEmbedding ι E v)).2

/-- The algebra structure of `K̄_v` over `E_w` given by `ι`. -/
abbrev completionAlgebra : Algebra ((localPlace ι E v).adicCompletion E) (AlgebraicClosure (v.adicCompletion K)) :=
  (completionEmbeddingOfAlgHom (placeEmbedding ι E v)).toRingHom.toAlgebra


omit [IsSepClosure K Ω] [FiniteDimensional K ↥E] [IsGalois K ↥E] in
/-- `K_v → E_w → K̄_v` is a scalar tower for the algebra given by `ι`. -/
theorem isScalarTower_completionAlgebra :
    letI := completionAlgebra ι E v
    IsScalarTower (v.adicCompletion K) ((localPlace ι E v).adicCompletion E)
      (AlgebraicClosure (v.adicCompletion K)) :=
  letI := completionAlgebra ι E v
  IsScalarTower.of_algHom (completionEmbeddingOfAlgHom (placeEmbedding ι E v))

/-- The decomposition homomorphism of the Library at the place of `ι`, as a continuous homomorphism of
the (discrete) finite Galois groups. -/
def localDecompositionHom :
    Gal((localPlace ι E v).adicCompletion E/v.adicCompletion K) →ₜ* Gal(E/K) :=
  ⟨FundamentalClass.decompositionHom v (localPlace ι E v), continuous_of_discreteTopology⟩

/-- The coefficient map `Eˣ → E_wˣ` along `localDecompositionHom`. -/
def localUnitsHom :
    Rep.res (localDecompositionHom ι E v : Gal((localPlace ι E v).adicCompletion E/v.adicCompletion K) →*
        Gal(E/K)) (unitsModule K E) ⟶
      unitsModule (v.adicCompletion K) ((localPlace ι E v).adicCompletion E) :=
  Rep.ofHom ⟨unitsLocalizationLinear v (localPlace ι E v), fun σ => by
    ext x
    exact congrArg Additive.ofMul (Units.ext
      (algebraMap_decompositionHom v (localPlace ι E v) σ ((@Additive.toMul E ˣ x : Eˣ) : E)))⟩

omit [IsSepClosure K Ω] [FiniteDimensional K ↥E] in
/-- The Library's local component map is the map along `localDecompositionHom` with `localUnitsHom`. -/
theorem unitsLocalMap_eq_map (n : ℕ) :
    unitsLocalMap v (localPlace ι E v) n =
      groupCohomology.map (localDecompositionHom ι E v :
        Gal((localPlace ι E v).adicCompletion E/v.adicCompletion K) →* Gal(E/K))
        (localUnitsHom ι E v) n :=
  Reciprocity.groupCohomology_map_congr (MonoidHom.ext fun _ => rfl) (fun _ => rfl) n

/-- Localization at `v` of a class inflated from `E` is the inflation from `E_w` of its Library local
component at the place of `ι`. -/
theorem brauerLocalization_unitsInflation (a : relativeCohomology K E 2) :
    letI := completionAlgebra ι E v
    haveI := isScalarTower_completionAlgebra ι E v
    brauerLocalization ι v 2 ((unitsInflation E 2).hom a) =
      (unitsTowerMap (v.adicCompletion K) ((localPlace ι E v).adicCompletion E)
          (AlgebraicClosure (v.adicCompletion K)) 2).hom
        ((isoGroupCohomology (unitsModule (v.adicCompletion K)
          ((localPlace ι E v).adicCompletion E)) 2).inv.hom
          ((unitsLocalMap v (localPlace ι E v) 2).hom a)) := by
  let := completionAlgebra ι E v
  have := isScalarTower_completionAlgebra ι E v
  rw [unitsInflation_apply_eq]
  set y := (isoGroupCohomology (unitsModule K E) 2).inv.hom a with hy
  have hR : (isoGroupCohomology (unitsModule (v.adicCompletion K)
      ((localPlace ι E v).adicCompletion E)) 2).inv.hom ((unitsLocalMap v (localPlace ι E v) 2).hom a) =
      (map (localDecompositionHom ι E v) (localUnitsHom ι E v) 2).hom y := by
    have h1 := congrArg (fun f => f.hom y)
      (map_comp_toGroupCohomology (localDecompositionHom ι E v) (localUnitsHom ι E v) 2)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
    rw [← isoGroupCohomology_hom, ← isoGroupCohomology_hom, hy, Iso.inv_hom_id_apply] at h1
    rw [unitsLocalMap_eq_map]
    erw [← h1, Iso.hom_inv_id_apply]
  rw [hR]
  have hgrp : (BrauerComparison.normalKrullRestriction K E Ω).comp
      (decompositionHom (v.adicCompletion K) (ι.finite v)) =
      (localDecompositionHom ι E v).comp (BrauerComparison.normalKrullRestriction (v.adicCompletion K)
        ((localPlace ι E v).adicCompletion E) (AlgebraicClosure (v.adicCompletion K))) := by
    refine ContinuousMonoidHom.ext fun σ => AlgEquiv.ext fun x => ?_
    apply (placeEmbedding ι E v).injective
    change ι.finite v (((AlgEquiv.restrictNormalHom E)
        (decompositionHom (v.adicCompletion K) (ι.finite v) σ) x : E) : Ω) =
      placeEmbedding ι E v (FundamentalClass.decompositionHom v (localPlace ι E v)
          ((AlgEquiv.restrictNormalHom ((localPlace ι E v).adicCompletion E)) σ) x)
    rw [← completionEmbeddingOfAlgHom_algebraMap (placeEmbedding ι E v), algebraMap_decompositionHom]
    have h1 := AlgEquiv.restrictNormal_commutes (decompositionHom (v.adicCompletion K) (ι.finite v) σ) E x
    have h2 := AlgEquiv.restrictNormal_commutes σ ((localPlace ι E v).adicCompletion E)
      (algebraMap E ((localPlace ι E v).adicCompletion E) x)
    change completionEmbeddingOfAlgHom (placeEmbedding ι E v) _ = _ at h2
    change ι.finite v (algebraMap E Ω _) = _
    erw [h1, decompositionHom_apply]
    erw [h2, completionEmbeddingOfAlgHom_algebraMap (placeEmbedding ι E v)]
    rfl
  have e1 := congrArg (fun F => F.hom y) (map_comp (BrauerComparison.normalKrullRestriction K E Ω)
    (underlyingHom _ (BrauerComparison.continuousUnitInflationCoefficients K E Ω))
    (decompositionHom (v.adicCompletion K) (ι.finite v)) (unitsLocalHom ι v) 2)
  have e2 := congrArg (fun F => F.hom y) (map_comp (localDecompositionHom ι E v) (localUnitsHom ι E v)
    (BrauerComparison.normalKrullRestriction (v.adicCompletion K)
        ((localPlace ι E v).adicCompletion E) (AlgebraicClosure (v.adicCompletion K)))
    (underlyingHom _ (BrauerComparison.continuousUnitInflationCoefficients (v.adicCompletion K)
        ((localPlace ι E v).adicCompletion E) (AlgebraicClosure (v.adicCompletion K)))) 2)
  refine e1.symm.trans (Eq.trans ?_ e2)
  refine congrArg (fun F => F.hom y) (map_congr (A := unitsModule K E)
    (B := unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))) _ _ hgrp (fun b => ?_) 2)
  apply Additive.toMul.injective
  apply Units.ext
  exact (completionEmbeddingOfAlgHom_algebraMap (placeEmbedding ι E v) _).symm

/-- **The local invariant of an inflated class** is the Library's local invariant of its local
component at the place of `ι`, for any local invariant family with the arithmetic normalization
and compatibility with inflation. -/
theorem localInvariant_unitsInflation (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (hA : ∀ (p : ℕ) [Fact p.Prime], (I p).ArithmeticNormalization)
    (hInf : ∀ (p : ℕ) [Fact p.Prime], (I p).InflationCompatibility) (a : relativeCohomology K E 2) :
    localInvariant ι v ((unitsInflation E 2).hom a) =
      Reciprocity.finiteLocalInvariant v (localPlace ι E v) I a := by
  let := completionAlgebra ι E v
  have := isScalarTower_completionAlgebra ι E v
  rw [localInvariant_apply, brauerLocalization_unitsInflation,
    finiteInvariant_unitsTowerMap v _ (I (residuePrime v)) (hA _) (hInf _)]
  rfl

end Compat

end Langlands.GaloisCohomology
