import Langlands.GaloisCohomology.Global.BrauerSequence.RealComparison
import Langlands.ClassFieldTheory.Global.GlobalReciprocityProof
import Langlands.ClassFieldTheory.Global.H1VanishingProof
import Langlands.ClassFieldTheory.Local.LocalRelativeClassFormationProof

/-!
# The Hasse principle and the reciprocity law for the Brauer group of a number field

* The localizations `brauerLocalization ι v n` and `realBrauerLocalization ι w n` do not depend on the
  embeddings `ι` (`brauerLocalization_eq`, `realBrauerLocalization_eq`): two choices differ by an
  automorphism `g` of `Ω`, and restriction along the conjugated homomorphism is restriction along the
  original one composed with the action of `g` on cohomology, which is the identity
  (`cohomologyInnerConj_eq_id` of the foundations).
* Every place of a finite Galois extension `E ⊆ Ω` above a place of `K` is the place of `E` given by
  some choice of embeddings (`exists_localPlace_eq`, `exists_realPlace_eq`).
* **Injectivity** (`eq_zero_of_brauerLocalization_eq_zero'`): a class `x` comes from some
  `H²(Gal(E/K), Eˣ)` (foundations, `exists_unitsInflation_eq`); its local components at all places
  of `E` vanish by the comparisons of `FiniteComparison.lean` and `RealComparison.lean` and the
  independence of `ι`, so it vanishes by the Library's Hasse principle at the finite level
  (`Reciprocity.eq_zero_of_local_eq_zero`, from `H¹(Gal(E/K), C_E) = 0`, `ideleClassH1Vanishing`).
* **Reciprocity** (`localInvariant_finite_support_and_sum_eq_zero`): the local invariants of `x` are
  the Library's local invariants of a representative at the places of `E` given by `ι`, which have
  finite support and sum zero by the Library's global reciprocity law (`globalReciprocity_of`).

The local invariant family is `brauerInvariantFamily`, chosen from the Library's local class
formation (`localRelativeClassFormation`); by `finiteInvariant_unitsTowerMap` every such family
gives the local theory's invariant.
-/

namespace Langlands.GaloisCohomology
open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

universe u

noncomputable section

section Independence

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- The localization at a finite place does not depend on the choice of embeddings. -/
theorem brauerLocalization_eq (ι ι' : PlaceEmbeddings K Ω) (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    brauerLocalization ι' v n = brauerLocalization ι v n := by
  obtain ⟨g, hg⟩ := exists_eq_comp_of_normal (ι.finite v) (ι'.finite v)
  have hgrp : decompositionHom (v.adicCompletion K) (ι'.finite v) =
      (⟨innerConjHom g, continuous_innerConjHom g⟩ : Gal(Ω/K) →ₜ* Gal(Ω/K)).comp
        (decompositionHom (v.adicCompletion K) (ι.finite v)) := by
    ext σ : 1
    rw [hg, decompositionHom_comp]
    rfl
  have e1 := map_comp (⟨innerConjHom g, continuous_innerConjHom g⟩ : Gal(Ω/K) →ₜ* Gal(Ω/K))
    (innerConjMor (unitsModule K Ω) g) (decompositionHom (v.adicCompletion K) (ι.finite v))
    (unitsLocalHom ι v) n
  rw [show map ⟨innerConjHom g, continuous_innerConjHom g⟩ (innerConjMor (unitsModule K Ω) g) n = 𝟙 _
    from cohomologyInnerConj_eq_id n _ g, Category.id_comp] at e1
  ext x
  change (map _ (unitsLocalHom ι' v) n).hom x = (map _ (unitsLocalHom ι v) n).hom x
  rw [← e1]
  refine congrArg (fun f => f.hom x) (map_congr (A := unitsModule K Ω)
    (B := unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))) _ _ hgrp (fun b => ?_) n)
  apply Additive.toMul.injective
  apply Units.ext
  change ι'.finite v _ = ι.finite v (g _)
  rw [hg]
  rfl

/-- The localization at an infinite place does not depend on the choice of embeddings. -/
theorem realBrauerLocalization_eq (ι ι' : PlaceEmbeddings K Ω) (w : InfinitePlace K) (n : ℕ) :
    realBrauerLocalization ι' w n = realBrauerLocalization ι w n := by
  obtain ⟨g, hg⟩ := exists_eq_comp_of_normal (ι.infinite w) (ι'.infinite w)
  have hgrp : decompositionHom w.Completion (ι'.infinite w) =
      (⟨innerConjHom g, continuous_innerConjHom g⟩ : Gal(Ω/K) →ₜ* Gal(Ω/K)).comp
        (decompositionHom w.Completion (ι.infinite w)) := by
    ext σ : 1
    rw [hg, decompositionHom_comp]
    rfl
  have e1 := map_comp (⟨innerConjHom g, continuous_innerConjHom g⟩ : Gal(Ω/K) →ₜ* Gal(Ω/K))
    (innerConjMor (unitsModule K Ω) g) (decompositionHom w.Completion (ι.infinite w))
    (realUnitsLocalHom ι w) n
  rw [show map ⟨innerConjHom g, continuous_innerConjHom g⟩ (innerConjMor (unitsModule K Ω) g) n = 𝟙 _
    from cohomologyInnerConj_eq_id n _ g, Category.id_comp] at e1
  ext x
  change (map _ (realUnitsLocalHom ι' w) n).hom x = (map _ (realUnitsLocalHom ι w) n).hom x
  rw [← e1]
  refine congrArg (fun f => f.hom x) (map_congr (A := unitsModule K Ω)
    (B := unitsModule w.Completion (AlgebraicClosure w.Completion)) _ _ hgrp (fun b => ?_) n)
  apply Additive.toMul.injective
  apply Units.ext
  change ι'.infinite w _ = ι.infinite w (g _)
  rw [hg]
  rfl

/-- The local invariant at a finite place does not depend on the choice of embeddings. -/
theorem localInvariant_eq (ι ι' : PlaceEmbeddings K Ω) (v : HeightOneSpectrum (𝓞 K)) :
    localInvariant ι' v = localInvariant ι v := by
  unfold localInvariant
  rw [brauerLocalization_eq ι ι' v 2]

/-- The local invariant at an infinite place does not depend on the choice of embeddings. -/
theorem realLocalInvariant_eq (ι ι' : PlaceEmbeddings K Ω) (w : InfinitePlace K) :
    realLocalInvariant ι' w = realLocalInvariant ι w := by
  funext x
  unfold realLocalInvariant
  rw [realBrauerLocalization_eq ι ι' w 2]

end Independence

section Extension

variable {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

/-- An embedding of an intermediate field `E` of `Ω / K` into an algebraically closed field extends
to `Ω`. -/
theorem exists_algHom_comp_val_eq {M : Type u} [Field M] [Algebra K M] [IsAlgClosed M]
    (E : IntermediateField K Ω) (j : E →ₐ[K] M) : ∃ J : Ω →ₐ[K] M, J.comp E.val = j := by
  let _ : Algebra E M := j.toRingHom.toAlgebra
  have : IsScalarTower K E M := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  have : Algebra.IsAlgebraic E Ω := Algebra.IsAlgebraic.tower_top (K := K) E
  let J : Ω →ₐ[E] M := IsAlgClosed.lift
  refine ⟨J.restrictScalars K, AlgHom.ext fun x => ?_⟩
  exact J.commutes x

end Extension

section Places

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E] [NumberField E]

omit [FiniteDimensional K ↥E] [IsGalois K ↥E] in
/-- Every finite place of `E` above `v` is the place of some choice of embeddings. -/
theorem exists_localPlace_eq (v : HeightOneSpectrum (𝓞 K))
    (w : Langlands.Global.AdelicFunctoriality.FinitePlacesAbove E v) :
    ∃ ι' : PlaceEmbeddings K Ω, localPlace ι' E v = w.1 := by
  classical
  obtain ⟨j, hj⟩ := exists_placeOfAlgHom_eq w
  obtain ⟨J, hJ⟩ := exists_algHom_comp_val_eq E j
  let ι₀ : PlaceEmbeddings K Ω := Classical.arbitrary _
  let ι' : PlaceEmbeddings K Ω := ⟨Function.update ι₀.finite v J, ι₀.infinite⟩
  have h1 : placeEmbedding ι' E v = j := by
    change (Function.update ι₀.finite v J v).comp E.val = j
    rw [Function.update_self, hJ]
  refine ⟨ι', ?_⟩
  unfold localPlace
  rw [h1, hj]

omit [NumberField K] in
/-- On `K`, `closureToComplex w` is the embedding of `w`. -/
theorem closureToComplex_algebraMap_base (w : InfinitePlace K) (k : K) :
    closureToComplex w (algebraMap K (AlgebraicClosure w.Completion) k) = w.embedding k := by
  rw [IsScalarTower.algebraMap_apply K w.Completion (AlgebraicClosure w.Completion),
    closureToComplex_algebraMap, InfinitePlace.Completion.algebraMap_apply,
    NumberField.InfinitePlace.Completion.extensionEmbedding_coe]
  rfl

omit [FiniteDimensional K ↥E] [IsGalois K ↥E] [NumberField ↥E] in
/-- Every infinite place of `E` above `w` is the place of some choice of embeddings. -/
theorem exists_realPlace_eq (w : InfinitePlace K) (u : InfinitePlace E) [u.LiesOver w] :
    ∃ ι' : PlaceEmbeddings K Ω, realPlace ι' E w = u := by
  classical
  -- a complex embedding of `E` representing `u` and extending `w.embedding`
  obtain ⟨ψ, hψu, hψw⟩ : ∃ ψ : E →+* ℂ, InfinitePlace.mk ψ = u ∧
      ψ.comp (algebraMap K E) = w.embedding := by
    rcases InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq u w with h | h
    · exact ⟨u.embedding, u.mk_embedding, h⟩
    · exact ⟨ComplexEmbedding.conjugate u.embedding, by rw [InfinitePlace.mk_conjugate_eq,
        u.mk_embedding], h⟩
  let j : E →ₐ[K] AlgebraicClosure w.Completion :=
    { (closureEquivComplex w).symm.toRingHom.comp ψ with
      commutes' := fun k => by
        change (closureEquivComplex w).symm (ψ (algebraMap K E k)) = _
        rw [RingEquiv.symm_apply_eq, closureEquivComplex_apply, closureToComplex_algebraMap_base]
        exact congrArg (fun φ : K →+* ℂ => φ k) hψw }
  obtain ⟨J, hJ⟩ := exists_algHom_comp_val_eq E j
  let ι₀ : PlaceEmbeddings K Ω := Classical.arbitrary _
  let ι' : PlaceEmbeddings K Ω := ⟨ι₀.finite, Function.update ι₀.infinite w J⟩
  have h1 : realPlaceEmbedding ι' E w = j := by
    change (Function.update ι₀.infinite w J w).comp E.val = j
    rw [Function.update_self, hJ]
  refine ⟨ι', ?_⟩
  have h2 : realComplexEmbedding ι' E w = ψ := by
    ext x
    change closureToComplex w (realPlaceEmbedding ι' E w x) = _
    rw [h1]
    change closureEquivComplex w ((closureEquivComplex w).symm (ψ x)) = _
    rw [RingEquiv.apply_symm_apply]
  rw [realPlace, h2, hψu]

/-- The place of `ι` lies over `w`. -/
instance liesOver_realPlace (ι : PlaceEmbeddings K Ω) (w : InfinitePlace K) :
    (realPlace ι E w).LiesOver w := by
  have : ComplexEmbedding.LiesOver (realComplexEmbedding ι E w) w.embedding :=
    ⟨realComplexEmbedding_comp_algebraMap ι E w⟩
  have h : (InfinitePlace.mk (realComplexEmbedding ι E w)).val.LiesOver (InfinitePlace.mk w.embedding).val :=
    inferInstance
  rw [w.mk_embedding] at h
  exact h

end Places

section Hasse

open Langlands.ClassFieldTheory.Global Langlands.ClassFieldTheory.Local Langlands.Global.CompletionPadic

/-- A local invariant family for every prime, with the class-formation properties and the arithmetic
normalization (chosen from the Library's `localRelativeClassFormation`). -/
def brauerInvariantFamily (p : ℕ) [Fact p.Prime] : InvariantFamily.{u, u} p :=
  (localRelativeClassFormation.{u} p).choose

/-- `brauerInvariantFamily` forms a relative class formation with the arithmetic normalization. -/
theorem brauerInvariantFamily_spec (p : ℕ) [Fact p.Prime] :
    (brauerInvariantFamily.{u} p).RelativeClassFormation ∧
      (brauerInvariantFamily.{u} p).ArithmeticNormalization :=
  ⟨(localRelativeClassFormation.{u} p).choose_spec.2.1,
    (localRelativeClassFormation.{u} p).choose_spec.1⟩

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω)

/-- **Injectivity of localization** (the Hasse principle for the Brauer group of `K`). -/
theorem eq_zero_of_brauerLocalization_eq_zero' (x : cohomology (unitsModule K Ω) 2)
    (hfin : ∀ v, brauerLocalization ι v 2 x = 0) (hinf : ∀ w, realBrauerLocalization ι w 2 x = 0) :
    x = 0 := by
  obtain ⟨E, a, rfl⟩ := exists_unitsInflation_eq 2 x
  have : NumberField E.toIntermediateField := NumberField.of_module_finite K E.toIntermediateField
  have hI := brauerInvariantFamily_spec.{u}
  have hImages : ∀ (p : ℕ) [Fact p.Prime], (brauerInvariantFamily.{u} p).RelativeImages :=
    fun p _ => (hI p).1.2.1
  suffices a = 0 by rw [this, map_zero]
  refine Reciprocity.eq_zero_of_local_eq_zero ideleClassH1Vanishing brauerInvariantFamily.{u} hImages a
    (fun v w' hw' => ?_) (fun u' => ?_)
  · obtain ⟨ι', hι'⟩ := exists_localPlace_eq E.toIntermediateField v ⟨w', hw'⟩
    have h0 : localInvariant ι' v ((unitsInflation E.toIntermediateField 2).hom a) = 0 := by
      rw [localInvariant_eq ι ι', localInvariant_apply, hfin v, map_zero]
    rw [localInvariant_unitsInflation ι' E.toIntermediateField v brauerInvariantFamily.{u}
      (fun p _ => (hI p).2) (fun p _ => (hI p).1.2.2.1)] at h0
    subst hι'
    have := Langlands.Global.AdelicFunctoriality.isGalois_adicCompletion v
      (localPlace ι' E.toIntermediateField v)
    have := Langlands.Global.AdelicFunctoriality.FiniteExtension.local_finite v
      (localPlace ι' E.toIntermediateField v)
    exact (injective_iff_map_eq_zero _).1 ((hImages (residuePrime v)) (padicField v) _).1 _ h0
  · let w := u'.comap (algebraMap K E.toIntermediateField)
    have : u'.LiesOver w := ⟨rfl⟩
    obtain ⟨ι', hι'⟩ := exists_realPlace_eq E.toIntermediateField w u'
    have h0 := realLocalInvariant_unitsInflation ι' E.toIntermediateField w a
    rw [hι'] at h0
    rw [← h0, realLocalInvariant_eq ι ι', realLocalInvariant, hinf w, realInvariant_zero]


/-- **The reciprocity law.** The local invariants of a global Brauer class have finite support and
sum zero. -/
theorem localInvariant_finite_support_and_sum_eq_zero (x : cohomology (unitsModule K Ω) 2) :
    (Function.support fun v => localInvariant ι v x).Finite ∧
      ∑ᶠ v, localInvariant ι v x + ∑ w, realLocalInvariant ι w x = 0 := by
  obtain ⟨E, a, rfl⟩ := exists_unitsInflation_eq 2 x
  have : NumberField E.toIntermediateField := NumberField.of_module_finite K E.toIntermediateField
  have hI := brauerInvariantFamily_spec.{u}
  have hrec := globalReciprocity_of ideleClassH1Vanishing brauerInvariantFamily.{u} hI K
    E.toIntermediateField a
  obtain ⟨h1, h2⟩ := hrec (fun v => ⟨localPlace ι E.toIntermediateField v, inferInstance⟩)
    (fun w => ⟨realPlace ι E.toIntermediateField w, inferInstance⟩)
  have hf : (fun v => localInvariant ι v ((unitsInflation E.toIntermediateField 2).hom a)) =
      fun v => Reciprocity.finiteLocalInvariant v (localPlace ι E.toIntermediateField v)
        brauerInvariantFamily.{u} a :=
    funext fun v => localInvariant_unitsInflation ι E.toIntermediateField v brauerInvariantFamily.{u}
      (fun p _ => (hI p).2) (fun p _ => (hI p).1.2.2.1) a
  have hr : (fun w => realLocalInvariant ι w ((unitsInflation E.toIntermediateField 2).hom a)) =
      fun w => Reciprocity.archimedeanInvariant (realPlace ι E.toIntermediateField w) a :=
    funext fun w => realLocalInvariant_unitsInflation ι E.toIntermediateField w a
  rw [hf, hr]
  exact ⟨h1, h2⟩

end Hasse



end

end Langlands.GaloisCohomology
