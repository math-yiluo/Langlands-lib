import Langlands.GaloisCohomology.Global.BrauerSequence.HigherDegrees.IdeleDecomposition
import Langlands.GaloisCohomology.Global.BrauerSequence.Hasse
import Langlands.GaloisCohomology.Global.BrauerSequence.Existence
import Langlands.ClassFieldTheory.Global.IdeleCohomologyTower
import Langlands.Cohomology.RestrictedProduct

/-!
# Archimedean components of idèle cohomology and the localization at a real place

Let `K` be a number field, `Ω` a separable closure, `ι` a choice of embeddings, `w` an infinite
place of `K` and `E ⊆ Ω` a finite Galois level, with `w' = realPlace ι E w` the place of `E` above
`w` given by `ι` and `K̄_w` the algebraic closure of `K_w`.

* `realCompletionToComplex ι E w : E_{w'} → ℂ` extends the complex embedding of `ι`;
  `realCompletionToClosure ι E w : E_{w'} → K̄_w` is its composite with `ℂ ≃ K̄_w`.
* `realIdeleCoefficient ι E w : J_E → K̄_wˣ`, `x ↦ (x_{w'} in K̄_w)`, is equivariant along
  `realRestrictHom ι E w : Gal(K̄_w/K_w) → Gal(E/K)`; it induces
  `realIdeleComparison ι E w n : Hⁿ(Gal(E/K), J_E) → Hⁿ(Gal(K̄_w/K_w), K̄_wˣ)` (the foundations'
  cochain model of the target).
* On principal classes it is the localization at `w` of the inflated class
  (`realIdeleComparison_principal`); it is compatible with inflation of idèle cohomology
  (`realIdeleComparison_inflation`); and it factors through the local component
  `Hⁿ(Gal(E/K), J_E) → Hⁿ(D_{w'}, E_{w'}ˣ)` by a map `realLocalComparison ι E w n` which is
  injective in positive degree and bijective when `w'` is complex
  (`realIdeleComparison_eq`, `injective_realLocalComparison`, `bijective_realLocalComparison`).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Limits NumberField IsDedekindDomain
open Langlands.ProfiniteCohomology Langlands.Galois
open Langlands.ClassFieldTheory.Global Langlands.ClassFieldTheory.Local Reciprocity
open Langlands.Global.AdelicFunctoriality
open InfinitePlace.Completion

universe u

noncomputable section

section Conj

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

/-- A conjugation for `φ` is also a conjugation for the conjugate embedding. -/
theorem isConj_conjugate {φ : L →+* ℂ} {σ : L ≃ₐ[k] L}
    (h : ComplexEmbedding.IsConj φ σ) : ComplexEmbedding.IsConj (ComplexEmbedding.conjugate φ) σ := by
  ext x
  simp [ComplexEmbedding.conjugate_coe_eq, h.eq]

/-- A conjugation for `φ` is a conjugation for the embedding of the place `mk φ`. -/
theorem isConj_embedding_mk {φ : L →+* ℂ} {σ : L ≃ₐ[k] L}
    (h : ComplexEmbedding.IsConj φ σ) : ComplexEmbedding.IsConj (InfinitePlace.mk φ).embedding σ := by
  rcases InfinitePlace.embedding_mk_eq φ with h' | h'
  · rw [h']
    exact h
  · rw [h']
    exact isConj_conjugate h

end Conj

/-- Two continuous maps out of the completion at an infinite place which agree on the field agree.-/
theorem infinitePlaceCompletion_ext {L : Type*} [Field L] {v : InfinitePlace L} {f g : v.Completion → ℂ}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ a : L, f (algebraMap L v.Completion a) = g (algebraMap L v.Completion a))
    (x : v.Completion) : f x = g x := by
  induction x using InfinitePlace.Completion.induction_on with
  | hp => exact isClosed_eq hf hg
  | ih a => exact h (WithAbs.ofAbs a)

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  (ι : PlaceEmbeddings K Ω) (E : IntermediateField K Ω) (w : InfinitePlace K)

section Completion

open Classical in
/-- The embedding `E_{w'} → ℂ` extending the complex embedding `realComplexEmbedding ι E w` of `ι`,
where `w' = realPlace ι E w`. -/
def realCompletionToComplex : (realPlace ι E w).Completion →+* ℂ :=
  if (realPlace ι E w).embedding = realComplexEmbedding ι E w then extensionEmbedding _
  else (starRingEnd ℂ).comp (extensionEmbedding _)

/-- `realCompletionToComplex` is continuous. -/
theorem continuous_realCompletionToComplex : Continuous (realCompletionToComplex ι E w) := by
  unfold realCompletionToComplex
  split_ifs
  · exact (isometry_extensionEmbedding _).continuous
  · exact Complex.continuous_conj.comp (isometry_extensionEmbedding _).continuous

/-- `realCompletionToComplex` extends the complex embedding of `ι`. -/
theorem realCompletionToComplex_algebraMap (a : E) :
    realCompletionToComplex ι E w (algebraMap E _ a) = realComplexEmbedding ι E w a := by
  unfold realCompletionToComplex
  split_ifs with h
  · rw [extensionEmbedding_algebraMap, h]
  · rcases InfinitePlace.embedding_mk_eq (realComplexEmbedding ι E w) with h' | h'
    · exact absurd h' h
    · change starRingEnd ℂ (extensionEmbedding _ (algebraMap E _ a)) = _
      rw [extensionEmbedding_algebraMap]
      rw [show (realPlace ι E w).embedding = ComplexEmbedding.conjugate (realComplexEmbedding ι E w)
        from h', ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]

/-- `realCompletionToComplex` commutes with complex conjugation of the extension embedding. -/
theorem realCompletionToComplex_star (x y : (realPlace ι E w).Completion)
    (h : extensionEmbedding _ x = star (extensionEmbedding _ y)) :
    realCompletionToComplex ι E w x = star (realCompletionToComplex ι E w y) := by
  unfold realCompletionToComplex
  split_ifs
  · exact h
  · change starRingEnd ℂ _ = star (starRingEnd ℂ _)
    rw [h]
    rfl

/-- At a complex place `w'`, `realCompletionToComplex` is bijective. -/
theorem bijective_realCompletionToComplex (hw : (realPlace ι E w).IsComplex) :
    Function.Bijective (realCompletionToComplex ι E w) := by
  have hb := bijective_extensionEmbedding_of_isComplex hw
  unfold realCompletionToComplex
  split_ifs
  · exact hb
  · refine ⟨(starRingEnd ℂ).injective.comp hb.1, fun z => ?_⟩
    obtain ⟨y, hy⟩ := hb.2 (starRingEnd ℂ z)
    exact ⟨y, by change starRingEnd ℂ _ = z; rw [hy, Complex.conj_conj]⟩

/-- The embedding `E_{w'} → K̄_w`: `realCompletionToComplex` followed by `ℂ ≃ K̄_w`. -/
def realCompletionToClosure : (realPlace ι E w).Completion →+* AlgebraicClosure w.Completion :=
  (closureEquivComplex w).symm.toRingHom.comp (realCompletionToComplex ι E w)

/-- Read in `ℂ`, `realCompletionToClosure` is `realCompletionToComplex`. -/
theorem closureToComplex_realCompletionToClosure (x : (realPlace ι E w).Completion) :
    closureToComplex w (realCompletionToClosure ι E w x) = realCompletionToComplex ι E w x := by
  rw [← closureEquivComplex_apply]
  exact RingEquiv.apply_symm_apply _ _

/-- `realCompletionToClosure` extends the embedding `E → K̄_w` of `ι`. -/
theorem realCompletionToClosure_algebraMap (a : E) :
    realCompletionToClosure ι E w (algebraMap E _ a) = realPlaceEmbedding ι E w a := by
  apply (closureToComplex w).injective
  rw [closureToComplex_realCompletionToClosure, realCompletionToComplex_algebraMap]
  rfl

/-- The place of `ι` on `E` lies over `w`. -/
theorem comap_realPlace_algebraMap : (realPlace ι E w).comap (algebraMap K E) = w := by
  change InfinitePlace.mk ((realComplexEmbedding ι E w).comp (algebraMap K E)) = w
  rw [realComplexEmbedding_comp_algebraMap, InfinitePlace.mk_embedding]

/-- At a level containing a square root of `-1`, the place of `ι` above `w` is complex. -/
theorem isComplex_realPlace_of_sq_eq_neg_one {i : E} (hi : i ^ 2 = -1) :
    (realPlace ι E w).IsComplex := by
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  change ¬ (InfinitePlace.mk (realComplexEmbedding ι E w)).IsReal
  rw [InfinitePlace.isReal_mk_iff]
  intro hr
  exact sq_ne_neg_one_of_isReal hr i hi

end Completion

section Coefficient

variable [IsSepClosure K Ω] [IsGalois K E] [NumberField E]

/-- The restriction `Gal(K̄_w/K_w) → Gal(E/K)` through the embedding `ι.infinite w`. -/
abbrev realRestrictHom : Gal(AlgebraicClosure w.Completion/w.Completion) →* Gal(E/K) :=
  (AlgEquiv.restrictNormalHom E).comp
    (decompositionHom w.Completion (ι.infinite w) : Gal(AlgebraicClosure w.Completion/w.Completion) →*
      Gal(Ω/K))

omit [NumberField E] in
/-- The image of the conjugation of `K̄_w` is a conjugation of the complex embedding of `ι`. -/
theorem isConj_realRestrict_closureConj (hw : w.IsReal) :
    ComplexEmbedding.IsConj (realComplexEmbedding ι E w) (realRestrict ι E w (closureConj w hw)) :=
  RingHom.ext fun x => (realComplexEmbedding_realRestrict_closureConj ι E w hw x).symm

omit [NumberField E] in
/-- The image of `σ ∈ Gal(K̄_w/K_w)` in `Gal(E/K)` fixes the place `w'` of `ι`. -/
theorem realRestrict_mem_stabilizer (σ : Gal(AlgebraicClosure w.Completion/w.Completion)) :
    realRestrict ι E w σ ∈ MulAction.stabilizer (E ≃ₐ[K] E) (realPlace ι E w) := by
  by_cases hw : w.IsReal
  · rcases eq_one_or_eq_closureConj w hw σ with rfl | rfl
    · rw [realRestrict_one]
      exact one_mem _
    · exact mem_stabilizer_of_isConj (isConj_embedding_mk (isConj_realRestrict_closureConj ι E w hw))
  · rw [eq_one_of_isComplex w (InfinitePlace.not_isReal_iff_isComplex.1 hw) σ, realRestrict_one]
    exact one_mem _

/-- **Equivariance** of the coordinate at `w'` read in `K̄_w`: for `σ ∈ Gal(K̄_w/K_w)` and an idele
`x`, the coordinate of `σ|_E • x` is `σ` applied to the coordinate of `x`. -/
theorem realCompletionToClosure_coordinate_smul (σ : Gal(AlgebraicClosure w.Completion/w.Completion))
    (x : IdeleGroup (𝓞 E) E) :
    realCompletionToClosure ι E w (ideleInfiniteCoordinate (realPlace ι E w)
        (relativeIdeleAut K E (realRestrict ι E w σ) x)) =
      σ (realCompletionToClosure ι E w (ideleInfiniteCoordinate (realPlace ι E w) x)) := by
  have hone : ∀ y : IdeleGroup (𝓞 E) E, relativeIdeleAut K E 1 y = y := fun y => by
    rw [map_one]
    rfl
  apply (closureToComplex w).injective
  rw [closureToComplex_realCompletionToClosure]
  by_cases hw : w.IsReal
  · rcases eq_one_or_eq_closureConj w hw σ with rfl | rfl
    · rw [realRestrict_one, hone, AlgEquiv.one_apply, closureToComplex_realCompletionToClosure]
    · rw [closureToComplex_closureConj, closureToComplex_realCompletionToClosure,
        starRingEnd_apply]
      apply realCompletionToComplex_star
      exact extensionEmbedding_ideleInfiniteCoordinate_of_isConj
        (isConj_embedding_mk (isConj_realRestrict_closureConj ι E w hw)) x
  · rw [eq_one_of_isComplex w (InfinitePlace.not_isReal_iff_isComplex.1 hw) σ, realRestrict_one, hone,
      AlgEquiv.one_apply, closureToComplex_realCompletionToClosure]

/-- The coefficient map `J_E → K̄_wˣ`, `x ↦ x_{w'}` read in `K̄_w`, equivariant along
`realRestrictHom ι E w`. -/
def realIdeleCoefficient :
    Rep.res (realRestrictHom ι E w) (relativeIdeleRepresentation K E) ⟶
      unitsModule w.Completion (AlgebraicClosure w.Completion) :=
  Rep.ofHom ⟨uliftIntLinearMap (A := Additive (IdeleGroup (𝓞 E) E))
      (B := Additive (AlgebraicClosure w.Completion)ˣ) (MonoidHom.toAdditive
        ((Units.map (realCompletionToClosure ι E w : _ →* AlgebraicClosure w.Completion)).comp
          (ideleInfiniteCoordinate (realPlace ι E w)))), fun σ => by
    ext x
    exact Units.ext (realCompletionToClosure_coordinate_smul ι E w σ (Additive.toMul x))⟩

/-- The value of `realIdeleCoefficient`. -/
theorem realIdeleCoefficient_apply (x : Additive (IdeleGroup (𝓞 E) E)) :
    ((Additive.toMul ((realIdeleCoefficient ι E w).hom x) : (AlgebraicClosure w.Completion)ˣ) :
        AlgebraicClosure w.Completion) =
      realCompletionToClosure ι E w (ideleInfiniteCoordinate (realPlace ι E w) (Additive.toMul x)) :=
  rfl

/-- **The real comparison map** `Hⁿ(Gal(E/K), J_E) → Hⁿ(Gal(K̄_w/K_w), K̄_wˣ)` induced by
`realIdeleCoefficient`, with the target in the cochain model of the foundations. -/
def realIdeleComparison (n : ℕ) :
    relativeIdeleCohomology K E n ⟶
      cohomology (unitsModule w.Completion (AlgebraicClosure w.Completion)) n :=
  groupCohomology.map (realRestrictHom ι E w) (realIdeleCoefficient ι E w) n ≫
    (isoGroupCohomology (unitsModule w.Completion (AlgebraicClosure w.Completion)) n).inv

variable [FiniteDimensional K E]

/-- **Principal classes.** The real comparison of the image of `a ∈ Hⁿ(Gal(E/K), Eˣ)` in idèle
cohomology is the localization at `w` of the inflation of `a` to `Gal(Ω/K)`. -/
theorem realIdeleComparison_principal (n : ℕ) (a : relativeCohomology K E n) :
    (realIdeleComparison ι E w n).hom (principalIdeleCohomologyMap K E n a) =
      realBrauerLocalization ι w n ((unitsInflation E n).hom a) := by
  rw [unitsInflation_apply_eq]
  set y := (isoGroupCohomology (unitsModule K E) n).inv.hom a with hy
  have e1 := congrArg (fun F => F.hom y) (map_comp (BrauerComparison.normalKrullRestriction K E Ω)
    (underlyingHom _ (BrauerComparison.continuousUnitInflationCoefficients K E Ω))
    (decompositionHom w.Completion (ι.infinite w)) (realUnitsLocalHom ι w) n)
  change _ = (map (decompositionHom w.Completion (ι.infinite w)) (realUnitsLocalHom ι w) n).hom
    ((map (BrauerComparison.normalKrullRestriction K E Ω)
      (underlyingHom _ (BrauerComparison.continuousUnitInflationCoefficients K E Ω)) n).hom y)
  refine Eq.trans ?_ e1
  -- move the comparison with `groupCohomology` across
  have hnat := congrArg (fun F => F.hom y) (map_comp_toGroupCohomology (A := unitsModule K E)
    (B := unitsModule w.Completion (AlgebraicClosure w.Completion))
    ((BrauerComparison.normalKrullRestriction K E Ω).comp
      (decompositionHom w.Completion (ι.infinite w)))
    ((Rep.resFunctor (decompositionHom w.Completion (ι.infinite w) :
        Gal(AlgebraicClosure w.Completion/w.Completion) →* Gal(Ω/K))).map (underlyingHom _
      (BrauerComparison.continuousUnitInflationCoefficients K E Ω)) ≫ realUnitsLocalHom ι w) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
  rw [← isoGroupCohomology_hom, ← isoGroupCohomology_hom, hy, Iso.inv_hom_id_apply] at hnat
  apply (isoGroupCohomology (unitsModule w.Completion (AlgebraicClosure w.Completion))
    n).toLinearEquiv.injective
  change (isoGroupCohomology _ n).hom.hom ((isoGroupCohomology _ n).inv.hom _) = _
  rw [Iso.inv_hom_id_apply]
  erw [hnat]
  refine (congrArg (fun F => F.hom a) (groupCohomology.map_comp (MonoidHom.id _)
    (realRestrictHom ι E w) (principalIdeleCoefficients K E) (realIdeleCoefficient ι E w)
    n)).symm.trans ?_
  refine congrArg (fun F => F.hom a) (groupCohomology.map_congr (A := unitsRepresentation K E)
    (B := unitsModule w.Completion (AlgebraicClosure w.Completion)) rfl ?_ n)
  refine LinearMap.ext fun b => ?_
  apply Additive.toMul.injective
  apply Units.ext
  change realCompletionToClosure ι E w (ideleInfiniteCoordinate (realPlace ι E w)
    (IdeleGroup.unitEmbedding (𝓞 E) E (Additive.toMul b))) = _
  rw [ideleInfiniteCoordinate_unitEmbedding, realCompletionToClosure_algebraMap]
  rfl

end Coefficient

section Tower

variable [IsSepClosure K Ω] {E} {L : IntermediateField K Ω} (hEL : E ≤ L) [IsGalois K E]
  [IsGalois K L] [NumberField E] [NumberField L]

omit [IsSepClosure K Ω] [IsGalois K E] [IsGalois K L] [NumberField E] [NumberField L] in
/-- The place of `ι` on `L` lies over the place of `ι` on `E`. -/
theorem comap_realPlace :
    letI : Algebra E L := (IntermediateField.inclusion hEL).toRingHom.toAlgebra
    (realPlace ι L w).comap (algebraMap E L) = realPlace ι E w := by
  let _ : Algebra E L := (IntermediateField.inclusion hEL).toRingHom.toAlgebra
  change InfinitePlace.mk ((realComplexEmbedding ι L w).comp (algebraMap E L)) =
    InfinitePlace.mk (realComplexEmbedding ι E w)
  exact congrArg _ (RingHom.ext fun _ => rfl)

omit [IsSepClosure K Ω] [IsGalois K E] [IsGalois K L] in
/-- The coordinate at `w''` of an included idele, read in `ℂ`, is the coordinate at `w'`. -/
theorem realCompletionToComplex_ideleInclusion (x : IdeleGroup (𝓞 E) E) :
    letI : Algebra E L := (IntermediateField.inclusion hEL).toRingHom.toAlgebra
    realCompletionToComplex ι L w (ideleInfiniteCoordinate (realPlace ι L w) (ideleInclusion x)) =
      realCompletionToComplex ι E w (ideleInfiniteCoordinate (realPlace ι E w) x) := by
  let _ : Algebra E L := (IntermediateField.inclusion hEL).toRingHom.toAlgebra
  have key : ∀ (q : InfinitePlace E) (hq : q = realPlace ι E w) (G : q.Completion → ℂ),
      Continuous G → (∀ a : E, G (algebraMap E _ a) = realComplexEmbedding ι E w a) →
      G ((x : AdeleRing (𝓞 E) E).1 q) =
        realCompletionToComplex ι E w ((x : AdeleRing (𝓞 E) E).1 (realPlace ι E w)) := by
    intro q hq G hG hGa
    subst hq
    exact infinitePlaceCompletion_ext hG (continuous_realCompletionToComplex ι E w)
      (fun a => (hGa a).trans (realCompletionToComplex_algebraMap ι E w a).symm) _
  exact key _ (comap_realPlace ι w hEL)
    (fun y => realCompletionToComplex ι L w
      (infiniteCompletionMap (algebraMap E L) (realPlace ι L w) y))
    ((continuous_realCompletionToComplex ι L w).comp (continuous_infiniteCompletionMap _ _))
    (fun a => by
      rw [infiniteCompletionMap_coe, realCompletionToComplex_algebraMap]
      rfl)

/-- **Inflation.** The real comparison at `L ⊇ E` of the inflation of an idèle class is its real
comparison at `E`. -/
theorem realIdeleComparison_inflation (n : ℕ) (z : relativeIdeleCohomology K E n) :
    letI : Algebra E L := (IntermediateField.inclusion hEL).toRingHom.toAlgebra
    haveI : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq' rfl
    (realIdeleComparison ι L w n).hom (relativeIdeleInflation K E L n z) =
      (realIdeleComparison ι E w n).hom z := by
  let _ : Algebra E L := (IntermediateField.inclusion hEL).toRingHom.toAlgebra
  have _ : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq' rfl
  change (isoGroupCohomology _ n).inv.hom ((groupCohomology.map (realRestrictHom ι L w)
      (realIdeleCoefficient ι L w) n).hom ((relativeIdeleInflation K E L n).hom z)) =
    (isoGroupCohomology _ n).inv.hom ((groupCohomology.map (realRestrictHom ι E w)
      (realIdeleCoefficient ι E w) n).hom z)
  congr 1
  refine (congrArg (fun F => F.hom z) (groupCohomology.map_comp (AlgEquiv.restrictNormalHom E)
    (realRestrictHom ι L w) (ideleInflationCoefficients K E L) (realIdeleCoefficient ι L w)
    n)).symm.trans ?_
  refine congrArg (fun F => F.hom z) (groupCohomology.map_congr (A := relativeIdeleRepresentation K E)
    (B := unitsModule w.Completion (AlgebraicClosure w.Completion)) ?_ ?_ n)
  · exact MonoidHom.ext fun σ => galRestrictOfLE_restrictNormalHom hEL _
  · refine LinearMap.ext fun x => ?_
    apply Additive.toMul.injective
    apply Units.ext
    apply (closureToComplex w).injective
    change closureToComplex w (realCompletionToClosure ι L w (ideleInfiniteCoordinate (realPlace ι L w)
      (ideleInclusion (Additive.toMul x)))) =
        closureToComplex w (realCompletionToClosure ι E w (ideleInfiniteCoordinate (realPlace ι E w)
          (Additive.toMul x)))
    rw [closureToComplex_realCompletionToClosure, closureToComplex_realCompletionToClosure]
    exact realCompletionToComplex_ideleInclusion ι w hEL _

end Tower

section Local

variable [IsSepClosure K Ω] [IsGalois K E] [NumberField E]

/-- `Gal(K̄_w/K_w) → D_{w'}`, the restriction through `ι` with values in the stabilizer of `w'`. -/
def realStabilizerHom :
    Gal(AlgebraicClosure w.Completion/w.Completion) →*
      MulAction.stabilizer (E ≃ₐ[K] E) (realPlace ι E w) :=
  (realRestrictHom ι E w).codRestrict _ (realRestrict_mem_stabilizer ι E w)

/-- The coefficient map `E_{w'}ˣ → K̄_wˣ` along `realStabilizerHom`. -/
def realLocalCoefficient :
    Rep.res (realStabilizerHom ι E w) (infiniteLocalRepresentation K (realPlace ι E w)) ⟶
      unitsModule w.Completion (AlgebraicClosure w.Completion) :=
  Rep.ofHom ⟨uliftIntLinearMap (A := Additive ((realPlace ι E w).Completion)ˣ)
      (B := Additive (AlgebraicClosure w.Completion)ˣ) (MonoidHom.toAdditive
        (Units.map (realCompletionToClosure ι E w : _ →* AlgebraicClosure w.Completion))), fun σ => by
    ext y
    apply Units.ext
    have h := realCompletionToClosure_coordinate_smul ι E w σ
      (IdeleGroup.ofCompletion (𝓞 E) E (realPlace ι E w) (Additive.toMul y))
    rw [ideleInfiniteCoordinate_ofCompletion_self] at h
    exact h⟩

/-- **The local real comparison** `Hⁿ(D_{w'}, E_{w'}ˣ) → Hⁿ(Gal(K̄_w/K_w), K̄_wˣ)`. -/
def realLocalComparison (n : ℕ) :
    groupCohomology (infiniteLocalRepresentation K (realPlace ι E w)) n ⟶
      cohomology (unitsModule w.Completion (AlgebraicClosure w.Completion)) n :=
  groupCohomology.map (realStabilizerHom ι E w) (realLocalCoefficient ι E w) n ≫
    (isoGroupCohomology (unitsModule w.Completion (AlgebraicClosure w.Completion)) n).inv

/-- The real comparison factors through the local component at `w'`. -/
theorem realIdeleComparison_eq (n : ℕ) :
    realIdeleComparison ι E w n =
      ideleInfiniteLocalMap (realPlace ι E w) n ≫ realLocalComparison ι E w n := by
  rw [realLocalComparison, realIdeleComparison, ← Category.assoc, ideleInfiniteLocalMap,
    ← groupCohomology.map_comp]
  congr 1

omit [IsSepClosure K Ω] [IsGalois K E] [NumberField E] in
/-- A nontrivial element of the stabilizer of `w'` forces `w'` to be complex and `w` real. -/
theorem isComplex_and_isReal_of_ne_one {c : E ≃ₐ[K] E}
    (hc : c ∈ MulAction.stabilizer (E ≃ₐ[K] E) (realPlace ι E w)) (hc1 : c ≠ 1) :
    ComplexEmbedding.IsConj (realPlace ι E w).embedding c ∧ (realPlace ι E w).IsComplex ∧
      w.IsReal := by
  have hconj := isConj_of_mem_stabilizer (realPlace ι E w) hc hc1
  refine ⟨hconj, InfinitePlace.isComplex_iff.2 ((ComplexEmbedding.isConj_ne_one_iff hconj).1 hc1), ?_⟩
  have hr := hconj.isReal_comp
  have hw : InfinitePlace.mk ((realPlace ι E w).embedding.comp (algebraMap K E)) = w := by
    rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
    change InfinitePlace.mk ((realComplexEmbedding ι E w).comp (algebraMap K E)) = w
    rw [realComplexEmbedding_comp_algebraMap, InfinitePlace.mk_embedding]
  exact hw ▸ InfinitePlace.isReal_mk_iff.2 hr

/-- **Bijectivity** of the local real comparison when the stabilizer of `w'` is nontrivial. -/
theorem bijective_realLocalComparison
    (h : ∃ c ∈ MulAction.stabilizer (E ≃ₐ[K] E) (realPlace ι E w), c ≠ 1) (n : ℕ) :
    Function.Bijective (realLocalComparison ι E w n) := by
  obtain ⟨c, hc, hc1⟩ := h
  obtain ⟨hconj, hcx, hw⟩ := isComplex_and_isReal_of_ne_one ι E w hc hc1
  have hρ : realStabilizerHom ι E w (closureConj w hw) = ⟨c, hc⟩ := by
    apply Subtype.ext
    exact ComplexEmbedding.IsConj.ext
      (isConj_embedding_mk (isConj_realRestrict_closureConj ι E w hw)) hconj
  have hbij : Function.Bijective (realStabilizerHom ι E w) := by
    constructor
    · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro σ hσ
      rcases eq_one_or_eq_closureConj w hw σ with rfl | rfl
      · exact one_mem _
      · rw [MonoidHom.mem_ker, hρ] at hσ
        exact absurd (congrArg Subtype.val hσ) hc1
    · intro d
      by_cases hd : d = 1
      · exact ⟨1, by rw [hd, map_one]⟩
      · refine ⟨closureConj w hw, ?_⟩
        rw [hρ]
        apply Subtype.ext
        exact ComplexEmbedding.IsConj.ext hconj
          (isConj_of_mem_stabilizer (realPlace ι E w) d.2 fun h => hd (Subtype.ext h))
  have hcoef : Function.Bijective (realLocalCoefficient ι E w).hom := by
    have hr : Function.Bijective (realCompletionToClosure ι E w) :=
      (closureEquivComplex w).symm.bijective.comp (bijective_realCompletionToComplex ι E w hcx)
    let e : (realPlace ι E w).Completion ≃+* AlgebraicClosure w.Completion :=
      RingEquiv.ofBijective (realCompletionToClosure ι E w) hr
    constructor
    · intro y y' hyy
      apply Additive.toMul.injective
      apply Units.ext
      exact hr.1 (congrArg (fun z : Additive (AlgebraicClosure w.Completion)ˣ =>
        ((Additive.toMul z : (AlgebraicClosure w.Completion)ˣ) : AlgebraicClosure w.Completion)) hyy)
    · intro z
      refine ⟨Additive.ofMul (Units.map (e.symm : _ →* (realPlace ι E w).Completion)
        (Additive.toMul z)), ?_⟩
      apply Additive.toMul.injective
      apply Units.ext
      exact e.apply_symm_apply _
  exact (isoGroupCohomology _ n).symm.toLinearEquiv.bijective.comp
    (Cohomology.bijective_groupCohomology_map _ hbij _ hcoef n)

/-- **Injectivity** of the local real comparison in positive degree. -/
theorem injective_realLocalComparison (n : ℕ) :
    Function.Injective (realLocalComparison ι E w (n + 1)) := by
  by_cases h : ∃ c ∈ MulAction.stabilizer (E ≃ₐ[K] E) (realPlace ι E w), c ≠ 1
  · exact (bijective_realLocalComparison ι E w h (n + 1)).1
  · push Not at h
    have : Subsingleton (MulAction.stabilizer (E ≃ₐ[K] E) (realPlace ι E w)) :=
      ⟨fun a b => Subtype.ext ((h a a.2).trans (h b b.2).symm)⟩
    intro a b _
    exact (ModuleCat.isZero_iff_subsingleton.1
      (isZero_groupCohomology_succ_of_subsingleton _ n)).elim a b

end Local

end

end Langlands.GaloisCohomology
