import Langlands.Cohomology.PerfectScalarDerivedTargetSource
import Langlands.Cohomology.DerivedExactComposition

/-!
# Scalar extension and cohomology of complexes of modules

For a ring map `φ : R →+* S` and a cochain complex `K` of `R`-modules, write `S ⊗_R K` for the
termwise scalar extension `(baseChange φ).obj K`. The canonical `S`-linear comparison
`S ⊗_R H^n(K) ⟶ H^n(S ⊗_R K)` is the `S`-linear adjunct of the map induced on `H^n` by the unit
`K ⟶ φ_* (S ⊗_R K)`, followed by the identification `H^n(φ_* -) ≅ φ_* H^n(-)` for the exact
functor `φ_*` of restriction of scalars. It is defined on homology of complexes
(`baseChangeHomologyMap`) and on cohomology of the localized complexes in the derived category
(`baseChangeDerivedHomologyMap`), and the two agree through
`DerivedCategory.homologyFunctorFactors` (`baseChangeDerivedHomologyMap_eq`).

By right exactness of scalar extension the comparison is an isomorphism in degree `n` whenever
`K` vanishes in degree `n + 1` (`isIso_baseChangeHomologyMap_of_isZero`,
`isIso_baseChangeDerivedHomologyMap_of_isZero`). The derived comparison is natural in chain maps
(`baseChangeDerivedHomologyMap_naturality`). For a strictly perfect `K` and a derived morphism
`b : S ⊗_R K ⟶ Y`, the comparison followed by `H^n(b)` is the `S`-linear adjunct of `H^n` of the
`R`-linear adjunct `perfectScalarDerivedTargetHomEquiv φ K hK Y b`
(`homEquiv_baseChangeDerivedHomologyMap_comp`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe wC wD u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology.ModuleComplex

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
  (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)

/-- The `S`-linear comparison `S ⊗_R H^n(K) ⟶ H^n(S ⊗_R K)` on homology of complexes: the
adjunct of `H^n` of the unit `K ⟶ φ_* (S ⊗_R K)`, followed by `H^n(φ_* -) ≅ φ_* H^n(-)`. -/
def baseChangeHomologyMap :
    (ModuleCat.extendScalars φ).obj (K.homology n) ⟶ ((baseChange φ).obj K).homology n :=
  ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).symm
    (HomologicalComplex.homologyMap
        ((complexAdjunction (ModuleCat.extendRestrictScalarsAdj φ) (.up ℤ)).unit.app K) n ≫
      ((((baseChange φ).obj K).sc n).mapHomologyIso (ModuleCat.restrictScalars φ)).hom)

/-- The adjunct of `baseChangeHomologyMap` is the defining `R`-linear map. -/
lemma homEquiv_baseChangeHomologyMap :
    (ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _ (baseChangeHomologyMap φ K n) =
      HomologicalComplex.homologyMap
          ((complexAdjunction (ModuleCat.extendRestrictScalarsAdj φ) (.up ℤ)).unit.app K) n ≫
        ((((baseChange φ).obj K).sc n).mapHomologyIso (ModuleCat.restrictScalars φ)).hom :=
  Equiv.apply_symm_apply _ _

/-- If `K` vanishes in degree `n + 1`, then `S ⊗_R H^n(K) ⟶ H^n(S ⊗_R K)` is an isomorphism:
both sides are cokernels of the differential into degree `n`, and scalar extension is right
exact. -/
theorem isIso_baseChangeHomologyMap_of_isZero (h : IsZero (K.X (n + 1))) :
    IsIso (baseChangeHomologyMap φ K n) := by
  let F := ModuleCat.extendScalars φ
  let G := ModuleCat.restrictScalars φ
  let adj := ModuleCat.extendRestrictScalarsAdj φ
  let FK := (baseChange φ).obj K
  have hnext : (ComplexShape.up ℤ).next n = n + 1 := CochainComplex.next ℤ n
  have hprev : (ComplexShape.up ℤ).prev n = n - 1 := CochainComplex.prev ℤ n
  have hK : K.d n (n + 1) = 0 := h.eq_of_tgt _ _
  have hFK : FK.d n (n + 1) = 0 := by
    change F.map (K.d n (n + 1)) = 0
    rw [hK, Functor.map_zero]
  let eK := K.iCyclesIso n (n + 1) hnext hK
  let eFK := FK.iCyclesIso n (n + 1) hnext hFK
  let pK : K.X n ⟶ K.homology n := eK.inv ≫ K.homologyπ n
  let pFK : FK.X n ⟶ FK.homology n := eFK.inv ≫ FK.homologyπ n
  have hcyc : eK.inv ≫ HomologicalComplex.cyclesMap
        ((complexAdjunction adj (.up ℤ)).unit.app K) n ≫
        ((FK.sc n).mapCyclesIso G).hom = adj.unit.app (K.X n) ≫ G.map eFK.inv := by
    rw [← cancel_mono (G.map eFK.hom)]
    simp only [Category.assoc, ← G.map_comp, Iso.inv_hom_id, G.map_id]
    erw [Category.comp_id]
    simp only [eFK, HomologicalComplex.iCyclesIso_hom]
    erw [ShortComplex.mapCyclesIso_hom_iCycles]
    erw [HomologicalComplex.cyclesMap_i]
    simp only [eK]
    erw [HomologicalComplex.iCyclesIso_inv_hom_id_assoc]
    rfl
  have hπ := DerivedPlus.homologyπ_mapHomologyIso_hom G (FK.sc n)
  have key : F.map pK ≫ baseChangeHomologyMap φ K n = pFK := by
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, homEquiv_baseChangeHomologyMap,
      Adjunction.homEquiv_unit]
    simp only [pK, pFK, Category.assoc, HomologicalComplex.homologyπ_naturality_assoc]
    erw [hπ]
    rw [G.map_comp, ← reassoc_of% hcyc]
    rfl
  have hzero : FK.toCycles (n - 1) n ≫ eFK.hom ≫ F.map pK = 0 := by
    simp only [eFK, HomologicalComplex.iCyclesIso_hom, HomologicalComplex.toCycles_i_assoc]
    change F.map (K.d (n - 1) n) ≫ F.map pK = 0
    rw [← F.map_comp]
    have : K.d (n - 1) n ≫ eK.inv = K.toCycles (n - 1) n := by
      rw [← HomologicalComplex.toCycles_i K (n - 1) n, Category.assoc]
      simp only [eK, HomologicalComplex.iCyclesIso_hom_inv_id, Category.comp_id]
    simp only [pK, ← Category.assoc, this, HomologicalComplex.toCycles_comp_homologyπ,
      Functor.map_zero]
  obtain ⟨ψ, hψ⟩ := CokernelCofork.IsColimit.desc' (FK.homologyIsCokernel (n - 1) n hprev)
    (eFK.hom ≫ F.map pK) hzero
  change FK.homologyπ n ≫ ψ = eFK.hom ≫ F.map pK at hψ
  have : F.IsLeftAdjoint := adj.isLeftAdjoint
  have : Epi (F.map pK) := F.map_epi _
  refine ⟨ψ, ?_, ?_⟩
  · rw [← cancel_epi (F.map pK), reassoc_of% key, Category.comp_id]
    simp only [pFK, Category.assoc, hψ, Iso.inv_hom_id_assoc]
  · rw [← cancel_epi (FK.homologyπ n), reassoc_of% hψ, key, Category.comp_id]
    simp only [pFK, Iso.hom_inv_id_assoc]

variable [HasDerivedCategory.{wC} (ModuleCat.{u} R)] [HasDerivedCategory.{wD} (ModuleCat.{u} S)]

/-- The `S`-linear comparison `S ⊗_R H^n(K) ⟶ H^n(S ⊗_R K)` on cohomology in the derived
category: the adjunct of `H^n` of the derived unit `K ⟶ φ_* (S ⊗_R K)`, followed by
`H^n(φ_* -) ≅ φ_* H^n(-)`. -/
def baseChangeDerivedHomologyMap :
    (ModuleCat.extendScalars φ).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj (DerivedCategory.Q.obj K)) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{u} S) n).obj
        (DerivedCategory.Q.obj ((baseChange φ).obj K)) :=
  ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).symm
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map
        (derivedComplexAdjunctionUnit (ModuleCat.extendRestrictScalarsAdj φ) K) ≫
      (DerivedPlus.mapDerivedCategoryHomologyIso (ModuleCat.restrictScalars φ) n).hom.app _)

/-- The adjunct of `baseChangeDerivedHomologyMap` is the defining `R`-linear map. -/
lemma homEquiv_baseChangeDerivedHomologyMap :
    (ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _ (baseChangeDerivedHomologyMap φ K n) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map
          (derivedComplexAdjunctionUnit (ModuleCat.extendRestrictScalarsAdj φ) K) ≫
        (DerivedPlus.mapDerivedCategoryHomologyIso (ModuleCat.restrictScalars φ) n).hom.app _ :=
  Equiv.apply_symm_apply _ _

/-- The derived comparison is the comparison on homology of complexes, through the canonical
identifications `H^n(Q K) ≅ K.homology n`. -/
theorem baseChangeDerivedHomologyMap_eq :
    baseChangeDerivedHomologyMap φ K n =
      (ModuleCat.extendScalars φ).map
          ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).hom.app K) ≫
        baseChangeHomologyMap φ K n ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} S) n).inv.app
          ((baseChange φ).obj K) := by
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    homEquiv_baseChangeDerivedHomologyMap]
  erw [homEquiv_baseChangeHomologyMap]
  rw [DerivedPlus.mapDerivedCategoryHomologyIso_hom_app_Q_obj]
  have hinv : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map
        ((ModuleCat.restrictScalars φ).mapDerivedCategoryFactors.inv.app
          (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj K)) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map
        ((ModuleCat.restrictScalars φ).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj K)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  simp only [derivedComplexAdjunctionUnit, Functor.map_comp, Category.assoc]
  erw [reassoc_of% hinv]
  have hn := (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).hom.naturality
    ((complexAdjunction (ModuleCat.extendRestrictScalarsAdj φ) (.up ℤ)).unit.app K)
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  rfl

/-- If `K` vanishes in degree `n + 1`, the derived comparison is an isomorphism in degree `n`. -/
theorem isIso_baseChangeDerivedHomologyMap_of_isZero (h : IsZero (K.X (n + 1))) :
    IsIso (baseChangeDerivedHomologyMap φ K n) := by
  have := isIso_baseChangeHomologyMap_of_isZero φ K n h
  rw [baseChangeDerivedHomologyMap_eq]
  infer_instance

variable {K} in
/-- The derived comparison is natural in chain maps. -/
@[reassoc]
theorem baseChangeDerivedHomologyMap_naturality {K' : CochainComplex (ModuleCat.{u} R) ℤ}
    (ψ : K ⟶ K') :
    (ModuleCat.extendScalars φ).map
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map (DerivedCategory.Q.map ψ)) ≫
      baseChangeDerivedHomologyMap φ K' n =
    baseChangeDerivedHomologyMap φ K n ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} S) n).map
        (DerivedCategory.Q.map ((baseChange φ).map ψ)) := by
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    homEquiv_baseChangeDerivedHomologyMap, homEquiv_baseChangeDerivedHomologyMap,
    ← Functor.map_comp_assoc, derivedComplexAdjunctionUnit_naturality, Functor.map_comp,
    Category.assoc, Category.assoc, DerivedPlus.mapDerivedCategoryHomologyIso_hom_naturality]
  rfl

variable {K} in
/-- Along a chain map that is a derived isomorphism and remains one after scalar extension, the
derived comparison of the source is an isomorphism exactly when that of the target is. -/
theorem isIso_baseChangeDerivedHomologyMap_iff {K' : CochainComplex (ModuleCat.{u} R) ℤ}
    (ψ : K ⟶ K') (hψ : IsIso (DerivedCategory.Q.map ψ))
    (hψ' : IsIso (DerivedCategory.Q.map ((baseChange φ).map ψ))) :
    IsIso (baseChangeDerivedHomologyMap φ K n) ↔ IsIso (baseChangeDerivedHomologyMap φ K' n) := by
  have h := baseChangeDerivedHomologyMap_naturality φ n ψ
  constructor
  · intro hc
    have : IsIso ((ModuleCat.extendScalars φ).map
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map (DerivedCategory.Q.map ψ)) ≫
        baseChangeDerivedHomologyMap φ K' n) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_left ((ModuleCat.extendScalars φ).map
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map (DerivedCategory.Q.map ψ)))
      (baseChangeDerivedHomologyMap φ K' n)
  · intro hc
    have : IsIso (baseChangeDerivedHomologyMap φ K n ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} S) n).map
          (DerivedCategory.Q.map ((baseChange φ).map ψ))) := by
      rw [← h]
      infer_instance
    exact IsIso.of_isIso_comp_right (baseChangeDerivedHomologyMap φ K n)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) n).map
        (DerivedCategory.Q.map ((baseChange φ).map ψ)))

/-- For a strictly perfect `K` and a derived morphism `b : S ⊗_R K ⟶ Y`, the comparison followed
by `H^n(b)` is the `S`-linear adjunct of `H^n` of the `R`-linear adjunct of `b`. -/
theorem homEquiv_baseChangeDerivedHomologyMap_comp (hK : IsStrictlyPerfect K)
    {Y : DerivedCategory (ModuleCat.{u} S)}
    (b : DerivedCategory.Q.obj ((baseChange φ).obj K) ⟶ Y) :
    (ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _
        (baseChangeDerivedHomologyMap φ K n ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} S) n).map b) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map
          (perfectScalarDerivedTargetHomEquiv φ K hK Y b) ≫
        (DerivedPlus.mapDerivedCategoryHomologyIso (ModuleCat.restrictScalars φ) n).hom.app Y := by
  rw [Adjunction.homEquiv_naturality_right, homEquiv_baseChangeDerivedHomologyMap,
    perfectScalarDerivedTargetHomEquiv_apply, Functor.map_comp, Category.assoc, Category.assoc,
    DerivedPlus.mapDerivedCategoryHomologyIso_hom_naturality]

end Langlands.Cohomology.ModuleComplex
