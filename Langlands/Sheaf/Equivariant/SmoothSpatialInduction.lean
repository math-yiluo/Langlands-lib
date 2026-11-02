import Langlands.Sheaf.Equivariant.SpatialLocallyConstant
import Langlands.Sheaf.Equivariant.SmoothPart

/-! # Smooth sheaves and local fixed sections under spatial induction -/

noncomputable section

universe u

namespace Langlands.Sheaf.Equivariant

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Topology
open Langlands.TopologicalInduction

variable (R : Type u) [CommRing R]

section LocalLifts

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Y : Type u} [TopologicalSpace Y] [MulAction G Y] [ContinuousConstSMul G Y]

/-- Local fixedness of a transported section lifts back at the translated point.
The witness is translated and its open subgroup is conjugated. -/
theorem IsLocallyFixedAt.of_map_arrow
    {F : (ActionOpens G Y)ᵒᵖ ⥤ ModuleCat.{u} R}
    {U W : ActionOpens G Y} (f : W ⟶ U) {s : F.obj (op U)} {x : Y}
    (hs : IsLocallyFixedAt R F ((F.map f.op).hom s) x) :
    IsLocallyFixedAt R F s (f.label • x) := by
  obtain ⟨V, hVW, K, hV, hxV, hfix⟩ := hs
  have hc : Continuous (MulAut.conj f.label⁻¹).toMonoidHom := by
    change Continuous fun k : G => f.label⁻¹ * k * (f.label⁻¹)⁻¹
    fun_prop
  let L : OpenSubgroup G := K.comap (MulAut.conj f.label⁻¹).toMonoidHom hc
  let V' := ActionOpens.translate f.label V
  have hconj (k : (L : Subgroup G)) : f.label⁻¹ * (k : G) * f.label ∈ K := by
    simpa [L, MulAut.conj_apply] using k.property
  have hV' : ∀ k : (L : Subgroup G), ∀ y ∈ V'.openSet, (k : G) • y ∈ V'.openSet := by
    intro k y hy
    change f.label⁻¹ • ((k : G) • y) ∈ V.openSet
    have hh := hV ⟨f.label⁻¹ * (k : G) * f.label, hconj k⟩
      (f.label⁻¹ • y) hy
    simpa only [mul_smul, smul_inv_smul] using hh
  have hV'U : V'.openSet ≤ U.openSet := by
    intro y hy
    have hh := f.mapsTo (f.label⁻¹ • y) (hVW hy)
    simpa only [smul_inv_smul] using hh
  let j := (ActionOpens.translationIso f.label V).inv
  have he : j ≫ ActionOpens.inclusionHom hVW ≫ f = ActionOpens.inclusionHom hV'U := by
    apply ActionOpens.Hom.ext
    simp [j, ActionOpens.translationIso, ActionOpens.inclusionHom]
  have hres := congrArg (fun k => (F.map k.op).hom s) he
  simp only [op_comp, CategoryTheory.Functor.map_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply] at hres
  refine ⟨V', hV'U, L, hV', ?_, fun k => ?_⟩
  · change f.label⁻¹ • (f.label • x) ∈ V.openSet
    simpa only [inv_smul_smul] using hxV
  · rw [← hres]
    exact map_invariantArrow_map_eq R F j K L hV hV'
      (fun k hk => by
        change f.label⁻¹ * k * (f.label⁻¹)⁻¹ ∈ K
        simpa only [inv_inv] using hconj ⟨k, hk⟩) _ hfix k

end LocalLifts

namespace SpatialInduction

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G) (hH : IsOpen (H : Set G))
  (X : Type u) [TopologicalSpace X] [MulAction H X] [ContinuousSMul H X]

/-- An open subgroup of the open subgroup is an actual open subgroup of the ambient group. -/
def openSubgroupImage (K : OpenSubgroup H) : OpenSubgroup G :=
  ⟨(K : Subgroup H).map H.subtype,
    hH.isOpenEmbedding_subtypeVal.isOpenMap _ K.isOpen⟩

omit [IsTopologicalGroup G] in
@[simp]
theorem mem_openSubgroupImage (K : OpenSubgroup H) (g : G) :
    g ∈ openSubgroupImage H hH K ↔ ∃ h : H, h ∈ K ∧ (h : G) = g := Iff.rfl

/-- Pull an actual ambient open back through the distinguished unit embedding. -/
def unitPreimage (U : ActionOpens G (Space H X)) : ActionOpens H X :=
  ⟨⟨unit H ⁻¹' U.openSet, U.openSet.isOpen.preimage continuous_unit⟩⟩

/-- The unit image of its preimage has its literal inclusion in the original open. -/
def unitPreimageArrow (U : ActionOpens G (Space H X)) :
    unitOpen H hH X (unitPreimage H X U) ⟶ U :=
  ActionOpens.inclusionHom (by rintro _ ⟨x, hx, rfl⟩; exact hx)

/-- A local fixed witness over the unit chart is a genuine ambient fixed witness. -/
theorem isLocallyFixedAt_of_restrict
    {F : (ActionOpens G (Space H X))ᵒᵖ ⥤ ModuleCat.{u} R}
    {U : ActionOpens H X} {s : F.obj (op (unitOpen H hH X U))} {x : X}
    (hs : IsLocallyFixedAt R ((unitFunctor H hH X).op ⋙ F) s x) :
    IsLocallyFixedAt R F s (unit H x) := by
  obtain ⟨V, hVU, K, hV, hxV, hfix⟩ := hs
  let L := openSubgroupImage H hH K
  have hunit : (unitOpen H hH X V).openSet ≤ (unitOpen H hH X U).openSet := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, hVU hy, rfl⟩
  have hstable : ∀ k : (L : Subgroup G), ∀ z ∈ (unitOpen H hH X V).openSet,
      (k : G) • z ∈ (unitOpen H hH X V).openSet := by
    rintro ⟨k, hk⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨h, hh, rfl⟩ := hk
    exact ⟨h • y, hV ⟨h, hh⟩ y hy, unit_subgroup_smul h y⟩
  have hi : (unitFunctor H hH X).map (ActionOpens.inclusionHom hVU) =
      ActionOpens.inclusionHom hunit := ActionOpens.Hom.ext rfl
  refine ⟨unitOpen H hH X V, hunit, L, hstable, ⟨x, hxV, rfl⟩, ?_⟩
  rintro ⟨k, hk⟩
  obtain ⟨h, hh, rfl⟩ := hk
  have ha : (unitFunctor H hH X).map
      (ActionOpens.invariantArrow (K : Subgroup H) V hV ⟨h, hh⟩) =
      ActionOpens.invariantArrow (L : Subgroup G) (unitOpen H hH X V) hstable
        ⟨(h : G), ⟨h, hh, rfl⟩⟩ := ActionOpens.Hom.ext rfl
  have ht := hfix ⟨h, hh⟩
  change (F.map ((unitFunctor H hH X).map
      (ActionOpens.invariantArrow (K : Subgroup H) V hV ⟨h, hh⟩)).op).hom
      ((F.map ((unitFunctor H hH X).map (ActionOpens.inclusionHom hVU)).op).hom s) =
    (F.map ((unitFunctor H hH X).map (ActionOpens.inclusionHom hVU)).op).hom s at ht
  rw [hi, ha] at ht
  exact ht

/-- Ambient local fixedness restricts to actual preimage neighbourhoods in the unit chart. -/
theorem isLocallyFixedAt_restrict
    {F : (ActionOpens G (Space H X))ᵒᵖ ⥤ ModuleCat.{u} R}
    {U : ActionOpens H X} {s : F.obj (op (unitOpen H hH X U))} {x : X}
    (hs : IsLocallyFixedAt R F s (unit H x)) :
    IsLocallyFixedAt R ((unitFunctor H hH X).op ⋙ F) s x := by
  obtain ⟨V, hVU, K, hV, hxV, hfix⟩ := hs
  let W := unitPreimage H X V
  let L := K.comap H.subtype continuous_subtype_val
  have hWU : W.openSet ≤ U.openSet := by
    intro y hy
    exact (mem_unitOpen H hH X U y).mp (hVU hy)
  have hW : ∀ h : (L : Subgroup H), ∀ y ∈ W.openSet, (h : H) • y ∈ W.openSet := by
    intro h y hy
    change unit H ((h : H) • y) ∈ V.openSet
    rw [unit_subgroup_smul]
    exact hV ⟨((h : H) : G), h.property⟩ _ hy
  let L' := openSubgroupImage H hH L
  have hW' : ∀ k : (L' : Subgroup G), ∀ z ∈ (unitOpen H hH X W).openSet,
      (k : G) • z ∈ (unitOpen H hH X W).openSet := by
    rintro ⟨k, hk⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨h, hh, rfl⟩ := hk
    exact ⟨h • y, hW ⟨h, hh⟩ y hy, unit_subgroup_smul h y⟩
  let i := unitPreimageArrow H hH X V
  have hi : i ≫ ActionOpens.inclusionHom hVU =
      (unitFunctor H hH X).map (ActionOpens.inclusionHom hWU) := by
    apply ActionOpens.Hom.ext
    simp [i, unitPreimageArrow, ActionOpens.inclusionHom]
  have hres := congrArg (fun k => (F.map k.op).hom s) hi
  simp only [op_comp, CategoryTheory.Functor.map_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply] at hres
  let j : unitOpen H hH X W ⟶ unitOpen H hH X U :=
    (unitFunctor H hH X).map (ActionOpens.inclusionHom hWU)
  change (F.map i.op).hom ((F.map (ActionOpens.inclusionHom hVU).op).hom s) =
    (F.map j.op).hom s at hres
  refine ⟨W, hWU, L, hW, hxV, fun h => ?_⟩
  have hk : (((h : H) : G)) ∈ L' := ⟨(h : H), h.property, rfl⟩
  change (F.map (ActionOpens.invariantArrow (L' : Subgroup G)
      (unitOpen H hH X W) hW' ⟨((h : H) : G), hk⟩).op).hom
      ((F.map j.op).hom s) = (F.map j.op).hom s
  rw [← hres]
  apply map_invariantArrow_map_eq R F i K L' hV hW' _ _ hfix
  intro k hk
  obtain ⟨h, hh, rfl⟩ := hk
  change (h : G) ∈ K at hh
  change (1 : G) * (h : G) * (1 : G)⁻¹ ∈ K
  simpa only [one_mul, inv_one, mul_one] using hh

/-- Unit-chart restriction preserves and reflects local fixedness of every section. -/
theorem isLocallyFixedAt_restrict_iff
    {F : (ActionOpens G (Space H X))ᵒᵖ ⥤ ModuleCat.{u} R}
    {U : ActionOpens H X} (s : F.obj (op (unitOpen H hH X U))) (x : X) :
    IsLocallyFixedAt R ((unitFunctor H hH X).op ⋙ F) s x ↔
      IsLocallyFixedAt R F s (unit H x) :=
  ⟨isLocallyFixedAt_of_restrict R H hH X, isLocallyFixedAt_restrict R H hH X⟩

/-- The full spatial restriction preserves and reflects smoothness. -/
theorem isSmoothSheaf_restrict_iff (F : TopologicalSheaf G (Space H X) (ModuleCat.{u} R)) :
    IsSmoothSheaf R H X ((restrict H hH X (ModuleCat.{u} R)).obj F) ↔
      IsSmoothSheaf R G (Space H X) F := by
  constructor
  · intro hs U s z hz
    obtain ⟨⟨g, x⟩, rfl⟩ := Quotient.exists_rep z
    let W := chartPreimage H X g U
    let f := chartArrow H hH X g U
    have hlocal := hs W ((F.obj.map f.op).hom s) x hz
    change IsLocallyFixedAt R ((unitFunctor H hH X).op ⋙ F.obj)
      ((F.obj.map f.op).hom s) x at hlocal
    have hamb := isLocallyFixedAt_of_restrict R H hH X (F := F.obj) hlocal
    have hresult := IsLocallyFixedAt.of_map_arrow R (F := F.obj) f hamb
    change IsLocallyFixedAt R F.obj s (g • unit H x) at hresult
    rw [smul_unit] at hresult
    change IsLocallyFixedAt R F.obj s (mk H g x)
    exact hresult
  · intro hs U s x hx
    exact isLocallyFixedAt_restrict R H hH X
      (hs (unitOpen H hH X U) s (unit H x) ⟨x, hx, rfl⟩)

/-- Unit-chart restriction on smooth sheaves retains the original full sheaf and maps. -/
def smoothRestrict :
    SmoothTopologicalSheaf R G (Space H X) ⥤ SmoothTopologicalSheaf R H X :=
  (smoothSheafProperty R H X).lift
    (smoothInclusion R G (Space H X) ⋙ restrict H hH X (ModuleCat.{u} R))
    (fun F => (isSmoothSheaf_restrict_iff R H hH X F.obj).2 F.property)

@[simp]
theorem smoothRestrict_obj_obj (F : SmoothTopologicalSheaf R G (Space H X)) :
    ((smoothRestrict R H hH X).obj F).obj =
      (restrict H hH X (ModuleCat.{u} R)).obj F.obj := rfl

@[simp]
theorem smoothRestrict_map_hom {F F' : SmoothTopologicalSheaf R G (Space H X)}
    (f : F ⟶ F') :
    ((smoothRestrict R H hH X).map f).hom =
      (restrict H hH X (ModuleCat.{u} R)).map f.hom := rfl

/-- Forgetting smoothness recovers the actual spatial restriction functor. -/
def smoothRestrictForgetIso :
    smoothRestrict R H hH X ⋙ smoothInclusion R H X ≅
      smoothInclusion R G (Space H X) ⋙ restrict H hH X (ModuleCat.{u} R) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The genuine right Kan spatial induction preserves and reflects smoothness. -/
theorem isSmoothSheaf_induce_iff (F : TopologicalSheaf H X (ModuleCat.{u} R)) :
    IsSmoothSheaf R G (Space H X) ((induce H hH X (ModuleCat.{u} R)).obj F) ↔
      IsSmoothSheaf R H X F := by
  constructor
  · intro hs
    exact IsSmoothSheaf.of_mono R
      ((restrictInduceIso H hH X (ModuleCat.{u} R)).app F).inv
      ((isSmoothSheaf_restrict_iff R H hH X _).2 hs)
  · intro hs
    apply (isSmoothSheaf_restrict_iff R H hH X _).1
    exact IsSmoothSheaf.of_mono R
      ((restrictInduceIso H hH X (ModuleCat.{u} R)).app F).hom hs

/-- Smooth spatial induction is the unchanged right Kan extension with proved smoothness. -/
def smoothInduce :
    SmoothTopologicalSheaf R H X ⥤ SmoothTopologicalSheaf R G (Space H X) :=
  (smoothSheafProperty R G (Space H X)).lift
    (smoothInclusion R H X ⋙ induce H hH X (ModuleCat.{u} R))
    (fun F => (isSmoothSheaf_induce_iff R H hH X F.obj).2 F.property)

@[simp]
theorem smoothInduce_obj_obj (F : SmoothTopologicalSheaf R H X) :
    ((smoothInduce R H hH X).obj F).obj =
      (induce H hH X (ModuleCat.{u} R)).obj F.obj := rfl

@[simp]
theorem smoothInduce_obj_presheaf (F : SmoothTopologicalSheaf R H X) :
    ((smoothInduce R H hH X).obj F).obj.obj =
      (unitFunctor H hH X).op.ran.obj F.obj.obj := rfl

@[simp]
theorem smoothInduce_map_hom {F F' : SmoothTopologicalSheaf R H X} (f : F ⟶ F') :
    ((smoothInduce R H hH X).map f).hom =
      (induce H hH X (ModuleCat.{u} R)).map f.hom := rfl

@[simp]
theorem smoothInduce_map_presheaf {F F' : SmoothTopologicalSheaf R H X} (f : F ⟶ F') :
    ((smoothInduce R H hH X).map f).hom.hom =
      (unitFunctor H hH X).op.ran.map f.hom.hom := rfl

/-- Forgetting smoothness recovers the original spatial right Kan functor. -/
def smoothInduceForgetIso :
    smoothInduce R H hH X ⋙ smoothInclusion R G (Space H X) ≅
      smoothInclusion R H X ⋙ induce H hH X (ModuleCat.{u} R) :=
  ObjectProperty.liftCompιIso _ _ _

/-- Restricting smooth spatial induction recovers the full local smooth sheaf. -/
def smoothRestrictInduceIso :
    smoothInduce R H hH X ⋙ smoothRestrict R H hH X ≅
      𝟭 (SmoothTopologicalSheaf R H X) :=
  NatIso.ofComponents (fun F => (smoothSheafProperty R H X).isoMk
    ((restrictInduceIso H hH X (ModuleCat.{u} R)).app F.obj)) (by
      intro F F' f
      apply ObjectProperty.hom_ext
      exact (restrictInduceIso H hH X (ModuleCat.{u} R)).hom.naturality f.hom)

/-- Smooth right Kan induction reconstructs the full ambient smooth sheaf. -/
def smoothInduceRestrictIso :
    smoothRestrict R H hH X ⋙ smoothInduce R H hH X ≅
      𝟭 (SmoothTopologicalSheaf R G (Space H X)) :=
  NatIso.ofComponents (fun F => (smoothSheafProperty R G (Space H X)).isoMk
    ((induceRestrictIso H hH X (ModuleCat.{u} R)).app F.obj)) (by
      intro F F' f
      apply ObjectProperty.hom_ext
      exact (induceRestrictIso H hH X (ModuleCat.{u} R)).hom.naturality f.hom)

/-- The equivalence of full smooth equivariant sheaf categories on the two actual spaces. -/
def smoothRestrictionEquivalence :
    SmoothTopologicalSheaf R G (Space H X) ≌ SmoothTopologicalSheaf R H X where
  functor := smoothRestrict R H hH X
  inverse := smoothInduce R H hH X
  unitIso := (smoothInduceRestrictIso R H hH X).symm
  counitIso := smoothRestrictInduceIso R H hH X
  functor_unitIso_comp F := by
    apply ObjectProperty.hom_ext
    exact (restrictionEquivalence H hH X (ModuleCat.{u} R)).functor_unit_comp F.obj

@[simp]
theorem smoothRestrictionEquivalence_functor :
    (smoothRestrictionEquivalence R H hH X).functor = smoothRestrict R H hH X := rfl

@[simp]
theorem smoothRestrictionEquivalence_inverse :
    (smoothRestrictionEquivalence R H hH X).inverse = smoothInduce R H hH X := rfl

instance smoothRestrict_full : (smoothRestrict R H hH X).Full :=
  (smoothRestrictionEquivalence R H hH X).fullyFaithfulFunctor.full

instance smoothRestrict_faithful : (smoothRestrict R H hH X).Faithful :=
  (smoothRestrictionEquivalence R H hH X).fullyFaithfulFunctor.faithful

instance smoothInduce_full : (smoothInduce R H hH X).Full :=
  (smoothRestrictionEquivalence R H hH X).fullyFaithfulInverse.full

instance smoothInduce_faithful : (smoothInduce R H hH X).Faithful :=
  (smoothRestrictionEquivalence R H hH X).fullyFaithfulInverse.faithful

instance smoothRestrict_isEquivalence : (smoothRestrict R H hH X).IsEquivalence :=
  (smoothRestrictionEquivalence R H hH X).isEquivalence_functor

instance smoothInduce_isEquivalence : (smoothInduce R H hH X).IsEquivalence :=
  (smoothRestrictionEquivalence R H hH X).isEquivalence_inverse

end SpatialInduction
end Langlands.Sheaf.Equivariant
