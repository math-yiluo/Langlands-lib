import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAffineQuotientDescent

/-! # Finite invariant covers with affine quotients descend to one level -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

/-- The object map determines a morphism of scheme-valued equivalence relations. -/
lemma CartesianMorphism.ext_of_objMap {E F : EtaleEquivalenceRelation.{u}}
    {a b : E ⟶ F} (h : a.objMap = b.objMap) : a = b := by
  apply CartesianMorphism.ext h
  apply F.hom_ext
  · rw [a.isCartesian.1, b.isCartesian.1, h]
  · rw [a.isCartesian.2.w, b.isCartesian.2.w, h]

/-- Affine quotients of open charts pull back along cartesian morphisms. -/
lemma IsCartesianHom.hasAffineQuotient_open_preimage
    {E F : EtaleEquivalenceRelation.{u}} [IsAffine E.U] [IsAffine F.U]
    {f : E.U ⟶ F.U} {g : E.R ⟶ F.R} (h : IsCartesianHom E F f g)
    (V : F.U.Opens) (hV : IsAffineOpen V)
    (hq : (F.chart V.ι).HasAffineQuotient) :
    (E.chart (f ⁻¹ᵁ V).ι).HasAffineQuotient := by
  let : IsAffine V.toScheme := hV
  let : IsAffine (f ⁻¹ᵁ V).toScheme := hV.preimage f
  exact etaleEquivalenceRelationCartesianAffineQuotient
    (E.chart (f ⁻¹ᵁ V).ι) (F.chart V.ι) (f ∣_ V)
    (h.invariantOpenMap V) (h.isCartesianHom_invariantOpenMap V)
    (show IsAffine (f ⁻¹ᵁ V).toScheme from hV.preimage f)
    (show IsAffine V.toScheme from hV) hq

namespace CartesianDiagram.OpenChart

variable {I : Type u} [Category.{u} I]
  (D : I ⥤ EtaleEquivalenceRelation.{u}) {S : Scheme.{u}}
  (t : D ⋙ objectFunctor ⟶ (Functor.const I).obj S) (V : S.Opens)

/-- The inverse-image open at each level. -/
def opens (i : I) : (D.obj i).U.Opens := t.app i ⁻¹ᵁ V

lemma preimage_opens {i j : I} (a : i ⟶ j) :
    (D.map a).objMap ⁻¹ᵁ opens D t V j = opens D t V i := by
  change (D.map a).objMap ⁻¹ᵁ (t.app j ⁻¹ᵁ V) = t.app i ⁻¹ᵁ V
  rw [← Scheme.Hom.comp_preimage]
  have hw : (D.map a).objMap ≫ t.app j = t.app i := by
    simpa using t.naturality a
  rw [hw]

/-- The actual restriction of a transition map to the inverse-image opens. -/
noncomputable def objMap {i j : I} (a : i ⟶ j) :
    (opens D t V i).toScheme ⟶ (opens D t V j).toScheme :=
  (D.map a).objMap.resLE _ _ (preimage_opens D t V a).ge

@[reassoc (attr := simp)]
lemma objMap_ι {i j : I} (a : i ⟶ j) :
    objMap D t V a ≫ (opens D t V j).ι =
      (opens D t V i).ι ≫ (D.map a).objMap :=
  Scheme.Hom.resLE_comp_ι _ _

lemma isPullback_objMap {i j : I} (a : i ⟶ j) :
    IsPullback (objMap D t V a) (opens D t V i).ι
      (opens D t V j).ι (D.map a).objMap := by
  apply IsOpenImmersion.isPullback
  · exact (objMap_ι D t V a).symm
  · simpa only [Scheme.Opens.opensRange_ι] using preimage_opens D t V a

/-- The induced cartesian map of open chart relations. -/
noncomputable def map {i j : I} (a : i ⟶ j) :
    (D.obj i).chart (opens D t V i).ι ⟶ (D.obj j).chart (opens D t V j).ι where
  objMap := objMap D t V a
  relMap := Chart.hom _ _ (objMap D t V a) (D.map a).isCartesian.1
    (D.map a).isCartesian.2.w (objMap_ι D t V a).symm
  isCartesian := Chart.isCartesianHom (D.map a).isCartesian
    (isPullback_objMap D t V a).flip

/-- The diagram of actual inverse-image open chart relations. -/
noncomputable def diagram : I ⥤ EtaleEquivalenceRelation.{u} where
  obj i := (D.obj i).chart (opens D t V i).ι
  map a := map D t V a
  map_id i := by
    apply CartesianMorphism.ext_of_objMap
    apply (cancel_mono (opens D t V i).ι).mp
    change objMap D t V (𝟙 i) ≫ _ = 𝟙 _ ≫ _
    simp
  map_comp a b := by
    apply CartesianMorphism.ext_of_objMap
    apply (cancel_mono (opens D t V _).ι).mp
    change objMap D t V (a ≫ b) ≫ _ =
      (objMap D t V a ≫ objMap D t V b) ≫ _
    simp [Category.assoc]

/-- Inclusion of each open chart into its original object scheme. -/
noncomputable def inclusion : diagram D t V ⋙ objectFunctor ⟶ D ⋙ objectFunctor where
  app i := (opens D t V i).ι
  naturality _ _ a := objMap_ι D t V a

variable (c : Cone D) (p : c.pt.U ⟶ S)
  (hp : ∀ i, (c.π.app i).objMap ≫ t.app i = p)

include hp in
lemma preimage_opens_cone (i : I) :
    (c.π.app i).objMap ⁻¹ᵁ opens D t V i = p ⁻¹ᵁ V := by
  change (c.π.app i).objMap ⁻¹ᵁ (t.app i ⁻¹ᵁ V) = p ⁻¹ᵁ V
  rw [← Scheme.Hom.comp_preimage, hp]

/-- The restricted object cone leg. -/
noncomputable def coneObjMap (i : I) :
    (p ⁻¹ᵁ V).toScheme ⟶ (opens D t V i).toScheme :=
  (c.π.app i).objMap.resLE _ _ (preimage_opens_cone D t V c p hp i).ge

@[reassoc (attr := simp)]
lemma coneObjMap_ι (i : I) :
    coneObjMap D t V c p hp i ≫ (opens D t V i).ι =
      (p ⁻¹ᵁ V).ι ≫ (c.π.app i).objMap :=
  Scheme.Hom.resLE_comp_ι _ _

lemma isPullback_coneObjMap (i : I) :
    IsPullback (coneObjMap D t V c p hp i) (p ⁻¹ᵁ V).ι
      (opens D t V i).ι (c.π.app i).objMap := by
  apply IsOpenImmersion.isPullback
  · exact (coneObjMap_ι D t V c p hp i).symm
  · simpa only [Scheme.Opens.opensRange_ι] using preimage_opens_cone D t V c p hp i

/-- The actual cartesian open-chart cone leg. -/
noncomputable def coneMap (i : I) :
    c.pt.chart (p ⁻¹ᵁ V).ι ⟶ (diagram D t V).obj i where
  objMap := coneObjMap D t V c p hp i
  relMap := Chart.hom _ _ (coneObjMap D t V c p hp i) (c.π.app i).isCartesian.1
    (c.π.app i).isCartesian.2.w (coneObjMap_ι D t V c p hp i).symm
  isCartesian := Chart.isCartesianHom (c.π.app i).isCartesian
    (isPullback_coneObjMap D t V c p hp i).flip

/-- The chart of the supplied cone over the fixed open. -/
noncomputable def cone : Cone (diagram D t V) where
  pt := c.pt.chart (p ⁻¹ᵁ V).ι
  π :=
    { app := coneMap D t V c p hp
      naturality := by
        intro i j a
        apply CartesianMorphism.ext_of_objMap
        apply (cancel_mono (opens D t V j).ι).mp
        change (𝟙 _ ≫ coneObjMap D t V c p hp j) ≫ _ =
          (coneObjMap D t V c p hp i ≫ objMap D t V a) ≫ _
        simp only [Category.id_comp, Category.assoc, objMap_ι, coneObjMap_ι_assoc,
          coneObjMap_ι]
        rw [← comp_objMap, c.w a] }

attribute [local instance] IsCofiltered.isConnected

/-- Restriction to a fixed open preserves the supplied cofiltered object limit. -/
noncomputable def isLimitObject [IsCofiltered I]
    (hc : IsLimit (objectFunctor.mapCone c)) :
    IsLimit (objectFunctor.mapCone (cone D t V c p hp)) :=
  isLimitOfIsPullbackOfIsConnected (inclusion D t V)
    (objectFunctor.mapCone (cone D t V c p hp)) (objectFunctor.mapCone c)
    { hom := (p ⁻¹ᵁ V).ι
      w := fun i => (coneObjMap_ι D t V c p hp i).symm }
    (isPullback_coneObjMap D t V c p hp) hc

variable [IsAffine S] [∀ i, IsAffine (D.obj i).U] [∀ i, IsAffine (D.obj i).R]

omit [∀ i, IsAffine (D.obj i).R] in
lemma isAffine_object (hV : IsAffineOpen V) (i : I) :
    IsAffine ((diagram D t V).obj i).U := by
  let : IsAffine ((D ⋙ objectFunctor).obj i) := inferInstanceAs (IsAffine (D.obj i).U)
  exact hV.preimage (t.app i)

lemma isAffine_relation (hV : IsAffineOpen V) (i : I) :
    IsAffine ((diagram D t V).obj i).R := by
  let : IsAffine (opens D t V i).toScheme := isAffine_object D t V hV i
  exact Chart.isAffine_arrows (D.obj i) (opens D t V i).ι

include hp in
/-- Affine quotients descend in the actual diagram of inverse-image charts. -/
lemma exists_hasAffineQuotient [IsCofiltered I]
    (hc : IsLimit (objectFunctor.mapCone c)) (hV : IsAffineOpen V)
    (hq : (c.pt.chart (p ⁻¹ᵁ V).ι).HasAffineQuotient) :
    ∃ i : I, ((D.obj i).chart (opens D t V i).ι).HasAffineQuotient := by
  let := isAffine_object D t V hV
  let := isAffine_relation D t V hV
  exact CartesianDiagram.exists_hasAffineQuotient (diagram D t V)
    (cone D t V c p hp) (isLimitObject D t V c p hp hc) hq

omit [∀ i, IsAffine (D.obj i).R] in
/-- A quotient in the open-chart diagram pulls back along every transition. -/
lemma hasAffineQuotient_of_map (hV : IsAffineOpen V) {i j : I} (a : i ⟶ j)
    (hq : ((diagram D t V).obj j).HasAffineQuotient) :
    ((diagram D t V).obj i).HasAffineQuotient :=
  etaleEquivalenceRelationCartesianAffineQuotient _ _
    ((diagram D t V).map a).objMap ((diagram D t V).map a).relMap
    ((diagram D t V).map a).isCartesian
    (isAffine_object D t V hV i) (isAffine_object D t V hV j) hq

end CartesianDiagram.OpenChart

namespace CartesianDiagram

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ EtaleEquivalenceRelation.{u}) (c : Cone D)
  [∀ i, IsAffine (D.obj i).U] [∀ i, IsAffine (D.obj i).R]
  (hc : IsLimit (objectFunctor.mapCone c))

include hc in
/-- A finite invariant affine cover with affine chart quotients descends to
one level with the same properties. -/
lemma exists_invariantAffineQuotientCover {K : Type u} [Finite K]
    (U : K → c.pt.U.Opens) (hcover : IsOpenCover U)
    (hU : ∀ k, IsAffineOpen (U k)) (hinv : ∀ k, c.pt.IsInvariantOpen (U k))
    (hq : ∀ k, (c.pt.chart (U k).ι).HasAffineQuotient) :
    ∃ (i : I) (V : K → (D.obj i).U.Opens), IsOpenCover V ∧
      ∀ k, IsAffineOpen (V k) ∧ (D.obj i).IsInvariantOpen (V k) ∧
        U k = (c.π.app i).objMap ⁻¹ᵁ V k ∧
        ((D.obj i).chart (V k).ι).HasAffineQuotient := by
  classical
  let M := invariantAffineCoverModel D c hc U hcover hU hinv
  let i := M.index
  let A := above D i
  let t := objectComparison D i
  let C := c.whisker (Over.forget i)
  let p := (c.π.app i).objMap
  have hp (j : Over i) : (C.π.app j).objMap ≫ t.app j = p :=
    cone_comparison D i c j
  have hA (j : Over i) : IsAffine (A.obj j).U := inferInstanceAs (IsAffine (D.obj j.left).U)
  have hAR (j : Over i) : IsAffine (A.obj j).R := inferInstanceAs (IsAffine (D.obj j.left).R)
  have hlimit : IsLimit (objectFunctor.mapCone C) := isLimitObjectAbove D i c hc
  have hquot (k : K) : (C.pt.chart (p ⁻¹ᵁ M.opens k).ι).HasAffineQuotient := by
    change (c.pt.chart (p ⁻¹ᵁ M.opens k).ι).HasAffineQuotient
    change (c.pt.chart ((c.π.app M.index).objMap ⁻¹ᵁ M.opens k).ι).HasAffineQuotient
    rw [← M.preimage_eq k]
    exact hq k
  choose j hj using fun k =>
    OpenChart.exists_hasAffineQuotient A t (M.opens k) C p hp hlimit
      (M.isAffine k) (hquot k)
  obtain ⟨l, fli, g, hg⟩ := IsCofiltered.wideCospan (fun k => (j k).hom)
  refine ⟨l, fun k => (D.map fli).objMap ⁻¹ᵁ M.opens k, ?_, fun k => ?_⟩
  · change (⨆ k, (D.map fli).objMap ⁻¹ᵁ M.opens k) = ⊤
    rw [← Scheme.Hom.preimage_iSup, M.isCover, Scheme.Hom.preimage_top]
  · refine ⟨(M.isAffine k).preimage _,
      (D.map fli).isCartesian.isInvariantOpen_preimage (M.isInvariant k), ?_, ?_⟩
    · rw [← Scheme.Hom.comp_preimage, ← comp_objMap, c.w fli]
      exact M.preimage_eq k
    · let a : (Over.mk fli : Over i) ⟶ j k := Over.homMk (g k) (hg k)
      exact OpenChart.hasAffineQuotient_of_map A t (M.opens k) (M.isAffine k) a (hj k)

/-- A common level retaining the finite cover and affine quotients of its
invariant chart relations. -/
structure InvariantAffineQuotientCoverModel {K : Type u} (U : K → c.pt.U.Opens)
    extends InvariantAffineCoverModel D c U where
  hasAffineQuotient : ∀ k, ((D.obj index).chart (opens k).ι).HasAffineQuotient

/-- Choose the actual descended finite invariant affine quotient cover. -/
noncomputable def invariantAffineQuotientCoverModel {K : Type u} [Finite K]
    (U : K → c.pt.U.Opens) (hcover : IsOpenCover U)
    (hU : ∀ k, IsAffineOpen (U k)) (hinv : ∀ k, c.pt.IsInvariantOpen (U k))
    (hq : ∀ k, (c.pt.chart (U k).ι).HasAffineQuotient) :
    InvariantAffineQuotientCoverModel D c U :=
  Classical.choice (by
    obtain ⟨i, V, hVcover, hV⟩ :=
      exists_invariantAffineQuotientCover D c hc U hcover hU hinv hq
    exact ⟨⟨⟨i, V, hVcover, fun k => (hV k).1, fun k => (hV k).2.1,
      fun k => (hV k).2.2.1⟩, fun k => (hV k).2.2.2⟩⟩)

/-- Pull back a chosen quotient cover to any further level, retaining its
prescribed inverse images in the limit. -/
noncomputable def InvariantAffineQuotientCoverModel.pullback
    {K : Type u} {U : K → c.pt.U.Opens}
    (M : InvariantAffineQuotientCoverModel D c U) {j : I} (a : j ⟶ M.index) :
    InvariantAffineQuotientCoverModel D c U where
  index := j
  opens k := (D.map a).objMap ⁻¹ᵁ M.opens k
  isCover := by
    change (⨆ k, (D.map a).objMap ⁻¹ᵁ M.opens k) = ⊤
    rw [← Scheme.Hom.preimage_iSup, M.isCover, Scheme.Hom.preimage_top]
  isAffine k := (M.isAffine k).preimage _
  isInvariant k := (D.map a).isCartesian.isInvariantOpen_preimage (M.isInvariant k)
  preimage_eq k := by
    rw [← Scheme.Hom.comp_preimage, ← comp_objMap, c.w a]
    exact M.preimage_eq k
  hasAffineQuotient k := (D.map a).isCartesian.hasAffineQuotient_open_preimage
    (M.opens k) (M.isAffine k) (M.hasAffineQuotient k)

end CartesianDiagram

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
