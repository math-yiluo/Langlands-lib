import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitUniquenessStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitMorphismDescentQuasiSeparatedProof

/-! # Eventual equality and uniqueness of algebraic-space models -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.Action

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace SpaceLimitUniqueness

open SpaceFilteredPoints SpaceLimitMorphisms BaseChangeComparison

variable {S B : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- A morphism is determined by its value on the universal point of an atlas. -/
theorem hom_ext_atlas {U : Over S} (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (ha : IsEtale a) (hs : IsSurjective a) (φ ψ : X ⟶ Y)
    (h : mapSections φ U (atlasSection a (𝟙 U)) =
      mapSections ψ U (atlasSection a (𝟙 U))) : φ = ψ := by
  apply (homEquiv X Y).injective
  ext T x
  obtain ⟨T⟩ := T
  obtain ⟨V, e, v, he, hse, hv⟩ := exists_atlas_lift a ha hs x
  have : Etale e.left := he
  have : Surjective e.left := hse
  apply pullback_injective Y e
  change Y.pullback e (mapSections φ T x) = Y.pullback e (mapSections ψ T x)
  rw [mapSections_naturality, mapSections_naturality, ← hv]
  have heval (f : X ⟶ Y) :
      mapSections f V (atlasSection a v) =
        Y.pullback v (mapSections f U (atlasSection a (𝟙 U))) := by
    rw [mapSections_naturality, atlasSection_pullback, Category.comp_id]
  rw [heval, heval, h]

/-- Equality after base change holds on any test whose structure map factors through it. -/
theorem section_eq_of_baseChangeMap_eq (p : B ⟶ S) (φ ψ : X ⟶ Y)
    (h : baseChangeMap p φ = baseChangeMap p ψ)
    (V : Over S) (q : V.left ⟶ B) (hq : q ≫ p = V.hom) (x : X.sections V) :
    mapSections φ V x = mapSections ψ V x := by
  let W : Over B := Over.mk q
  let e : (Over.map p).obj W ≅ V := Over.isoMk (Iso.refl _) (by simp [W, hq])
  apply (Y.presheaf.mapIso e.op).toEquiv.injective
  change Y.pullback e.hom (mapSections φ V x) =
    Y.pullback e.hom (mapSections ψ V x)
  rw [mapSections_naturality, mapSections_naturality]
  exact congrArg (fun f => mapSections f W (X.pullback e.hom x)) h

/-- On the base-changed atlas, equality is detected on its original atlas section. -/
theorem baseChangeMap_eq_of_section_eq (p : B ⟶ S) {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ X.presheaf) (ha : IsEtale a) (hs : IsSurjective a)
    (φ ψ : X ⟶ Y)
    (h : Y.pullback (overHom (T := U) (pullback.snd p U.hom))
          (mapSections φ U (atlasSection a (𝟙 U))) =
      Y.pullback (overHom (T := U) (pullback.snd p U.hom))
          (mapSections ψ U (atlasSection a (𝟙 U)))) :
    baseChangeMap p φ = baseChangeMap p ψ := by
  apply hom_ext_atlas (baseAtlas p a) (isEtale_baseAtlas p a ha)
    (isSurjective_baseAtlas p a hs)
  let V := overOf (T := U) (pullback.snd p U.hom)
  let W := (Over.map p).obj (baseOver p U)
  let e : W ≅ V := Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ pullback.snd p U.hom ≫ U.hom = pullback.fst p U.hom ≫ p
    rw [Category.id_comp, pullback.condition])
  have hx : X.pullback e.hom (X.pullback (overHom (T := U) (pullback.snd p U.hom))
      (atlasSection a (𝟙 U))) = atlasSection (baseAtlas p a) (𝟙 _) := by
    rw [← X.pullback_comp, atlasSection_pullback, baseAtlas_app]
    congr 2
  have hh := congrArg (Y.pullback e.hom) h
  rw [mapSections_naturality, mapSections_naturality,
    mapSections_naturality, mapSections_naturality, hx] at hh
  exact hh

/-- Eventual equality for fixed spaces over an affine base and a relative affine diagram. -/
theorem eventual_eq {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)] [IsAffine S]
    (t : D ⟶ (Functor.const I).obj S) (c : Cone D) (hc : IsLimit c)
    (p : c.pt ⟶ S) (hp : ∀ i, c.π.app i ≫ t.app i = p)
    (hX : HasAtlasProperty (@QuasiCompact.{u}) X)
    (hY : LocallyOfFiniteTypeOverBase Y) (φ ψ : X ⟶ Y)
    (h : baseChangeMap p φ = baseChangeMap p ψ) :
    ∃ i, baseChangeMap (t.app i) φ = baseChangeMap (t.app i) ψ := by
  obtain ⟨U, a, ha, hs, hU⟩ := exists_affine_qc_atlas X hX
  obtain ⟨V, b, hb, hsb, hV⟩ := hY
  have : LocallyOfFiniteType V.hom := hV
  let DU := TargetLimit.diagram D t U.hom
  let cU := TargetLimit.cone D t U.hom c p hp
  have hcU : IsLimit cU := TargetLimit.isLimitCone D t U.hom c p hp hc
  let tU := TargetLimit.comparison D t U.hom
  have hpU : ∀ i, cU.π.app i ≫ tU.app i = pullback.snd p U.hom :=
    fun i => AffineLimit.cone_π_snd D t U.hom c p hp i
  let x : X.sections U := atlasSection a (𝟙 U)
  have heq : Y.pullback (overHom (T := U) (pullback.snd p U.hom))
        (mapSections φ U x) =
      Y.pullback (overHom (T := U) (pullback.snd p U.hom))
        (mapSections ψ U x) := by
    rw [mapSections_naturality, mapSections_naturality]
    exact section_eq_of_baseChangeMap_eq p φ ψ h _ (pullback.fst p U.hom)
      pullback.condition _
  obtain ⟨j, hj⟩ := exists_eq_of_limit b hb hsb DU tU cU hcU _ hpU
    (mapSections φ U x) (mapSections ψ U x) heq
  exact ⟨j, baseChangeMap_eq_of_section_eq (t.app j) a ha hs φ ψ hj⟩

section Rebase

/-- Reindex a morphism between base changes, retaining the chosen common base. -/
def rebase {U V : Over S} (f : V ⟶ U)
    (a : baseChange U.hom X ⟶ baseChange U.hom Y) :
    baseChange V.hom X ⟶ baseChange V.hom Y :=
  (compIso U.hom f.left V.hom (Over.w f) X).inv ≫ baseChangeMap f.left a ≫
    (compIso U.hom f.left V.hom (Over.w f) Y).hom

theorem mapSections_rebase {U V : Over S} (f : V ⟶ U)
    (a : baseChange U.hom X ⟶ baseChange U.hom Y) (T : Over V.left)
    (x : (baseChange V.hom X).sections T) :
    mapSections (rebase f a) T x =
      Y.pullback (overIso U.hom f.left V.hom (Over.w f) T).hom
        (mapSections a ((Over.map f.left).obj T)
          (X.pullback (overIso U.hom f.left V.hom (Over.w f) T).inv x)) := rfl

@[simp]
theorem rebase_id {U V : Over S} (f : V ⟶ U) :
    rebase (X := X) f (𝟙 (baseChange U.hom X)) = 𝟙 _ := by
  unfold rebase
  change _ ≫ 𝟙 _ ≫ _ = _
  simp

@[simp]
theorem rebase_comp {Z : AlgebraicSpace S} {U V : Over S} (f : V ⟶ U)
    (a : baseChange U.hom X ⟶ baseChange U.hom Y)
    (b : baseChange U.hom Y ⟶ baseChange U.hom Z) :
    rebase f (a ≫ b) = rebase f a ≫ rebase f b := by
  unfold rebase
  change _ ≫ (baseChangeMap f.left a ≫ baseChangeMap f.left b) ≫ _ = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

theorem rebase_injective {U V : Over S} (f : V ⟶ U)
    {a b : baseChange U.hom X ⟶ baseChange U.hom Y}
    (h : rebase f a = rebase f b) : baseChangeMap f.left a = baseChangeMap f.left b := by
  simpa only [rebase, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
    Iso.hom_inv_id, Category.comp_id] using congrArg
      (fun k => (compIso U.hom f.left V.hom (Over.w f) X).hom ≫ k ≫
        (compIso U.hom f.left V.hom (Over.w f) Y).inv) h

/-- Coherence of reindexing along two successive maps of schemes over the base. -/
theorem rebase_rebase {U V W : Over S} (f : V ⟶ U) (g : W ⟶ V)
    (a : baseChange U.hom X ⟶ baseChange U.hom Y) :
    rebase g (rebase f a) = rebase (g ≫ f) a := by
  apply (homEquiv _ _).injective
  ext T x
  obtain ⟨T⟩ := T
  change mapSections (rebase g (rebase f a)) T x = mapSections (rebase (g ≫ f) a) T x
  rw [mapSections_rebase, mapSections_rebase, mapSections_rebase]
  let eg := overIso V.hom g.left W.hom (Over.w g) T
  let ef := overIso U.hom f.left V.hom (Over.w f) ((Over.map g.left).obj T)
  let efg := overIso U.hom (g ≫ f).left W.hom (Over.w (g ≫ f)) T
  let q := overIso f.left g.left (g ≫ f).left rfl T
  have hout : eg.hom ≫ ef.hom = efg.hom ≫ (Over.map U.hom).map q.hom := by
    ext1
    simp [eg, ef, efg, q]
  have hin : (Over.map U.hom).map q.hom ≫ ef.inv ≫ eg.inv = efg.inv := by
    ext1
    simp [eg, ef, efg, q]
  change Y.pullback eg.hom (Y.pullback ef.hom
      (mapSections a _ (X.pullback ef.inv (X.pullback eg.inv x)))) =
    Y.pullback efg.hom (mapSections a _ (X.pullback efg.inv x))
  rw [← Y.pullback_comp, hout, Y.pullback_comp]
  have hn := mapSections_naturality a q.hom (X.pullback ef.inv (X.pullback eg.inv x))
  change Y.pullback ((Over.map U.hom).map q.hom) _ = _ at hn
  rw [hn]
  congr 2
  change X.pullback ((Over.map U.hom).map q.hom)
    (X.pullback ef.inv (X.pullback eg.inv x)) = X.pullback efg.inv x
  rw [← X.pullback_comp, ← X.pullback_comp, Category.assoc, hin]

/-- Solve the comparison equation for the literal base change of the morphism. -/
theorem baseChangeMap_eq_of_rebase_eq {U V : Over S} (f : V ⟶ U)
    (a : baseChange U.hom X ⟶ baseChange U.hom Y)
    (b : baseChange V.hom X ⟶ baseChange V.hom Y) (h : rebase f a = b) :
    baseChangeMap f.left a =
      (compIso U.hom f.left V.hom (Over.w f) X).hom ≫ b ≫
        (compIso U.hom f.left V.hom (Over.w f) Y).inv := by
  simpa only [rebase, Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using congrArg
      (fun k => (compIso U.hom f.left V.hom (Over.w f) X).hom ≫ k ≫
        (compIso U.hom f.left V.hom (Over.w f) Y).inv) h

end Rebase

section RelativeDiagram

variable {I : Type u} [SmallCategory I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)] [IsAffine S]
  (t : D ⟶ (Functor.const I).obj S) (c : Cone D) (hc : IsLimit c)
  (p : c.pt ⟶ S) (hp : ∀ i, c.π.app i ≫ t.app i = p)

include hc in
/-- Morphism descent expressed using the iterated-base-change comparison. -/
theorem exists_rebase_map (hXqs : IsQuasiSeparated X)
    (hX : HasAtlasProperty (@QuasiCompact.{u}) X)
    (hY : LocallyOfFinitePresentationOverBase Y)
    (a : baseChange p X ⟶ baseChange p Y) :
    ∃ (i : I) (b : baseChange (t.app i) X ⟶ baseChange (t.app i) Y),
      rebase ((Over.liftCone D t c p hp).π.app i) b = a := by
  obtain ⟨i, b, hb⟩ := spaceLimitMorphismDescentQuasiSeparated I D S t c hc p hp
    X Y hXqs hX hY a
  refine ⟨i, b, ?_⟩
  apply (homEquiv _ _).injective
  ext T x
  obtain ⟨T⟩ := T
  exact (hb T x).symm

include hc in
omit [IsAffine S] in
/-- Stage morphisms with equal limit maps become equal at a later stage. -/
theorem eventual_rebase_eq (hX : HasAtlasProperty (@QuasiCompact.{u}) X)
    (hY : LocallyOfFiniteTypeOverBase Y) {i : I}
    (a b : baseChange (t.app i) X ⟶ baseChange (t.app i) Y)
    (h : rebase ((Over.liftCone D t c p hp).π.app i) a =
      rebase ((Over.liftCone D t c p hp).π.app i) b) :
    ∃ (j : I) (f : j ⟶ i), rebase ((Over.lift D t).map f) a =
      rebase ((Over.lift D t).map f) b := by
  have hlim := rebase_injective _ h
  have hXqc := hX.baseChange (g := t.app i)
  have hYft := hY.baseChange (g := t.app i)
  obtain ⟨j, hj⟩ := eventual_eq (overDiagram D i) (overStructure D i)
    (c.whisker (Over.forget i)) (overConeIsLimit i c hc) (c.π.app i)
    (overCone_π_comp i c) hXqc hYft a b hlim
  refine ⟨j.left, j.hom, ?_⟩
  unfold rebase
  change _ ≫ baseChangeMap (D.map j.hom) a ≫ _ =
    _ ≫ baseChangeMap (D.map j.hom) b ≫ _
  change baseChangeMap (D.map j.hom) a = baseChangeMap (D.map j.hom) b at hj
  rw [hj]

include hc in
/-- An isomorphism over the affine limit descends to a stage. -/
theorem exists_rebase_iso (hXqs : IsQuasiSeparated X)
    (hX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (hYqs : IsQuasiSeparated Y)
    (hY : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Y)
    (e : baseChange p X ≅ baseChange p Y) :
    ∃ (i : I) (b : baseChange (t.app i) X ≅ baseChange (t.app i) Y),
      rebase ((Over.liftCone D t c p hp).π.app i) b.hom = e.hom := by
  have hXqc : HasAtlasProperty (@QuasiCompact.{u}) X := hX.mono (fun _ _ _ h => h.2)
  have hYqc : HasAtlasProperty (@QuasiCompact.{u}) Y := hY.mono (fun _ _ _ h => h.2)
  have hXfp : LocallyOfFinitePresentationOverBase X := hX.mono (fun _ _ _ h => h.1)
  have hYfp : LocallyOfFinitePresentationOverBase Y := hY.mono (fun _ _ _ h => h.1)
  obtain ⟨i, a, ha⟩ := exists_rebase_map D t c hc p hp hXqs hXqc hYfp e.hom
  obtain ⟨j, b, hb⟩ := exists_rebase_map D t c hc p hp hYqs hYqc hXfp e.inv
  let d := Over.lift D t
  let l := Over.liftCone D t c p hp
  obtain ⟨k, f, g, _⟩ := IsCofilteredOrEmpty.cone_objs i j
  let ak := rebase (d.map f) a
  let bk := rebase (d.map g) b
  have hak : rebase (l.π.app k) ak = e.hom := by
    dsimp only [ak]
    rw [rebase_rebase, l.w f]
    exact ha
  have hbk : rebase (l.π.app k) bk = e.inv := by
    dsimp only [bk]
    rw [rebase_rebase, l.w g]
    exact hb
  have hab : rebase (l.π.app k) (ak ≫ bk) = rebase (l.π.app k) (𝟙 _) := by
    rw [rebase_comp, hak, hbk, e.hom_inv_id, rebase_id]
    rfl
  have hba : rebase (l.π.app k) (bk ≫ ak) = rebase (l.π.app k) (𝟙 _) := by
    rw [rebase_comp, hbk, hak, e.inv_hom_id, rebase_id]
    rfl
  obtain ⟨v, r, hr⟩ := eventual_rebase_eq D t c hc p hp hXqc
    hXfp.locallyOfFiniteType (ak ≫ bk) (𝟙 _) hab
  obtain ⟨w, s, hs⟩ := eventual_rebase_eq D t c hc p hp hYqc
    hYfp.locallyOfFiniteType (bk ≫ ak) (𝟙 _) hba
  change rebase (d.map r) (ak ≫ bk) =
    rebase (d.map r) (𝟙 (baseChange (d.obj k).hom X)) at hr
  change rebase (d.map s) (bk ≫ ak) =
    rebase (d.map s) (𝟙 (baseChange (d.obj k).hom Y)) at hs
  obtain ⟨m, r', s', hcomm⟩ := IsCofiltered.cospan r s
  let q := r' ≫ r
  let am := rebase (d.map q) ak
  let bm := rebase (d.map q) bk
  have ham : am ≫ bm = 𝟙 _ := by
    dsimp only [am, bm]
    rw [← rebase_comp]
    have hh := congrArg (rebase (d.map r')) hr
    simpa only [rebase_rebase, ← d.map_comp, rebase_id] using hh
  have hbm : bm ≫ am = 𝟙 _ := by
    dsimp only [am, bm]
    rw [← rebase_comp]
    have hh := congrArg (rebase (d.map s')) hs
    simpa only [rebase_rebase, ← d.map_comp, rebase_id, ← hcomm] using hh
  refine ⟨m, ⟨am, bm, ham, hbm⟩, ?_⟩
  change rebase (l.π.app m) am = e.hom
  dsimp only [am]
  rw [rebase_rebase, l.w q, hak]

end RelativeDiagram

end SpaceLimitUniqueness

open SpaceLimitUniqueness SpaceFilteredPoints

/-- Eventual equality of morphisms of finitely presented algebraic spaces. -/
theorem spaceLimitMorphismEventualEquality : SpaceLimitMorphismEventualEquality.{u} := by
  intro I _ _ D _ c hc i X Y hXqs hX hYqs hY φ ψ h
  have hXqc : HasAtlasProperty (@QuasiCompact.{u}) X :=
    hX.mono (fun _ _ _ h => h.2)
  have hYfp : LocallyOfFinitePresentationOverBase Y := hY.mono (fun _ _ _ h => h.1)
  have hYft : LocallyOfFiniteTypeOverBase Y := hYfp.locallyOfFiniteType
  obtain ⟨j, hj⟩ := eventual_eq (overDiagram D i) (overStructure D i)
    (c.whisker (Over.forget i)) (overConeIsLimit i c hc) (c.π.app i)
    (overCone_π_comp i c) hXqc hYft φ ψ h
  exact ⟨j.left, j.hom, hj⟩

/-- Essential uniqueness of finitely presented algebraic-space models. -/
theorem spaceLimitModelUniqueness : SpaceLimitModelUniqueness.{u} := by
  intro I _ _ D _ c hc i X Y hXqs hX hYqs hY e
  constructor
  · obtain ⟨j, h, hj⟩ := exists_rebase_iso (overDiagram D i) (overStructure D i)
      (c.whisker (Over.forget i)) (overConeIsLimit i c hc) (c.π.app i)
      (overCone_π_comp i c) hXqs hX hYqs hY e
    refine ⟨j.left, j.hom, h, ?_⟩
    change rebase (Over.homMk (c.π.app j.left) (c.w j.hom) :
      Over.mk (c.π.app i) ⟶ Over.mk (D.map j.hom)) h.hom = e.hom at hj
    exact baseChangeMap_eq_of_rebase_eq (X := X) (Y := Y)
      (U := Over.mk (D.map j.hom)) (V := Over.mk (c.π.app i))
      (Over.homMk (c.π.app j.left) (c.w j.hom)) h.hom e.hom hj
  · intro j f h h' hh hh'
    exact spaceLimitMorphismEventualEquality I D c hc j _ _
      (hXqs.baseChange (g := D.map f)) (hX.baseChange (g := D.map f))
      (hYqs.baseChange (g := D.map f)) (hY.baseChange (g := D.map f))
      h.hom h'.hom (hh.trans hh'.symm)

/-- Conrad's Theorem 3.4(1), injectivity, and (3), for algebraic spaces. -/
theorem spaceLimitUniquenessStatement : SpaceLimitUniquenessStatement.{u} :=
  ⟨spaceLimitMorphismEventualEquality, spaceLimitModelUniqueness⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
