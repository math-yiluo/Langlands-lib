import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeTargetUniversallyClosed
import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineTargetFamilyBaseChange

/-! # Universal closedness of target families after arbitrary scheme base change -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Topology

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S T : Scheme.{u}}

/-- The actual projection of a presheaf fibre to its test scheme's ordinary points. -/
def fibreSchemeProjection {F G : Presheaf S} (f : F ⟶ G) {U : Over S}
    (y : (schemeYoneda S).obj U ⟶ G) : Points (Limits.pullback f y) → U.left :=
  schemePointsTo U ∘ Points.map (pullback.snd f y)

/-- Closedness of a fibre projection can be tested on ordinary scheme points. -/
theorem isClosedMap_fibreSchemeProjection_iff {F G : Presheaf S} (f : F ⟶ G) {U : Over S}
    (y : (schemeYoneda S).obj U ⟶ G) :
    @IsClosedMap _ _ (pointTopology (Limits.pullback f y)) _ (fibreSchemeProjection f y) ↔
      @IsClosedMap _ _ (pointTopology (Limits.pullback f y))
        (pointTopology ((schemeYoneda S).obj U)) (Points.map (pullback.snd f y)) := by
  let := pointTopology (Limits.pullback f y)
  let := pointTopology ((schemeYoneda S).obj U)
  constructor
  · intro h
    have hc := (schemePointsHomeomorph U).symm.isClosedMap.comp h
    have he : (schemePointsHomeomorph U).symm ∘ fibreSchemeProjection f y =
        Points.map (pullback.snd f y) := by
      funext x
      exact schemePoint_schemePointsTo U _
    rwa [he] at hc
  · exact fun h => (schemePointsHomeomorph U).isClosedMap.comp h

/-- Forgetting the recorded base fixes the underlying point of a represented scheme. -/
theorem schemePointsTo_forgetBaseHomeomorph (g : T ⟶ S) (U : Over T)
    (x : Points ((schemeYoneda T).obj U)) :
    schemePointsTo ((Over.map g).obj U) (forgetBaseSchemePointsHomeomorph g U x) =
      schemePointsTo U x := by
  exact schemePointsTo_schemePoint _ _

/-- The standard fibre-restriction homeomorphism preserves ordinary test-scheme projection. -/
theorem fibreSchemeProjection_restriction (g : T ⟶ S)
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) {U : Over T}
    (y : (schemeYoneda T).obj U ⟶ (baseChange g Y).presheaf)
    (x : Points (Limits.pullback (hom (baseChangeMap g f)) y)) :
    fibreSchemeProjection (hom f) (originalBaseChart g y)
      (fibreRestrictionPointsHomeomorph g f y x) =
      fibreSchemeProjection (hom (baseChangeMap g f)) y x := by
  dsimp only [fibreSchemeProjection, Function.comp_apply]
  rw [fibreRestrictionPointsHomeomorph_snd, schemePointsTo_forgetBaseHomeomorph]

/-- Structural fibre comparison after base change preserves ordinary scheme projection. -/
theorem structuralBaseChangeFibreHomeomorph_schemeProjection (g : T ⟶ S)
    (X : AlgebraicSpace S) {Q : Scheme.{u}} (t : Q ⟶ T)
    (x : Points (Limits.pullback (hom (structuralMorphism (baseChange g X)))
      ((schemeYoneda T).map (SchemeTargetRebase.baseTest (V := Over.mk (𝟙 T)) t)))) :
    fibreSchemeProjection (hom (structuralMorphism X))
      ((schemeYoneda S).map (SchemeTargetRebase.baseTest (V := Over.mk (𝟙 S)) (t ≫ g)))
      (structuralBaseChangeFibreHomeomorph g X t x) =
    fibreSchemeProjection (hom (structuralMorphism (baseChange g X)))
      ((schemeYoneda T).map (SchemeTargetRebase.baseTest (V := Over.mk (𝟙 T)) t)) x := by
  let e := (forgetToPresheaf T).mapIso (restrictedBaseIso g)
  have w : (𝟙 (baseChange g X).presheaf) ≫ hom (baseChangeMap g (structuralMorphism X)) =
      hom (structuralMorphism (baseChange g X)) ≫ e.hom :=
    (restrictedBaseIsTerminal g).hom_ext _ _
  let y := (schemeYoneda T).map (SchemeTargetRebase.baseTest (V := Over.mk (𝟙 T)) t)
  let e₁ := fibrePullbackIsoOfArrowIso
    (hom (structuralMorphism (baseChange g X)))
    (hom (baseChangeMap g (structuralMorphism X))) (Iso.refl _) e w (y ≫ e.hom)
  have he : (y ≫ e.hom) ≫ e.inv = y := by simp
  let e₂ := pullback.congrHom
    (f₁ := hom (structuralMorphism (baseChange g X))) rfl he
  have hy : originalBaseChart g (y ≫ e.hom) =
      (schemeYoneda S).map (SchemeTargetRebase.baseTest (V := Over.mk (𝟙 S)) (t ≫ g)) :=
    (basePresheafIsTerminal S).hom_ext _ _
  let e₃ := pullback.congrHom (f₁ := hom (structuralMorphism X)) rfl hy
  have h₃ : e₃.hom ≫ pullback.snd (hom (structuralMorphism X))
      ((schemeYoneda S).map (SchemeTargetRebase.baseTest (V := Over.mk (𝟙 S)) (t ≫ g))) =
      pullback.snd (hom (structuralMorphism X)) (originalBaseChart g (y ≫ e.hom)) := by
    simp only [e₃, pullback.congrHom_hom, pullback.map, pullback.lift_snd, Category.comp_id]
  have h₁ := fibrePullbackIsoOfArrowIso_hom_snd
    (hom (structuralMorphism (baseChange g X)))
    (hom (baseChangeMap g (structuralMorphism X))) (Iso.refl _) e w (y ≫ e.hom)
  have h₂ : e₂.inv ≫ pullback.snd (hom (structuralMorphism (baseChange g X)))
      ((y ≫ e.hom) ≫ e.inv) =
      pullback.snd (hom (structuralMorphism (baseChange g X))) y := by
    simp only [e₂, pullback.congrHom_inv, pullback.map, pullback.lift_snd, Category.comp_id]
  change schemePointsTo _ (Points.map _
    (Points.map e₃.hom (fibreRestrictionPointsHomeomorph g (structuralMorphism X)
      (y ≫ e.hom) (Points.map e₁.hom (Points.map e₂.inv x))))) = _
  erw [← Points.map_comp, h₃, fibreRestrictionPointsHomeomorph_snd,
    schemePointsTo_forgetBaseHomeomorph]
  erw [← Points.map_comp, h₁, ← Points.map_comp, h₂]
  rfl

/-- The recovered test homeomorphism fixes its underlying ordinary scheme point. -/
theorem schemePointsTo_testSchemeHomeomorph {V U : Over S} (r : U ⟶ V)
    (x : Points ((schemeYoneda V.left).obj (Over.mk r.left))) :
    schemePointsTo U (SchemeTargetRebase.testSchemePointsHomeomorph r x) =
      schemePointsTo (Over.mk r.left) x := by
  change schemePointsTo U (Points.map
    ((schemeYoneda S).map (SchemeTargetRebase.testBaseIso r).hom)
    (forgetBaseSchemePointsHomeomorph V.hom (Over.mk r.left) x)) = _
  rw [schemePointsTo_map, schemePointsTo_forgetBaseHomeomorph]
  rfl

namespace AffineTargetFamily

variable {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {V : Over S} (b : (schemeYoneda S).obj V ⟶ Y.presheaf)

/-- A family-test homeomorphism preserves projection to the ordinary test scheme. -/
theorem testFibreHomeomorph_schemeProjection {U : Over S} (r : U ⟶ V)
    (x : Points (Limits.pullback (hom (structuralMorphism (space f b)))
      ((schemeYoneda V.left).map (SchemeTargetRebase.baseTest r.left)))) :
    fibreSchemeProjection (hom f) ((schemeYoneda S).map r ≫ b)
      (testFibreHomeomorph f b r x) =
      fibreSchemeProjection (hom (structuralMorphism (space f b)))
        ((schemeYoneda V.left).map (SchemeTargetRebase.baseTest r.left)) x := by
  let p := FibreProduct.snd f (homMk b : (schemeToSpace S).obj V ⟶ Y)
  let h := FibreProduct.isPullback_presheaf f (homMk b : (schemeToSpace S).obj V ⟶ Y)
  have he := ((IsPullback.of_hasPullback (hom p) ((schemeYoneda S).map r)).paste_horiz h).isoPullback_hom_snd
  change schemePointsTo U (Points.map _ (Points.map (iteratedFibrePullbackIso h _).hom
    (SchemeTargetRebase.testFibrePointsHomeomorph p r x))) = _
  erw [← Points.map_comp, he, SchemeTargetRebase.testFibrePointsHomeomorph_snd,
    schemePointsTo_testSchemeHomeomorph]
  rfl

variable (g : T ⟶ S)

/-- The actual changed family test and changed original test have homeomorphic fibres. -/
def baseChangeSchemeTestFibreHomeomorph {U : Over T} (r : U ⟶ (Over.pullback g).obj V) :
    @Homeomorph
      (Points (Limits.pullback
        (hom (structuralMorphism (baseChange (pullback.fst V.hom g) (space f b))))
        ((schemeYoneda (Limits.pullback V.hom g)).map
          (SchemeTargetRebase.baseTest
            (V := Over.mk (𝟙 (Limits.pullback V.hom g))) r.left))))
      (Points (Limits.pullback (hom (baseChangeMap g f))
        ((schemeYoneda T).map r ≫ restrictAtlas g b)))
      (pointTopology _) (pointTopology _) := by
  let rS := ((Over.mapPullbackAdj g).homEquiv U V).symm r
  let y := (schemeYoneda T).map r ≫ restrictAtlas g b
  let e₀ := structuralBaseChangeFibreHomeomorph (pullback.fst V.hom g) (space f b) r.left
  let e₁ := testFibreHomeomorph f b rS
  let e₂ := pullback.congrHom (f₁ := hom f) rfl (originalBaseChart_restrictAtlas b g r)
  let e₃ := fibreRestrictionPointsHomeomorph g f y
  let := pointTopology (Limits.pullback
    (hom (structuralMorphism (baseChange (pullback.fst V.hom g) (space f b))))
    ((schemeYoneda (Limits.pullback V.hom g)).map
      (SchemeTargetRebase.baseTest (V := Over.mk (𝟙 (Limits.pullback V.hom g))) r.left)))
  let := pointTopology (Limits.pullback (hom (structuralMorphism (space f b)))
    ((schemeYoneda V.left).map
      (SchemeTargetRebase.baseTest (V := Over.mk (𝟙 V.left)) (r.left ≫ pullback.fst V.hom g))))
  let := pointTopology (Limits.pullback (hom (structuralMorphism (space f b)))
    ((schemeYoneda V.left).map (SchemeTargetRebase.baseTest rS.left)))
  let := pointTopology (Limits.pullback (hom f) ((schemeYoneda S).map rS ≫ b))
  let := pointTopology (Limits.pullback (hom f) (originalBaseChart g y))
  let := pointTopology (Limits.pullback (hom (baseChangeMap g f)) y)
  exact e₀.trans (e₁.trans ((Points.isoHomeomorph e₂).symm.trans e₃.symm))

/-- The changed family comparison preserves the ordinary test-scheme projection. -/
theorem baseChangeSchemeTestFibreHomeomorph_schemeProjection
    {U : Over T} (r : U ⟶ (Over.pullback g).obj V)
    (x : Points (Limits.pullback
      (hom (structuralMorphism (baseChange (pullback.fst V.hom g) (space f b))))
      ((schemeYoneda (Limits.pullback V.hom g)).map
        (SchemeTargetRebase.baseTest
          (V := Over.mk (𝟙 (Limits.pullback V.hom g))) r.left)))) :
    fibreSchemeProjection (hom (baseChangeMap g f))
      ((schemeYoneda T).map r ≫ restrictAtlas g b)
      (baseChangeSchemeTestFibreHomeomorph f b g r x) =
      fibreSchemeProjection
        (hom (structuralMorphism (baseChange (pullback.fst V.hom g) (space f b))))
        ((schemeYoneda (Limits.pullback V.hom g)).map
          (SchemeTargetRebase.baseTest
            (V := Over.mk (𝟙 (Limits.pullback V.hom g))) r.left)) x := by
  let rS := ((Over.mapPullbackAdj g).homEquiv U V).symm r
  let y := (schemeYoneda T).map r ≫ restrictAtlas g b
  let e₀ := structuralBaseChangeFibreHomeomorph (pullback.fst V.hom g) (space f b) r.left
  let e₁ := testFibreHomeomorph f b rS
  let e₂ := pullback.congrHom (f₁ := hom f) rfl (originalBaseChart_restrictAtlas b g r)
  let e₃ := fibreRestrictionPointsHomeomorph g f y
  have h₂ : e₂.inv ≫ pullback.snd (hom f) (originalBaseChart g y) =
      pullback.snd (hom f) ((schemeYoneda S).map rS ≫ b) := by
    simp [e₂, pullback.congrHom_inv, pullback.map, y, rS]
  let := pointTopology (Limits.pullback (hom (baseChangeMap g f)) y)
  let := pointTopology (Limits.pullback (hom f) (originalBaseChart g y))
  let := pointTopology (Limits.pullback (hom f) ((schemeYoneda S).map rS ≫ b))
  let := pointTopology (Limits.pullback (hom (structuralMorphism (space f b)))
    ((schemeYoneda V.left).map (SchemeTargetRebase.baseTest rS.left)))
  let := pointTopology (Limits.pullback (hom (structuralMorphism (space f b)))
    ((schemeYoneda V.left).map
      (SchemeTargetRebase.baseTest (V := Over.mk (𝟙 V.left)) (r.left ≫ pullback.fst V.hom g))))
  let := pointTopology (Limits.pullback
    (hom (structuralMorphism (baseChange (pullback.fst V.hom g) (space f b))))
    ((schemeYoneda (Limits.pullback V.hom g)).map
      (SchemeTargetRebase.baseTest (V := Over.mk (𝟙 (Limits.pullback V.hom g))) r.left)))
  let z := Points.map e₂.inv (e₁ (e₀ x))
  have h₃ := fibreSchemeProjection_restriction g f y (e₃.symm z)
  change fibreSchemeProjection (hom f) (originalBaseChart g y) (e₃ (e₃.symm z)) = _ at h₃
  rw [e₃.apply_symm_apply] at h₃
  change fibreSchemeProjection (hom (baseChangeMap g f)) y (e₃.symm z) = _
  rw [← h₃]
  change schemePointsTo _ (Points.map _ (Points.map e₂.inv (e₁ (e₀ x)))) = _
  erw [← Points.map_comp, h₂]
  change fibreSchemeProjection (hom f) ((schemeYoneda S).map rS ≫ b) (e₁ (e₀ x)) = _
  rw [testFibreHomeomorph_schemeProjection]
  exact structuralBaseChangeFibreHomeomorph_schemeProjection
    (pullback.fst V.hom g) (space f b) r.left x

/-- The actual target family tests universal closedness after arbitrary scheme base change. -/
theorem isUniversallyClosedMorphism_baseChange_iff
    (hb : IsEtale b) (hs : IsSurjective b) :
    IsUniversallyClosedMorphism (baseChangeMap g f) ↔
      IsUniversallyClosedMorphism
        (structuralMorphism (baseChange (pullback.fst V.hom g) (space f b))) := by
  let VT := (Over.pullback g).obj V
  let F := structuralMorphism (baseChange (pullback.fst V.hom g) (space f b))
  constructor
  · intro hf U y
    have hy : y = (schemeYoneda VT.left).map
        (SchemeTargetRebase.baseTest (V := Over.mk (𝟙 VT.left)) U.hom) :=
      (basePresheafIsTerminal VT.left).hom_ext _ _
    rw [hy]
    let r : Over.mk (U.hom ≫ VT.hom) ⟶ VT := Over.homMk U.hom rfl
    let z := (schemeYoneda T).map r ≫ restrictAtlas g b
    let := pointTopology (Limits.pullback (hom (baseChangeMap g f)) z)
    let := pointTopology (Limits.pullback (hom F)
      ((schemeYoneda VT.left).map (SchemeTargetRebase.baseTest U.hom)))
    let := pointTopology (Limits.pullback
      (hom (structuralMorphism (baseChange (pullback.fst V.hom g) (space f b))))
      ((schemeYoneda (Limits.pullback V.hom g)).map
        (SchemeTargetRebase.baseTest (V := Over.mk (𝟙 (Limits.pullback V.hom g))) r.left)))
    let e := baseChangeSchemeTestFibreHomeomorph f b g r
    have hc := (isClosedMap_fibreSchemeProjection_iff _ z).mpr (hf _ z)
    have h := hc.comp e.isClosedMap
    have he : fibreSchemeProjection (hom (baseChangeMap g f)) z ∘ e =
        fibreSchemeProjection (hom F)
          ((schemeYoneda VT.left).map (SchemeTargetRebase.baseTest U.hom)) := by
      funext x
      exact baseChangeSchemeTestFibreHomeomorph_schemeProjection f b g r x
    rw [he] at h
    exact (isClosedMap_fibreSchemeProjection_iff _ _).mp h
  · intro hf
    apply (isUniversallyClosedMorphism_iff_targetAtlas (baseChangeMap g f)
      (restrictAtlas g b) (relative_restrictAtlas _ hb) (relative_restrictAtlas _ hs)).mpr
    intro U y
    obtain ⟨r, rfl⟩ := (schemeYoneda T).map_surjective y
    let z := (schemeYoneda T).map r ≫ restrictAtlas g b
    let := pointTopology (Limits.pullback (hom (baseChangeMap g f)) z)
    let := pointTopology (Limits.pullback (hom F)
      ((schemeYoneda VT.left).map (SchemeTargetRebase.baseTest r.left)))
    let := pointTopology (Limits.pullback
      (hom (structuralMorphism (baseChange (pullback.fst V.hom g) (space f b))))
      ((schemeYoneda (Limits.pullback V.hom g)).map
        (SchemeTargetRebase.baseTest (V := Over.mk (𝟙 (Limits.pullback V.hom g))) r.left)))
    let e := baseChangeSchemeTestFibreHomeomorph f b g r
    have hc := (isClosedMap_fibreSchemeProjection_iff _ _).mpr
      (hf (Over.mk r.left) ((schemeYoneda VT.left).map (SchemeTargetRebase.baseTest r.left)))
    have h := hc.comp e.symm.isClosedMap
    have he : fibreSchemeProjection (hom F)
        ((schemeYoneda VT.left).map (SchemeTargetRebase.baseTest r.left)) ∘ e.symm =
        fibreSchemeProjection (hom (baseChangeMap g f)) z := by
      funext x
      have h := baseChangeSchemeTestFibreHomeomorph_schemeProjection f b g r (e.symm x)
      change fibreSchemeProjection (hom (baseChangeMap g f)) z (e (e.symm x)) = _ at h
      rw [e.apply_symm_apply] at h
      exact h.symm
    rw [he] at h
    have h' := (isClosedMap_fibreSchemeProjection_iff _ z).mp h
    let p := FibreProduct.snd (baseChangeMap g f)
      (homMk (restrictAtlas g b) : (schemeToSpace T).obj VT ⟶ baseChange g Y)
    let hP := FibreProduct.isPullback_presheaf (baseChangeMap g f)
      (homMk (restrictAtlas g b) : (schemeToSpace T).obj VT ⟶ baseChange g Y)
    let eP := iteratedFibrePullbackIso hP ((schemeYoneda T).map r)
    have heP : eP.hom ≫ pullback.snd (hom (baseChangeMap g f)) z =
        pullback.snd (hom p) ((schemeYoneda T).map r) :=
      ((IsPullback.of_hasPullback (hom p) ((schemeYoneda T).map r)).paste_horiz hP).isoPullback_hom_snd
    apply Points.isClosedMap_of_iso eP.symm _ _ _ h'
    change eP.inv ≫ pullback.snd (hom p) ((schemeYoneda T).map r) = _
    rw [← heP, Iso.inv_hom_id_assoc]

end AffineTargetFamily

end Langlands.AlgebraicGeometry.AlgebraicSpace
