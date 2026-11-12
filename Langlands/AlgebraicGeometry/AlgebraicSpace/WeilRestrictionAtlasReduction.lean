import Langlands.AlgebraicGeometry.AlgebraicSpace.TestFibreRepresentation
import Langlands.AlgebraicGeometry.AlgebraicSpace.QuasiAffineWeilRestrictionComparison
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionBaseChange
import Langlands.AlgebraicGeometry.AlgebraicSpace.FinitePresentationChartSquares
import Langlands.AlgebraicGeometry.AlgebraicSpace.WeilRestrictionGeometricInputsStatement
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-! # Reduction of restricted atlases to restricted schemes over test schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace WeilRestrictionAtlas

open TestFibre

section Comparison

variable {S S' : Scheme.{u}} (π : S' ⟶ S) (V : Over S)

/-- The base-change square of a test scheme `V` along `π`. -/
lemma testSquare : IsPullback (pullback.snd V.hom π) (pullback.fst V.hom π) π V.hom :=
  (IsPullback.of_hasPullback V.hom π).flip

/-- The tautological point of the restriction of the represented presheaf of `V ×_S S'`. -/
def unitPoint : (schemeYoneda S).obj V ⟶
    (Over.pullback π).op ⋙ (schemeYoneda S').obj ((Over.pullback π).obj V) :=
  uliftYonedaEquiv.symm (pt (𝟙 ((Over.pullback π).obj V)))

lemma unitPoint_app_pt {T : Over S} (c : T ⟶ V) :
    (unitPoint π V).app (op T) (pt c) = pt ((Over.pullback π).map c) := by
  rw [app_pt]
  simp only [unitPoint, Equiv.apply_symm_apply]
  exact (map_pt ((Over.pullback π).map c) (𝟙 _)).trans (congrArg pt (Category.comp_id _))

variable {V}

/-- The comparison of test schemes for the base-change square of `V`. -/
abbrev testIso (T : Over V.left) :=
  WeilRestrictionBaseChange.testIso (testSquare π V) T

lemma testIso_hom_map_toTest (T : Over V.left) :
    (testIso π T).hom.left ≫ ((Over.pullback π).map (toTest T)).left =
      pullback.snd T.hom (pullback.fst V.hom π) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst]
    rw [← Category.assoc]
    erw [WeilRestrictionBaseChange.testIso_hom_fst]
    exact pullback.condition
  · simp only [Category.assoc, Over.pullback_map_left, pullback.lift_snd]
    exact WeilRestrictionBaseChange.testIso_hom_snd _ _

lemma testIso_inv_naturality {T₁ T₂ : Over V.left} (k : T₂ ⟶ T₁) :
    (testIso π T₂).inv.left ≫ ((Over.pullback (pullback.fst V.hom π)).map k).left =
      ((Over.pullback π).map ((Over.map V.hom).map k)).left ≫ (testIso π T₁).inv.left := by
  have h := congrArg CommaMorphism.left
    ((WeilRestrictionBaseChange.testNatIso (testSquare π V)).inv.naturality k)
  simpa [WeilRestrictionBaseChange.testNatIso] using h.symm

variable {Y : Over S'} (qY : Y ⟶ (Over.pullback π).obj V)

/-- The scheme `Y` over `V ×_S S'` given by `qY`. -/
abbrev fibreScheme : Over (Limits.pullback V.hom π) :=
  Over.mk qY.left

/-- The fibre of the restricted projection `qY` over the tautological point. -/
abbrev fibre : Presheaf V.left :=
  TestFibre.presheaf (Functor.whiskerLeft (Over.pullback π).op ((schemeYoneda S').map qY))
    (unitPoint π V)

variable {π qY}

/-- A section of the restricted scheme gives a morphism to `Y` over `S'`. -/
def toFibreHom {T : Over V.left}
    (z : (Over.pullback (pullback.fst V.hom π)).obj T ⟶ fibreScheme π qY) :
    (Over.pullback π).obj ((Over.map V.hom).obj T) ⟶ Y :=
  Over.homMk ((testIso π T).inv.left ≫ z.left) (by
    have hz : z.left ≫ qY.left = pullback.snd T.hom (pullback.fst V.hom π) := Over.w z
    have hq := Over.w qY
    have hi := Over.w (testIso π T).inv
    simp only [Over.pullback_obj_hom, Over.map_obj_hom] at hq hi ⊢
    rw [← hq, Category.assoc, ← Category.assoc z.left, hz, ← hi])

lemma toFibreHom_comp {T : Over V.left}
    (z : (Over.pullback (pullback.fst V.hom π)).obj T ⟶ fibreScheme π qY) :
    toFibreHom z ≫ qY = (Over.pullback π).map (toTest T) := by
  have hz : z.left ≫ qY.left = pullback.snd T.hom (pullback.fst V.hom π) := Over.w z
  ext
  simp only [toFibreHom, Over.comp_left, Over.homMk_left, Category.assoc]
  rw [hz, ← testIso_hom_map_toTest π T, ← Category.assoc, ← Over.comp_left, Iso.inv_hom_id,
    Over.id_left, Category.id_comp]

/-- A morphism to `Y` over the tautological point gives a section of the restricted scheme. -/
def ofFibreHom {T : Over V.left} (y : (Over.pullback π).obj ((Over.map V.hom).obj T) ⟶ Y)
    (hy : y ≫ qY = (Over.pullback π).map (toTest T)) :
    (Over.pullback (pullback.fst V.hom π)).obj T ⟶ fibreScheme π qY :=
  Over.homMk ((testIso π T).hom.left ≫ y.left) (by
    have h := congrArg CommaMorphism.left hy
    simp only [Over.comp_left] at h
    change ((testIso π T).hom.left ≫ y.left) ≫ qY.left = _
    rw [Category.assoc, h, testIso_hom_map_toTest]
    rfl)

lemma mem_fibre_iff {T : Over V.left} (y : (Over.pullback π).obj ((Over.map V.hom).obj T) ⟶ Y) :
    (Functor.whiskerLeft (Over.pullback π).op ((schemeYoneda S').map qY)).app
        (op ((Over.map V.hom).obj T)) (pt y) =
      (unitPoint π V).app (op ((Over.map V.hom).obj T)) (pt (toTest T)) ↔
    y ≫ qY = (Over.pullback π).map (toTest T) := by
  rw [unitPoint_app_pt]
  exact ⟨fun h => pt_injective h, fun h => congrArg pt h⟩

/-- Sections of the restricted scheme over `T` are sections of the fibre over `T`. -/
def fibreEquiv (T : Over V.left) :
    ((Over.pullback (pullback.fst V.hom π)).op ⋙
        (schemeYoneda _).obj (fibreScheme π qY)).obj (op T) ≃ (fibre π qY).obj (op T) where
  toFun z := ⟨pt (toFibreHom z.down), (mem_fibre_iff _).2 (toFibreHom_comp z.down)⟩
  invFun y := ULift.up (ofFibreHom y.1.down ((mem_fibre_iff _).1 y.2))
  left_inv z := by
    obtain ⟨z⟩ := z
    apply ULift.ext
    apply Over.OverMorphism.ext
    change (testIso π T).hom.left ≫ (testIso π T).inv.left ≫ z.left = z.left
    rw [← Category.assoc, ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.id_comp]
  right_inv y := by
    obtain ⟨y, hy⟩ := y
    obtain ⟨y, rfl⟩ := exists_pt y
    apply Subtype.ext
    change pt _ = pt y
    congr 1
    ext
    simp [toFibreHom, ofFibreHom]
    rfl

variable (π qY)

/-- The restriction of `Y` along the base change of `π` to `V.left` is the fibre of the
restricted projection over the tautological point. -/
def fibreIso :
    (Over.pullback (pullback.fst V.hom π)).op ⋙ (schemeYoneda _).obj (fibreScheme π qY) ≅
      fibre π qY :=
  NatIso.ofComponents (fun T => (fibreEquiv T.unop).toIso) (by
    intro T₁ T₂ k
    ext z
    obtain ⟨z⟩ := z
    apply Subtype.ext
    change pt (toFibreHom ((Over.pullback (pullback.fst V.hom π)).map k.unop ≫ z)) =
      pt ((Over.pullback π).map ((Over.map V.hom).map k.unop) ≫ toFibreHom z)
    congr 1
    ext
    simp only [toFibreHom, Over.comp_left, Over.homMk_left]
    rw [← Category.assoc, testIso_inv_naturality, Category.assoc])

end Comparison

section Separation

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- A represented base change of a chart `a` of a quasi-separated space along a point `x`,
with affine chart, has quasi-compact separated projection. -/
theorem quasiCompact_isSeparated_of_isPullback (hX : IsQuasiSeparated X)
    {U V Y : Over S} [IsAffineHom U.hom] (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (x : (schemeYoneda S).obj V ⟶ X.presheaf) (p : Y ⟶ U) (q : Y ⟶ V)
    (sq : IsPullback ((schemeYoneda S).map p) ((schemeYoneda S).map q) a x) :
    QuasiCompact q.left ∧ _root_.AlgebraicGeometry.IsSeparated q.left := by
  let m : Y ⟶ U ⨯ V := prod.lift p q
  have hqc : QuasiCompact m.left := relative_diagonal_property_chart_pairing @QuasiCompact hX p q a x sq
  have hm : Mono m := by
    constructor
    intro Z u v huv
    apply (schemeYoneda S).map_injective
    apply sq.hom_ext
    · rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      simpa [m] using congrArg (· ≫ prod.fst) huv
    · rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      simpa [m] using congrArg (· ≫ prod.snd) huv
  have hsnd : (prod.snd : U ⨯ V ⟶ V).left =
      (Over.prodLeftIsoPullback U V).hom ≫ pullback.snd U.hom V.hom :=
    (Over.prodLeftIsoPullback_hom_snd U V).symm
  have hq : q.left = m.left ≫ (prod.snd : U ⨯ V ⟶ V).left := by
    rw [← Over.comp_left, prod.lift_snd]
  rw [hq, hsnd]
  exact ⟨inferInstance, inferInstance⟩

end Separation

section Assembly

/-- The local representation input: restriction along the base change of `Spec R' ⟶ Spec R`
to a test scheme `V` represents every étale surjective quasi-compact separated scheme over
`V ×_{Spec R} Spec R'` by an étale surjective scheme over `V`. -/
def RepresentationInput : Prop :=
  ∀ (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Finite R R']
    [Module.Projective R R'] (V : Over (Spec (CommRingCat.of R)))
    (Y : Over (Limits.pullback V.hom (Spec.algebraMap R R'))),
    Etale Y.hom → Surjective Y.hom → QuasiCompact Y.hom →
      _root_.AlgebraicGeometry.IsSeparated Y.hom →
      ∃ W : Over V.left,
        Nonempty ((schemeYoneda V.left).obj W ≅
          (Over.pullback (pullback.fst V.hom (Spec.algebraMap R R'))).op ⋙
            (schemeYoneda _).obj Y) ∧
        Etale W.hom ∧ Surjective W.hom

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] [Module.Finite R R']
  [Module.Projective R R']

/-- Every base change of the restricted atlas along a point of the restricted space over a
test scheme `V` is represented over `V` by an étale surjective scheme. -/
theorem exists_isPullback (hD : RepresentationInput.{u})
    (X' : AlgebraicSpace (Spec (CommRingCat.of R'))) (hX' : IsQuasiSeparated X')
    (U' : Over (Spec (CommRingCat.of R'))) [IsAffine U'.left]
    (a : (schemeYoneda _).obj U' ⟶ X'.presheaf) (ha : IsEtale a) (hs : IsSurjective a)
    (V : Over (Spec (CommRingCat.of R)))
    (g : (schemeYoneda _).obj V ⟶
      (Over.pullback (Spec.algebraMap R R')).op ⋙ X'.presheaf) :
    ∃ (W : Over V.left) (fst : (schemeYoneda _).obj ((Over.map V.hom).obj W) ⟶
        (Over.pullback (Spec.algebraMap R R')).op ⋙ (schemeYoneda _).obj U'),
      IsPullback fst ((schemeYoneda _).map (toTest W))
        (Functor.whiskerLeft (Over.pullback (Spec.algebraMap R R')).op a) g ∧
      Etale W.hom ∧ Surjective W.hom := by
  let π := Spec.algebraMap R R'
  let V' := (Over.pullback π).obj V
  let γ : ((Over.pullback π).op ⋙ X'.presheaf).obj (op V) := uliftYonedaEquiv.{u + 1} g
  let x : (schemeYoneda _).obj V' ⟶ X'.presheaf :=
    uliftYonedaEquiv.{u + 1}.symm (show X'.presheaf.obj (op V') from γ)
  have sq := ha.rep.isPullback' x
  let qY := ha.rep.snd x
  have hEt : Etale qY.left := ha.2 x _ qY sq
  have hSu : Surjective qY.left := hs.2 x _ qY sq
  obtain ⟨hqc, hsep⟩ := quasiCompact_isSeparated_of_isPullback hX' a x _ qY sq
  obtain ⟨W, ⟨e⟩, hWe, hWs⟩ := hD R R' V (fibreScheme π qY) hEt hSu hqc hsep
  let e' := e ≪≫ fibreIso π qY
  have sq₁ := TestFibre.isPullback W e'
  have sq₂ := weilRestriction_presheaf_isPullback π sq
  have hg : unitPoint π V ≫ Functor.whiskerLeft (Over.pullback π).op x = g := by
    apply uliftYonedaEquiv.{u + 1}.injective
    rw [uliftYonedaEquiv_comp]
    simp only [unitPoint, Equiv.apply_symm_apply]
    change x.app (op V') (pt (𝟙 V')) = _
    rw [app_pt]
    simp [x, γ]
  have sq := sq₁.paste_horiz sq₂
  rw [hg] at sq
  exact ⟨W, _, sq, hWe, hWs⟩

/-- The affine-atlas input for Conrad's Lemma 5.10, given the local representation input. -/
theorem weilRestrictionAffineEtaleAtlas_of_representationInput
    (hD : RepresentationInput.{u}) : WeilRestrictionAffineEtaleAtlasStatement.{u} := by
  intro R R' _ _ _ _ _ X' hX' U' _ _ a ha hs
  constructor
  · change (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget _)).relative
      (schemeYoneda _) _
    let : MorphismProperty.RespectsIso (@Etale.{u}) :=
      Etale.etale_isStableUnderBaseChange.respectsIso
    let := MorphismProperty.RespectsIso.inverseImage (@Etale.{u})
      (Over.forget (Spec (CommRingCat.of R)))
    apply MorphismProperty.relative.of_exists
    intro V g
    obtain ⟨W, fst, sq, hWe, -⟩ := exists_isPullback hD X' hX' U' a ha hs V g
    exact ⟨(Over.map V.hom).obj W, fst, toTest W, sq, hWe⟩
  · change (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget _)).relative
      (schemeYoneda _) _
    let := MorphismProperty.RespectsIso.inverseImage (@Surjective.{u})
      (Over.forget (Spec (CommRingCat.of R)))
    apply MorphismProperty.relative.of_exists
    intro V g
    obtain ⟨W, fst, sq, -, hWs⟩ := exists_isPullback hD X' hX' U' a ha hs V g
    exact ⟨(Over.map V.hom).obj W, fst, toTest W, sq, hWs⟩

end Assembly

end WeilRestrictionAtlas

end Langlands.AlgebraicGeometry.AlgebraicSpace
