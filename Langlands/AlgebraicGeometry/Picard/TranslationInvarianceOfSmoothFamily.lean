import Langlands.AlgebraicGeometry.Picard.SmoothFamilyAlgebraicTriviality
import Langlands.AlgebraicGeometry.Picard.FieldCubeTrivialitySmoothThirdStatement
import Langlands.AlgebraicGeometry.Picard.MumfordBundlePicardZeroReduction
import Langlands.AlgebraicGeometry.Picard.FieldLineBundleTrivialityProof
import Langlands.AlgebraicGeometry.Picard.LineBundleDualEvaluation
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof

/-! # Bundles algebraically trivial via a smooth family are translation invariant

Let `N` be a line bundle on `C ×_K A` with `N(c₀, -)` trivial and `N(c₁, -) ≅ L`, and
let `N'` be a tensor inverse of `N`. On `A × A × C` the bundle
`N(c, x + y) ⊗ N'(c, x) ⊗ N'(c, y) ⊗ N(c, 0)` is trivial on the three faces
`x = 0`, `y = 0` and `c = c₀`, so the theorem of the cube with a smooth third factor
makes it trivial. Restricting to `(x, a, c₁)` gives `t_x^*L ⊗ L⁻¹` trivial. The cube
theorem is an explicit hypothesis. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme.TranslationOfSmoothFamily

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AbelianScheme.MumfordPicardZero (pullbackTensorIso pullbackCompIso tensorIsoOf
  constantIso)

/-- A geometrically integral morphism is geometrically connected. -/
lemma geometricallyConnected_of_geometricallyIntegral {X Y : Scheme.{u}} (f : X ⟶ Y)
    [GeometricallyIntegral f] : GeometricallyConnected f :=
  ⟨fun _ _ y _ fst snd h ↦
    have : IrreducibleSpace _ :=
      GeometricallyIrreducible.geometrically_irreducibleSpace (f := f) y fst snd h
    inferInstance⟩

variable {S : Scheme.{u}} (A : AbelianScheme S) (C : Over S)

/-- The scheme map `w ↦ (c w, a w)` into the parameter-first product `C ×_S A`. -/
def pairMap {W : Over S} (c : W ⟶ C) (a : W ⟶ A.X) :
    W.left ⟶ (relativeSpace A.X.hom).obj C :=
  pullback.lift c.left a.left (by rw [Over.w c, Over.w a])

@[simp] lemma pairMap_fst {W : Over S} (c : W ⟶ C) (a : W ⟶ A.X) :
    pairMap A C c a ≫ pullback.fst C.hom A.X.hom = c.left :=
  pullback.lift_fst _ _ _

@[simp] lemma pairMap_snd {W : Over S} (c : W ⟶ C) (a : W ⟶ A.X) :
    pairMap A C c a ≫ pullback.snd C.hom A.X.hom = a.left :=
  pullback.lift_snd _ _ _

lemma pairMap_pullback {V W : Over S} (g : V ⟶ W) {c : W ⟶ C} {a : W ⟶ A.X}
    {c' : V ⟶ C} {a' : V ⟶ A.X} (hc : g ≫ c = c') (ha : g ≫ a = a') :
    g.left ≫ pairMap A C c a = pairMap A C c' a' := by
  subst hc ha
  apply pullback.hom_ext
  · rw [Category.assoc, pairMap_fst, pairMap_fst, Over.comp_left]
  · rw [Category.assoc, pairMap_snd, pairMap_snd, Over.comp_left]

/-- With a constant parameter, the pair map factors through the point map. -/
lemma pairMap_const {W : Over S} (c : Over.mk (𝟙 S) ⟶ C) (a : W ⟶ A.X) :
    a.left ≫ smoothFamilyPointMap A C c = pairMap A C (Over.mkIdTerminal.from W ≫ c) a := by
  apply pullback.hom_ext
  · rw [Category.assoc, smoothFamilyPointMap_fst, pairMap_fst, Over.comp_left,
      Over.mkIdTerminal_from_left, ← Category.assoc, Over.w a]
  · rw [Category.assoc, smoothFamilyPointMap_snd, pairMap_snd, Category.comp_id]

variable {C}

section Shape

variable (N N' : ((relativeSpace A.X.hom).obj C).Modules)

/-- `N(c, a + b) ⊗ (N'(c, a) ⊗ (N'(c, b) ⊗ N(c, 0)))` on `W`. -/
abbrev cubeShape {W : Over S} (c : W ⟶ C) (a b : W ⟶ A.X) : W.left.Modules :=
  tensorObj ((Scheme.Modules.pullback (pairMap A C c (a * b))).obj N)
    (tensorObj ((Scheme.Modules.pullback (pairMap A C c a)).obj N')
      (tensorObj ((Scheme.Modules.pullback (pairMap A C c b)).obj N')
        ((Scheme.Modules.pullback (pairMap A C c 1)).obj N)))

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})

/-- Pull one pair factor back along a morphism over `S`. -/
def pairPullbackIso {V W : Over S} (g : V ⟶ W) {c : W ⟶ C} {a : W ⟶ A.X}
    {c' : V ⟶ C} {a' : V ⟶ A.X} (hc : g ≫ c = c') (ha : g ≫ a = a')
    (F : ((relativeSpace A.X.hom).obj C).Modules) :
    (Scheme.Modules.pullback g.left).obj ((Scheme.Modules.pullback (pairMap A C c a)).obj F) ≅
      (Scheme.Modules.pullback (pairMap A C c' a')).obj F :=
  (pullbackCompIso g.left _ _ (pairMap_pullback A C g hc ha) F).symm

/-- The cube shape is natural in the test object. -/
def cubeShapePullbackIso {V W : Over S} (g : V ⟶ W) {c : W ⟶ C} {a b : W ⟶ A.X}
    {c' : V ⟶ C} {a' b' : V ⟶ A.X} (hc : g ≫ c = c') (ha : g ≫ a = a') (hb : g ≫ b = b') :
    (Scheme.Modules.pullback g.left).obj (cubeShape A N N' c a b) ≅
      cubeShape A N N' c' a' b' :=
  pullbackTensorIso preservation g.left _ _ ≪≫
    tensorIsoOf (pairPullbackIso A g hc (by rw [MonObj.comp_mul, ha, hb]) N)
      (pullbackTensorIso preservation g.left _ _ ≪≫
        tensorIsoOf (pairPullbackIso A g hc ha N')
          (pullbackTensorIso preservation g.left _ _ ≪≫
            tensorIsoOf (pairPullbackIso A g hc hb N')
              (pairPullbackIso A g hc (MonObj.comp_one g) N)))

/-- `U ⊗ (U' ⊗ (Z' ⊗ Z))` is trivial when `U ⊗ U'` and `Z ⊗ Z'` are. -/
def tensorFourTrivialIso {X : Scheme.{u}} (U U' Z Z' : X.Modules)
    (eU : tensorObj U U' ≅ structureSheaf X) (eZ : tensorObj Z Z' ≅ structureSheaf X) :
    tensorObj U (tensorObj U' (tensorObj Z' Z)) ≅ structureSheaf X :=
  (tensorAssociator U U' (tensorObj Z' Z)).symm ≪≫ tensorIsoOf eU (Iso.refl _) ≪≫
    tensorLeftUnitor _ ≪≫ tensorComm Z' Z ≪≫ eZ

variable (ev : tensorObj N N' ≅ structureSheaf ((relativeSpace A.X.hom).obj C))

/-- The evaluation pulled back along a pair map. -/
def pairEvaluation {W : Over S} (c : W ⟶ C) (a : W ⟶ A.X) :
    tensorObj ((Scheme.Modules.pullback (pairMap A C c a)).obj N)
      ((Scheme.Modules.pullback (pairMap A C c a)).obj N') ≅ structureSheaf W.left :=
  pullbackTensorEvaluation preservation (pairMap A C c a) N N' ev

/-- The face `a = 0`. -/
def firstFaceIso {W : Over S} (c : W ⟶ C) (b : W ⟶ A.X) :
    cubeShape A N N' c 1 b ≅ structureSheaf W.left :=
  tensorIsoOf ((Scheme.Modules.pullbackCongr (by rw [one_mul])).app N)
      ((tensorAssociator _ _ _).symm ≪≫ tensorIsoOf (tensorComm _ _) (Iso.refl _) ≪≫
        tensorAssociator _ _ _) ≪≫
    tensorFourTrivialIso _ _ _ _ (pairEvaluation A N N' preservation ev c b)
      (pairEvaluation A N N' preservation ev c 1)

/-- The face `b = 0`. -/
def secondFaceIso {W : Over S} (c : W ⟶ C) (a : W ⟶ A.X) :
    cubeShape A N N' c a 1 ≅ structureSheaf W.left :=
  tensorIsoOf ((Scheme.Modules.pullbackCongr (by rw [mul_one])).app N) (Iso.refl _) ≪≫
    tensorFourTrivialIso _ _ _ _ (pairEvaluation A N N' preservation ev c a)
      (pairEvaluation A N N' preservation ev c 1)

/-- A pair factor with a constant parameter at which the module is trivial. -/
def constPairIso {W : Over S} (c₀ : Over.mk (𝟙 S) ⟶ C) (a : W ⟶ A.X)
    (F : ((relativeSpace A.X.hom).obj C).Modules)
    (e : (Scheme.Modules.pullback (smoothFamilyPointMap A C c₀)).obj F ≅
      structureSheaf A.X.left) :
    (Scheme.Modules.pullback (pairMap A C (Over.mkIdTerminal.from W ≫ c₀) a)).obj F ≅
      structureSheaf W.left :=
  pullbackCompIso a.left (smoothFamilyPointMap A C c₀) _ (pairMap_const A C c₀ a) F ≪≫
    (Scheme.Modules.pullback a.left).mapIso e ≪≫ pullbackUnitIso a.left

/-- The inverse of a module trivial at a point is trivial there. -/
def inverseAtPointIso (c₀ : Over.mk (𝟙 S) ⟶ C)
    (e : (Scheme.Modules.pullback (smoothFamilyPointMap A C c₀)).obj N ≅
      structureSheaf A.X.left) :
    (Scheme.Modules.pullback (smoothFamilyPointMap A C c₀)).obj N' ≅
      structureSheaf A.X.left :=
  (tensorLeftUnitor _).symm ≪≫ tensorIsoOf e.symm (Iso.refl _) ≪≫
    pullbackTensorEvaluation preservation (smoothFamilyPointMap A C c₀) N N' ev

/-- The face `c = c₀`. -/
def thirdFaceIso {W : Over S} (c₀ : Over.mk (𝟙 S) ⟶ C) (a b : W ⟶ A.X)
    (e : (Scheme.Modules.pullback (smoothFamilyPointMap A C c₀)).obj N ≅
      structureSheaf A.X.left) :
    cubeShape A N N' (Over.mkIdTerminal.from W ≫ c₀) a b ≅ structureSheaf W.left :=
  let e' := inverseAtPointIso A N N' preservation ev c₀ e
  tensorIsoOf (constPairIso A c₀ (a * b) N e)
      (tensorIsoOf (constPairIso A c₀ a N' e')
          (tensorIsoOf (constPairIso A c₀ b N' e') (constPairIso A c₀ 1 N e) ≪≫
            tensorLeftUnitor _) ≪≫
        tensorLeftUnitor _) ≪≫
    tensorLeftUnitor _

/-- The cube shape on `A × (A × C)`, with coordinates `(x, y, c)`. -/
abbrev cubeModule : (A.X ⨯ (A.X ⨯ C)).left.Modules :=
  cubeShape A N N' (prod.snd ≫ prod.snd) prod.fst (prod.snd ≫ prod.fst)

include preservation ev in
lemma first_face_trivial :
    Nonempty ((Scheme.Modules.pullback (CubeFace.first A.X A.X C 1).left).obj
        (cubeModule A N N') ≅ structureSheaf (A.X ⨯ C).left) :=
  ⟨cubeShapePullbackIso A N N' preservation (CubeFace.first A.X A.X C 1)
      (c' := prod.snd) (a' := 1) (b' := prod.fst)
      (by simp [CubeFace.first]) (by simp [CubeFace.first, MonObj.comp_one])
      (by simp [CubeFace.first]) ≪≫
    firstFaceIso A N N' preservation ev _ _⟩

include preservation ev in
lemma second_face_trivial :
    Nonempty ((Scheme.Modules.pullback (CubeFace.second A.X A.X C 1).left).obj
        (cubeModule A N N') ≅ structureSheaf (A.X ⨯ C).left) :=
  ⟨cubeShapePullbackIso A N N' preservation (CubeFace.second A.X A.X C 1)
      (c' := prod.snd) (a' := prod.fst) (b' := 1)
      (by simp [CubeFace.second]) (by simp [CubeFace.second])
      (by simp [CubeFace.second, MonObj.comp_one]) ≪≫
    secondFaceIso A N N' preservation ev _ _⟩

include preservation ev in
lemma third_face_trivial (c₀ : Over.mk (𝟙 S) ⟶ C)
    (e : (Scheme.Modules.pullback (smoothFamilyPointMap A C c₀)).obj N ≅
      structureSheaf A.X.left) :
    Nonempty ((Scheme.Modules.pullback (CubeFace.third A.X A.X C c₀).left).obj
        (cubeModule A N N') ≅ structureSheaf (A.X ⨯ A.X).left) :=
  ⟨cubeShapePullbackIso A N N' preservation (CubeFace.third A.X A.X C c₀)
      (c' := Over.mkIdTerminal.from _ ≫ c₀) (a' := prod.fst) (b' := prod.snd)
      (by simp [CubeFace.third]) (by simp [CubeFace.third])
      (by simp [CubeFace.third]) ≪≫
    thirdFaceIso A N N' preservation ev c₀ _ _ e⟩

end Shape

/-- The cube shape as an actual line bundle on `A × (A × C)`. -/
def cubeBundle (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (N N' : LineBundle ((relativeSpace A.X.hom).obj C)) :
    LineBundle (A.X ⨯ (A.X ⨯ C)).left :=
  LineBundle.tensor preservation
    ((LineBundle.pullback
      (pairMap A C (prod.snd ≫ prod.snd) (prod.fst * (prod.snd ≫ prod.fst)))).obj N)
    (LineBundle.tensor preservation
      ((LineBundle.pullback (pairMap A C (prod.snd ≫ prod.snd) prod.fst)).obj N')
      (LineBundle.tensor preservation
        ((LineBundle.pullback (pairMap A C (prod.snd ≫ prod.snd) (prod.snd ≫ prod.fst))).obj N')
        ((LineBundle.pullback (pairMap A C (prod.snd ≫ prod.snd) 1)).obj N)))

lemma cubeBundle_obj (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (N N' : LineBundle ((relativeSpace A.X.hom).obj C)) :
    (cubeBundle A preservation N N').obj = cubeModule A N.obj N'.obj := rfl

section Restriction

variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))
  {C : Over (Spec (CommRingCat.of K))}

/-- On `A ≅ {x} × A × {c₁}`, the cube shape is `t_x^*N(c₁, -) ⊗ N'(c₁, -)`. -/
def restrictionIso (triviality : FieldLineBundleTrivialityStatement.{u})
    (N N' : LineBundle ((relativeSpace A.X.hom).obj C))
    (c₁ : Over.mk (𝟙 _) ⟶ C) (x : Over.mk (𝟙 _) ⟶ A.X) :
    cubeShape A N.obj N'.obj (Over.mkIdTerminal.from A.X ≫ c₁)
        (Over.mkIdTerminal.from A.X ≫ x) (𝟙 A.X) ≅
      tensorObj ((Scheme.Modules.pullback (GroupScheme.translation A.toGrp x).left).obj
          ((Scheme.Modules.pullback (smoothFamilyPointMap A C c₁)).obj N.obj))
        ((Scheme.Modules.pullback (smoothFamilyPointMap A C c₁)).obj N'.obj) :=
  tensorIsoOf
    (pullbackCompIso _ _ _ (pairMap_const A C c₁ _) N.obj)
    (tensorIsoOf
        (pullbackCompIso _ _ _ (pairMap_const A C c₁ _) N'.obj ≪≫
          constantIso triviality A.toGrp x
            ((LineBundle.pullback (smoothFamilyPointMap A C c₁)).obj N'))
        (tensorIsoOf
            ((Scheme.Modules.pullbackCongr (by rw [← pairMap_const]; simp)).app N'.obj)
            (pullbackCompIso _ _ _
                (by rw [pairMap_const, MonObj.comp_one]) N.obj ≪≫
              constantIso triviality A.toGrp 1
                ((LineBundle.pullback (smoothFamilyPointMap A C c₁)).obj N)) ≪≫
          tensorRightUnitor _) ≪≫
      tensorLeftUnitor _)

/-- The point `(x, a, c₁)` of `A × (A × C)`. -/
def restrictionMap (c₁ : Over.mk (𝟙 _) ⟶ C) (x : Over.mk (𝟙 _) ⟶ A.X) :
    A.X ⟶ A.X ⨯ (A.X ⨯ C) :=
  prod.lift (Over.mkIdTerminal.from A.X ≫ x)
    (prod.lift (𝟙 A.X) (Over.mkIdTerminal.from A.X ≫ c₁))

/-- A trivialization of the cube shape restricts to `t_x^*N(c₁, -) ⊗ N'(c₁, -)`. -/
lemma translate_tensor_trivial (triviality : FieldLineBundleTrivialityStatement.{u})
    (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (N N' : LineBundle ((relativeSpace A.X.hom).obj C))
    (c₁ : Over.mk (𝟙 _) ⟶ C) (x : Over.mk (𝟙 _) ⟶ A.X)
    (eM : cubeModule A N.obj N'.obj ≅ structureSheaf (A.X ⨯ (A.X ⨯ C)).left) :
    Nonempty (tensorObj ((Scheme.Modules.pullback (GroupScheme.translation A.toGrp x).left).obj
          ((Scheme.Modules.pullback (smoothFamilyPointMap A C c₁)).obj N.obj))
        ((Scheme.Modules.pullback (smoothFamilyPointMap A C c₁)).obj N'.obj) ≅
      structureSheaf A.X.left) :=
  ⟨(restrictionIso A triviality N N' c₁ x).symm ≪≫
    (cubeShapePullbackIso A N.obj N'.obj preservation (restrictionMap A c₁ x)
      (by simp [restrictionMap]) (by simp [restrictionMap])
      (by simp [restrictionMap])).symm ≪≫
    (Scheme.Modules.pullback (restrictionMap A c₁ x).left).mapIso eM ≪≫
    pullbackUnitIso (restrictionMap A c₁ x).left⟩

/-- The cube theorem trivializes the cube shape. -/
lemma cubeModule_trivial (cube : FieldCubeTrivialitySmoothThirdStatement.{u})
    (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (hSm : Smooth C.hom) (hConn : GeometricallyConnected C.hom)
    (N N' : LineBundle ((relativeSpace A.X.hom).obj C))
    (ev : tensorObj N.obj N'.obj ≅ structureSheaf ((relativeSpace A.X.hom).obj C))
    (c₀ : Over.mk (𝟙 _) ⟶ C)
    (e₀ : (Scheme.Modules.pullback (smoothFamilyPointMap A C c₀)).obj N.obj ≅
      structureSheaf A.X.left) :
    Nonempty (cubeModule A N.obj N'.obj ≅ structureSheaf (A.X ⨯ (A.X ⨯ C)).left) :=
  cube K A.X A.X C inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance hSm hConn 1 1 c₀ (cubeBundle A preservation N N')
    (first_face_trivial A N.obj N'.obj preservation ev)
    (second_face_trivial A N.obj N'.obj preservation ev)
    (third_face_trivial A N.obj N'.obj preservation ev c₀ e₀)

end Restriction

/-- If `t^*(s^*N) ⊗ s^*N'` is trivial for a tensor inverse `N'` of `N`, then
`t^*L ≅ L` for every `L ≅ s^*N`. -/
lemma pullback_iso_of_tensor_trivial (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    {X P : Scheme.{u}} (s : X ⟶ P) (t : X ⟶ X) (N N' : LineBundle P)
    (ev : tensorObj N.obj N'.obj ≅ structureSheaf P) {L : LineBundle X}
    (h : (LineBundle.pullback s).obj N ≅ L)
    (e : tensorObj ((Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback s).obj N.obj))
        ((Scheme.Modules.pullback s).obj N'.obj) ≅ structureSheaf X) :
    Nonempty ((LineBundle.pullback t).obj L ≅ L) :=
  ⟨(LineBundle.pullback t).mapIso h.symm ≪≫
    LineBundle.tensorInverseComparisonIso ((LineBundle.pullback s).obj N')
      ((LineBundle.pullback t).obj ((LineBundle.pullback s).obj N))
      ((LineBundle.pullback s).obj N)
      (tensorComm _ _ ≪≫ e)
      (tensorComm _ _ ≪≫ pullbackTensorEvaluation preservation s N.obj N'.obj ev) ≪≫ h⟩

end Langlands.AbelianScheme.TranslationOfSmoothFamily

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open TranslationOfSmoothFamily

/-- A line bundle algebraically trivial via a smooth family is translation invariant,
given the theorem of the cube with a smooth, not necessarily proper, third factor. -/
theorem isTranslationInvariant_of_isAlgebraicallyTrivialViaSmoothFamily
    (cube : FieldCubeTrivialitySmoothThirdStatement.{u})
    {K : Type u} [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (L : LineBundle A.X.left)
    (hL : IsAlgebraicallyTrivialViaSmoothFamily A L) :
    GroupScheme.IsTranslationInvariant A.toGrp L := by
  obtain ⟨C, hSm, -, -, -, hInt, c₀, c₁, N, ⟨h₀⟩, ⟨h₁⟩⟩ := hL
  obtain ⟨N', ⟨ev⟩⟩ := LineBundle.exists_tensorObj_iso_structureSheaf N
  obtain ⟨eM⟩ := cubeModule_trivial A cube pullbackTensorComparisonIsIso hSm
    (geometricallyConnected_of_geometricallyIntegral _) N N' ev c₀
    ((LineBundle.forget _).mapIso h₀)
  intro x
  obtain ⟨e₁⟩ := translate_tensor_trivial A fieldLineBundleTriviality
    pullbackTensorComparisonIsIso N N' c₁ x eM
  exact pullback_iso_of_tensor_trivial pullbackTensorComparisonIsIso _ _ N N' ev h₁ e₁

end Langlands.AbelianScheme
