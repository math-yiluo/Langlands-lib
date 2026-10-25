import Langlands.AlgebraicGeometry.Picard.MumfordBundlePicardZeroStatement
import Langlands.AlgebraicGeometry.Picard.FieldLineBundleTrivialityStatement
import Langlands.AlgebraicGeometry.Picard.GeometricPicardZeroInverse
import Langlands.AbelianScheme.FieldCubePullbackStatement
import Langlands.AbelianScheme.KernelBaseChange

/-! # The Mumford family is geometrically Picard zero, assuming the cube identity

The theorem `mumfordBundlePicardZero_of_cube` derives the geometric Picard-zero
condition for the actual Mumford family from the field cube-pullback proposition
and the triviality of line bundles on the spectrum of a field. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme.MumfordPicardZero

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable {X : Scheme.{u}}

/-- Tensor two isomorphisms of module sheaves. -/
abbrev tensorIsoOf {M M' N N' : X.Modules} (e : M ≅ M') (d : N ≅ N') :
    tensorObj M N ≅ tensorObj M' N' :=
  (tensorFunctor X).mapIso (e.prod d)

/-- Exchange the two middle factors of a fourfold tensor. -/
def middleFourIso (A B C D : X.Modules) :
    tensorObj (tensorObj A B) (tensorObj C D) ≅ tensorObj (tensorObj A C) (tensorObj B D) :=
  tensorAssociator A B (tensorObj C D) ≪≫
    tensorIsoOf (Iso.refl A) ((tensorAssociator B C D).symm ≪≫
      tensorIsoOf (tensorComm B C) (Iso.refl D) ≪≫ tensorAssociator C B D) ≪≫
    (tensorAssociator A C (tensorObj B D)).symm

/-- The fixed pullback-tensor comparison as an isomorphism on objects. -/
def pullbackTensorIso (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    {Y : Scheme.{u}} (f : Y ⟶ X) (M N : X.Modules) :
    (Scheme.Modules.pullback f).obj (tensorObj M N) ≅
      tensorObj ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) := by
  letI := preservation f
  exact (asIso (pullbackTensorComparison f)).app (M, N)

/-- Pull back along a composite, written as successive pullbacks. -/
def pullbackCompIso {Y Z : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ X) (h : Y ⟶ X)
    (w : f ≫ g = h) (M : X.Modules) :
    (Scheme.Modules.pullback h).obj M ≅
      (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) :=
  (Scheme.Modules.pullbackCongr w.symm).app M ≪≫ ((Scheme.Modules.pullbackComp f g).app M).symm


open Langlands.GroupScheme (translation IsTranslationInvariant points_translation
  isTranslationInvariant_of_iso isTranslationInvariant_tensor)

/-- Pullbacks of line bundles from the base are invariant under every translation. -/
lemma isTranslationInvariant_pullback_hom {S : Scheme.{u}} (G : GroupScheme S)
    (P : LineBundle S) : IsTranslationInvariant G ((LineBundle.pullback G.X.hom).obj P) :=
  fun x ↦ ⟨ObjectProperty.isoMk _
    (pullbackCompIso _ _ _ (Over.w (translation G x)) P.obj).symm⟩

section Square

variable {K : Type u} [Field K]

/-- Over a field, a line bundle pulled back along a constant map is trivial. -/
def constantIso (triviality : FieldLineBundleTrivialityStatement.{u})
    (G : Grp (Over (Spec (CommRingCat.of K)))) (b : Over.mk (𝟙 _) ⟶ G.X)
    (N : LineBundle G.X.left) :
    (Scheme.Modules.pullback (Over.mkIdTerminal.from G.X ≫ b).left).obj N.obj ≅
      structureSheaf G.X.left :=
  pullbackCompIso G.X.hom b.left _ (by simp) N.obj ≪≫
    (Scheme.Modules.pullback G.X.hom).mapIso
      (triviality K ((LineBundle.pullback b.left).obj N)).some ≪≫
    pullbackUnitIso G.X.hom

/-- The theorem of the square for one line bundle, as an explicit isomorphism
obtained from a supplied cube isomorphism with `f = a`, `g = x` and `h = 𝟙`. -/
def squareIso (triviality : FieldLineBundleTrivialityStatement.{u})
    (G : Grp (Over (Spec (CommRingCat.of K)))) (a x : Over.mk (𝟙 _) ⟶ G.X)
    (N : LineBundle G.X.left)
    (cubeIso : tensorObj
        ((Scheme.Modules.pullback
          ((Over.mkIdTerminal.from G.X ≫ a) * (Over.mkIdTerminal.from G.X ≫ x) *
            𝟙 G.X).left).obj N.obj)
        (tensorObj
          ((Scheme.Modules.pullback (Over.mkIdTerminal.from G.X ≫ a).left).obj N.obj)
          (tensorObj
            ((Scheme.Modules.pullback (Over.mkIdTerminal.from G.X ≫ x).left).obj N.obj)
            ((Scheme.Modules.pullback (𝟙 G.X : G.X ⟶ G.X).left).obj N.obj))) ≅
      tensorObj
        ((Scheme.Modules.pullback
          ((Over.mkIdTerminal.from G.X ≫ a) * (Over.mkIdTerminal.from G.X ≫ x)).left).obj N.obj)
        (tensorObj
          ((Scheme.Modules.pullback ((Over.mkIdTerminal.from G.X ≫ a) * 𝟙 G.X).left).obj N.obj)
          ((Scheme.Modules.pullback ((Over.mkIdTerminal.from G.X ≫ x) * 𝟙 G.X).left).obj
            N.obj))) :
    tensorObj ((Scheme.Modules.pullback (translation G x).left).obj
        ((Scheme.Modules.pullback (translation G a).left).obj N.obj)) N.obj ≅
      tensorObj ((Scheme.Modules.pullback (translation G a).left).obj N.obj)
        ((Scheme.Modules.pullback (translation G x).left).obj N.obj) :=
  tensorIsoOf
      (pullbackCompIso (translation G x).left (translation G a).left _
        (by rw [← Over.comp_left, points_translation, mul_assoc]; rfl) N.obj).symm
      ((tensorLeftUnitor N.obj).symm ≪≫
        tensorIsoOf (constantIso triviality G a N).symm
          ((tensorLeftUnitor N.obj).symm ≪≫
            tensorIsoOf (constantIso triviality G x N).symm
              ((Scheme.Modules.pullbackId G.X.left).app N.obj).symm)) ≪≫
    cubeIso ≪≫
    tensorIsoOf
      ((Scheme.Modules.pullbackCongr (by rw [MonObj.comp_mul])).app N.obj ≪≫
        constantIso triviality G (a * x) N)
      (Iso.refl _) ≪≫
    tensorLeftUnitor _

/-- The theorem of the square makes `t_a^* N ⊗ N'` translation invariant when
`N'` is a supplied tensor inverse of `N`. -/
lemma isTranslationInvariant_square (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (cube : Langlands.GroupScheme.FieldCubePullbackStatement.{u})
    (triviality : FieldLineBundleTrivialityStatement.{u})
    (G : AbelianScheme (Spec (CommRingCat.of K))) (a : Over.mk (𝟙 _) ⟶ G.X)
    (N N' : LineBundle G.X.left)
    (evaluation : tensorObj N.obj N'.obj ≅ structureSheaf G.X.left) :
    IsTranslationInvariant G.toGrp (LineBundle.tensor preservation
      ((LineBundle.pullback (translation G.toGrp a).left).obj N) N') := by
  intro x
  obtain ⟨cubeIso⟩ := cube K G.toGrp G.smooth G.proper G.geometricallyConnected G.X
    (Over.mkIdTerminal.from G.X ≫ a) (Over.mkIdTerminal.from G.X ≫ x) (𝟙 G.X) N
  let tx := (translation G.toGrp x).left
  exact ⟨ObjectProperty.isoMk _
    (pullbackTensorIso preservation tx _ N'.obj ≪≫
      (tensorRightUnitor _).symm ≪≫
      tensorIsoOf (Iso.refl _) evaluation.symm ≪≫
      middleFourIso _ _ _ _ ≪≫
      tensorIsoOf (squareIso triviality G.toGrp a x N cubeIso) (Iso.refl _) ≪≫
      tensorAssociator _ _ _ ≪≫
      tensorIsoOf (Iso.refl _)
        ((tensorAssociator _ _ _).symm ≪≫
          tensorIsoOf (pullbackTensorEvaluation preservation tx N.obj N'.obj evaluation)
            (Iso.refl _) ≪≫
          tensorLeftUnitor _))⟩

end Square

section Fibre

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} (A : AbelianScheme S) {K : Type u} [Field K]
  (s : Spec (CommRingCat.of K) ⟶ A.X.left)

/-- The abelian scheme `A ×_S A` over its second factor, the parameter space. -/
abbrev paramChange : AbelianScheme A.X.left := (baseChange A.X.hom).obj A

/-- The fibre of the parameter family over a point of the parameter space. -/
abbrev fibre : AbelianScheme (Spec (CommRingCat.of K)) := (baseChange s).obj (paramChange A)

/-- The fibre maps to the parameter-first self-product. -/
def fibreToProduct : (fibre A s).X.left ⟶ (mumfordProduct A).left :=
  pullback.fst (paramChange A).X.hom s ≫ (pullbackSymmetry A.X.hom A.X.hom).inv

/-- The fibre maps to the abelian scheme by its non-parameter coordinate. -/
def fibreInclusion : (fibre A s).X.left ⟶ A.X.left :=
  pullback.fst (paramChange A).X.hom s ≫ pullback.fst A.X.hom A.X.hom

/-- The point of the fibre given by the parameter itself. -/
def fibrePoint : Over.mk (𝟙 _) ⟶ (fibre A s).X :=
  Over.homMk (pullback.lift (pullback.lift s s rfl) (𝟙 _)
    (by change _ ≫ pullback.snd A.X.hom A.X.hom = _; simp))
    (by change _ ≫ pullback.snd _ _ = _; simp)

/-- The parameter point lies over the parameter. -/
lemma fibrePoint_inclusion : (fibrePoint A s).left ≫ fibreInclusion A s = s := by
  simp [fibrePoint, fibreInclusion]

/-- On the fibre, the parameter coordinate is constant. -/
lemma fibreToProduct_fst :
    fibreToProduct A s ≫ pullback.fst A.X.hom A.X.hom = (fibre A s).X.hom ≫ s := by
  change pullback.fst (paramChange A).X.hom s ≫ (pullbackSymmetry A.X.hom A.X.hom).inv ≫
    pullback.fst A.X.hom A.X.hom = pullback.snd (paramChange A).X.hom s ≫ s
  rw [pullbackSymmetry_inv_comp_fst, ← pullback.condition]
  rfl

/-- On the fibre, the second coordinate is the fibre inclusion. -/
lemma fibreToProduct_snd :
    fibreToProduct A s ≫ pullback.snd A.X.hom A.X.hom = fibreInclusion A s := by
  simp [fibreToProduct, fibreInclusion]

/-- On the fibre, addition on the self-product is translation by the parameter. -/
lemma fibreToProduct_addition : fibreToProduct A s ≫ mumfordAddition A =
    (translation (fibre A s).toGrp (fibrePoint A s)).left ≫ fibreInclusion A s := by
  let G := fibre A s
  let Φ : (G.X ⟶ G.X) ≃* ((Over.map A.X.hom).obj ((Over.map s).obj G.X) ⟶ A.X) :=
    (Langlands.GroupScheme.baseChangePointsEquiv s (paramChange A).toGrp G.X).trans
    (Langlands.GroupScheme.baseChangePointsEquiv A.X.hom A.toGrp ((Over.map s).obj G.X))
  have hΦ (y : G.X ⟶ G.X) : (Φ y).left = y.left ≫ fibreInclusion A s := by
    change (y.left ≫ pullback.fst _ _) ≫ pullback.fst _ _ = _
    simp [fibreInclusion]
  let φ : (Over.map A.X.hom).obj ((Over.map s).obj G.X) ⟶ mumfordProduct A :=
    Over.homMk (fibreToProduct A s) (by
      change _ ≫ (pullback.fst _ _ ≫ _) = (_ ≫ s) ≫ _
      rw [← Category.assoc, fibreToProduct_fst]
      rfl)
  have h1 : φ ≫ mumfordFirst A = Φ (Over.mkIdTerminal.from G.X ≫ fibrePoint A s) := by
    apply Over.OverMorphism.ext
    rw [hΦ, Over.comp_left, Over.comp_left, Over.mkIdTerminal_from_left, Category.assoc,
      fibrePoint_inclusion]
    exact fibreToProduct_fst A s
  have h2 : φ ≫ mumfordSecond A = Φ (𝟙 G.X) := by
    apply Over.OverMorphism.ext
    rw [hΦ]
    exact (fibreToProduct_snd A s).trans (Category.id_comp _).symm
  have h : φ ≫ (mumfordFirst A * mumfordSecond A) =
      Φ (translation G.toGrp (fibrePoint A s)) := by
    rw [MonObj.comp_mul, h1, h2, translation, map_mul]
  exact (congrArg CommaMorphism.left h).trans (hΦ _)

/-- The fibre restriction of the three Mumford factors, regrouped as a constant
factor tensored with `t^*(ι^*L₀) ⊗ ι^*M`. -/
def mumfordFibreIso (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (L₀ M : A.X.left.Modules) :
    (Scheme.Modules.pullback (pullback.fst (paramChange A).X.hom s)).obj
        ((Scheme.Modules.pullback (relativeSpaceSymmetry A.X.hom A.X).inv).obj
          (tensorObj (tensorObj ((Scheme.Modules.pullback (mumfordAddition A)).obj L₀)
            ((Scheme.Modules.pullback (pullback.fst A.X.hom A.X.hom)).obj M))
            ((Scheme.Modules.pullback (pullback.snd A.X.hom A.X.hom)).obj M))) ≅
      tensorObj ((Scheme.Modules.pullback (fibre A s).X.hom).obj
          ((Scheme.Modules.pullback s).obj M))
        (tensorObj ((Scheme.Modules.pullback
            (translation (fibre A s).toGrp (fibrePoint A s)).left).obj
              ((Scheme.Modules.pullback (fibreInclusion A s)).obj L₀))
          ((Scheme.Modules.pullback (fibreInclusion A s)).obj M)) :=
  (Scheme.Modules.pullbackComp (pullback.fst (paramChange A).X.hom s)
      (pullbackSymmetry A.X.hom A.X.hom).inv).app _ ≪≫
    pullbackTensorIso preservation (fibreToProduct A s) _ _ ≪≫
    tensorIsoOf (pullbackTensorIso preservation (fibreToProduct A s) _ _ ≪≫
        tensorIsoOf
          ((Scheme.Modules.pullbackComp (fibreToProduct A s) (mumfordAddition A)).app L₀ ≪≫
            pullbackCompIso _ _ _ (fibreToProduct_addition A s).symm L₀)
          ((Scheme.Modules.pullbackComp (fibreToProduct A s)
              (pullback.fst A.X.hom A.X.hom)).app M ≪≫
            pullbackCompIso _ _ _ (fibreToProduct_fst A s).symm M))
      ((Scheme.Modules.pullbackComp (fibreToProduct A s)
          (pullback.snd A.X.hom A.X.hom)).app M ≪≫
        (Scheme.Modules.pullbackCongr (fibreToProduct_snd A s)).app M) ≪≫
    tensorIsoOf (tensorComm _ _) (Iso.refl _) ≪≫
    tensorAssociator _ _ _

end Fibre

/-- The Mumford family is geometrically Picard zero, given the field cube identity
and the triviality of line bundles over a field. -/
theorem mumfordBundlePicardZero_of_cube
    (cube : Langlands.GroupScheme.FieldCubePullbackStatement.{u})
    (triviality : FieldLineBundleTrivialityStatement.{u}) :
    MumfordBundlePicardZeroStatement.{u} := by
  intro preservation S A L M evaluation K _ _ s
  let L₀ := (RigidifiedLineBundle.forget (unitSection A)).obj L
  let incl := fibreInclusion A s
  exact isTranslationInvariant_of_iso _
    (ObjectProperty.isoMk _ (mumfordFibreIso A s preservation L₀.obj M.obj).symm)
    (isTranslationInvariant_tensor preservation _
      (isTranslationInvariant_pullback_hom (fibre A s).toGrp ((LineBundle.pullback s).obj M))
      (isTranslationInvariant_square preservation cube triviality (fibre A s) (fibrePoint A s)
        ((LineBundle.pullback incl).obj L₀) ((LineBundle.pullback incl).obj M)
        (pullbackTensorEvaluation preservation incl L₀.obj M.obj evaluation)))

end Langlands.AbelianScheme.MumfordPicardZero
