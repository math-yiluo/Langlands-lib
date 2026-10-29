import Langlands.AlgebraicGeometry.Picard.CubeRelativeTransport
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiSeparatedStatement
import Langlands.AlgebraicGeometry.Picard.RigidificationAdjustment
import Langlands.AlgebraicGeometry.Picard.RelativeCubeDualComparison
import Langlands.AlgebraicGeometry.Picard.RelativeRigidifiedCubeStatement
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Mathlib.AlgebraicGeometry.Fiber

/-! # Assembling relative cube triviality from fibrewise and local inputs -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

namespace RelativeCubeAssembly

/-- A module sheaf becomes trivial after pullback along a morphism. -/
def TrivialAlong {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) : Prop :=
  Nonempty ((Scheme.Modules.pullback f).obj M ≅ Langlands.Scheme.Modules.structureSheaf X)

namespace TrivialAlong

variable {W X Y : Scheme.{u}} {f : X ⟶ Y} {M : Y.Modules}

/-- Triviality along `f` gives triviality along every composite `g ≫ f`. -/
lemma comp (h : TrivialAlong f M) (g : W ⟶ X) : TrivialAlong (g ≫ f) M := by
  obtain ⟨τ⟩ := h
  exact ⟨((Scheme.Modules.pullbackComp g f).app M).symm ≪≫
    (Scheme.Modules.pullback g).mapIso τ ≪≫ Langlands.Scheme.Modules.pullbackUnitIso g⟩

/-- Triviality along `f` gives triviality along any morphism factoring through `f`. -/
lemma of_fac (h : TrivialAlong f M) (g : W ⟶ X) {k : W ⟶ Y} (e : g ≫ f = k) :
    TrivialAlong k M :=
  e ▸ h.comp g

/-- Triviality of a pullback along `g` is triviality along the composite. -/
lemma pullback_iff (g : W ⟶ X) (f : X ⟶ Y) (M : Y.Modules) :
    TrivialAlong g ((Scheme.Modules.pullback f).obj M) ↔ TrivialAlong (g ≫ f) M :=
  ⟨fun ⟨τ⟩ ↦ ⟨((Scheme.Modules.pullbackComp g f).app M).symm ≪≫ τ⟩,
    fun ⟨τ⟩ ↦ ⟨(Scheme.Modules.pullbackComp g f).app M ≪≫ τ⟩⟩

end TrivialAlong

section BaseChange

variable {S T : Scheme.{u}} (t : T ⟶ S)

@[reassoc (attr := simp)]
lemma prod_lift_left_fst {B : Scheme.{u}} {W P Q : Over B} (f : W ⟶ P) (g : W ⟶ Q) :
    (prod.lift f g).left ≫ (prod.fst : P ⨯ Q ⟶ P).left = f.left := by
  rw [← Over.comp_left, prod.lift_fst]

@[reassoc (attr := simp)]
lemma prod_lift_left_snd {B : Scheme.{u}} {W P Q : Over B} (f : W ⟶ P) (g : W ⟶ Q) :
    (prod.lift f g).left ≫ (prod.snd : P ⨯ Q ⟶ Q).left = g.left := by
  rw [← Over.comp_left, prod.lift_snd]

@[reassoc (attr := simp)]
lemma prodLeftIsoPullback_inv_hom {B : Scheme.{u}} (P Q : Over B) :
    (Over.prodLeftIsoPullback P Q).inv ≫ (P ⨯ Q).hom = pullback.snd P.hom Q.hom ≫ Q.hom := by
  rw [← Over.w (prod.snd : P ⨯ Q ⟶ Q), Over.prodLeftIsoPullback_inv_snd_assoc]

@[reassoc (attr := simp)]
lemma terminal_comp {A B X : Over S} (k : A ⟶ B) (x₀ : Over.mk (𝟙 S) ⟶ X) :
    k ≫ Over.mkIdTerminal.from B ≫ x₀ = Over.mkIdTerminal.from A ≫ x₀ := by
  rw [← Category.assoc, Over.mkIdTerminal.comp_from]

/-- Base change of an `S`-scheme along `t`, as the actual scheme pullback. -/
abbrev bc (X : Over S) : Over T :=
  Over.mk (pullback.snd X.hom t)

/-- The section of a base change induced by a section. -/
def baseChangeSection {X : Over S} (x₀ : Over.mk (𝟙 S) ⟶ X) :
    Over.mk (𝟙 T) ⟶ bc t X :=
  Over.homMk (pullback.lift (t ≫ x₀.left) (𝟙 T)
    (by simp [overSection_comp X x₀]))
    (pullback.lift_snd _ _ _)

@[reassoc (attr := simp)]
lemma baseChangeSection_left_fst {X : Over S} (x₀ : Over.mk (𝟙 S) ⟶ X) :
    (baseChangeSection t x₀).left ≫ pullback.fst X.hom t = t ≫ x₀.left :=
  pullback.lift_fst _ _ _

/-- An `S`-morphism into `X` induced by a `T`-morphism into the base change of `X`. -/
def toBase {W : Over T} {X : Over S} (φ : W ⟶ bc t X) :
    (Over.map t).obj W ⟶ X :=
  Over.homMk (φ.left ≫ pullback.fst X.hom t) (by
    have h : φ.left ≫ pullback.snd X.hom t = W.hom := by simpa using Over.w φ
    simp [pullback.condition, reassoc_of% h])

@[simp]
lemma toBase_left {W : Over T} {X : Over S} (φ : W ⟶ bc t X) :
    (toBase t φ).left = φ.left ≫ pullback.fst X.hom t :=
  rfl

@[reassoc (attr := simp)]
lemma map_toBase {V W : Over T} {X : Over S} (g : V ⟶ W)
    (φ : W ⟶ bc t X) :
    (Over.map t).map g ≫ toBase t φ = toBase t (g ≫ φ) := by
  ext
  simp

lemma toBase_terminal_section {W : Over T} {X : Over S} (x₀ : Over.mk (𝟙 S) ⟶ X) :
    toBase t (Over.mkIdTerminal.from W ≫ baseChangeSection t x₀) =
      Over.mkIdTerminal.from ((Over.map t).obj W) ≫ x₀ := by
  ext
  simp

variable (X Y Z : Over S)

/-- The canonical comparison from the triple product of base changes to the triple product. -/
def cubeBaseChange :
    (Over.map t).obj (bc t X ⨯
      (bc t Y ⨯ bc t Z)) ⟶ X ⨯ (Y ⨯ Z) :=
  prod.lift (toBase t prod.fst)
    (prod.lift (toBase t (prod.snd ≫ prod.fst)) (toBase t (prod.snd ≫ prod.snd)))

/-- The canonical comparison from the product of two base changes to the product. -/
def pairBaseChange :
    (Over.map t).obj (bc t Y ⨯ bc t Z) ⟶ Y ⨯ Z :=
  prod.lift (toBase t prod.fst) (toBase t prod.snd)

@[reassoc (attr := simp)]
lemma cubeBaseChange_fst :
    (cubeBaseChange t X Y Z).left ≫ (prod.fst : X ⨯ (Y ⨯ Z) ⟶ X).left =
      (prod.fst : bc t X ⨯ (bc t Y ⨯ bc t Z) ⟶ _).left ≫ pullback.fst X.hom t := by
  simp [cubeBaseChange]

@[reassoc (attr := simp)]
lemma cubeBaseChange_snd_fst :
    (cubeBaseChange t X Y Z).left ≫ (prod.snd : X ⨯ (Y ⨯ Z) ⟶ Y ⨯ Z).left ≫
        (prod.fst : Y ⨯ Z ⟶ Y).left =
      (prod.snd : bc t X ⨯ (bc t Y ⨯ bc t Z) ⟶ _).left ≫
        (prod.fst : bc t Y ⨯ bc t Z ⟶ _).left ≫ pullback.fst Y.hom t := by
  simp [cubeBaseChange]

@[reassoc (attr := simp)]
lemma cubeBaseChange_snd_snd :
    (cubeBaseChange t X Y Z).left ≫ (prod.snd : X ⨯ (Y ⨯ Z) ⟶ Y ⨯ Z).left ≫
        (prod.snd : Y ⨯ Z ⟶ Z).left =
      (prod.snd : bc t X ⨯ (bc t Y ⨯ bc t Z) ⟶ _).left ≫
        (prod.snd : bc t Y ⨯ bc t Z ⟶ _).left ≫ pullback.fst Z.hom t := by
  simp [cubeBaseChange]

lemma cubeBaseChange_first (x₀ : Over.mk (𝟙 S) ⟶ X) :
    (Over.map t).map (CubeFace.first _ _ _ (baseChangeSection t x₀)) ≫
        cubeBaseChange t X Y Z =
      pairBaseChange t Y Z ≫ CubeFace.first X Y Z x₀ := by
  apply prod.hom_ext
  · simp [cubeBaseChange, pairBaseChange, CubeFace.first, toBase_terminal_section]
  · apply prod.hom_ext <;> simp [cubeBaseChange, pairBaseChange, CubeFace.first]

lemma cubeBaseChange_second (y₀ : Over.mk (𝟙 S) ⟶ Y) :
    (Over.map t).map (CubeFace.second _ _ _ (baseChangeSection t y₀)) ≫
        cubeBaseChange t X Y Z =
      pairBaseChange t X Z ≫ CubeFace.second X Y Z y₀ := by
  apply prod.hom_ext
  · simp [cubeBaseChange, pairBaseChange, CubeFace.second]
  · apply prod.hom_ext <;>
      simp [cubeBaseChange, pairBaseChange, CubeFace.second, toBase_terminal_section]

lemma cubeBaseChange_third (z₀ : Over.mk (𝟙 S) ⟶ Z) :
    (Over.map t).map (CubeFace.third _ _ _ (baseChangeSection t z₀)) ≫
        cubeBaseChange t X Y Z =
      pairBaseChange t X Y ≫ CubeFace.third X Y Z z₀ := by
  apply prod.hom_ext
  · simp [cubeBaseChange, pairBaseChange, CubeFace.third]
  · apply prod.hom_ext <;>
      simp [cubeBaseChange, pairBaseChange, CubeFace.third, toBase_terminal_section]

/-- A `T`-morphism into a base change from compatible scheme morphisms. -/
def liftBc {F : Scheme.{u}} {X : Over S} (a : F ⟶ X.left) (s : F ⟶ T)
    (h : a ≫ X.hom = s ≫ t) : Over.mk s ⟶ bc t X :=
  Over.homMk (pullback.lift a s h) (pullback.lift_snd _ _ _)

@[reassoc (attr := simp)]
lemma liftBc_left_fst {F : Scheme.{u}} {X : Over S} (a : F ⟶ X.left) (s : F ⟶ T)
    (h : a ≫ X.hom = s ≫ t) : (liftBc t a s h).left ≫ pullback.fst X.hom t = a :=
  pullback.lift_fst _ _ _

/-- The structure map of a `T`-scheme, as an `S`-morphism to the base `T`-scheme. -/
def toSelf {Z : Over S} (W : Over Z.left) : (Over.map Z.hom).obj W ⟶ Z :=
  Over.homMk W.hom rfl

@[simp]
lemma toSelf_left {Z : Over S} (W : Over Z.left) : (toSelf W).left = W.hom :=
  rfl

end BaseChange

section Field

variable {S : Scheme.{u}}

/-- The field theorem of the cube, applied after base change to a field, makes an
actual three-face trivial bundle trivial along the base-change comparison. -/
lemma trivialAlong_cubeBaseChange (hF : FieldCubeTrivialityStatement.{u})
    (K : Type u) [Field K] (t : Spec (CommRingCat.of K) ⟶ S) (X Y Z : Over S)
    [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
    [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom]
    [Smooth Z.hom] [IsProper Z.hom] [GeometricallyConnected Z.hom]
    (x₀ : Over.mk (𝟙 S) ⟶ X) (y₀ : Over.mk (𝟙 S) ⟶ Y) (z₀ : Over.mk (𝟙 S) ⟶ Z)
    (D : LineBundle (X ⨯ (Y ⨯ Z)).left)
    (h₁ : TrivialAlong (CubeFace.first X Y Z x₀).left D.obj)
    (h₂ : TrivialAlong (CubeFace.second X Y Z y₀).left D.obj)
    (h₃ : TrivialAlong (CubeFace.third X Y Z z₀).left D.obj) :
    TrivialAlong (cubeBaseChange t X Y Z).left D.obj := by
  have hX₁ : Smooth (bc t X).hom := show Smooth (pullback.snd X.hom t) from inferInstance
  have hX₂ : IsProper (bc t X).hom := show IsProper (pullback.snd X.hom t) from inferInstance
  have hX₃ : GeometricallyConnected (bc t X).hom :=
    show GeometricallyConnected (pullback.snd X.hom t) from inferInstance
  have hY₁ : Smooth (bc t Y).hom := show Smooth (pullback.snd Y.hom t) from inferInstance
  have hY₂ : IsProper (bc t Y).hom := show IsProper (pullback.snd Y.hom t) from inferInstance
  have hY₃ : GeometricallyConnected (bc t Y).hom :=
    show GeometricallyConnected (pullback.snd Y.hom t) from inferInstance
  have hZ₁ : Smooth (bc t Z).hom := show Smooth (pullback.snd Z.hom t) from inferInstance
  have hZ₂ : IsProper (bc t Z).hom := show IsProper (pullback.snd Z.hom t) from inferInstance
  have hZ₃ : GeometricallyConnected (bc t Z).hom :=
    show GeometricallyConnected (pullback.snd Z.hom t) from inferInstance
  exact hF K (bc t X) (bc t Y) (bc t Z) hX₁ hX₂ hX₃ hY₁ hY₂ hY₃ hZ₁ hZ₂ hZ₃
    (baseChangeSection t x₀) (baseChangeSection t y₀) (baseChangeSection t z₀)
    ((LineBundle.pullback (cubeBaseChange t X Y Z).left).obj D)
    ((TrivialAlong.pullback_iff _ _ _).2 (h₁.of_fac (pairBaseChange t Y Z).left
      (congrArg (fun φ ↦ φ.left) (cubeBaseChange_first t X Y Z x₀)).symm))
    ((TrivialAlong.pullback_iff _ _ _).2 (h₂.of_fac (pairBaseChange t X Z).left
      (congrArg (fun φ ↦ φ.left) (cubeBaseChange_second t X Y Z y₀)).symm))
    ((TrivialAlong.pullback_iff _ _ _).2 (h₃.of_fac (pairBaseChange t X Y).left
      (congrArg (fun φ ↦ φ.left) (cubeBaseChange_third t X Y Z z₀)).symm))

end Field

section Comparison

variable {S : Scheme.{u}} (X Y Z : Over S)

lemma triple_hom_ext {W : Scheme.{u}} {f g : W ⟶ (X ⨯ (Y ⨯ Z)).left}
    (h₁ : f ≫ (prod.fst : X ⨯ (Y ⨯ Z) ⟶ X).left = g ≫ (prod.fst : X ⨯ (Y ⨯ Z) ⟶ X).left)
    (h₂ : f ≫ (prod.snd : X ⨯ (Y ⨯ Z) ⟶ Y ⨯ Z).left ≫ (prod.fst : Y ⨯ Z ⟶ Y).left =
      g ≫ (prod.snd : X ⨯ (Y ⨯ Z) ⟶ Y ⨯ Z).left ≫ (prod.fst : Y ⨯ Z ⟶ Y).left)
    (h₃ : f ≫ (prod.snd : X ⨯ (Y ⨯ Z) ⟶ Y ⨯ Z).left ≫ (prod.snd : Y ⨯ Z ⟶ Z).left =
      g ≫ (prod.snd : X ⨯ (Y ⨯ Z) ⟶ Y ⨯ Z).left ≫ (prod.snd : Y ⨯ Z ⟶ Z).left) :
    f = g := by
  apply (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd X (Y ⨯ Z))).hom_ext
  · exact h₁
  · apply (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd Y Z)).hom_ext
    · rw [Category.assoc, Category.assoc]
      exact h₂
    · rw [Category.assoc, Category.assoc]
      exact h₃

/-- The projection of the triple product to its third factor. -/
abbrev thirdProjection : (X ⨯ (Y ⨯ Z)).left ⟶ Z.left :=
  (prod.snd : X ⨯ (Y ⨯ Z) ⟶ Y ⨯ Z).left ≫ (prod.snd : Y ⨯ Z ⟶ Z).left

/-- The comparison from the product of the base changes over `Z` to the triple product. -/
def productComparison :
    (Over.map Z.hom).obj (bc Z.hom X ⨯ bc Z.hom Y) ⟶ X ⨯ (Y ⨯ Z) :=
  prod.lift (toBase Z.hom prod.fst) (prod.lift (toBase Z.hom prod.snd) (toSelf _))

@[reassoc (attr := simp)]
lemma productComparison_fst :
    (productComparison X Y Z).left ≫ (prod.fst : X ⨯ (Y ⨯ Z) ⟶ X).left =
      (prod.fst : bc Z.hom X ⨯ bc Z.hom Y ⟶ _).left ≫ pullback.fst X.hom Z.hom := by
  rw [← Over.comp_left, productComparison, prod.lift_fst, toBase_left]

@[reassoc (attr := simp)]
lemma productComparison_snd_fst :
    (productComparison X Y Z).left ≫ (prod.snd : X ⨯ (Y ⨯ Z) ⟶ Y ⨯ Z).left ≫
        (prod.fst : Y ⨯ Z ⟶ Y).left =
      (prod.snd : bc Z.hom X ⨯ bc Z.hom Y ⟶ _).left ≫ pullback.fst Y.hom Z.hom := by
  rw [← Over.comp_left, ← Over.comp_left, productComparison, prod.lift_snd_assoc,
    prod.lift_fst, toBase_left]

@[reassoc (attr := simp)]
lemma productComparison_snd_snd :
    (productComparison X Y Z).left ≫ (prod.snd : X ⨯ (Y ⨯ Z) ⟶ Y ⨯ Z).left ≫
        (prod.snd : Y ⨯ Z ⟶ Z).left = (bc Z.hom X ⨯ bc Z.hom Y).hom := by
  rw [← Over.comp_left, ← Over.comp_left, productComparison, prod.lift_snd_assoc,
    prod.lift_snd, toSelf_left]

/-- The comparison from the triple product to the product of base changes over `Z`. -/
def productSection : Over.mk (thirdProjection X Y Z) ⟶ bc Z.hom X ⨯ bc Z.hom Y :=
  prod.lift
    (liftBc Z.hom (prod.fst : X ⨯ (Y ⨯ Z) ⟶ X).left (thirdProjection X Y Z) (by simp))
    (liftBc Z.hom ((prod.snd : X ⨯ (Y ⨯ Z) ⟶ Y ⨯ Z).left ≫ (prod.fst : Y ⨯ Z ⟶ Y).left)
      (thirdProjection X Y Z) (by simp))

@[reassoc (attr := simp)]
lemma productSection_fst :
    (productSection X Y Z).left ≫ (prod.fst : bc Z.hom X ⨯ bc Z.hom Y ⟶ _).left ≫
        pullback.fst X.hom Z.hom = (prod.fst : X ⨯ (Y ⨯ Z) ⟶ X).left := by
  rw [← Category.assoc, ← Over.comp_left, productSection, prod.lift_fst, liftBc_left_fst]

@[reassoc (attr := simp)]
lemma productSection_snd :
    (productSection X Y Z).left ≫ (prod.snd : bc Z.hom X ⨯ bc Z.hom Y ⟶ _).left ≫
        pullback.fst Y.hom Z.hom =
      (prod.snd : X ⨯ (Y ⨯ Z) ⟶ Y ⨯ Z).left ≫ (prod.fst : Y ⨯ Z ⟶ Y).left := by
  rw [← Category.assoc, ← Over.comp_left, productSection, prod.lift_snd, liftBc_left_fst]

@[reassoc (attr := simp)]
lemma productSection_hom :
    (productSection X Y Z).left ≫ (bc Z.hom X ⨯ bc Z.hom Y).hom = thirdProjection X Y Z :=
  Over.w (productSection X Y Z)

lemma productSection_comparison :
    (productSection X Y Z).left ≫ (productComparison X Y Z).left = 𝟙 _ := by
  apply triple_hom_ext <;> simp

/-- The `X`-axis of the product over `Z` is the second cube face. -/
lemma axisX_productComparison (y₀ : Over.mk (𝟙 S) ⟶ Y) :
    (prod.lift (𝟙 (bc Z.hom X))
        (Over.mkIdTerminal.from (bc Z.hom X) ≫ baseChangeSection Z.hom y₀)).left ≫
        (productComparison X Y Z).left =
      (Over.prodLeftIsoPullback X Z).inv ≫ (CubeFace.second X Y Z y₀).left := by
  apply triple_hom_ext <;> simp [CubeFace.second]

/-- The `Y`-axis of the product over `Z` is the first cube face. -/
lemma axisY_productComparison (x₀ : Over.mk (𝟙 S) ⟶ X) :
    (prod.lift (Over.mkIdTerminal.from (bc Z.hom Y) ≫ baseChangeSection Z.hom x₀)
        (𝟙 (bc Z.hom Y))).left ≫ (productComparison X Y Z).left =
      (Over.prodLeftIsoPullback Y Z).inv ≫ (CubeFace.first X Y Z x₀).left := by
  apply triple_hom_ext <;> simp [CubeFace.first]

/-- The base map from the residue field of a point of `Z`. -/
abbrev residueBase (c : Z.left) : Spec (Z.left.residueField c) ⟶ S :=
  Z.left.fromSpecResidueField c ≫ Z.hom

lemma fibre_comparison_cond (c : Z.left) {V : Over S} (p : X ⨯ (Y ⨯ Z) ⟶ V) :
    ((bc Z.hom X ⨯ bc Z.hom Y).hom.fiberι c ≫ (productComparison X Y Z).left ≫ p.left) ≫
        V.hom =
      (bc Z.hom X ⨯ bc Z.hom Y).hom.fiberToSpecResidueField c ≫ residueBase Z c := by
  rw [Category.assoc, Category.assoc, Over.w p, Over.w (productComparison X Y Z)]
  simp [Scheme.Hom.fiber_fac_assoc]

/-- The scheme-theoretic fibre of the product over `Z` maps to the triple product of the
base changes to the residue field. -/
def fibreMap (c : Z.left) :
    (bc Z.hom X ⨯ bc Z.hom Y).hom.fiber c ⟶
      (bc (residueBase Z c) X ⨯ (bc (residueBase Z c) Y ⨯ bc (residueBase Z c) Z)).left :=
  (prod.lift
    (liftBc (residueBase Z c) _ _ (fibre_comparison_cond X Y Z c prod.fst))
    (prod.lift
      (liftBc (residueBase Z c) _ _ (fibre_comparison_cond X Y Z c (prod.snd ≫ prod.fst)))
      (liftBc (residueBase Z c) _ _
        (fibre_comparison_cond X Y Z c (prod.snd ≫ prod.snd))))).left

lemma fibreMap_cubeBaseChange (c : Z.left) :
    fibreMap X Y Z c ≫ (cubeBaseChange (residueBase Z c) X Y Z).left =
      (bc Z.hom X ⨯ bc Z.hom Y).hom.fiberι c ≫ (productComparison X Y Z).left := by
  apply triple_hom_ext <;> simp [fibreMap]

end Comparison

section Local

variable {S : Scheme.{u}}

/-- The three face trivializations make the bundle trivial over a neighbourhood of every
point of the third factor. -/
lemma exists_local_triviality (hF : FieldCubeTrivialityStatement.{u})
    (hL : ∀ (T : Scheme.{u}) (P Q : Over T),
      Smooth P.hom → IsProper P.hom → GeometricallyConnected P.hom →
      Smooth Q.hom → IsProper Q.hom → GeometricallyConnected Q.hom →
      ∀ (p₀ : Over.mk (𝟙 T) ⟶ P) (q₀ : Over.mk (𝟙 T) ⟶ Q)
        (L : LineBundle (P ⨯ Q).left) (t : T),
        Nonempty ((Scheme.Modules.pullback
          (prod.lift (𝟙 P) (Over.mkIdTerminal.from P ≫ q₀)).left).obj L.obj ≅
            Langlands.Scheme.Modules.structureSheaf P.left) →
        Nonempty ((Scheme.Modules.pullback
          (prod.lift (Over.mkIdTerminal.from Q ≫ p₀) (𝟙 Q)).left).obj L.obj ≅
            Langlands.Scheme.Modules.structureSheaf Q.left) →
        Nonempty ((Scheme.Modules.pullback ((P ⨯ Q).hom.fiberι t)).obj L.obj ≅
          Langlands.Scheme.Modules.structureSheaf ((P ⨯ Q).hom.fiber t)) →
        ∃ U : T.Opens, t ∈ U ∧
          Nonempty ((Scheme.Modules.pullback
            (pullback.fst (P ⨯ Q).hom U.ι)).obj L.obj ≅
              Langlands.Scheme.Modules.structureSheaf (pullback (P ⨯ Q).hom U.ι)))
    (X Y Z : Over S)
    [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
    [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom]
    [Smooth Z.hom] [IsProper Z.hom] [GeometricallyConnected Z.hom]
    (x₀ : Over.mk (𝟙 S) ⟶ X) (y₀ : Over.mk (𝟙 S) ⟶ Y) (z₀ : Over.mk (𝟙 S) ⟶ Z)
    (D : LineBundle (X ⨯ (Y ⨯ Z)).left)
    (h₁ : TrivialAlong (CubeFace.first X Y Z x₀).left D.obj)
    (h₂ : TrivialAlong (CubeFace.second X Y Z y₀).left D.obj)
    (h₃ : TrivialAlong (CubeFace.third X Y Z z₀).left D.obj) (c : Z.left) :
    ∃ U : Z.left.Opens, c ∈ U ∧
      ∀ {W : Scheme.{u}} (j : W ⟶ (X ⨯ (Y ⨯ Z)).left) (k : W ⟶ U),
        j ≫ thirdProjection X Y Z = k ≫ U.ι → TrivialAlong j D.obj := by
  have hX₁ : Smooth (bc Z.hom X).hom :=
    show Smooth (pullback.snd X.hom Z.hom) from inferInstance
  have hX₂ : IsProper (bc Z.hom X).hom :=
    show IsProper (pullback.snd X.hom Z.hom) from inferInstance
  have hX₃ : GeometricallyConnected (bc Z.hom X).hom :=
    show GeometricallyConnected (pullback.snd X.hom Z.hom) from inferInstance
  have hY₁ : Smooth (bc Z.hom Y).hom :=
    show Smooth (pullback.snd Y.hom Z.hom) from inferInstance
  have hY₂ : IsProper (bc Z.hom Y).hom :=
    show IsProper (pullback.snd Y.hom Z.hom) from inferInstance
  have hY₃ : GeometricallyConnected (bc Z.hom Y).hom :=
    show GeometricallyConnected (pullback.snd Y.hom Z.hom) from inferInstance
  obtain ⟨U, hcU, ⟨τ⟩⟩ := hL Z.left (bc Z.hom X) (bc Z.hom Y) hX₁ hX₂ hX₃ hY₁ hY₂ hY₃
    (baseChangeSection Z.hom x₀) (baseChangeSection Z.hom y₀)
    ((LineBundle.pullback (productComparison X Y Z).left).obj D) c
    ((TrivialAlong.pullback_iff _ _ _).2
      (h₂.of_fac _ (axisX_productComparison X Y Z y₀).symm))
    ((TrivialAlong.pullback_iff _ _ _).2
      (h₁.of_fac _ (axisY_productComparison X Y Z x₀).symm))
    ((TrivialAlong.pullback_iff _ _ _).2
      ((trivialAlong_cubeBaseChange hF (Z.left.residueField c) (residueBase Z c) X Y Z
        x₀ y₀ z₀ D h₁ h₂ h₃).of_fac _ (fibreMap_cubeBaseChange X Y Z c)))
  refine ⟨U, hcU, fun j k hjk ↦ ?_⟩
  have hU : TrivialAlong (pullback.fst (bc Z.hom X ⨯ bc Z.hom Y).hom U.ι ≫
      (productComparison X Y Z).left) D.obj :=
    (TrivialAlong.pullback_iff _ _ _).1 ⟨τ⟩
  refine hU.of_fac (pullback.lift (j ≫ (productSection X Y Z).left) k ?_) ?_
  · rw [Category.assoc, productSection_hom, hjk]
  · rw [pullback.lift_fst_assoc, Category.assoc, productSection_comparison]
    exact Category.comp_id j

end Local

section Gluing

open Langlands.AbelianScheme
open scoped CategoryTheory.MonObj

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- A rigidified family whose carrier is trivial after a base change has the trivial
class there. -/
lemma classesPullback_eq_trivial {T V : Over S} (h : V ⟶ T) (L : RigidifiedFamily A T)
    (e : TrivialAlong ((relativeSpace A.X.hom).map h) L.obj.carrier) :
    RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A) h
        (⟦L⟧ : RigidifiedClasses A T) =
      ⟦RigidifiedLineBundle.trivial
        ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app V)⟧ :=
  Quotient.sound ⟨RigidifiedLineBundle.trivialIsoOfCarrierIso
    ((relativeProjection A.X.hom).app V) _ (relativeSection_projection _ _ _ V) _ e.some⟩

/-- The ordinary relative three-face cube criterion for abelian schemes, assembled from the
field theorem of the cube, local two-axis triviality and Zariski separatedness of
rigidified classes. -/
theorem nonempty_iso_structureSheaf_of_faces (hF : FieldCubeTrivialityStatement.{u})
    (hL : ∀ (T : Scheme.{u}) (P Q : Over T),
      Smooth P.hom → IsProper P.hom → GeometricallyConnected P.hom →
      Smooth Q.hom → IsProper Q.hom → GeometricallyConnected Q.hom →
      ∀ (p₀ : Over.mk (𝟙 T) ⟶ P) (q₀ : Over.mk (𝟙 T) ⟶ Q)
        (L : LineBundle (P ⨯ Q).left) (t : T),
        Nonempty ((Scheme.Modules.pullback
          (prod.lift (𝟙 P) (Over.mkIdTerminal.from P ≫ q₀)).left).obj L.obj ≅
            Langlands.Scheme.Modules.structureSheaf P.left) →
        Nonempty ((Scheme.Modules.pullback
          (prod.lift (Over.mkIdTerminal.from Q ≫ p₀) (𝟙 Q)).left).obj L.obj ≅
            Langlands.Scheme.Modules.structureSheaf Q.left) →
        Nonempty ((Scheme.Modules.pullback ((P ⨯ Q).hom.fiberι t)).obj L.obj ≅
          Langlands.Scheme.Modules.structureSheaf ((P ⨯ Q).hom.fiber t)) →
        ∃ U : T.Opens, t ∈ U ∧
          Nonempty ((Scheme.Modules.pullback
            (pullback.fst (P ⨯ Q).hom U.ι)).obj L.obj ≅
              Langlands.Scheme.Modules.structureSheaf (pullback (P ⨯ Q).hom U.ι)))
    (hZ : RigidifiedClassesZariskiSeparatedStatement.{u}) (B C : AbelianScheme S)
    (D : LineBundle (A.X ⨯ (B.X ⨯ C.X)).left)
    (h₁ : Nonempty ((Scheme.Modules.pullback
      (CubeFace.first A.X B.X C.X (1 : Over.mk (𝟙 S) ⟶ A.X)).left).obj D.obj ≅
        Langlands.Scheme.Modules.structureSheaf (B.X ⨯ C.X).left))
    (h₂ : Nonempty ((Scheme.Modules.pullback
      (CubeFace.second A.X B.X C.X (1 : Over.mk (𝟙 S) ⟶ B.X)).left).obj D.obj ≅
        Langlands.Scheme.Modules.structureSheaf (A.X ⨯ C.X).left))
    (h₃ : Nonempty ((Scheme.Modules.pullback
      (CubeFace.third A.X B.X C.X (1 : Over.mk (𝟙 S) ⟶ C.X)).left).obj D.obj ≅
        Langlands.Scheme.Modules.structureSheaf (A.X ⨯ B.X).left)) :
    Nonempty (D.obj ≅ Langlands.Scheme.Modules.structureSheaf (A.X ⨯ (B.X ⨯ C.X)).left) := by
  obtain ⟨τ₁⟩ := h₁
  choose U hcU hU using exists_local_triviality hF hL A.X B.X C.X 1 1 1 D ⟨τ₁⟩ h₂ h₃
  let q : (B.X ⨯ C.X).left ⟶ C.X.left := (prod.snd : B.X ⨯ C.X ⟶ C.X).left
  let 𝒰 : (B.X ⨯ C.X).left.OpenCover :=
    (B.X ⨯ C.X).left.openCoverOfIsOpenCover (fun c : C.X.left ↦ q ⁻¹ᵁ U c)
      (TopologicalSpace.IsOpenCover.mk (eq_top_iff.2 fun x _ ↦
        TopologicalSpace.Opens.mem_iSup.2 ⟨q x, hcU (q x)⟩))
  let R : RigidifiedFamily A (B.X ⨯ C.X) :=
    CubeRelativeTransport.cubeRigidified A.X B.X C.X 1 D τ₁
  have key : (⟦R⟧ : RigidifiedClasses A (B.X ⨯ C.X)) =
      ⟦RigidifiedLineBundle.trivial
        ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app
          (B.X ⨯ C.X))⟧ := by
    refine hZ S A (B.X ⨯ C.X) 𝒰 _ _ fun c ↦ ?_
    rw [classesPullback_eq_trivial A _ _ ?_, classesPullback_eq_trivial A _ _ ?_]
    · exact ⟨Langlands.Scheme.Modules.pullbackUnitIso _⟩
    · refine (TrivialAlong.pullback_iff _ _ _).2
        (hU c _ ((relativeProjection A.X.hom).app (Over.mk (𝒰.f c ≫ (B.X ⨯ C.X).hom)) ≫
          q ∣_ U c) ?_)
      simp only [thirdProjection, Category.assoc]
      rw [relativeSpaceProdIso_hom_snd_assoc, (relativeProjection A.X.hom).naturality_assoc]
      show _ ≫ (q ⁻¹ᵁ U c).ι ≫ q = _ ≫ (q ∣_ U c) ≫ (U c).ι
      rw [morphismRestrict_ι]
  obtain ⟨e⟩ := Quotient.exact key
  exact ⟨CubeRelativeTransport.cubeRecoverTrivialization A.X B.X C.X 1 D τ₁
    ((LineBundle.forget _).mapIso ((RigidifiedLineBundle.forget _).mapIso e))⟩

end Gluing

end RelativeCubeAssembly

end Langlands.AlgebraicGeometry.Picard

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Relative cube detection for rigidified families, assembled from the field theorem of the
cube, local two-axis triviality and Zariski separatedness of rigidified classes. -/
theorem relativeRigidifiedCube_of_field_local_zariski
    (hF : FieldCubeTrivialityStatement.{u})
    (hL : ∀ (T : Scheme.{u}) (P Q : Over T),
      Smooth P.hom → IsProper P.hom → GeometricallyConnected P.hom →
      Smooth Q.hom → IsProper Q.hom → GeometricallyConnected Q.hom →
      ∀ (p₀ : Over.mk (𝟙 T) ⟶ P) (q₀ : Over.mk (𝟙 T) ⟶ Q)
        (L : LineBundle (P ⨯ Q).left) (t : T),
        Nonempty ((Scheme.Modules.pullback
          (prod.lift (𝟙 P) (Over.mkIdTerminal.from P ≫ q₀)).left).obj L.obj ≅
            Langlands.Scheme.Modules.structureSheaf P.left) →
        Nonempty ((Scheme.Modules.pullback
          (prod.lift (Over.mkIdTerminal.from Q ≫ p₀) (𝟙 Q)).left).obj L.obj ≅
            Langlands.Scheme.Modules.structureSheaf Q.left) →
        Nonempty ((Scheme.Modules.pullback ((P ⨯ Q).hom.fiberι t)).obj L.obj ≅
          Langlands.Scheme.Modules.structureSheaf ((P ⨯ Q).hom.fiber t)) →
        ∃ U : T.Opens, t ∈ U ∧
          Nonempty ((Scheme.Modules.pullback
            (pullback.fst (P ⨯ Q).hom U.ι)).obj L.obj ≅
              Langlands.Scheme.Modules.structureSheaf (pullback (P ⨯ Q).hom U.ι)))
    (hZ : RigidifiedClassesZariskiSeparatedStatement.{u}) :
    RelativeRigidifiedCubeStatement.{u} :=
  fun _ _ A B C q r hB hC ↦
    rigidifiedClasses_eq_of_ordinaryCubeTriviality
      Langlands.Scheme.Modules.pullbackTensorComparisonIsIso A B C
      (fun D h₁ h₂ h₃ ↦
        RelativeCubeAssembly.nonempty_iso_structureSheaf_of_faces A hF hL hZ B C D h₁ h₂ h₃)
      q r hB hC

end Langlands.AbelianScheme
