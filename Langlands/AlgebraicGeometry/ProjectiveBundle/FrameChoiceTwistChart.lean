import Langlands.AlgebraicGeometry.ProjectiveBundle.FrameChoiceTwist

/-! # Chart compatibility of degree-one comparisons for frame families -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.SchemeModule.RigidifiedModule
open Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.RelativeProjectiveSpace

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Scheme.Modules

/-- The canonical comparisons commute around two compatible chart squares. -/
lemma chartSquare_compHom {P Q R B C F : Scheme.{u}}
    (a : P ⟶ Q) (b : Q ⟶ R) (c : P ⟶ R) (hab : a ≫ b = c)
    (j : P ⟶ B) (k : Q ⟶ C) (l : R ⟶ F)
    (f : B ⟶ C) (t : B ⟶ F) (v : C ⟶ F)
    (hf : f ≫ v = t) (hw : j ≫ f = a ≫ k)
    (hj : j ≫ t = c ≫ l) (hk : k ≫ v = b ≫ l)
    (N : F.Modules) :
    (Scheme.Modules.pullback j).map (compHom f v t hf N) ≫
        (squarePullbackIso l j c t hj N).hom =
      (squarePullbackIso k j a f hw ((Scheme.Modules.pullback v).obj N)).hom ≫
        (Scheme.Modules.pullback a).map (squarePullbackIso l k b v hk N).hom ≫
          compHom a b c hab ((Scheme.Modules.pullback l).obj N) := by
  subst t
  let z := j ≫ (f ≫ v)
  have ha : a ≫ (k ≫ v) = z := by
    dsimp only [z]
    rw [← Category.assoc, ← hw, Category.assoc]
  have hb : a ≫ (b ≫ l) = z := by rw [← hk, ha]
  have hc : c ≫ l = z := by rw [← hab, Category.assoc, hb]
  have hcomp := compHom_assoc a b l c (b ≫ l) z hab rfl hc hb N
  rw [compHom_rfl] at hcomp
  apply (cancel_mono (compHom c l z hc N)).mp
  simp only [Category.assoc]
  rw [CommonSourceCocycle.square_normalize l j c (f ≫ v) hj N z hc,
    hcomp]
  change CommonSourceCocycle.normalize j f v z rfl N =
    (squarePullbackIso k j a f hw ((Scheme.Modules.pullback v).obj N)).hom ≫
      (Scheme.Modules.pullback a).map (squarePullbackIso l k b v hk N).hom ≫
        CommonSourceCocycle.normalize a b l z hb N
  rw [CommonSourceCocycle.inner_square_normalize a k b v l hk N z ha hb,
    CommonSourceCocycle.outer_square_normalize j a f k v hw N z rfl ha]

/-- Chartwise degree-one comparisons inherit a proved local composition law. -/
lemma chartTwist_transport {P Q R B C F : Scheme.{u}}
    (a : P ⟶ Q) (b : Q ⟶ R) (c : P ⟶ R) (hab : a ≫ b = c)
    (j : P ⟶ B) (k : Q ⟶ C) (l : R ⟶ F)
    (f : B ⟶ C) (t : B ⟶ F) (v : C ⟶ F)
    (hf : f ≫ v = t) (hw : j ≫ f = a ≫ k)
    (hj : j ≫ t = c ≫ l) (hk : k ≫ v = b ≫ l)
    (N : F.Modules) {L : R.Modules} {LQ : Q.Modules} {LP : P.Modules}
    (e : (Scheme.Modules.pullback l).obj N ≅ L)
    (α : (Scheme.Modules.pullback a).obj LQ ≅ LP)
    (β : (Scheme.Modules.pullback b).obj L ≅ LQ)
    (γ : (Scheme.Modules.pullback c).obj L ≅ LP)
    (hαβ : (Scheme.Modules.pullback a).map β.hom ≫ α.hom =
      (Scheme.Modules.pullbackComp a b).hom.app L ≫
        (Scheme.Modules.pullbackCongr hab).hom.app L ≫ γ.hom) :
    (Scheme.Modules.pullback j).map (compHom f v t hf N) ≫
        (squarePullbackIso l j c t hj N).hom ≫
          (Scheme.Modules.pullback c).map e.hom ≫ γ.hom =
      (squarePullbackIso k j a f hw ((Scheme.Modules.pullback v).obj N)).hom ≫
        (Scheme.Modules.pullback a).map
          ((squarePullbackIso l k b v hk N).hom ≫
            (Scheme.Modules.pullback b).map e.hom ≫ β.hom) ≫ α.hom := by
  have hαβ' : (Scheme.Modules.pullback a).map β.hom ≫ α.hom =
      compHom a b c hab L ≫ γ.hom := by
    simpa only [compHom, Category.assoc] using hαβ
  simp only [Functor.map_comp, Category.assoc]
  rw [hαβ',
    reassoc_of% (CommonSourceCocycle.compHom_naturality a b c hab e.hom)]
  rw [← reassoc_of% (chartSquare_compHom a b c hab j k l f t v hf hw hj hk N)]

end Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.LinearSystem

/-- The relative twist comparisons compose with any named resulting coordinate change. -/
lemma relativeLinearActionTwistIso_comp_named {K : Type u} [CommRing K]
    {S : Scheme.{u}} {n : ℕ} (a : S ⟶ Spec (CommRingCat.of K))
    (e f g : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K))
    (hef : e.trans f = g) (hw : linearAction a e ≫ linearAction a f = linearAction a g) :
    (Scheme.Modules.pullback (linearAction a e)).map
        (relativeLinearActionTwistIso a f).hom ≫ (relativeLinearActionTwistIso a e).hom =
      (Scheme.Modules.pullbackComp (linearAction a e) (linearAction a f)).hom.app
          (RelativeProjectiveSpace.twistOne S n).obj ≫
        (Scheme.Modules.pullbackCongr hw).hom.app
          (RelativeProjectiveSpace.twistOne S n).obj ≫
        (relativeLinearActionTwistIso a g).hom := by
  apply linearChange_pullback_comparison_comp (L := RelativeProjectiveSpace.twistOne S n)
    (RelativeProjectiveSpace.toBase S n ≫ a)
    (RelativeProjectiveSpace.twistOneCoordinate S n)
    (isOpenCover_trivializationOpen (L := RelativeProjectiveSpace.twistOne S n)
      (relativeProjectiveCoordinates_generate S n))
    (linearAction a e) (linearAction a f) (linearAction a g) hw
    (by rw [← Category.assoc, linearAction_toBase]) e f
    (relativeLinearActionTwistIso a e).hom (relativeLinearActionTwistIso a f).hom
    (relativeLinearActionTwistIso a g).hom
    (relativeLinearActionTwistIso_coordinate a e)
    (relativeLinearActionTwistIso_coordinate a f)
  intro i
  rw [relativeLinearActionTwistIso_coordinate, hef]
  rfl

set_option linter.defProp false in
/-- Transport of the proved relative linear-action law through three chart squares. -/
def relativeLinearActionTwistIso_chart
    {K : Type u} [CommRing K] {T : Scheme.{u}} {n : ℕ}
    (a : T ⟶ Spec (CommRingCat.of K))
    (e f g : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K))
    (hef : e.trans f = g)
    (hw : linearAction a e ≫ linearAction a f = linearAction a g)
    {B C F : Scheme.{u}}
    (j : RelativeProjectiveSpace T n ⟶ B)
    (k : RelativeProjectiveSpace T n ⟶ C)
    (l : RelativeProjectiveSpace T n ⟶ F)
    (r : B ⟶ C) (t : B ⟶ F) (v : C ⟶ F)
    (hrt : r ≫ v = t)
    (hj : j ≫ r = linearAction a e ≫ k)
    (hjt : j ≫ t = linearAction a g ≫ l)
    (hk : k ≫ v = linearAction a f ≫ l)
    (N : F.Modules)
    (ι : (Scheme.Modules.pullback l).obj N ≅ (RelativeProjectiveSpace.twistOne T n).obj) :=
  chartTwist_transport
    (linearAction a e) (linearAction a f) (linearAction a g) hw
    j k l r t v hrt hj hjt hk N ι
    (relativeLinearActionTwistIso a e) (relativeLinearActionTwistIso a f)
    (relativeLinearActionTwistIso a g)
    (relativeLinearActionTwistIso_comp_named a e f g hef hw)

end Langlands.AlgebraicGeometry.LinearSystem

namespace Langlands.AlgebraicGeometry.ProjectiveBundle

variable {S : Scheme.{u}} {M : S.Modules} {n : ℕ}

/-- The relative actions associated with genuine dual-frame changes compose. -/
lemma familyRelativeLinearAction_comp (b c d : FrameFamily M n) (U : FrameOpen M n) :
    linearAction U.val.toScheme.toSpecΓ (familyCoordinate b c U) ≫
        linearAction U.val.toScheme.toSpecΓ (familyCoordinate c d U) =
      linearAction U.val.toScheme.toSpecΓ (familyCoordinate b d U) := by
  rw [linearAction_comp, familyCoordinate_trans]

-- Inferred proof types preserve the coefficient-ring expression of the generic law.
-- Restating the expanded open-scheme type makes kernel conversion unnecessarily costly.
set_option linter.defProp false in
/-- The actual dual-frame twist comparisons obey the named coordinate composition law. -/
def familyLinearActionTwist_comp (b c d : FrameFamily M n) (U : FrameOpen M n) :=
  @LinearSystem.relativeLinearActionTwistIso_comp_named
    (Γ(U.val.toScheme, ⊤)) (Γ(U.val.toScheme, ⊤)).commRing
    U.val.toScheme n U.val.toScheme.toSpecΓ
    (familyCoordinate b c U) (familyCoordinate c d U) (familyCoordinate b d U)
    (familyCoordinate_trans b c d U) (familyRelativeLinearAction_comp b c d U)

variable (hM : IsLocallyFreeOfRank M (n + 1))

set_option linter.defProp false in
/-- In charts, the global comparison is given by the actual dual-frame twist action. -/
def frameChoiceTwistIso_chart (b c : FrameFamily M n) (U : FrameOpen M n) :=
  @LinearSystem.relativeLinearActionTwistIso_chart
    (Γ(U.val.toScheme, ⊤)) (Γ(U.val.toScheme, ⊤)).commRing
    U.val.toScheme n U.val.toScheme.toSpecΓ
    (familyCoordinate b c U) (familyCoordinate c (frame M n) U)
    (familyCoordinate b (frame M n) U)
    (familyCoordinate_trans b c (frame M n) U)
    (familyRelativeLinearAction_comp b c (frame M n) U)
    (familyBundle hM b) (familyBundle hM c) (frameBundle M n hM)
    ((familyCocycle hM b).chart U) ((familyCocycle hM c).chart U)
    (FrameBundle.chart hM U)
    (frameChoiceIso hM b c).hom (toFrameBundleIso hM b).hom
    (toFrameBundleIso hM c).hom (frameChoiceIso_hom_toFrameBundle hM b c)
    (chart_frameChoiceIso_hom hM b c U)
    (familyChart_toFrameBundle hM b U) (familyChart_toFrameBundle hM c U)
    (FrameBundle.twistOne hM).obj (FrameBundle.twistOneModuleIso hM U)

end Langlands.AlgebraicGeometry.ProjectiveBundle
