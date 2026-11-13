import Langlands.AlgebraicGeometry.Picard.ArtinianChartVersality
import Langlands.AlgebraicGeometry.Picard.AtlasArrowInversion
import Langlands.CategoryTheory.Sites.PseudofunctorParallelIsomorphisms

/-! # Pointed Picard versality along towers of Artinian levels -/

noncomputable section

universe u v v' w w'

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.CategoryTheory.PseudofunctorPointFiber

variable {C : Type w} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', w'}}

/-- Two actual points are equal when their maps agree and the first isomorphism,
transported along the identity, is the second. -/
lemma points_eq_of_pullIso {U T : C} {ξ : F.obj (.mk (op U))} {η : F.obj (.mk (op T))}
    {Z : Over T} {a₁ a₂ : Z.left ⟶ U}
    (e₁ : (F.map a₁.op.toLoc).toFunctor.obj ξ ≅ (F.map Z.hom.op.toLoc).toFunctor.obj η)
    (e₂ : (F.map a₂.op.toLoc).toFunctor.obj ξ ≅ (F.map Z.hom.op.toLoc).toFunctor.obj η)
    (h : 𝟙 Z.left ≫ a₁ = a₂)
    (he : pullIso e₁ (𝟙 Z.left) a₂ Z.hom h (Category.id_comp _) = e₂) :
    (⟨a₁, e₁⟩ : Points F ξ η Z) = ⟨a₂, e₂⟩ := by
  have ha : a₁ = a₂ := by simpa using h
  subst ha
  have : pullIso e₁ (𝟙 Z.left) a₁ Z.hom h (Category.id_comp _) = e₁ := pullIso_id e₁
  rw [this] at he
  subst he
  rfl

/-- Equal actual points have equal isomorphisms after transport along the identity. -/
lemma pullIso_eq_of_points_eq {U T : C} {ξ : F.obj (.mk (op U))} {η : F.obj (.mk (op T))}
    {Z : Over T} {a₁ a₂ : Z.left ⟶ U}
    {e₁ : (F.map a₁.op.toLoc).toFunctor.obj ξ ≅ (F.map Z.hom.op.toLoc).toFunctor.obj η}
    {e₂ : (F.map a₂.op.toLoc).toFunctor.obj ξ ≅ (F.map Z.hom.op.toLoc).toFunctor.obj η}
    (H : (⟨a₁, e₁⟩ : Points F ξ η Z) = ⟨a₂, e₂⟩) (h : 𝟙 Z.left ≫ a₁ = a₂) :
    pullIso e₁ (𝟙 Z.left) a₂ Z.hom h (Category.id_comp _) = e₂ := by
  cases H
  exact pullIso_id e₁

/-- **Transfer of one lifting problem through a level.** Let `x` be a point of
`ξ` with values in `ξ'` over a level `c : Z ⟶ U`, whose chart map is a
monomorphism. A point `y` of `ξ'` factoring through the level yields a point of
`ξ`; if that point lifts along `g` to a point factoring through the same level,
then `y` itself lifts along `g`. -/
theorem exists_restrict_eq_of_factor {U V T : C} {ξ : F.obj (.mk (op V))}
    {ξ' : F.obj (.mk (op U))} {M : F.obj (.mk (op T))} {Z : C} {c : Z ⟶ U}
    (x : Points F ξ ξ' (Over.mk c)) [Mono x.1]
    {A B : C} {a : A ⟶ T} {b : B ⟶ T} (g : B ⟶ A) (w : g ≫ a = b)
    (y : Points F ξ' M (Over.mk b)) (j : B ⟶ Z) (hj : j ≫ c = y.1)
    (xL : Points F ξ M (Over.mk a))
    (hxL : restrict F ξ M (Over.homMk g w : Over.mk b ⟶ Over.mk a) xL =
      ⟨j ≫ x.1, (restrict F ξ ξ' (Over.homMk j hj : Over.mk y.1 ⟶ Over.mk c) x).2 ≪≫ y.2⟩)
    (j' : A ⟶ Z) (hj' : j' ≫ x.1 = xL.1) :
    ∃ x' : Points F ξ' M (Over.mk a),
      restrict F ξ' M (Over.homMk g w : Over.mk b ⟶ Over.mk a) x' = y := by
  rcases y with ⟨y₁, y₂⟩
  dsimp only at hj
  subst hj
  rcases xL with ⟨xL₁, xL₂⟩
  dsimp only at hj'
  subst hj'
  have h₁ := congrArg Sigma.fst hxL
  have hE : g ≫ j' = j := by
    rw [← cancel_mono x.1]
    simpa only [restrict, Over.homMk_left, Category.assoc] using h₁
  subst hE
  -- the comparison of the two levels used to define `xL`
  have h₂ := pullIso_eq_of_points_eq hxL (by simp)
  simp only [restrict, Over.homMk_left] at h₂
  rw [pullIso_pullIso _ _ _ _ _ _ _ _ _ _ _] at h₂
  refine ⟨⟨j' ≫ c, (pullIso x.2 j' (j' ≫ x.1) (j' ≫ c) rfl rfl).symm ≪≫ xL₂⟩, ?_⟩
  simp only [restrict, Over.homMk_left]
  refine points_eq_of_pullIso _ _ (by simp) ?_
  rw [pullIso_pullIso _ _ _ _ _ _ _ _ _ _ _]
  have h1 : (𝟙 (Over.mk b).left ≫ g) ≫ (j' ≫ c) = (g ≫ j') ≫ c := by simp
  have h2 : (𝟙 (Over.mk b).left ≫ g) ≫ (j' ≫ x.1) = (g ≫ j') ≫ x.1 := by simp
  have h3 : (𝟙 (Over.mk b).left ≫ g) ≫ (Over.mk a).hom = (Over.mk b).hom := by simpa using w
  have e1 := pullIso_trans (pullIso x.2 j' (j' ≫ x.1) (j' ≫ c) rfl rfl).symm xL₂
    (𝟙 (Over.mk b).left ≫ g) ((g ≫ j') ≫ c) ((g ≫ j') ≫ x.1) (Over.mk b).hom h1 h2 h3
  have e2 := pullIso_symm (pullIso x.2 j' (j' ≫ x.1) (j' ≫ c) rfl rfl)
    (𝟙 (Over.mk b).left ≫ g) ((g ≫ j') ≫ x.1) ((g ≫ j') ≫ c) h2 h1
  have e3 := pullIso_pullIso x.2 j' (j' ≫ x.1) (j' ≫ c)
    (𝟙 (Over.mk b).left ≫ g) ((g ≫ j') ≫ x.1) ((g ≫ j') ≫ c) rfl rfl h2 h1
  have e4 := pullIso_congr x.2 ((𝟙 (Over.mk b).left ≫ g) ≫ j') (g ≫ j') (by simp)
    ((g ≫ j') ≫ x.1) ((g ≫ j') ≫ c) (by simp) (by simp) rfl rfl
  rw [e1, e2, e3, e4, h₂]
  exact Iso.symm_self_id_assoc _ _

end Langlands.CategoryTheory.PseudofunctorPointFiber

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

open Langlands.AlgebraicGeometry.Deformation
open Langlands.CategoryTheory

namespace ArtinianChartVersality

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  {V : Over (Spec (CommRingCat.of k))}
  (L : LineBundle ((relativeSpace f).obj V))
  (pV : ArtinianTest.residueBase k K ⟶ V)

/-- The composite of a tower of Artinian test arrows down to its bottom level. -/
def towerDown (T : ℕ → ArtinianTest k K) (π : ∀ n, T (n + 1) ⟶ T n) :
    ∀ n, T n ⟶ T 0
  | 0 => 𝟙 _
  | n + 1 => π n ≫ towerDown T π n

/-- **Versal lifting along a tower.** A pointed fibre point at the bottom of a
tower of surjective Artinian tests mapping compatibly to a chart lifts to every
level of the tower, compatibly with the bottom point. -/
theorem exists_tower_points (hL : IsFormallyVersalAt f L pV)
    {U : Over (Spec (CommRingCat.of k))} (L' : LineBundle ((relativeSpace f).obj U))
    (T : ℕ → ArtinianTest k K) (π : ∀ n, T (n + 1) ⟶ T n)
    (hπ : ∀ n, Function.Surjective (ArtinianTest.toAlgHom (π n)))
    (c : ∀ n, ArtinianTest.base (T n) ⟶ U)
    (hc : ∀ n, ArtinianTest.baseMap (π n) ≫ c (n + 1) = c n)
    (x₀ : FiberPoints f L L' (Over.mk (c 0)))
    (hx₀ : ArtinianTest.reduction (T 0) ≫ x₀.1 = pV) :
    ∀ n, ∃ x : FiberPoints f L L' (Over.mk (c n)),
      ArtinianTest.reduction (T n) ≫ x.1 = pV ∧
        ArtinianTest.baseMap (towerDown T π n) ≫ x.1 = x₀.1 := by
  intro n
  induction n with
  | zero =>
    refine ⟨x₀, hx₀, ?_⟩
    simp [towerDown, ArtinianTest.baseMap_id]
  | succ n ih =>
    obtain ⟨x, hx, hdown⟩ := ih
    obtain ⟨x', hx', hres⟩ := exists_lift_at f L pV (hL (π n) (hπ n)) U L'
      (c (n + 1)) (c n) (hc n) x hx
    refine ⟨x', hx', ?_⟩
    have h1 : ArtinianTest.baseMap (π n) ≫ x'.1 = x.1 := by
      rw [← ArtinianChartLifting.restrict_baseMap f L (π n) L' (hc n) x', hres]
    simp only [towerDown, ← ArtinianTest.baseMap_comp, Category.assoc, h1, hdown]

/-- **Versality transfer along levels.** Let `L` be formally versal at `pV`, and
let `x n` be fibre points of `L` with values in `L'` over levels `c n` of a chart
`U`, with monomorphic chart maps. Suppose that, for each Artinian test, every
pointed map to `U` factors through all sufficiently high levels, and every pointed
map to the chart of `L` factors through the chart maps of all sufficiently high
levels. Then `L'` is formally versal at `pU`. -/
theorem isFormallyVersalAt_of_levels (hL : IsFormallyVersalAt f L pV)
    {U : Over (Spec (CommRingCat.of k))} (L' : LineBundle ((relativeSpace f).obj U))
    (pU : ArtinianTest.residueBase k K ⟶ U)
    (Z : ℕ → Over (Spec (CommRingCat.of k))) (c : ∀ n, Z n ⟶ U)
    (x : ∀ n, FiberPoints f L L' (Over.mk (c n)))
    (hmono : ∀ n, Mono (x n).1)
    (hpt : ∀ n (r : ArtinianTest.residueBase k K ⟶ Z n), r ≫ c n = pU → r ≫ (x n).1 = pV)
    (hU : ∀ B : ArtinianTest k K, ∃ n₀, ∀ n ≥ n₀, ∀ y : ArtinianTest.base B ⟶ U,
      ArtinianTest.reduction B ≫ y = pU → ∃ j, j ≫ c n = y)
    (hV : ∀ A : ArtinianTest k K, ∃ n₀, ∀ n ≥ n₀, ∀ z : ArtinianTest.base A ⟶ V,
      ArtinianTest.reduction A ≫ z = pV → ∃ j, j ≫ (x n).1 = z) :
    IsFormallyVersalAt f L' pU := by
  intro A B q hq T M a b w y hy
  obtain ⟨n₀, hn₀⟩ := hU B
  obtain ⟨n₁, hn₁⟩ := hV A
  obtain ⟨j, hj⟩ := hn₀ (max n₀ n₁) (le_max_left _ _) y.1 hy
  let yL : FiberPoints f L M (Over.mk b) :=
    ⟨j ≫ (x (max n₀ n₁)).1,
      (PseudofunctorPointFiber.restrict (relative f) (Core.mk L) (Core.mk L')
        (Over.homMk j hj : Over.mk y.1 ⟶ Over.mk (c (max n₀ n₁))) (x (max n₀ n₁))).2 ≪≫
        y.2⟩
  have hyL : ArtinianTest.reduction B ≫ yL.1 = pV := by
    change ArtinianTest.reduction B ≫ j ≫ (x (max n₀ n₁)).1 = pV
    rw [← Category.assoc]
    apply hpt
    rw [Category.assoc, hj, hy]
  obtain ⟨xL, hxL⟩ := hL q hq T M a b w yL hyL
  have hxLp : ArtinianTest.reduction A ≫ xL.1 = pV :=
    (residueMap_of_restrict_eq f L q M w hxL).trans hyL
  obtain ⟨j', hj'⟩ := hn₁ (max n₀ n₁) (le_max_right _ _) xL.1 hxLp
  have := hmono (max n₀ n₁)
  exact PseudofunctorPointFiber.exists_restrict_eq_of_factor (x (max n₀ n₁))
    (ArtinianTest.baseMap q) w y j hj xL hxL j' hj'

end ArtinianChartVersality

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
