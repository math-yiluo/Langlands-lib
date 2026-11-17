import Langlands.GroupScheme.RelativeUnipotent.SectionDescent
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Descent of compatible local section charts for one fixed module -/

noncomputable section
universe u
open CategoryTheory Limits AlgebraicGeometry
open Langlands.SchemeModule
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent

variable {S : Scheme.{u}}

/-- A matching family consisting of one represented point on a cover. -/
def PointCompatible {T U Z : Over S} (b : U ⟶ T) (x : U ⟶ Z) : Prop :=
  ∀ (W : Over S) (a c : W ⟶ U), a ≫ b = c ≫ b → a ≫ x = c ≫ x

lemma existsUnique_point_of_compatible {T U Z : Over S} (b : U ⟶ T)
    [IsAffineHom b.left] [Flat b.left] [Surjective b.left]
    (x : U ⟶ Z) (hx : PointCompatible b x) :
    ∃! y : T ⟶ Z, b ≫ y = x := by
  have H : ∀ {W : Scheme.{u}} (a c : W ⟶ U.left),
      a ≫ b.left = c ≫ b.left → a ≫ x.left = c ≫ x.left := by
    intro W a c h
    let V : Over S := Over.mk (a ≫ U.hom)
    let aa : V ⟶ U := Over.homMk a rfl
    have hc : c ≫ U.hom = a ≫ U.hom := by
      rw [← Over.w b, ← Category.assoc, ← Category.assoc, h]
    let cc : V ⟶ U := Over.homMk c hc
    have he : aa ≫ b = cc ≫ b := by ext; exact h
    exact congrArg (fun f => f.left) (hx V aa cc he)
  let f := EffectiveEpi.desc b.left x.left H
  have hf : b.left ≫ f = x.left := EffectiveEpi.fac b.left x.left H
  have hw : f ≫ Z.hom = T.hom := by
    apply (cancel_epi b.left).1
    rw [← Category.assoc, hf, Over.w x, Over.w b]
  let y : T ⟶ Z := Over.homMk f hw
  have hy : b ≫ y = x := by ext; exact hf
  refine ⟨y, hy, fun z hz => ?_⟩
  ext
  apply (cancel_epi b.left).1
  exact congrArg (fun f => f.left) (hz.trans hy.symm)

/-- Compatible point/section charts for tests admitting a lift to a fixed cover. -/
structure LocalSectionCharts {X : Scheme.{u}} (p : X ⟶ S)
    (V : GroupScheme S) (M : S.Modules) where
  equiv : ∀ (T : Over S) (a : T.left ⟶ X) (_ha : a ≫ p = T.hom),
    (T ⟶ V.X) ≃* Multiplicative
      (GlobalSections ((Scheme.Modules.pullback T.hom).obj M))
  natural : ∀ (T W : Over S) (b : W ⟶ T) (a : T.left ⟶ X)
    (ha : a ≫ p = T.hom) (x : T ⟶ V.X),
    (equiv W (b.left ≫ a) (by rw [Category.assoc, ha, Over.w b]) (b ≫ x)).toAdd =
      sectionPullback M b (equiv T a ha x).toAdd
  independent : ∀ (T : Over S) (a c : T.left ⟶ X)
    (ha : a ≫ p = T.hom) (hc : c ≫ p = T.hom) (x : T ⟶ V.X),
    equiv T a ha x = equiv T c hc x

namespace LocalSectionCharts

variable {X : Scheme.{u}} {p : X ⟶ S} {V : GroupScheme S} {M : S.Modules}
    (C : LocalSectionCharts p V M)

/-- The pullback of the base cover to a test. -/
abbrev cover (_C : LocalSectionCharts p V M) (T : Over S) : Over S :=
  Over.mk (pullback.snd p T.hom ≫ T.hom)

abbrev coverMap (T : Over S) : C.cover T ⟶ T :=
  Over.homMk (pullback.snd p T.hom) rfl

/-- The cover construction does not depend on the chart data. -/
instance coverMap_affine [IsAffineHom p] (T : Over S) :
    IsAffineHom (C.coverMap T).left := by
  exact MorphismProperty.of_isPullback (P := @IsAffineHom)
    (IsPullback.of_hasPullback p T.hom) inferInstance

instance coverMap_flat [Flat p] (T : Over S) : Flat (C.coverMap T).left := by
  exact MorphismProperty.of_isPullback (P := @Flat)
    (IsPullback.of_hasPullback p T.hom) inferInstance

instance coverMap_surjective [Surjective p] (T : Over S) :
    Surjective (C.coverMap T).left := by
  exact MorphismProperty.of_isPullback (P := @Surjective)
    (IsPullback.of_hasPullback p T.hom) inferInstance

/-- A section chart on the pullback cover, applied to a global point. -/
def coverSection (T : Over S) (x : T ⟶ V.X) :
    GlobalSections ((Scheme.Modules.pullback (C.cover T).hom).obj M) :=
  (C.equiv (C.cover T) (pullback.fst p T.hom) pullback.condition
    (C.coverMap T ≫ x)).toAdd

lemma coverSection_compatible (T : Over S) (x : T ⟶ V.X) :
    SectionCompatible M (C.coverMap T) (C.coverSection T x) := by
  intro W a c h
  rw [coverSection, ← C.natural, ← C.natural]
  simp only [← Category.assoc]
  rw [h]
  exact congrArg Multiplicative.toAdd (C.independent W _ _ _ _ _)

variable [IsAffineHom p] [Flat p] [Surjective p] [M.IsQuasicoherent]

/-- Descend the chart section of the pulled-back point. -/
def toSection (T : Over S) (x : T ⟶ V.X) :
    GlobalSections ((Scheme.Modules.pullback T.hom).obj M) :=
  sectionOfCompatible M (C.coverMap T) (C.coverSection T x)
    (C.coverSection_compatible T x)

@[simp]
lemma toSection_cover (T : Over S) (x : T ⟶ V.X) :
    sectionPullback M (C.coverMap T) (C.toSection T x) = C.coverSection T x :=
  sectionPullback_sectionOfCompatible M _ _ _

/-- A map from a test with a chosen lift factors through the pullback cover. -/
def liftToCover {T W : Over S} (b : W ⟶ T) (a : W.left ⟶ X)
    (ha : a ≫ p = W.hom) : W ⟶ C.cover T :=
  Over.homMk (pullback.lift a b.left (ha.trans (Over.w b).symm)) (by
    change pullback.lift a b.left _ ≫ (pullback.snd p T.hom ≫ T.hom) = W.hom
    rw [← Category.assoc, pullback.lift_snd, Over.w b])

omit [IsAffineHom p] [Flat p] [Surjective p] [M.IsQuasicoherent] in
@[simp]
lemma liftToCover_fac {T W : Over S} (b : W ⟶ T) (a : W.left ⟶ X)
    (ha : a ≫ p = W.hom) : C.liftToCover b a ha ≫ C.coverMap T = b := by
  ext
  exact pullback.lift_snd _ _ _

/-- On a test admitting a lift, descended sections have exactly the supplied chart. -/
lemma toSection_pullback_lift {T W : Over S} (b : W ⟶ T)
    (a : W.left ⟶ X) (ha : a ≫ p = W.hom) (x : T ⟶ V.X) :
    sectionPullback M b (C.toSection T x) = (C.equiv W a ha (b ≫ x)).toAdd := by
  rw [← C.liftToCover_fac b a ha, ← sectionPullback_comp, C.toSection_cover]
  rw [coverSection, ← C.natural]
  simp only [← Category.assoc, C.liftToCover_fac]
  exact congrArg Multiplicative.toAdd (C.independent W _ _ _ _ _)

lemma toSection_natural (T W : Over S) (b : W ⟶ T) (x : T ⟶ V.X) :
    C.toSection W (b ≫ x) = sectionPullback M b (C.toSection T x) := by
  apply sectionPullback_injective M (C.coverMap W)
  rw [sectionPullback_comp,
    C.toSection_pullback_lift (C.coverMap W) (pullback.fst p W.hom) pullback.condition,
    C.toSection_pullback_lift (C.coverMap W ≫ b) (pullback.fst p W.hom) pullback.condition,
    Category.assoc]

lemma toSection_injective (T : Over S) : Function.Injective (C.toSection T) := by
  intro x y h
  have H := congrArg (sectionPullback M (C.coverMap T)) h
  rw [C.toSection_cover, C.toSection_cover] at H
  have H' : C.coverMap T ≫ x = C.coverMap T ≫ y :=
    (C.equiv (C.cover T) _ pullback.condition).injective H
  ext
  apply (cancel_epi (C.coverMap T).left).1
  exact congrArg (fun f => f.left) H'

omit [IsAffineHom p] [Flat p] [Surjective p] [M.IsQuasicoherent] in
/-- Naturality applied to a local inverse chart. -/
lemma equiv_inverse_natural (T W : Over S) (b : W ⟶ T)
    (a : T.left ⟶ X) (ha : a ≫ p = T.hom)
    (s : GlobalSections ((Scheme.Modules.pullback T.hom).obj M)) :
    (C.equiv W (b.left ≫ a) (by rw [Category.assoc, ha, Over.w b])
      (b ≫ (C.equiv T a ha).symm (Multiplicative.ofAdd s))).toAdd =
        sectionPullback M b s := by
  rw [C.natural T W b a ha, MulEquiv.apply_symm_apply]
  rfl

omit [IsAffineHom p] [Flat p] [Surjective p] [M.IsQuasicoherent] in
/-- Equal section pullbacks give equal inverse-chart points. -/
lemma inverse_equiv_matching (T W : Over S) (a : T.left ⟶ X)
    (ha : a ≫ p = T.hom) (b c : W ⟶ T)
    (s : GlobalSections ((Scheme.Modules.pullback T.hom).obj M))
    (hs : sectionPullback M b s = sectionPullback M c s) :
    b ≫ (C.equiv T a ha).symm (Multiplicative.ofAdd s) =
      c ≫ (C.equiv T a ha).symm (Multiplicative.ofAdd s) := by
  apply (C.equiv W (b.left ≫ a)
    (by rw [Category.assoc, ha, Over.w b])).injective
  change (C.equiv W _ _ _).toAdd = (C.equiv W _ _ _).toAdd
  rw [C.equiv_inverse_natural]
  rw [C.independent W (b.left ≫ a) (c.left ≫ a) _
    (by rw [Category.assoc, ha, Over.w c])]
  exact hs.trans (C.equiv_inverse_natural T W c a ha s).symm

omit [IsAffineHom p] [Flat p] [Surjective p] [M.IsQuasicoherent] in
/-- The local inverse chart of a pulled-back section is a matching represented point. -/
lemma inverseChart_compatible (T : Over S)
    (s : GlobalSections ((Scheme.Modules.pullback T.hom).obj M)) :
    PointCompatible (C.coverMap T)
      ((C.equiv (C.cover T) (pullback.fst p T.hom) pullback.condition).symm
        (Multiplicative.ofAdd (sectionPullback M (C.coverMap T) s))) := by
  intro W a c h
  apply C.inverse_equiv_matching (C.cover T) W (pullback.fst p T.hom)
    pullback.condition a c
  rw [sectionPullback_comp, sectionPullback_comp, h]

lemma toSection_surjective (T : Over S) : Function.Surjective (C.toSection T) := by
  intro s
  let z := (C.equiv (C.cover T) (pullback.fst p T.hom) pullback.condition).symm
    (Multiplicative.ofAdd (sectionPullback M (C.coverMap T) s))
  obtain ⟨x, hx, -⟩ := existsUnique_point_of_compatible (C.coverMap T) z
    (C.inverseChart_compatible T s)
  refine ⟨x, ?_⟩
  apply sectionPullback_injective M (C.coverMap T)
  rw [C.toSection_cover, coverSection, hx]
  exact congrArg Multiplicative.toAdd
    ((C.equiv (C.cover T) _ pullback.condition).apply_symm_apply _)

/-- The descended chart map respects the actual point group law. -/
def toSectionHom (T : Over S) :
    (T ⟶ V.X) →* Multiplicative
      (GlobalSections ((Scheme.Modules.pullback T.hom).obj M)) where
  toFun x := Multiplicative.ofAdd (C.toSection T x)
  map_one' := by
    change C.toSection T 1 = 0
    apply sectionPullback_injective M (C.coverMap T)
    rw [C.toSection_cover, AffineSectionCoordinates.sectionPullback_zero]
    simp only [coverSection, MonObj.comp_one, map_one, toAdd_one]
  map_mul' x y := by
    change C.toSection T (x * y) = C.toSection T x + C.toSection T y
    apply sectionPullback_injective M (C.coverMap T)
    rw [C.toSection_cover, AffineSectionCoordinates.sectionPullback_add,
      C.toSection_cover, C.toSection_cover]
    simp only [coverSection, MonObj.comp_mul, map_mul, toAdd_mul]

/-- The global multiplicative point/section equivalence descended from the charts. -/
def globalEquiv (T : Over S) :
    (T ⟶ V.X) ≃* Multiplicative
      (GlobalSections ((Scheme.Modules.pullback T.hom).obj M)) :=
  MulEquiv.ofBijective (C.toSectionHom T)
    ⟨C.toSection_injective T, C.toSection_surjective T⟩

lemma globalEquiv_natural (T W : Over S) (b : W ⟶ T) (x : T ⟶ V.X) :
    (C.globalEquiv W (b ≫ x)).toAdd =
      sectionPullback M b (C.globalEquiv T x).toAdd :=
  C.toSection_natural T W b x

include C in
/-- Finite local bases and the descended chart equivalences give the target predicate. -/
lemma isVectorBundleAdditive [IsAffineHom V.X.hom] [Smooth V.X.hom]
    (hM : IsFiniteLocallyFree M) : IsVectorBundleAdditive V :=
  ⟨inferInstance, inferInstance, M, hM, C.globalEquiv, C.globalEquiv_natural⟩

end LocalSectionCharts
end Langlands.GroupScheme.RelativeUnipotent
