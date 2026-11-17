import Langlands.GroupScheme.IsomorphismPresheaf
import Langlands.GroupScheme.LocalGroupIsoCoproduct
import Langlands.GroupScheme.OuterIsomorphismConstantSection

/-! # Classification by disjoint coproduct families and descent of labels -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.LocalGroupIso

open Langlands.AlgebraicGeometry.AlgebraicSpace.CoproductChart

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- Equality of natural isomorphism families descends along every covering sieve
for a subcanonical topology on relative schemes. -/
theorem eq_of_refine_coveringSieve (J : GrothendieckTopology (Over S))
    [J.Subcanonical] {T : Over S} (R : Sieve T) (hR : R ∈ J T)
    {e f : LocalGroupIso G H T}
    (h : ∀ (W : Over S) (p : W ⟶ T), R p → e.refine p = f.refine p) : e = f := by
  apply ext_toFun
  intro W a g
  have hs := (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := J) (yoneda.obj H.X)) _ (J.pullback_stable a hR)
  apply hs.isSeparatedFor.ext
  intro Z p hp
  change p ≫ e.toFun a g = p ≫ f.toFun a g
  rw [← e.naturality, ← f.naturality]
  have hv := congrArg (fun E : LocalGroupIso G H Z => E.toFun (𝟙 Z) (p ≫ g))
    (h Z (p ≫ a) hp)
  simpa only [refine_toFun, Category.id_comp] using hv

/-- Equality of natural families can be tested on any covering family. -/
theorem eq_of_refine_cover (J : GrothendieckTopology (Over S)) [J.Subcanonical]
    {K : Type v} {T : Over S} (V : K → Over S) (p : ∀ i, V i ⟶ T)
    (hp : Sieve.ofArrows V p ∈ J T) {e f : LocalGroupIso G H T}
    (h : ∀ i, e.refine (p i) = f.refine (p i)) : e = f := by
  apply eq_of_refine_coveringSieve J (Sieve.ofArrows V p) hp
  intro W a ha
  obtain ⟨i, b, rfl⟩ := (Sieve.mem_ofArrows_iff V p a).mp ha
  simpa only [refine_comp] using congrArg (fun E => E.refine b) (h i)

variable {U : Over S} (E : LocalGroupIso G H U)
    (hinj : ∀ (T : Over S), Function.Injective (fun a : T ⟶ U => E.refine a))

include hinj in
/-- Locally classifying morphisms glue uniquely on the original test scheme.
Only subcanonicity and all-test injectivity of the family are required. -/
theorem existsUnique_classify_of_cover (J : GrothendieckTopology (Over S))
    [J.Subcanonical] {K : Type v} {T : Over S} (V : K → Over S)
    (p : ∀ i, V i ⟶ T) (hp : Sieve.ofArrows V p ∈ J T)
    (e : LocalGroupIso G H T) (a : ∀ i, V i ⟶ U)
    (ha : ∀ i, E.refine (a i) = e.refine (p i)) :
    ∃! b : T ⟶ U, E.refine b = e := by
  have hc : Presieve.Arrows.Compatible (yoneda.obj U) p a := by
    intro i j W f g hfg
    change f ≫ a i = g ≫ a j
    apply hinj W
    change E.refine (f ≫ a i) = E.refine (g ≫ a j)
    rw [← refine_comp, ← refine_comp, ha i, ha j, refine_comp, refine_comp, hfg]
  have hs : Presieve.IsSheafFor (yoneda.obj U) (Presieve.ofArrows V p) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := J) (yoneda.obj U)) _ hp
  obtain ⟨b, hb, _⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp hs a hc
  have he : E.refine b = e := by
    apply eq_of_refine_cover J V p hp
    intro i
    rw [refine_comp, show p i ≫ b = a i from hb i, ha i]
  exact ⟨b, he, fun c hc => hinj T (hc.trans he.symm)⟩

/-- The unique classifying morphism obtained by descent from a covering family. -/
def classifyOfCover (J : GrothendieckTopology (Over S)) [J.Subcanonical]
    {K : Type v} {T : Over S} (V : K → Over S) (p : ∀ i, V i ⟶ T)
    (hp : Sieve.ofArrows V p ∈ J T) (e : LocalGroupIso G H T)
    (a : ∀ i, V i ⟶ U) (ha : ∀ i, E.refine (a i) = e.refine (p i)) : T ⟶ U :=
  (existsUnique_classify_of_cover E hinj J V p hp e a ha).choose

@[simp] theorem refine_classifyOfCover (J : GrothendieckTopology (Over S))
    [J.Subcanonical] {K : Type v} {T : Over S} (V : K → Over S)
    (p : ∀ i, V i ⟶ T) (hp : Sieve.ofArrows V p ∈ J T)
    (e : LocalGroupIso G H T) (a : ∀ i, V i ⟶ U)
    (ha : ∀ i, E.refine (a i) = e.refine (p i)) :
    E.refine (classifyOfCover E hinj J V p hp e a ha) = e :=
  (existsUnique_classify_of_cover E hinj J V p hp e a ha).choose_spec.1

variable {K : Type u} (V : K → Over S) (e : ∀ i, LocalGroupIso G H (V i))
    (hcomp : ∀ (i : K) (T : Over S),
      Function.Injective (fun a : T ⟶ V i => (e i).refine a))
    (hdisj : ∀ (i j : K) (T : Over S) (a : T ⟶ V i) (b : T ⟶ V j),
      (e i).refine a = (e j).refine b → i = j ∨ IsEmpty T.left)

include hcomp hdisj in
/-- Distinct component labels cannot classify equal families on a nonempty test. -/
theorem eq_coproduct_ι_of_refine_eq {T : Over S} (i j : K)
    (a : T ⟶ V i) (b : T ⟶ V j) (hab : (e i).refine a = (e j).refine b) :
    a ≫ sigmaOverι V i = b ≫ sigmaOverι V j := by
  rcases hdisj i j T a b hab with hij | hT
  · subst j
    exact congrArg (fun c => c ≫ sigmaOverι V i) (hcomp i T hab)
  · let : IsEmpty T.left := hT
    exact Over.OverMorphism.ext (isInitialOfIsEmpty.hom_ext _ _)

include hcomp hdisj in
/-- All-test component injectivity and disjointness imply all-test injectivity
of the family on the actual scheme coproduct. -/
theorem coproduct_refine_injective (T : Over S) :
    Function.Injective (fun a : T ⟶ sigmaOver V => (coproduct V e).refine a) := by
  intro a b hab
  apply Over.OverMorphism.ext
  apply Scheme.Cover.hom_ext (pullbackOpenCover V a) a.left b.left
  intro i
  change K at i
  let A := pullback a (sigmaOverι V i)
  let p : A ⟶ T := pullback.fst a (sigmaOverι V i)
  let x : A ⟶ V i := pullback.snd a (sigmaOverι V i)
  change p.left ≫ a.left = p.left ≫ b.left
  apply Scheme.Cover.hom_ext (pullbackOpenCover V (p ≫ b))
    (p.left ≫ a.left) (p.left ≫ b.left)
  intro j
  change K at j
  let B := pullback (p ≫ b) (sigmaOverι V j)
  let r : B ⟶ A := pullback.fst (p ≫ b) (sigmaOverι V j)
  let y : B ⟶ V j := pullback.snd (p ≫ b) (sigmaOverι V j)
  let c : B ⟶ T := r ≫ p
  change r.left ≫ (p.left ≫ a.left) = r.left ≫ (p.left ≫ b.left)
  have hca : c ≫ a = (r ≫ x) ≫ sigmaOverι V i := by
    dsimp [c, x, p]
    rw [Category.assoc, pullback.condition, ← Category.assoc]
  have hcb : c ≫ b = y ≫ sigmaOverι V j := by
    dsimp [c, r, y]
    rw [Category.assoc, pullback.condition]
  have hF : (e i).refine (r ≫ x) = (e j).refine y := by
    have h := congrArg (fun E => E.refine c) hab
    rw [refine_comp, refine_comp, hca, hcb] at h
    have hi := refine_comp (coproduct V e) (sigmaOverι V i) (r ≫ x)
    have hj := refine_comp (coproduct V e) (sigmaOverι V j) y
    rw [coproduct_refine_ι] at hi hj
    exact hi.trans (h.trans hj.symm)
  have heq : c ≫ a = c ≫ b :=
    hca.trans ((eq_coproduct_ι_of_refine_eq V e hcomp hdisj i j (r ≫ x) y hF).trans
      hcb.symm)
  simpa only [c, Over.comp_left, Category.assoc] using
    congrArg (fun f : B ⟶ sigmaOver V => f.left) heq

/-- The canonical map from a relative test scheme to the base object. -/
def terminalBasePoint (T : Over S) : T ⟶ Over.mk (𝟙 S) :=
  Over.homMk T.hom (Category.comp_id _)

theorem terminalBasePoint_unique {T : Over S} (a : T ⟶ Over.mk (𝟙 S)) :
    a = terminalBasePoint T := by
  apply Over.OverMorphism.ext
  change a.left = T.hom
  have h := Over.w a
  change a.left ≫ 𝟙 S = T.hom at h
  exact (Category.comp_id a.left).symm.trans h

/-- The family on the actual constant scheme induced by base representatives. -/
def constantFamily {D : Type u} (r : D → LocalGroupIso G H (Over.mk (𝟙 S))) :
    LocalGroupIso G H (GroupIsomorphismScheme.constantParameter S D) :=
  coproduct (fun _ => Over.mk (𝟙 S)) r

/-- Disjoint base representatives give a unique constant-scheme label on each test. -/
theorem constantFamily_refine_injective {D : Type u}
    (r : D → LocalGroupIso G H (Over.mk (𝟙 S)))
    (hr : ∀ (i j : D) (T : Over S),
      (r i).refine (terminalBasePoint T) = (r j).refine (terminalBasePoint T) →
        i = j ∨ IsEmpty T.left) (T : Over S) :
    Function.Injective (fun a : T ⟶ GroupIsomorphismScheme.constantParameter S D =>
      (constantFamily r).refine a) := by
  apply coproduct_refine_injective (fun _ => Over.mk (𝟙 S)) r
  · intro i W a b _
    exact (terminalBasePoint_unique a).trans (terminalBasePoint_unique b).symm
  · intro i j W a b hab
    rw [terminalBasePoint_unique a, terminalBasePoint_unique b] at hab
    exact hr i j W hab

end Langlands.GroupScheme.LocalGroupIso
