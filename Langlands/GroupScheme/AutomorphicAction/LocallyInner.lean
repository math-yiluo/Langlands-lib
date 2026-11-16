import Langlands.GroupScheme.AutomorphicAction.FppfCenterQuotient
import Langlands.GroupScheme.AutomorphicActionPointIso
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Global adjoint sections for fppf-locally inner automorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.AutomorphicAction

variable {S : Scheme.{u}} {A G : GroupScheme S} (a : AutomorphicAction A G)

/-- A relative acting point realizes the given automorphism on every refinement. -/
def RepresentsIso (σ : G ≅ G) {T : Over S} (x : T ⟶ A.X) : Prop :=
  ∀ {W : Over S} (t : W ⟶ T) (g : W ⟶ G.X),
    a.act (t ≫ x) g = g ≫ σ.hom.hom.hom

/-- A representing point remains a representative after any refinement. -/
theorem RepresentsIso.comp {σ : G ≅ G} {T V : Over S} {x : T ⟶ A.X}
    (hx : a.RepresentsIso σ x) (p : V ⟶ T) : a.RepresentsIso σ (p ≫ x) := by
  intro W t g
  simpa only [← Category.assoc] using hx (t ≫ p) g

/-- Faithfulness makes representatives unique on every test scheme. -/
theorem RepresentsIso.unique (ha : a.IsFaithful) {σ : G ≅ G}
    {T : Over S} {x y : T ⟶ A.X}
    (hx : a.RepresentsIso σ x) (hy : a.RepresentsIso σ y) : x = y := by
  apply ha x y
  intro W t g
  exact (hx t g).trans (hy t g).symm

/-- For a section, the all-refinement equation is equality of actual automorphisms. -/
theorem representsIso_iff_basePointIso (σ : G ≅ G)
    (x : Over.mk (𝟙 S) ⟶ A.X) :
    a.RepresentsIso σ x ↔ a.basePointIso x = σ := by
  constructor
  · intro hx
    apply Iso.ext
    apply hom_ext_points
    intro W g
    rw [comp_basePointIso_hom]
    exact hx (Over.homMk W.hom (by simp)) g
  · intro hx W t g
    have ht : t = Over.homMk W.hom (by simp) := by
      apply Over.OverMorphism.ext
      simpa using t.w
    rw [ht]
    change a.act (A.constantPoint x W) g = _
    rw [← comp_basePointIso_hom, hx]

/-- Equality of section automorphisms detects sections of a faithful action. -/
theorem basePointIso_injective_of_isFaithful (ha : a.IsFaithful) :
    Function.Injective a.basePointIso := by
  intro x y hxy
  exact RepresentsIso.unique a ha
    ((a.representsIso_iff_basePointIso (a.basePointIso y) x).mpr hxy)
    ((a.representsIso_iff_basePointIso (a.basePointIso y) y).mpr rfl)

/-- The representing equation can be checked after an fppf cover. -/
theorem representsIso_of_fppf_cover {σ : G ≅ G} {T V : Over S}
    (p : V ⟶ T) [Flat p.left] [Surjective p.left]
    [LocallyOfFinitePresentation p.left] {x : T ⟶ A.X}
    (hx : a.RepresentsIso σ (p ≫ x)) : a.RepresentsIso σ x := by
  intro W t g
  let Z : Over S := Over.mk (CategoryTheory.Limits.pullback.fst t.left p.left ≫ W.hom)
  let r : Z ⟶ W := Over.homMk (CategoryTheory.Limits.pullback.fst t.left p.left) rfl
  let s : Z ⟶ V := Over.homMk (CategoryTheory.Limits.pullback.snd t.left p.left) (by
    rw [← Over.w p, ← Category.assoc, ← CategoryTheory.Limits.pullback.condition,
      Category.assoc, Over.w t]
    rfl)
  have hrs : r ≫ t = s ≫ p :=
    Over.OverMorphism.ext CategoryTheory.Limits.pullback.condition
  have : Epi r.left := by
    change Epi (CategoryTheory.Limits.pullback.fst t.left p.left)
    infer_instance
  have : Epi r := Over.epi_of_epi_left r
  apply (cancel_epi r).mp
  rw [a.naturality]
  simpa only [← Category.assoc, hrs] using hx s (r ≫ g)

/-- A representative for a faithful action agrees on every relation of its cover. -/
theorem RepresentsIso.relation (ha : a.IsFaithful) {σ : G ≅ G}
    {T V : Over S} (p : V ⟶ T) {x : V ⟶ A.X}
    (hx : a.RepresentsIso σ x) {W : Over S} (r s : W ⟶ V)
    (_hrs : r ≫ p = s ≫ p) : r ≫ x = s ≫ x :=
  RepresentsIso.unique a ha (hx.comp a r) (hx.comp a s)

/-- Compatible local representatives descend as actual morphisms, over any base. -/
def descendedIsoRepresentative (ha : a.IsFaithful) {σ : G ≅ G}
    {T V : Over S} (p : V ⟶ T) [Flat p.left] [Surjective p.left]
    [LocallyOfFinitePresentation p.left] (x : V ⟶ A.X)
    (hx : a.RepresentsIso σ x) : T ⟶ A.X := by
  let hrel : ∀ {Z : Scheme.{u}} (r s : Z ⟶ V.left),
      r ≫ p.left = s ≫ p.left → r ≫ x.left = s ≫ x.left :=
    fun {Z} r s hrs => by
      have hs : s ≫ V.hom = r ≫ V.hom := by
        rw [← Over.w p, ← Category.assoc, ← Category.assoc, hrs]
      let r₀ : Over.mk (r ≫ V.hom) ⟶ V := Over.homMk r rfl
      let s₀ : Over.mk (r ≫ V.hom) ⟶ V := Over.homMk s hs
      exact congrArg (fun f => f.left)
        (hx.relation a ha p r₀ s₀ (Over.OverMorphism.ext hrs))
  let y : T.left ⟶ A.X.left := EffectiveEpi.desc p.left x.left hrel
  have hy : p.left ≫ y = x.left := EffectiveEpi.fac p.left x.left hrel
  exact Over.homMk y (by
    apply (cancel_epi p.left).mp
    rw [← Category.assoc, hy, Over.w x, Over.w p])

/-- The descended point pulls back to the given representative. -/
theorem descendedIsoRepresentative_fac (ha : a.IsFaithful) {σ : G ≅ G}
    {T V : Over S} (p : V ⟶ T) [Flat p.left] [Surjective p.left]
    [LocallyOfFinitePresentation p.left] (x : V ⟶ A.X)
    (hx : a.RepresentsIso σ x) :
    p ≫ a.descendedIsoRepresentative ha p x hx = x := by
  apply Over.OverMorphism.ext
  change p.left ≫ EffectiveEpi.desc p.left x.left _ = x.left
  exact EffectiveEpi.fac p.left x.left _

/-- The descended point realizes the original automorphism on every refinement. -/
theorem descendedIsoRepresentative_spec (ha : a.IsFaithful) {σ : G ≅ G}
    {T V : Over S} (p : V ⟶ T) [Flat p.left] [Surjective p.left]
    [LocallyOfFinitePresentation p.left] (x : V ⟶ A.X)
    (hx : a.RepresentsIso σ x) :
    a.RepresentsIso σ (a.descendedIsoRepresentative ha p x hx) := by
  apply a.representsIso_of_fppf_cover p
  rwa [a.descendedIsoRepresentative_fac ha p x hx]

/-- A local representative gives a unique global section of a faithful action. -/
theorem existsUnique_basePointIso_eq_of_fppf_cover (ha : a.IsFaithful)
    (σ : G ≅ G) {V : Over S} (p : V ⟶ Over.mk (𝟙 S))
    [Flat p.left] [Surjective p.left] [LocallyOfFinitePresentation p.left]
    (x : V ⟶ A.X) (hx : a.RepresentsIso σ x) :
    ∃! y : Over.mk (𝟙 S) ⟶ A.X, a.basePointIso y = σ := by
  refine ⟨a.descendedIsoRepresentative ha p x hx, ?_, ?_⟩
  · exact (a.representsIso_iff_basePointIso σ _).mp
      (a.descendedIsoRepresentative_spec ha p x hx)
  · intro y hy
    apply a.basePointIso_injective_of_isFaithful ha
    exact hy.trans ((a.representsIso_iff_basePointIso σ _).mp
      (a.descendedIsoRepresentative_spec ha p x hx)).symm

end Langlands.GroupScheme.AutomorphicAction

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G A : GroupScheme S}

/-- An actual automorphism is fppf-locally conjugation by a point of the original
 group. The cover and equation allow arbitrary schemes and every refinement. -/
def IsFppfLocallyInner (σ : G ≅ G) : Prop :=
  ∃ V : Over S, Flat V.hom ∧ Surjective V.hom ∧
    LocallyOfFinitePresentation V.hom ∧ ∃ y : V ⟶ G.X,
      (AutomorphicAction.conjugation (𝟙 G)).RepresentsIso σ y

/-- A locally inner automorphism has a unique section in every supplied quotient
 by the full centre, acting through every supplied descended conjugation action. -/
theorem IsFppfLocallyInner.existsUnique_adjointPoint {σ : G ≅ G}
    (hσ : IsFppfLocallyInner σ) (q : G ⟶ A)
    (hq : RelativeRoot.IsFppfQuotient (center G) q)
    (a : AutomorphicAction A G)
    (ha : a.restrict q = AutomorphicAction.conjugation (𝟙 G)) :
    ∃! x : Over.mk (𝟙 S) ⟶ A.X, a.basePointIso x = σ := by
  obtain ⟨V, hf, hs, hl, y, hy⟩ := hσ
  let p : V ⟶ Over.mk (𝟙 S) := Over.homMk V.hom (by simp)
  let : Flat p.left := hf
  let : Surjective p.left := hs
  let : LocallyOfFinitePresentation p.left := hl
  apply a.existsUnique_basePointIso_eq_of_fppf_cover
    (a.isFaithful_of_isFppfQuotient_center hq ha) σ p (y ≫ q.hom.hom)
  intro W t g
  rw [← Category.assoc, a.act_lift_of_restrict_eq_conjugation ha]
  simpa only [AutomorphicAction.conjugation_act, Grp.id_hom_hom,
    Category.comp_id] using hy t g

/-- An adjoint section acts by conjugation after the canonical fppf local lift. -/
theorem IsFppfLocallyInner.of_adjointPoint {σ : G ≅ G} (q : G ⟶ A)
    (hq : RelativeRoot.IsFppfQuotient (center G) q)
    (a : AutomorphicAction A G)
    (ha : a.restrict q = AutomorphicAction.conjugation (𝟙 G))
    (x : Over.mk (𝟙 S) ⟶ A.X) (hx : a.basePointIso x = σ) :
    IsFppfLocallyInner σ := by
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  let : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  let L := AutomorphicAction.fppfQuotientPointLift q x
  have hp : L.cover.hom = L.projection.left := by
    have hw := L.projection.w.symm
    change L.cover.hom = L.projection.left ≫ 𝟙 S at hw
    exact hw.trans (Category.comp_id L.projection.left)
  refine ⟨L.cover, ?_, ?_, ?_, L.lift, ?_⟩
  · rw [hp]
    exact L.flat
  · rw [hp]
    exact L.surjective
  · rw [hp]
    exact L.locallyOfFinitePresentation
  · intro W t g
    have he := ((a.representsIso_iff_basePointIso σ x).mpr hx) (t ≫ L.projection) g
    rw [Category.assoc, L.commutes, ← Category.assoc,
      a.act_lift_of_restrict_eq_conjugation ha] at he
    simpa only [AutomorphicAction.conjugation_act, Grp.id_hom_hom,
      Category.comp_id] using he

/-- For any full-centre quotient and compatible action, local innerness is
equivalent to representation by a unique global adjoint section. -/
theorem isFppfLocallyInner_iff_existsUnique_adjointPoint (σ : G ≅ G) (q : G ⟶ A)
    (hq : RelativeRoot.IsFppfQuotient (center G) q)
    (a : AutomorphicAction A G)
    (ha : a.restrict q = AutomorphicAction.conjugation (𝟙 G)) :
    IsFppfLocallyInner σ ↔
      ∃! x : Over.mk (𝟙 S) ⟶ A.X, a.basePointIso x = σ := by
  constructor
  · exact fun hσ => hσ.existsUnique_adjointPoint q hq a ha
  · rintro ⟨x, hx, _⟩
    exact IsFppfLocallyInner.of_adjointPoint q hq a ha x hx

end Langlands.GroupScheme
