import Langlands.GroupScheme.Dynamic.FlagQuotientAction
import Langlands.GroupScheme.Reductive.RationalPointDensityStatement

/-! # Rational lifting from density and an identity-coset section -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable (k : Type u) [Field k]
variable (G : GroupScheme (Spec (CommRingCat.of k)))
variable (H : SubgroupFunctor G) {Q : Over (Spec (CommRingCat.of k))}
variable (q : G.X ⟶ Q)
variable (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
  g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ H.carrier T)
variable [QuasiCompact q.left] [Flat q.left] [Surjective q.left]

/-- The actual orbit morphism of an arbitrary rational quotient point. -/
def flagQuotientOrbitHom (p : RationalPoint k Q) : G.X ⟶ Q :=
  flagQuotientAct G H q hfib (𝟙 G.X) (toUnit G.X ≫ p)

/-- Precomposition evaluates the orbit morphism on any relative test scheme. -/
theorem comp_flagQuotientOrbitHom (p : RationalPoint k Q)
    {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ G.X) :
    g ≫ flagQuotientOrbitHom k G H q hfib p =
      flagQuotientAct G H q hfib g (toUnit T ≫ p) := by
  rw [flagQuotientOrbitHom, flagQuotientAct_naturality, Category.comp_id,
    comp_toUnit_assoc]

/-- Every rational quotient orbit meets each open neighborhood of the identity
coset on underlying scheme points, without assuming a rational lift. -/
theorem flagQuotientOrbit_preimage_nonempty (p : RationalPoint k Q)
    (U : Q.left.Opens)
    (hU : Set.range ((1 : RationalPoint k G.X) ≫ q).left ⊆ U) :
    ((flagQuotientOrbitHom k G H q hfib p).left ⁻¹' (U : Set Q.left)).Nonempty := by
  let V : Over (Spec (CommRingCat.of k)) :=
    Over.mk (pullback.fst p.left q.left)
  let g : V ⟶ G.X := Over.homMk (pullback.snd p.left q.left) (by
    rw [← Over.w q, ← Category.assoc, ← pullback.condition, Category.assoc, Over.w p]
    exact Category.comp_id _)
  have hp : toUnit V ≫ p = g ≫ q :=
    Over.OverMorphism.ext pullback.condition
  have he : g⁻¹ ≫ flagQuotientOrbitHom k G H q hfib p =
      toUnit V ≫ ((1 : RationalPoint k G.X) ≫ q) := by
    rw [comp_flagQuotientOrbitHom, hp, flagQuotientAct_lift, inv_mul_cancel,
      ← Category.assoc, MonObj.comp_one]
  let z : Spec (CommRingCat.of k) := IsLocalRing.closedPoint k
  obtain ⟨v, _⟩ := (pullback.fst p.left q.left).surjective z
  refine ⟨(g⁻¹).left v, ?_⟩
  have hev := congrArg (fun f : V ⟶ Q => f.left v) he
  change (flagQuotientOrbitHom k G H q hfib p).left ((g⁻¹).left v) ∈ U
  change (flagQuotientOrbitHom k G H q hfib p).left ((g⁻¹).left v) =
    ((1 : RationalPoint k G.X) ≫ q).left ((toUnit V).left v) at hev
  rw [hev]
  exact hU ⟨(toUnit V).left v, rfl⟩

include hfib

/-- Dense rational group points and one actual identity-coset section give a
rational lift of every point of the same quotient. -/
theorem rational_lifts_of_dense_identity_section
    (hdense : Dense (⋃ a : RationalPoint k G.X, Set.range a.left))
    (U : Q.left.Opens) (s : openOver k Q U ⟶ G.X)
    (hU : Set.range ((1 : RationalPoint k G.X) ≫ q).left ⊆ U)
    (hs : s ≫ q = openOverι k Q U) :
    ∀ p : RingPoint k Q k, ∃ g : RingPoint k G.X k, g ≫ q = p := by
  intro p
  dsimp only [RingPoint] at p
  let p₀ : RationalPoint k Q := (rationalPointEquiv k Q).symm p
  let o := flagQuotientOrbitHom k G H q hfib p₀
  obtain ⟨x, hx, hxu⟩ := hdense.exists_mem_open
    (U.isOpen.preimage o.left.continuous)
    (flagQuotientOrbit_preimage_nonempty k G H q hfib p₀ U hU)
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
  obtain ⟨z, rfl⟩ := ha
  change o.left (a.left z) ∈ U at hxu
  have hrange : Set.range (rationalPointEquiv k Q (a ≫ o)).left ⊆ U := by
    rw [rationalPointEquiv_left]
    rintro _ ⟨w, rfl⟩
    change o.left (a.left w) ∈ U
    have hw : w = z := by
      exact Subsingleton.elim (α := PrimeSpectrum k) w z
    simpa only [hw] using hxu
  let b : ringTest k k ⟶ openOver k Q U := openPointLift k Q k U (rationalPointEquiv k Q (a ≫ o)) hrange
  let h : RationalPoint k G.X := (rationalPointEquiv k G.X).symm (b ≫ s)
  have hh : h ≫ q = a ≫ o := by
    apply (rationalPointEquiv k Q).injective
    rw [rationalPointEquiv_natural]
    have hh₀ : rationalPointEquiv k G.X h = b ≫ s :=
      Equiv.apply_symm_apply _ _
    rw [hh₀, Category.assoc, hs]
    exact openPointMap_lift k Q k U _ hrange
  refine ⟨rationalPointEquiv k G.X (a⁻¹ * h), ?_⟩
  rw [← rationalPointEquiv_natural]
  have he : (a⁻¹ * h) ≫ q = p₀ := by
    rw [← flagQuotientAct_lift G H q hfib a⁻¹ h, hh]
    change flagQuotientAct G H q hfib a⁻¹
      (a ≫ flagQuotientOrbitHom k G H q hfib p₀) = p₀
    rw [comp_flagQuotientOrbitHom, flagQuotientAct_inv_cancel]
    apply Over.OverMorphism.ext
    change (𝟙 _) ≫ p₀.left = p₀.left
    exact Category.id_comp _
  rw [he]
  exact Equiv.apply_symm_apply _ _

/-- The generic density-to-lifting adapter specialized to the existing
connected reductive density proposition over an infinite field. -/
theorem rational_lifts_of_reductive_density [Infinite k]
    (hdensity : ReductiveRationalPointDensityStatement.{u})
    (hG : IsConnectedReductive G)
    (U : Q.left.Opens) (s : openOver k Q U ⟶ G.X)
    (hU : Set.range ((1 : RationalPoint k G.X) ≫ q).left ⊆ U)
    (hs : s ≫ q = openOverι k Q U) :
    ∀ p : RingPoint k Q k, ∃ g : RingPoint k G.X k, g ≫ q = p :=
  rational_lifts_of_dense_identity_section k G H q hfib (hdensity k G hG) U s hU hs

/-- Density also propagates the given section to neighborhoods of all rational
points on this same quotient model. -/
theorem localSections_of_dense_identity_section
    (hdense : Dense (⋃ a : RationalPoint k G.X, Set.range a.left))
    (U : Q.left.Opens) (s : openOver k Q U ⟶ G.X)
    (hU : Set.range ((1 : RationalPoint k G.X) ≫ q).left ⊆ U)
    (hs : s ≫ q = openOverι k Q U) :
    ∀ p : RingPoint k Q k,
      ∃ (V : Q.left.Opens) (t : openOver k Q V ⟶ G.X),
        Set.range p.left ⊆ V ∧ t ≫ q = openOverι k Q V := by
  have hq : Set.range
      (rationalPointEquiv k Q ((1 : RationalPoint k G.X) ≫ q)).left ⊆ U := by
    rw [rationalPointEquiv_left]
    exact hU
  exact localSections_of_rational_lifts k G H q hfib
    (rational_lifts_of_dense_identity_section k G H q hfib hdense U s hU hs) U s hq hs

end Langlands.GroupScheme.Dynamic
