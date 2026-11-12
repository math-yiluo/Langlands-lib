import Langlands.AlgebraicGeometry.LangWeil.SpaceFamily.Counting
import Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasComponentIncidence
import Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasPointTopology
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceValuativeExistenceProof
import Langlands.AlgebraicGeometry.SmoothDomainStalksProof
import Langlands.AlgebraicGeometry.ConnectedLocallyNoetherianDomainStalksIntegralProof

/-!
# Charts of the fibres of a presheaf over a scheme

For a presheaf `X` over the terminal base with a morphism `g : X → h_M` to a scheme `M`, the
fibre of `g` over a morphism `s : T → M` is the presheaf pullback `X ×_{h_M} h_T`. A scheme
chart `b : h_V → X` lying over `q : V → M` induces the chart `h_{V ×_M T} → X ×_{h_M} h_T`, the
base change of `b`; it is étale (surjective) when `b` is. When `X` has a smooth chart over `M`
and the fibre over the spectrum of a field has connected points, these points form an
irreducible space: the smooth chart has irreducible open neighbourhoods of all its points.
Two nonempty open sets of étale charts of such a fibre then contain points with a common
image, and hence points with values in one algebraically closed field with the same image.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.LangWeil.SpaceFamily

open Langlands.AlgebraicGeometry.AlgebraicSpace

set_option backward.isDefEq.respectTransparency false

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

/-- A connected topological space in which every point has an irreducible open
neighbourhood is irreducible: the irreducible component of a point is open. -/
theorem irreducibleSpace_of_connectedSpace {T : Type*} [TopologicalSpace T] [ConnectedSpace T]
    (h : ∀ x : T, ∃ O : Set T, IsOpen O ∧ x ∈ O ∧ IsPreirreducible O) :
    IrreducibleSpace T := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty T)
  have hZopen : IsOpen (irreducibleComponent x₀) := by
    rw [isOpen_iff_forall_mem_open]
    intro y hy
    obtain ⟨O, hO, hyO, hOirr⟩ := h y
    have hcl : IsIrreducible (closure O) := (IsIrreducible.closure ⟨⟨y, hyO⟩, hOirr⟩)
    have hZO : irreducibleComponent x₀ ⊆ closure O :=
      (subset_closure_inter_of_isPreirreducible_of_isOpen
        isIrreducible_irreducibleComponent.isPreirreducible hO ⟨y, hy, hyO⟩).trans
        (closure_mono Set.inter_subset_right)
    have heq := eq_irreducibleComponent hcl.isPreirreducible hZO
    exact ⟨O, heq ▸ subset_closure, hO, hyO⟩
  have hclopen : IsClopen (irreducibleComponent x₀) :=
    ⟨isClosed_irreducibleComponent, hZopen⟩
  have huniv := hclopen.eq_univ ⟨x₀, mem_irreducibleComponent⟩
  refine (irreducibleSpace_def T).mpr ?_
  rw [Set.top_eq_univ, ← huniv]
  exact isIrreducible_irreducibleComponent

/-- A morphism from a scheme over the terminal base to a scheme, as a morphism over the
base. -/
def overHom {V : Over S0.{u}} {T : Scheme.{u}} (q : V.left ⟶ T) : V ⟶ toOver T :=
  Over.homMk q (specULiftZIsTerminal.hom_ext _ _)

@[simp]
theorem overHom_left {V : Over S0.{u}} {T : Scheme.{u}} (q : V.left ⟶ T) :
    (overHom q).left = q := rfl

/-- Two points of étale charts of a presheaf with the same image in its points come from
points with values in one algebraically closed field with equal images in the presheaf. -/
theorem exists_common_point {F : Presheaf S0.{u}} {V₁ V₂ : Over S0.{u}}
    (b₁ : (schemeYoneda S0).obj V₁ ⟶ F) (b₂ : (schemeYoneda S0).obj V₂ ⟶ F)
    {x₁ : V₁.left} {x₂ : V₂.left} (h : chartPointMap b₁ x₁ = chartPointMap b₂ x₂) :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω)
      (ξ₁ : Spec (CommRingCat.of Ω) ⟶ V₁.left) (ξ₂ : Spec (CommRingCat.of Ω) ⟶ V₂.left),
      ξ₁ (IsLocalRing.closedPoint Ω) = x₁ ∧ ξ₂ (IsLocalRing.closedPoint Ω) = x₂ ∧
        (schemeYoneda S0).map (homOver ξ₁) ≫ b₁ = (schemeYoneda S0).map (homOver ξ₂) ≫ b₂ := by
  obtain ⟨T, g₁, g₂, t, hg, h₁, h₂⟩ := (chartPointMap_eq_iff_sameImage₂ b₁ b₂ x₁ x₂).mp h
  let Ω := AlgebraicClosure (T.left.residueField t)
  let ξ : Spec (CommRingCat.of Ω) ⟶ T.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField t) Ω)) ≫
      T.left.fromSpecResidueField t
  have hξ : ξ (IsLocalRing.closedPoint Ω) = t := T.left.fromSpecResidueField_apply t _
  refine ⟨Ω, inferInstance, inferInstance, ξ ≫ g₁.left, ξ ≫ g₂.left, ?_, ?_, ?_⟩
  · change g₁.left (ξ (IsLocalRing.closedPoint Ω)) = x₁
    rw [hξ, h₁]
  · change g₂.left (ξ (IsLocalRing.closedPoint Ω)) = x₂
    rw [hξ, h₂]
  · rw [homOver_comp_left, homOver_comp_left, Functor.map_comp_assoc, Functor.map_comp_assoc, hg]

variable {X : Presheaf S0.{u}} {M : Scheme.{u}} (g : X ⟶ (schemeYoneda S0).obj (toOver M))

/-- The fibre of `g` over a morphism `s : T → M`, the presheaf pullback `X ×_{h_M} h_T`. -/
abbrev fib {T : Scheme.{u}} (s : T ⟶ M) : Presheaf S0.{u} :=
  pullback g ((schemeYoneda S0).map (toOverHom s))

variable {V : Over S0.{u}} (b : (schemeYoneda S0).obj V ⟶ X) (q : V.left ⟶ M)
  (hb : b ≫ g = (schemeYoneda S0).map (overHom q))

/-- The chart `h_{V ×_M T} → X ×_{h_M} h_T` of the fibre induced by a chart `b : h_V → X`
lying over `q : V → M`. -/
def fibChart {T : Scheme.{u}} (s : T ⟶ M) :
    (schemeYoneda S0).obj (toOver (pullback q s)) ⟶ fib g s :=
  pullback.lift ((schemeYoneda S0).map (homOver (pullback.fst q s)) ≫ b)
    ((schemeYoneda S0).map (toOverHom (pullback.snd q s))) (by
      rw [Category.assoc, hb, ← Functor.map_comp, ← Functor.map_comp]
      congr 1
      ext
      exact pullback.condition)

@[reassoc (attr := simp)]
theorem fibChart_fst {T : Scheme.{u}} (s : T ⟶ M) :
    fibChart g b q hb s ≫ pullback.fst _ _ =
      (schemeYoneda S0).map (homOver (pullback.fst q s)) ≫ b :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fibChart_snd {T : Scheme.{u}} (s : T ⟶ M) :
    fibChart g b q hb s ≫ pullback.snd _ _ =
      (schemeYoneda S0).map (toOverHom (pullback.snd q s)) :=
  pullback.lift_snd _ _ _

/-- The fibre chart is the base change of the chart along the fibre. -/
theorem fibChart_isPullback {T : Scheme.{u}} (s : T ⟶ M) :
    IsPullback ((schemeYoneda S0).map (homOver (pullback.fst q s))) (fibChart g b q hb s) b
      (pullback.fst g ((schemeYoneda S0).map (toOverHom s))) := by
  have hO : IsPullback (homOver (Y := V) (pullback.fst q s)) (toOverHom (pullback.snd q s))
      (overHom q) (toOverHom s) := by
    apply IsPullback.of_map_of_faithful (Over.forget S0)
    exact IsPullback.of_hasPullback q s
  refine IsPullback.of_bot ?_ (fibChart_fst g b q hb s).symm (IsPullback.of_hasPullback _ _)
  rw [fibChart_snd, hb]
  exact hO.map (schemeYoneda S0)

theorem fibChart_isEtale (hbe : IsEtale b) {T : Scheme.{u}} (s : T ⟶ M) :
    IsEtale (fibChart g b q hb s) :=
  MorphismProperty.of_isPullback (P := (MorphismProperty.inverseImage (@Etale.{u})
    (Over.forget S0)).relative (schemeYoneda S0)) (fibChart_isPullback g b q hb s) hbe

theorem fibChart_isSurjective (hbs : IsSurjective b) {T : Scheme.{u}} (s : T ⟶ M) :
    IsSurjective (fibChart g b q hb s) :=
  MorphismProperty.of_isPullback (P := (MorphismProperty.inverseImage (@Surjective.{u})
    (Over.forget S0)).relative (schemeYoneda S0)) (fibChart_isPullback g b q hb s) hbs

/-- The image in `X` of a field-valued point of a fibre chart. -/
theorem homOver_fibChart_fst {T T' : Scheme.{u}} (s : T ⟶ M) (ξ : T' ⟶ pullback q s) :
    (schemeYoneda S0).map (homOver ξ) ≫ fibChart g b q hb s ≫ pullback.fst _ _ =
      (schemeYoneda S0).map (homOver (ξ ≫ pullback.fst q s)) ≫ b := by
  rw [fibChart_fst, ← Functor.map_comp_assoc]
  rfl

/-- The image in `T` of a field-valued point of a fibre chart. -/
theorem homOver_fibChart_snd {T T' : Scheme.{u}} (s : T ⟶ M) (ξ : T' ⟶ pullback q s) :
    (schemeYoneda S0).map (homOver ξ) ≫ fibChart g b q hb s ≫ pullback.snd _ _ =
      (schemeYoneda S0).map (toOverHom (ξ ≫ pullback.snd q s)) := by
  rw [fibChart_snd, ← Functor.map_comp]
  rfl

/-- The points of the fibre of `g` over the spectrum of a field form an irreducible space when
they form a connected space and `X` has a surjective étale chart smooth over `M`. -/
theorem irreducibleSpace_points_fib {K : Type u} [Field K] (s : Spec (CommRingCat.of K) ⟶ M)
    {U : Over S0.{u}} (a : (schemeYoneda S0).obj U ⟶ X) (π : U.left ⟶ M)
    (ha : a ≫ g = (schemeYoneda S0).map (overHom π)) (hae : IsEtale a)
    (has : IsSurjective a) [Smooth π]
    (hconn : @ConnectedSpace (Points (fib g s)) (pointTopology _)) :
    @IrreducibleSpace (Points (fib g s)) (pointTopology _) := by
  let _ := pointTopology (fib g s)
  apply irreducibleSpace_of_connectedSpace
  intro p
  have he := fibChart_isEtale g a π ha hae s
  obtain ⟨x, rfl⟩ := surjective_chartPointMap _ (fibChart_isSurjective g a π ha has s) p
  have : Smooth (pullback.snd π s) := MorphismProperty.pullback_snd π s inferInstance
  have hdom := smoothDomainStalks K (pullback π s) (pullback.snd π s) this x
  obtain ⟨O, hxO, hO⟩ := exists_irreducible_open (pullback π s) x inferInstance hdom
  refine ⟨chartPointMap (fibChart g a π ha s) '' SetLike.coe O,
    isOpen_image_chartPointMap _ he O.isOpen, ⟨x, hxO, rfl⟩, ?_⟩
  exact (hO.image _ (continuous_schemePoint_chart _ he).continuousOn).isPreirreducible

/-- In a fibre whose points form an irreducible space, two nonempty open sets of étale
charts contain points with values in one algebraically closed field with the same image. -/
theorem exists_common_point_of_isOpen {T : Scheme.{u}} (s : T ⟶ M)
    (hirr : @IrreducibleSpace (Points (fib g s)) (pointTopology _))
    {V₁ V₂ : Over S0.{u}} (b₁ : (schemeYoneda S0).obj V₁ ⟶ fib g s)
    (b₂ : (schemeYoneda S0).obj V₂ ⟶ fib g s) (hb₁ : IsEtale b₁) (hb₂ : IsEtale b₂)
    {W₁ : Set V₁.left} {W₂ : Set V₂.left} (hW₁ : IsOpen W₁) (hW₂ : IsOpen W₂)
    (hne₁ : W₁.Nonempty) (hne₂ : W₂.Nonempty) :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω)
      (ξ₁ : Spec (CommRingCat.of Ω) ⟶ V₁.left) (ξ₂ : Spec (CommRingCat.of Ω) ⟶ V₂.left),
      ξ₁ (IsLocalRing.closedPoint Ω) ∈ W₁ ∧ ξ₂ (IsLocalRing.closedPoint Ω) ∈ W₂ ∧
        (schemeYoneda S0).map (homOver ξ₁) ≫ b₁ = (schemeYoneda S0).map (homOver ξ₂) ≫ b₂ := by
  let _ := pointTopology (fib g s)
  obtain ⟨p, -, ⟨x₁, hx₁, rfl⟩, ⟨x₂, hx₂, hx⟩⟩ :=
    (IrreducibleSpace.isIrreducible_univ (Points (fib g s))).isPreirreducible _ _
      (isOpen_image_chartPointMap b₁ hb₁ hW₁) (isOpen_image_chartPointMap b₂ hb₂ hW₂)
      (by obtain ⟨x, hx⟩ := hne₁; exact ⟨_, trivial, x, hx, rfl⟩)
      (by obtain ⟨x, hx⟩ := hne₂; exact ⟨_, trivial, x, hx, rfl⟩)
  obtain ⟨Ω, _, _, ξ₁, ξ₂, h₁, h₂, h⟩ := exists_common_point b₁ b₂ hx.symm
  exact ⟨Ω, inferInstance, inferInstance, ξ₁, ξ₂, h₁ ▸ hx₁, h₂ ▸ hx₂, h⟩

end Langlands.AlgebraicGeometry.LangWeil.SpaceFamily
