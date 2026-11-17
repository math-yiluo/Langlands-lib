import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.AbelianScheme.KernelBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Torsion-closed immersions: transport and fppf descent -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorsionDetermination

variable {S : Scheme.{u}}

/-- A point `x : T ⟶ X` of a scheme `X` over `S` lifts through a morphism of schemes
`j : Z ⟶ X.left` if its underlying morphism of schemes factors through `j`. -/
def PointLifts {X : Over S} {Z : Scheme.{u}} (j : Z ⟶ X.left) {T : Over S} (x : T ⟶ X) : Prop :=
  ∃ a : T.left ⟶ Z, a ≫ j = x.left

theorem PointLifts.comp {X : Over S} {Z : Scheme.{u}} {j : Z ⟶ X.left} {T T' : Over S}
    (f : T' ⟶ T) {x : T ⟶ X} (h : PointLifts j x) : PointLifts j (f ≫ x) := by
  obtain ⟨a, ha⟩ := h
  exact ⟨f.left ≫ a, by rw [Category.assoc, ha, Over.comp_left]⟩

/-- A monomorphism through which the identity point lifts is an isomorphism. -/
theorem isIso_of_lifts_id {X : Over S} {Z : Scheme.{u}} (j : Z ⟶ X.left) [Mono j]
    (h : PointLifts j (𝟙 X)) : IsIso j := by
  obtain ⟨a, ha⟩ := h
  have : IsSplitEpi j := ⟨⟨a, ha⟩⟩
  exact isIso_of_mono_of_isSplitEpi j

theorem lifts_id_of_isIso {X : Over S} {Z : Scheme.{u}} (j : Z ⟶ X.left) [IsIso j] :
    PointLifts j (𝟙 X) :=
  ⟨inv j, by simp⟩

/-- The points of `G` lifting through `j` are closed under multiplication and contain every
torsion point. -/
structure IsTorsionClosed (G : GroupScheme S) {Z : Scheme.{u}} (j : Z ⟶ G.X.left) : Prop where
  mul : ∀ {T : Over S} (x y : T ⟶ G.X), PointLifts j x → PointLifts j y → PointLifts j (x * y)
  torsion : ∀ n : ℕ, 0 < n → ∀ {T : Over S} (x : T ⟶ G.X), x ^ n = 1 → PointLifts j x

theorem IsTorsionClosed.one {G : GroupScheme S} {Z : Scheme.{u}} {j : Z ⟶ G.X.left}
    (hj : IsTorsionClosed G j) (T : Over S) : PointLifts j (1 : T ⟶ G.X) :=
  hj.torsion 1 Nat.one_pos 1 (one_pow 1)

theorem IsTorsionClosed.prod {G : GroupScheme S} [IsCommMonObj G.X] {Z : Scheme.{u}}
    {j : Z ⟶ G.X.left} (hj : IsTorsionClosed G j) {T : Over S} {κ : Type*} (s : Finset κ)
    (x : κ → (T ⟶ G.X)) (hx : ∀ i ∈ s, PointLifts j (x i)) : PointLifts j (∏ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hj.one T
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact hj.mul _ _ (hx a (Finset.mem_insert_self a s))
      (ih fun i hi => hx i (Finset.mem_insert_of_mem hi))

section Pullback

variable {G G' : GroupScheme S} (φ : G' ⟶ G) {Z : Scheme.{u}} (j : Z ⟶ G.X.left)

/-- Points of `G'` lift through the pullback of `j` along `φ` exactly when their images in `G`
lift through `j`. -/
theorem lifts_pullback_iff {T : Over S} (y : T ⟶ G'.X) :
    PointLifts (pullback.snd j φ.hom.hom.left) y ↔ PointLifts j (y ≫ φ.hom.hom) := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a ≫ pullback.fst j φ.hom.hom.left, ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, ha, Over.comp_left]
  · rintro ⟨b, hb⟩
    refine ⟨pullback.lift b y.left (by rw [hb, Over.comp_left]), ?_⟩
    exact pullback.lift_snd _ _ _

theorem IsTorsionClosed.pullback (hj : IsTorsionClosed G j) :
    IsTorsionClosed G' (pullback.snd j φ.hom.hom.left) where
  mul x y hx hy := by
    rw [lifts_pullback_iff] at hx hy ⊢
    rw [MonObj.mul_comp]
    exact hj.mul _ _ hx hy
  torsion n hn T x hx := by
    rw [lifts_pullback_iff]
    refine hj.torsion n hn _ ?_
    rw [← MonObj.pow_comp, hx, MonObj.one_comp]

/-- If the identity point of `G'` lifts through the pullback of `j` along an isomorphism `φ`,
then the identity point of `G` lifts through `j`. -/
theorem lifts_id_of_pullback_iso (e : G' ≅ G)
    (h : PointLifts (pullback.snd j e.hom.hom.hom.left) (𝟙 G'.X)) : PointLifts j (𝟙 G.X) := by
  rw [lifts_pullback_iff, Category.id_comp] at h
  have h' := h.comp e.inv.hom.hom
  rwa [← Grp.comp_hom_hom, e.inv_hom_id] at h'

end Pullback

section BaseChange

variable {S' : Scheme.{u}} (b : S' ⟶ S) (G : GroupScheme S) {Z : Scheme.{u}}
  (j : Z ⟶ G.X.left)

/-- The base change of `j : Z ⟶ G.X.left` along `b : S' ⟶ S`, as a morphism into the
underlying scheme of the base-changed group. -/
abbrev baseChangeι : pullback j (pullback.fst G.X.hom b) ⟶
    ((GroupScheme.baseChange b).obj G).X.left :=
  pullback.snd j (pullback.fst G.X.hom b)

theorem lifts_baseChange_iff {T : Over S'} (y : T ⟶ ((GroupScheme.baseChange b).obj G).X) :
    PointLifts (baseChangeι b G j) y ↔ PointLifts j (baseChangePointsEquiv b G T y) := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a ≫ pullback.fst j (pullback.fst G.X.hom b), ?_⟩
    rw [baseChangePointsEquiv_left, Category.assoc, pullback.condition, ← Category.assoc, ha]
  · rintro ⟨c, hc⟩
    rw [baseChangePointsEquiv_left] at hc
    exact ⟨pullback.lift c y.left hc, pullback.lift_snd _ _ _⟩

theorem IsTorsionClosed.baseChange (hj : IsTorsionClosed G j) :
    IsTorsionClosed ((GroupScheme.baseChange b).obj G) (baseChangeι b G j) where
  mul x y hx hy := by
    rw [lifts_baseChange_iff] at hx hy ⊢
    rw [map_mul]
    exact hj.mul _ _ hx hy
  torsion n hn T x hx := by
    rw [lifts_baseChange_iff]
    refine hj.torsion n hn _ ?_
    rw [← map_pow, hx, map_one]

theorem lifts_baseChange_id_iff :
    PointLifts (baseChangeι b G j) (𝟙 ((GroupScheme.baseChange b).obj G).X) ↔
      ∃ a : pullback G.X.hom b ⟶ Z, a ≫ j = pullback.fst G.X.hom b := by
  rw [lifts_baseChange_iff]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by rw [ha, baseChangePointsEquiv_left]; exact Category.id_comp _⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by rw [ha, baseChangePointsEquiv_left]; exact (Category.id_comp _).symm⟩

end BaseChange

section Descent

/-- Every fppf cover is an effective epimorphic family. -/
theorem effectiveEpiFamily_of_fppf {X : Scheme.{u}}
    (𝒱 : X.Cover.{u} (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation))) :
    EffectiveEpiFamily 𝒱.X 𝒱.f := by
  rw [← Sieve.effectiveEpimorphic_family, Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]
  intro Y
  exact (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := Scheme.fppfTopology) (yoneda.obj Y)).isSheafFor _
    (Precoverage.generate_mem_toGrothendieck (J := Scheme.fppfPrecoverage) 𝒱.mem₀)

/-- **fppf descent of lifting the identity point.** If `j` is a monomorphism and, over every
member of an fppf cover of `S`, the base change of the identity point lifts through the base
change of `j`, then the identity point of `G` lifts through `j`. -/
theorem lifts_id_of_cover (G : GroupScheme S) {Z : Scheme.{u}} (j : Z ⟶ G.X.left) [Mono j]
    (𝒰 : S.Cover.{u} (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)))
    (h : ∀ i, PointLifts (baseChangeι (𝒰.f i) G j) (𝟙 ((GroupScheme.baseChange (𝒰.f i)).obj G).X)) :
    PointLifts j (𝟙 G.X) := by
  have h' : ∀ i, ∃ a : pullback G.X.hom (𝒰.f i) ⟶ Z, a ≫ j = pullback.fst G.X.hom (𝒰.f i) :=
    fun i => (lifts_baseChange_id_iff (𝒰.f i) G j).1 (h i)
  choose a ha using h'
  let 𝒱 := 𝒰.pullback₁ G.X.hom
  have : EffectiveEpiFamily 𝒱.X 𝒱.f := effectiveEpiFamily_of_fppf 𝒱
  have hc : ∀ {W : Scheme.{u}} (i₁ i₂ : 𝒱.I₀) (g₁ : W ⟶ 𝒱.X i₁) (g₂ : W ⟶ 𝒱.X i₂),
      g₁ ≫ 𝒱.f i₁ = g₂ ≫ 𝒱.f i₂ → g₁ ≫ a i₁ = g₂ ≫ a i₂ := by
    intro W i₁ i₂ g₁ g₂ hg
    rw [← cancel_mono j, Category.assoc, Category.assoc, ha, ha]
    exact hg
  refine ⟨EffectiveEpiFamily.desc 𝒱.X 𝒱.f a hc, ?_⟩
  apply EffectiveEpiFamily.hom_ext 𝒱.X 𝒱.f
  intro i
  rw [EffectiveEpiFamily.fac_assoc, ha]
  exact (Category.comp_id _).symm

end Descent

end Langlands.GroupScheme.TorsionDetermination
