import Langlands.GroupScheme.Torus.MultiplicativeTypeTorsionDeterminationStatement
import Langlands.GroupScheme.SubgroupFunctor
import Langlands.GroupScheme.Torus.TorsionDetermination.Descent

/-! # Corollaries 4.8 and 4.9 of SGA 3 IX from the torsion-closed immersion lemma -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorsionDetermination

open RelativeMultiplicativeType

variable {S : Scheme.{u}}

/-- A point of `G` lifts through the underlying morphism of schemes of a homomorphism
`h : H ⟶ G` exactly when it lies in the range of `h`. -/
theorem lifts_iff_mem_range {G H : GroupScheme S} (h : H ⟶ G) {T : Over S} (x : T ⟶ G.X) :
    PointLifts h.hom.hom.left x ↔ x ∈ (SubgroupFunctor.range h).carrier T := by
  rw [SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨Over.homMk a ?_, ?_⟩
    · rw [← Over.w h.hom.hom, ← Category.assoc, ha, Over.w x]
    · ext1
      exact ha
  · rintro ⟨y, rfl⟩
    exact ⟨y.left, rfl⟩

/-- The range of a homomorphism lifts through its underlying morphism in a torsion-closed
way as soon as it contains every torsion point. -/
theorem isTorsionClosed_of_range {G H : GroupScheme S} (h : H ⟶ G)
    (htors : ∀ n : ℕ, 0 < n → ∀ (T : Over S) (x : T ⟶ G.X), x ^ n = 1 →
      x ∈ (SubgroupFunctor.range h).carrier T) :
    IsTorsionClosed G h.hom.hom.left where
  mul x y hx hy := by
    rw [lifts_iff_mem_range] at hx hy ⊢
    exact Subgroup.mul_mem _ hx hy
  torsion n hn T x hx := (lifts_iff_mem_range h x).2 (htors n hn T x hx)

/-- A homomorphism of group schemes whose underlying morphism of schemes is an isomorphism is
an isomorphism. -/
theorem isIso_of_isIso_left {G H : GroupScheme S} (h : H ⟶ G) [IsIso h.hom.hom.left] :
    IsIso h := by
  have : IsIso ((Over.forget _).map h.hom.hom) := ‹IsIso h.hom.hom.left›
  have : IsIso h.hom.hom := isIso_of_reflects_iso _ (Over.forget _)
  have : IsIso ((Mon.forget _).map h.hom) := ‹IsIso h.hom.hom›
  have : IsIso h.hom := isIso_of_reflects_iso _ (Mon.forget _)
  have : IsIso ((Grp.forget₂Mon _).map h) := ‹IsIso h.hom›
  exact isIso_of_reflects_iso h (Grp.forget₂Mon _)

/-- The hypothesis shared by the three parts: every torsion-closed immersion into a group of
multiplicative type is an isomorphism. -/
abbrev TorsionClosedImmersionIsIso : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S), IsMultiplicativeType G →
    ∀ (Z : Scheme.{u}) (j : Z ⟶ G.X.left), IsImmersion j → IsTorsionClosed G j → IsIso j

section Parts

variable (hM : TorsionClosedImmersionIsIso.{u})
include hM

/-- **SGA 3 IX 4.9** from the torsion-closed immersion lemma. -/
theorem part_c (G H : GroupScheme S) (h : H ⟶ G) (hG : IsMultiplicativeType G)
    (himm : IsImmersion h.hom.hom.left)
    (htors : ∀ n : ℕ, 0 < n → ∀ (T : Over S) (x : T ⟶ G.X), x ^ n = 1 →
      x ∈ (SubgroupFunctor.range h).carrier T) :
    IsIso h := by
  have : IsIso h.hom.hom.left :=
    hM S G hG _ h.hom.hom.left himm (isTorsionClosed_of_range h htors)
  exact isIso_of_isIso_left h

/-- One inclusion of **SGA 3 IX 4.8 b)**. -/
theorem part_b_le (G H₁ H₂ : GroupScheme S) (h₁ : H₁ ⟶ G) (h₂ : H₂ ⟶ G)
    (himm₂ : IsImmersion h₂.hom.hom.left) (hH₁ : IsMultiplicativeType H₁)
    (htors : ∀ n : ℕ, 0 < n → ∀ (T : Over S) (x : T ⟶ G.X), x ^ n = 1 →
      x ∈ (SubgroupFunctor.range h₁).carrier T → x ∈ (SubgroupFunctor.range h₂).carrier T) :
    SubgroupFunctor.range h₁ ≤ SubgroupFunctor.range h₂ := by
  have hj : IsTorsionClosed H₁ (pullback.snd h₂.hom.hom.left h₁.hom.hom.left) :=
    { mul := fun x y hx hy => by
        rw [lifts_pullback_iff, lifts_iff_mem_range] at hx hy ⊢
        rw [MonObj.mul_comp]
        exact Subgroup.mul_mem _ hx hy
      torsion := fun n hn T x hx => by
        rw [lifts_pullback_iff, lifts_iff_mem_range]
        refine htors n hn T _ ?_ ⟨x, rfl⟩
        rw [← MonObj.pow_comp, hx, MonObj.one_comp] }
  have : IsIso (pullback.snd h₂.hom.hom.left h₁.hom.hom.left) :=
    hM S H₁ hH₁ _ _ inferInstance hj
  rw [SubgroupFunctor.le_def]
  rintro T x ⟨y, rfl⟩
  have hy : PointLifts (pullback.snd h₂.hom.hom.left h₁.hom.hom.left) y :=
    ⟨y.left ≫ inv (pullback.snd h₂.hom.hom.left h₁.hom.hom.left), by simp⟩
  rw [lifts_pullback_iff, lifts_iff_mem_range] at hy
  exact hy

/-- **SGA 3 IX 4.8 b)** from the torsion-closed immersion lemma. -/
theorem part_b (G H₁ H₂ : GroupScheme S) (h₁ : H₁ ⟶ G) (h₂ : H₂ ⟶ G)
    (himm₁ : IsImmersion h₁.hom.hom.left) (himm₂ : IsImmersion h₂.hom.hom.left)
    (hH₁ : IsMultiplicativeType H₁) (hH₂ : IsMultiplicativeType H₂)
    (htors : ∀ n : ℕ, 0 < n → ∀ (T : Over S) (x : T ⟶ G.X), x ^ n = 1 →
      (x ∈ (SubgroupFunctor.range h₁).carrier T ↔ x ∈ (SubgroupFunctor.range h₂).carrier T)) :
    SubgroupFunctor.range h₁ = SubgroupFunctor.range h₂ :=
  le_antisymm
    (part_b_le hM G H₁ H₂ h₁ h₂ himm₂ hH₁ fun n hn T x hx => (htors n hn T x hx).1)
    (part_b_le hM G H₂ H₁ h₂ h₁ himm₁ hH₂ fun n hn T x hx => (htors n hn T x hx).2)

/-- **SGA 3 IX 4.8 a)** from the torsion-closed immersion lemma. -/
theorem part_a (H G : GroupScheme S) (hH : IsMultiplicativeType H) (u v : H ⟶ G)
    (huv : ∀ n : ℕ, 0 < n → ∀ (T : Over S) (x : T ⟶ H.X), x ^ n = 1 →
      x ≫ u.hom.hom = x ≫ v.hom.hom) :
    u = v := by
  have hlift : ∀ {T : Over S} (x : T ⟶ H.X),
      PointLifts (equalizer.ι u.hom.hom.left v.hom.hom.left) x ↔ x ≫ u.hom.hom = x ≫ v.hom.hom := by
    intro T x
    constructor
    · rintro ⟨a, ha⟩
      ext1
      rw [Over.comp_left, Over.comp_left, ← ha, Category.assoc, Category.assoc,
        equalizer.condition]
    · intro hx
      refine ⟨equalizer.lift x.left ?_, equalizer.lift_ι _ _⟩
      rw [← Over.comp_left, ← Over.comp_left, hx]
  have hj : IsTorsionClosed H (equalizer.ι u.hom.hom.left v.hom.hom.left) :=
    { mul := fun x y hx hy => by
        rw [hlift] at hx hy ⊢
        rw [MonObj.mul_comp, MonObj.mul_comp, hx, hy]
      torsion := fun n hn T x hx => (hlift x).2 (huv n hn T x hx) }
  have : IsIso (equalizer.ι u.hom.hom.left v.hom.hom.left) :=
    hM S H hH _ _ inferInstance hj
  have h1 := (hlift (𝟙 H.X)).1 (lifts_id_of_isIso _)
  rw [Category.id_comp, Category.id_comp] at h1
  exact Grp.hom_ext _ _ h1

/-- The statement of SGA 3 IX 4.8–4.9 follows from the torsion-closed immersion lemma. -/
theorem statement_of_torsionClosedImmersionIsIso :
    MultiplicativeTypeTorsionDeterminationStatement.{u} := by
  intro S
  exact ⟨fun H G hH u v huv => part_a hM H G hH u v huv,
    fun G H₁ H₂ h₁ h₂ himm₁ himm₂ hH₁ hH₂ htors =>
      part_b hM G H₁ H₂ h₁ h₂ himm₁ himm₂ hH₁ hH₂ htors,
    fun G H h hG himm htors => part_c hM G H h hG himm htors⟩

end Parts

end Langlands.GroupScheme.TorsionDetermination
