import Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleIsoSubalgebraDescentProof

/-! # Simultaneous descent of two line-bundle isomorphisms -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

open Langlands.AlgebraicGeometry.Picard

/-- The spectrum map induced by an inclusion of algebra stages. -/
noncomputable def subalgebraInclusionSpecMap
    {A₀ A : Type u} [CommRing A₀] [CommRing A] [Algebra A₀ A]
    {T₁ T₂ : Subalgebra A₀ A} (hle : T₁ ≤ T₂) :
    Spec (CommRingCat.of T₂) ⟶ Spec (CommRingCat.of T₁) :=
  Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom)

/-- The inclusion of algebra stages respects the original base ring. -/
theorem subalgebraInclusionSpecMap_comp
    {A₀ A : Type u} [CommRing A₀] [CommRing A] [Algebra A₀ A]
    {T₁ T₂ : Subalgebra A₀ A} (hle : T₁ ≤ T₂) :
    subalgebraInclusionSpecMap hle ≫
        Spec.map (CommRingCat.ofHom (algebraMap A₀ T₁)) =
      Spec.map (CommRingCat.ofHom (algebraMap A₀ T₂)) := by
  dsimp only [subalgebraInclusionSpecMap]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- Two generic line-bundle comparisons descend to the same finite algebra stage,
with comparisons along every compatible pullback square. -/
theorem exists_fg_pair_lineBundle_iso
    {A₀ A : Type u} [CommRing A₀] [CommRing A] [Algebra A₀ A]
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [QuasiCompact f₀] [QuasiSeparated f₀]
    (M₁ N₁ M₂ N₂ : X₀.Modules)
    (hM₁ : IsLocallyFreeRankOne M₁) (hN₁ : IsLocallyFreeRankOne N₁)
    (hM₂ : IsLocallyFreeRankOne M₂) (hN₂ : IsLocallyFreeRankOne N₂)
    {X : Scheme.{u}} (a : X ⟶ X₀) (f : X ⟶ Spec (CommRingCat.of A))
    (hpb : IsPullback a f f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))
    (h₁ : Nonempty ((Scheme.Modules.pullback a).obj M₁ ≅
      (Scheme.Modules.pullback a).obj N₁))
    (h₂ : Nonempty ((Scheme.Modules.pullback a).obj M₂ ≅
      (Scheme.Modules.pullback a).obj N₂)) (s : Finset A) :
    ∃ T : Subalgebra A₀ A, T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∀ {X' : Scheme.{u}} (a' : X' ⟶ X₀) (f' : X' ⟶ Spec (CommRingCat.of T)),
        IsPullback a' f' f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ T))) →
        Nonempty ((Scheme.Modules.pullback a').obj M₁ ≅
          (Scheme.Modules.pullback a').obj N₁) ∧
        Nonempty ((Scheme.Modules.pullback a').obj M₂ ≅
          (Scheme.Modules.pullback a').obj N₂) := by
  classical
  obtain ⟨T₁, hT₁, _, hstage₁⟩ := lineBundleIsoSubalgebraDescent
    f₀ M₁ N₁ hM₁ hN₁ a f hpb h₁ s
  obtain ⟨s₁, hs₁⟩ := hT₁
  obtain ⟨T₂, hT₂, hs₂, hstage₂⟩ := lineBundleIsoSubalgebraDescent
    f₀ M₂ N₂ hM₂ hN₂ a f hpb h₂ (s₁ ∪ s)
  have hle : T₁ ≤ T₂ := by
    rw [← hs₁]
    exact Algebra.adjoin_le fun x hx => hs₂ (Finset.mem_union_left s hx)
  refine ⟨T₂, hT₂, fun x hx => hs₂ (Finset.mem_union_right s₁ hx), ?_⟩
  intro X' a' f' hpb'
  refine ⟨?_, hstage₂ a' f' hpb'⟩
  let ι := subalgebraInclusionSpecMap hle
  have hι : ι ≫ Spec.map (CommRingCat.ofHom (algebraMap A₀ T₁)) =
      Spec.map (CommRingCat.ofHom (algebraMap A₀ T₂)) := by
    exact subalgebraInclusionSpecMap_comp hle
  have hw : a' ≫ f₀ = (f' ≫ ι) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A₀ T₁)) := by
    rw [Category.assoc, hι]
    exact hpb'.w
  exact nonempty_iso_pullback_of_fac (pullback.lift a' (f' ≫ ι) hw)
    (pullback.lift_fst _ _ _)
    (hstage₁ (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _))

end Langlands.AlgebraicGeometry.NoetherianApproximation
