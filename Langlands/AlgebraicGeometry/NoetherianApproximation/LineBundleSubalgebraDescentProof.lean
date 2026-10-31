import Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleDescentStatements
import Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleDescentBridge
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit

/-! # Descent of line bundles to finitely generated subalgebras

The ported FLT theorem
`AlgebraicGeometry.Scheme.Modules.exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit`
is stated for an arbitrary directed system of rings with a direct limit, and for line bundles on
the chosen base change of a scheme over a stage. Here it is applied to the finitely generated
`A₀`-subalgebras of `A`, and transported to the given pullback square over `Spec A`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

open Langlands.AlgebraicGeometry.Picard

variable {A₀ A : Type u} [CommRing A₀] [CommRing A] [Algebra A₀ A]

/-- The ported FLT descent theorem for line bundles, specialised to the system of finitely
generated `A₀`-subalgebras of `A`. -/
theorem exists_fg_isInvertible_nonempty_pullback_iso (T : FGIndex A₀ A) {Y : Scheme.{u}}
    (fY : Y ⟶ Spec (CommRingCat.of (FGStage T))) [QuasiCompact fY] [QuasiSeparated fY]
    (L : (pullback fY (Spec.map (CommRingCat.ofHom (fgToLimit T)))).Modules)
    (hL : Scheme.Modules.IsInvertible L) :
    ∃ (U : FGIndex A₀ A) (hTU : T ≤ U)
      (LU : (pullback fY (Spec.map (CommRingCat.ofHom (fgTransition T U hTU)))).Modules),
      Scheme.Modules.IsInvertible LU ∧
      ∀ cX : pullback fY (Spec.map (CommRingCat.ofHom (fgToLimit T))) ⟶
          pullback fY (Spec.map (CommRingCat.ofHom (fgTransition T U hTU))),
        cX ≫ pullback.fst fY (Spec.map (CommRingCat.ofHom (fgTransition T U hTU))) =
          pullback.fst fY (Spec.map (CommRingCat.ofHom (fgToLimit T))) →
        cX ≫ pullback.snd fY (Spec.map (CommRingCat.ofHom (fgTransition T U hTU))) =
          pullback.snd fY (Spec.map (CommRingCat.ofHom (fgToLimit T))) ≫
            Spec.map (CommRingCat.ofHom (fgToLimit U)) →
        Nonempty ((Scheme.Modules.pullback cX).obj LU ≅ L) :=
  Scheme.Modules.exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit
    (ι := FGIndex A₀ A) (G := FGStage) (R := A) (φ := fgTransition) (g := fgToLimit)
    fgIsDirectLimit T fY L hL

/-- Proof of `LineBundleSubalgebraDescentStatement`. -/
theorem lineBundleSubalgebraDescent : LineBundleSubalgebraDescentStatement.{u} := by
  intro A₀ _ A _ _ X₀ f₀ _ _ X a f hpb M hM s
  let i : FGIndex A₀ A := ⟨Algebra.adjoin A₀ (↑s : Set A), Subalgebra.fg_adjoin_finset s⟩
  let ι₀ := Spec.map (CommRingCat.ofHom (algebraMap A₀ (FGStage i)))
  -- `e : P ⟶ X` from the base change `P` of `X₀ ×_{A₀} Spec i` to `Spec A`, and a section `e'`.
  have hw : (pullback.fst (pullback.snd f₀ ι₀) (Spec.map (CommRingCat.ofHom (fgToLimit i))) ≫
      pullback.fst f₀ ι₀) ≫ f₀ =
      pullback.snd (pullback.snd f₀ ι₀) (Spec.map (CommRingCat.ofHom (fgToLimit i))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A₀ A)) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
      Category.assoc, spec_map_fgToLimit_comp]
  obtain ⟨e, he₁, he₂⟩ : ∃ e : pullback (pullback.snd f₀ ι₀)
      (Spec.map (CommRingCat.ofHom (fgToLimit i))) ⟶ X,
      e ≫ a = pullback.fst (pullback.snd f₀ ι₀) (Spec.map (CommRingCat.ofHom (fgToLimit i))) ≫
        pullback.fst f₀ ι₀ ∧
      e ≫ f = pullback.snd (pullback.snd f₀ ι₀) (Spec.map (CommRingCat.ofHom (fgToLimit i))) :=
    ⟨hpb.lift _ _ hw, hpb.lift_fst _ _ _, hpb.lift_snd _ _ _⟩
  have hw' : a ≫ f₀ = (f ≫ Spec.map (CommRingCat.ofHom (fgToLimit i))) ≫ ι₀ := by
    rw [hpb.w, Category.assoc, spec_map_fgToLimit_comp]
  obtain ⟨e', he'₁, he'₂⟩ : ∃ e' : X ⟶ pullback (pullback.snd f₀ ι₀)
      (Spec.map (CommRingCat.ofHom (fgToLimit i))),
      e' ≫ pullback.fst (pullback.snd f₀ ι₀) (Spec.map (CommRingCat.ofHom (fgToLimit i))) =
        pullback.lift a (f ≫ Spec.map (CommRingCat.ofHom (fgToLimit i))) hw' ∧
      e' ≫ pullback.snd (pullback.snd f₀ ι₀) (Spec.map (CommRingCat.ofHom (fgToLimit i))) = f :=
    ⟨pullback.lift _ f (pullback.lift_snd _ _ _), pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
  have he : e' ≫ e = 𝟙 X := by
    apply hpb.hom_ext
    · rw [Category.assoc, he₁, ← Category.assoc, he'₁, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, he₂, he'₂, Category.id_comp]
  -- Descend the pullback of `M` along `e` to a stage `j`.
  obtain ⟨j, hij, Lj, hLj, hj⟩ := exists_fg_isInvertible_nonempty_pullback_iso i
    (pullback.snd f₀ ι₀) ((Scheme.Modules.pullback e).obj M)
    ((isInvertible_of_isLocallyFreeRankOne hM).pullback e)
  -- `u` from the chosen base change of `X₀` to `Spec j` to the base change of `X₀ ×_{A₀} Spec i`.
  have hu : pullback.fst f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ (FGStage j)))) ≫ f₀ =
      (pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ (FGStage j)))) ≫
        Spec.map (CommRingCat.ofHom (fgTransition i j hij))) ≫ ι₀ := by
    rw [pullback.condition, Category.assoc, spec_map_fgTransition_comp]
  obtain ⟨u, hu₁, hu₂⟩ : ∃ u : pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ (FGStage j)))) ⟶
      pullback (pullback.snd f₀ ι₀) (Spec.map (CommRingCat.ofHom (fgTransition i j hij))),
      u ≫ pullback.fst (pullback.snd f₀ ι₀) (Spec.map (CommRingCat.ofHom (fgTransition i j hij))) =
        pullback.lift _ _ hu ∧
      u ≫ pullback.snd (pullback.snd f₀ ι₀) (Spec.map (CommRingCat.ofHom (fgTransition i j hij))) =
        pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ (FGStage j)))) :=
    ⟨pullback.lift _ _ (pullback.lift_snd _ _ _), pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
  refine ⟨j.1, j.2, fun x hx => hij (Algebra.subset_adjoin hx),
    (Scheme.Modules.pullback u).obj Lj, isLocallyFreeRankOne_of_isInvertible (hLj.pullback u), ?_⟩
  intro c hc₁ hc₂
  have h₁ : (e ≫ c ≫ u) ≫
      pullback.fst (pullback.snd f₀ ι₀) (Spec.map (CommRingCat.ofHom (fgTransition i j hij))) =
      pullback.fst (pullback.snd f₀ ι₀) (Spec.map (CommRingCat.ofHom (fgToLimit i))) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, reassoc_of% hu₁, pullback.lift_fst]
      rw [hc₁, he₁]
    · simp only [Category.assoc, reassoc_of% hu₁, pullback.lift_snd]
      rw [← Category.assoc c, hc₂]
      simp only [Category.assoc]
      rw [← Category.assoc e, he₂, algebraMap_fgStage j, spec_map_fgToLimit_fgTransition]
      exact pullback.condition.symm
  have h₂ : (e ≫ c ≫ u) ≫
      pullback.snd (pullback.snd f₀ ι₀) (Spec.map (CommRingCat.ofHom (fgTransition i j hij))) =
      pullback.snd (pullback.snd f₀ ι₀) (Spec.map (CommRingCat.ofHom (fgToLimit i))) ≫
        Spec.map (CommRingCat.ofHom (fgToLimit j)) := by
    simp only [Category.assoc, hu₂]
    rw [hc₂, ← Category.assoc, he₂, algebraMap_fgStage j]
  obtain ⟨φ⟩ := nonempty_iso_pullback_of_section he (c ≫ u) (hj (e ≫ c ≫ u) h₁ h₂)
  exact ⟨(Scheme.Modules.pullbackComp c u).app Lj ≪≫ φ⟩

end Langlands.AlgebraicGeometry.NoetherianApproximation
