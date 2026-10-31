import Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleDescentStatements
import Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleDescentBridge
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit

/-! # Descent of isomorphisms of line bundles to finitely generated subalgebras

The ported FLT theorem
`AlgebraicGeometry.Scheme.Modules.exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit`
is stated for an arbitrary directed system of rings with a direct limit. Here it is applied to the
finitely generated `A₀`-subalgebras of `A`, which form such a system with limit `A`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

open Langlands.AlgebraicGeometry.Picard

variable {A₀ A : Type u} [CommRing A₀] [CommRing A] [Algebra A₀ A]

/-- The ported FLT descent theorem, specialised to the system of finitely generated
`A₀`-subalgebras of `A`. -/
theorem exists_fg_nonempty_iso_pullback (T : FGIndex A₀ A) {Y : Scheme.{u}}
    (fY : Y ⟶ Spec (CommRingCat.of (FGStage T))) [QuasiCompact fY] [QuasiSeparated fY]
    (M N : Y.Modules) (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N)
    (h : Nonempty
      ((Scheme.Modules.pullback (pullback.fst fY (Spec.map (CommRingCat.ofHom (fgToLimit T))))).obj M ≅
       (Scheme.Modules.pullback (pullback.fst fY
          (Spec.map (CommRingCat.ofHom (fgToLimit T))))).obj N)) :
    ∃ (U : FGIndex A₀ A) (hTU : T ≤ U), Nonempty
      ((Scheme.Modules.pullback (pullback.fst fY
          (Spec.map (CommRingCat.ofHom (fgTransition T U hTU))))).obj M ≅
       (Scheme.Modules.pullback (pullback.fst fY
          (Spec.map (CommRingCat.ofHom (fgTransition T U hTU))))).obj N) :=
  Scheme.Modules.exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit
    (ι := FGIndex A₀ A) (G := FGStage) (R := A) (φ := fgTransition) (g := fgToLimit)
    fgIsDirectLimit T fY M N hM hN h

/-- Proof of `LineBundleIsoSubalgebraDescentStatement`. -/
theorem lineBundleIsoSubalgebraDescent : LineBundleIsoSubalgebraDescentStatement.{u} := by
  intro A₀ _ A _ _ X₀ f₀ _ _ M N hM hN X a f hpb hiso s
  let i : FGIndex A₀ A := ⟨Algebra.adjoin A₀ (↑s : Set A), Subalgebra.fg_adjoin_finset s⟩
  let ι₀ := Spec.map (CommRingCat.ofHom (algebraMap A₀ (FGStage i)))
  have h₀ : Nonempty
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd f₀ ι₀)
          (Spec.map (CommRingCat.ofHom (fgToLimit i))))).obj
          ((Scheme.Modules.pullback (pullback.fst f₀ ι₀)).obj M) ≅
        (Scheme.Modules.pullback (pullback.fst (pullback.snd f₀ ι₀)
          (Spec.map (CommRingCat.ofHom (fgToLimit i))))).obj
          ((Scheme.Modules.pullback (pullback.fst f₀ ι₀)).obj N)) := by
    rw [nonempty_iso_pullback_pullback_iff]
    refine nonempty_iso_pullback_of_fac
      (hpb.lift (pullback.fst _ _ ≫ pullback.fst f₀ ι₀) (pullback.snd _ _) ?_)
      (hpb.lift_fst _ _ _) hiso
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
      Category.assoc, spec_map_fgToLimit_comp]
  obtain ⟨j, hij, hj⟩ :=
    exists_fg_nonempty_iso_pullback i (pullback.snd f₀ ι₀)
      ((Scheme.Modules.pullback (pullback.fst f₀ ι₀)).obj M)
      ((Scheme.Modules.pullback (pullback.fst f₀ ι₀)).obj N)
      ((isInvertible_of_isLocallyFreeRankOne hM).pullback _)
      ((isInvertible_of_isLocallyFreeRankOne hN).pullback _) h₀
  rw [nonempty_iso_pullback_pullback_iff] at hj
  refine ⟨j.1, j.2, fun x hx => hij (Algebra.subset_adjoin hx), ?_⟩
  intro X' a' f' hpb'
  refine nonempty_iso_pullback_of_fac
    (pullback.lift (pullback.lift a' (f' ≫ Spec.map (CommRingCat.ofHom (fgTransition i j hij)))
      ?_) f' (pullback.lift_snd _ _ _)) ?_ hj
  · rw [hpb'.w, Category.assoc, spec_map_fgTransition_comp]
  · rw [pullback.lift_fst_assoc, pullback.lift_fst]

end Langlands.AlgebraicGeometry.NoetherianApproximation
