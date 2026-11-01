import Langlands.AlgebraicGeometry.Picard.FibreFrameLifting.Core
import Langlands.AlgebraicGeometry.Picard.FibreFrameLifting.FibreIso
import Mathlib.AlgebraicGeometry.Fiber

/-!
# A section whose fibre pullback is a frame

Let `b : X' ⟶ B` be smooth, proper and geometrically connected, and let `g' : Y' ⟶ X'` be such
that `g' ≫ b` is geometrically connected. If a module `M` on `X'` is trivial on `Y'` and on the
fibre of `b` over `x`, and every section of `M` over `Y'` extends to `X'`, then some section of
`M` on `X'` pulls back to a frame on the fibre of `b` over `x`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Langlands.SchemeModule

namespace Langlands.AlgebraicGeometry.Picard.FibreFrameLifting

/-- A section of `M` extending a frame of `M` on `Y'` pulls back to a frame on the fibre of
`b` over `x`. -/
theorem exists_isIso_fiber_pullback {X' Y' B : Scheme.{u}} (b : X' ⟶ B) [Smooth b]
    [IsProper b] [GeometricallyConnected b] (g' : Y' ⟶ X') [GeometricallyConnected (g' ≫ b)]
    (x : B) (M : X'.Modules)
    (ζ : (Scheme.Modules.pullback g').obj M ≅ SheafOfModules.unit Y'.ringCatSheaf)
    (hsurj : Function.Surjective
      (((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app M).app ⊤))
    (e : (Scheme.Modules.pullback (b.fiberι x)).obj M ≅
      SheafOfModules.unit (b.fiber x).ringCatSheaf) :
    ∃ σ : structureModule X' ⟶ M, IsIso ((Scheme.Modules.pullback (b.fiberι x)).map σ) := by
  obtain ⟨σ₀, hσ₀⟩ := hsurj (ζ.inv.app (g' ⁻¹ᵁ ⊤) (1 : Γ(Y', g' ⁻¹ᵁ ⊤)))
  refine ⟨sectionHom M σ₀, ?_⟩
  have hone : (sectionHom M σ₀).app ⊤ (1 : Γ(X', ⊤)) = σ₀ := by
    refine (sectionHom_app_one M σ₀ ⊤).trans ?_
    rw [show (homOfLE (le_top : (⊤ : X'.Opens) ≤ ⊤)).op = 𝟙 (Opposite.op ⊤) from rfl,
      CategoryTheory.Functor.map_id]
    rfl
  have hσ : IsIso ((Scheme.Modules.pullback g').map (sectionHom M σ₀)) :=
    isIso_pullback_map_of_unit_app g' ζ _ (by rw [hone]; exact hσ₀)
  -- the fibre over `x` has global functions forming a field
  obtain ⟨hb₁, hb₂, hb₃⟩ :=
    smoothProperConnected_of_isPullback (IsPullback.of_hasPullback b (B.fromSpecResidueField x))
  have : Smooth (b.fiberToSpecResidueField x) := hb₁
  have : IsProper (b.fiberToSpecResidueField x) := hb₂
  have : GeometricallyConnected (b.fiberToSpecResidueField x) := hb₃
  have hF := eq_zero_or_isUnit_of_smoothProperConnected (Field.toIsField _)
    (b.fiberToSpecResidueField x)
  -- the fibre of `g' ≫ b` over `x` is nonempty and maps to the fibre of `b`
  let hmap : (g' ≫ b).fiber x ⟶ b.fiber x :=
    pullback.lift ((g' ≫ b).fiberι x ≫ g') ((g' ≫ b).fiberToSpecResidueField x)
      (by rw [Category.assoc]; exact (g' ≫ b).fiber_fac x)
  have hcomm : hmap ≫ b.fiberι x = (g' ≫ b).fiberι x ≫ g' := pullback.lift_fst _ _ _
  let τ := (Langlands.Scheme.Modules.pullbackUnitIso (b.fiberι x)).inv ≫
    (Scheme.Modules.pullback (b.fiberι x)).map (sectionHom M σ₀)
  have hτ : IsIso ((Scheme.Modules.pullback hmap).map τ) := by
    have h₁ : IsIso ((Scheme.Modules.pullback ((g' ≫ b).fiberι x)).map
        ((Scheme.Modules.pullback g').map (sectionHom M σ₀))) := inferInstance
    have h₂ : IsIso ((Scheme.Modules.pullback ((g' ≫ b).fiberι x ≫ g')).map
        (sectionHom M σ₀)) :=
      (NatIso.isIso_map_iff (Scheme.Modules.pullbackComp ((g' ≫ b).fiberι x) g') _).mp h₁
    have h₃ : IsIso ((Scheme.Modules.pullback (hmap ≫ b.fiberι x)).map (sectionHom M σ₀)) := by
      rw [hcomm]; exact h₂
    have h₄ : IsIso ((Scheme.Modules.pullback hmap).map
        ((Scheme.Modules.pullback (b.fiberι x)).map (sectionHom M σ₀))) :=
      (NatIso.isIso_map_iff (Scheme.Modules.pullbackComp hmap (b.fiberι x)) _).mpr h₃
    have hc : (Scheme.Modules.pullback hmap).map τ =
        (Scheme.Modules.pullback hmap).map
          (Langlands.Scheme.Modules.pullbackUnitIso (b.fiberι x)).inv ≫
        (Scheme.Modules.pullback hmap).map
          ((Scheme.Modules.pullback (b.fiberι x)).map (sectionHom M σ₀)) :=
      Functor.map_comp _ _ _
    rw [hc]
    exact IsIso.comp_isIso' (Iso.isIso_hom ((Scheme.Modules.pullback hmap).mapIso
      (Langlands.Scheme.Modules.pullbackUnitIso (b.fiberι x)).symm)) h₄
  have hτi : IsIso τ := isIso_of_isIso_pullback_map hF e τ hmap hτ
  have hτ' : (Scheme.Modules.pullback (b.fiberι x)).map (sectionHom M σ₀) =
      (Langlands.Scheme.Modules.pullbackUnitIso (b.fiberι x)).hom ≫ τ :=
    (Iso.hom_inv_id_assoc _ _).symm
  rw [hτ']
  exact IsIso.comp_isIso' (Iso.isIso_hom (Langlands.Scheme.Modules.pullbackUnitIso (b.fiberι x)))
    hτi

end Langlands.AlgebraicGeometry.Picard.FibreFrameLifting
