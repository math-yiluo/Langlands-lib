import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescent.Submodule
import Langlands.AlgebraicGeometry.Picard.LineBundleDescent

/-! # Unit sections of the cocycle subsheaf are local frames -/

universe u

open CategoryTheory AlgebraicGeometry Opposite Langlands.SchemeModule

namespace Langlands.Scheme.UnitCocycleDescent

variable {X Y : Scheme.{u}} (p : X ⟶ Y)
  (c : ∀ (U : Scheme.{u}) (a b : U ⟶ X), a ≫ p = b ≫ p → Γ(U, ⊤)ˣ)

/-- The quotient of a cocycle section by a cocycle section that is a unit is invariant under
all pairs of maps with equal composites. -/
lemma isPairInvariant_mul_inv {W : Y.Opens} {σ τ : Γ(X, p ⁻¹ᵁ W)}
    (hσ : IsCocycleSection p c W σ) (hτ : IsCocycleSection p c W τ) (hu : IsUnit σ) :
    IsPairInvariant p (p ⁻¹ᵁ W) (τ * ↑hu.unit⁻¹) := by
  intro U a b h V ha hb
  have e1 := hσ U a b h V ha hb
  have e2 := hτ U a b h V ha hb
  have e3 : a.appLE (p ⁻¹ᵁ W) V ha ↑hu.unit⁻¹ * a.appLE (p ⁻¹ᵁ W) V ha σ = 1 := by
    rw [← map_mul, IsUnit.val_inv_mul, map_one]
  have e4 : b.appLE (p ⁻¹ᵁ W) V hb ↑hu.unit⁻¹ * b.appLE (p ⁻¹ᵁ W) V hb σ = 1 := by
    rw [← map_mul, IsUnit.val_inv_mul, map_one]
  rw [map_mul, map_mul]
  set C := U.presheaf.map (homOfLE le_top).op (c U a b h).1
  set Aσ := a.appLE (p ⁻¹ᵁ W) V ha σ
  set Bσ := b.appLE (p ⁻¹ᵁ W) V hb σ
  set Aτ := a.appLE (p ⁻¹ᵁ W) V ha τ
  set Bτ := b.appLE (p ⁻¹ᵁ W) V hb τ
  set As := a.appLE (p ⁻¹ᵁ W) V ha ↑hu.unit⁻¹
  set Bs := b.appLE (p ⁻¹ᵁ W) V hb ↑hu.unit⁻¹
  linear_combination Bs * e2 - Aτ * As * e4 - Aτ * As * Bs * e1 + Aτ * C * Bs * e3

variable [QuasiCompact p] [Flat p] [Surjective p]

/-- A cocycle section over `W` that is a unit upstairs trivializes the cocycle sheaf on `W`. -/
theorem nonempty_restrict_iso_unit {W : Y.Opens} (σ : Γ(X, p ⁻¹ᵁ W))
    (hσ : IsCocycleSection p c W σ) (hu : IsUnit σ) :
    Nonempty ((cocycleModule p c).restrict W.ι ≅
      SheafOfModules.unit W.toScheme.ringCatSheaf) := by
  let M := (cocycleModule p c).restrict W.ι
  let σ₀ : Γ(X, p ⁻¹ᵁ (W.ι ''ᵁ ⊤)) :=
    X.presheaf.map (homOfLE (p.preimage_mono (W.ι_image_le ⊤))).op σ
  have hσ₀ : IsCocycleSection p c _ σ₀ := hσ.map (W.ι_image_le ⊤)
  let s : GlobalSections M := (⟨σ₀, hσ₀⟩ : (cocycleSubmodule p c).obj (op (W.ι ''ᵁ ⊤)))
  let ιV : ∀ V : W.toScheme.Opens, Γ(M, V) → Γ(X, p ⁻¹ᵁ (W.ι ''ᵁ V)) :=
    fun V x ↦ (x : ↥((cocycleSubmodule p c).obj (op (W.ι ''ᵁ V)))).1
  have hιV : ∀ V, Function.Injective (ιV V) := fun V a b h ↦ Subtype.ext h
  have hmem : ∀ V (x : Γ(M, V)), IsCocycleSection p c _ (ιV V x) := fun V x ↦ x.2
  let σV : ∀ V : W.toScheme.Opens, Γ(X, p ⁻¹ᵁ (W.ι ''ᵁ V)) := fun V ↦
    X.presheaf.map (homOfLE (p.preimage_mono (W.ι_image_le V))).op σ
  have huV : ∀ V, IsUnit (σV V) := fun V ↦ hu.map _
  have hval : ∀ V (r : Γ(W.toScheme, V)),
      ιV V ((sectionHom M s).app V r) = p.app (W.ι ''ᵁ V) ((W.ι.appIso V).inv r) * σV V := by
    intro V r
    rw [LineBundleDescent.sectionHom_app]
    change p.app (W.ι ''ᵁ V) ((W.ι.appIso V).inv r) *
      (X.presheaf.map (homOfLE (p.preimage_mono (W.ι.image_mono le_top))).op σ₀ :
        Γ(X, p ⁻¹ᵁ (W.ι ''ᵁ V))) = _
    refine congrArg (_ * ·) ?_
    change X.presheaf.map _ (X.presheaf.map _ σ) = X.presheaf.map _ σ
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  have hiso : IsIso (sectionHom M s) := by
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro V
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun r r' h ↦ ?_, fun t ↦ ?_⟩
    · have h' := (hval V r).symm.trans ((congrArg (ιV V) h).trans (hval V r'))
      exact (ConcreteCategory.bijective_of_isIso (W.ι.appIso V).inv).1
        (app_injective p _ ((huV V).mul_left_injective h'))
    · obtain ⟨g, hg⟩ := exists_app_eq_of_isPairInvariant p (W.ι ''ᵁ V) _
        (isPairInvariant_mul_inv p c ((hσ.map (W.ι_image_le V))) (hmem V t) (huV V))
      refine ⟨(W.ι.appIso V).hom g, hιV V ((hval V _).trans ?_)⟩
      rw [Iso.hom_inv_id_apply, hg, mul_assoc, IsUnit.val_inv_mul, mul_one]
  exact ⟨(asIso (sectionHom M s)).symm⟩

end Langlands.Scheme.UnitCocycleDescent
