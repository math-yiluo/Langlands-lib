import Langlands.LinearAlgebra.FiniteRankTrace
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective

/-! # Finite-rank trace on an exact sequence of complex vector spaces -/

noncomputable section

universe uA uB uC

namespace Langlands.FiniteRankEnd

variable {A : Type uA} [AddCommGroup A] [Module ℂ A]
variable {B : Type uB} [AddCommGroup B] [Module ℂ B]
variable {C : Type uC} [AddCommGroup C] [Module ℂ C]

/-- Cyclicity when one of the maps has finite-dimensional range. -/
theorem trace_comp_of_hasNoetherianRange
    (f : A →ₗ[ℂ] B) (hf : f.HasNoetherianRange) (g : B →ₗ[ℂ] A) :
    trace ⟨g.comp f, hf.comp_left g⟩ =
      trace ⟨f.comp g, hf.comp_right g⟩ := by
  let : IsNoetherian ℂ f.range := hf
  let : FiniteDimensional ℂ f.range := inferInstance
  rw [trace_eq_of_factorization
    ⟨g.comp f, hf.comp_left g⟩ f.rangeRestrict
      (g.comp f.range.subtype) (by ext a; rfl)]
  rw [trace_eq_of_factorization
    ⟨f.comp g, hf.comp_right g⟩ (f.rangeRestrict.comp g)
      f.range.subtype (by ext b; rfl)]
  rfl

/-- A short exact sequence of vector spaces has compatible linear splittings.
The splittings are not asserted to respect any additional action. -/
theorem exists_splittings_of_exact
    (f : A →ₗ[ℂ] B) (g : B →ₗ[ℂ] C)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : f.range = g.ker) :
    ∃ (p : B →ₗ[ℂ] A) (s : C →ₗ[ℂ] B),
      p.comp f = LinearMap.id ∧ g.comp s = LinearMap.id ∧
        f.comp p + s.comp g = LinearMap.id := by
  obtain ⟨p₀, hp₀⟩ := f.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hf)
  obtain ⟨s, hs⟩ := g.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hg)
  have hp₀_apply (a : A) : p₀ (f a) = a :=
    LinearMap.congr_fun hp₀ a
  have hs_apply (c : C) : g (s c) = c :=
    LinearMap.congr_fun hs c
  have hgf (a : A) : g (f a) = 0 := by
    have hmem : f a ∈ g.ker := hfg ▸ LinearMap.mem_range_self f a
    exact hmem
  let p : B →ₗ[ℂ] A := p₀.comp (LinearMap.id - s.comp g)
  refine ⟨p, s, ?_, hs, ?_⟩
  · ext a
    simp [p, hgf, hp₀_apply]
  · ext b
    have hmem : b - s (g b) ∈ g.ker := by
      change g (b - s (g b)) = 0
      simp [hs_apply]
    rw [← hfg] at hmem
    obtain ⟨a, ha⟩ := hmem
    change f (p₀ (b - s (g b))) + s (g b) = b
    rw [← ha, hp₀_apply, ha]
    exact sub_add_cancel _ _

/-- Additivity of the genuine finite-rank trace on every short exact sequence.
The carriers have independent universes and need not be finite-dimensional. -/
theorem trace_shortExact
    (f : A →ₗ[ℂ] B) (g : B →ₗ[ℂ] C)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : f.range = g.ker)
    (TA : finiteRankEnd A) (TB : finiteRankEnd B) (TC : finiteRankEnd C)
    (hfT : TB.val.comp f = f.comp TA.val)
    (hgT : g.comp TB.val = TC.val.comp g) :
    trace TB = trace TA + trace TC := by
  obtain ⟨p, s, hpf, hgs, hsplit⟩ :=
    exists_splittings_of_exact f g hf hg hfg
  let SA : finiteRankEnd B :=
    ⟨f.comp (p.comp TB.val), (TB.property.comp_left p).comp_left f⟩
  let SC : finiteRankEnd B :=
    ⟨s.comp (g.comp TB.val), (TB.property.comp_left g).comp_left s⟩
  have hsum : TB = SA + SC := by
    apply Subtype.ext
    ext b
    exact (LinearMap.congr_fun hsplit (TB.val b)).symm
  have hTA : trace SA = trace TA := by
    change trace ⟨f.comp (p.comp TB.val), _⟩ = trace TA
    rw [trace_comp_of_hasNoetherianRange
      (p.comp TB.val) (TB.property.comp_left p) f]
    congr 1
    apply Subtype.ext
    ext a
    change p (TB.val (f a)) = TA.val a
    exact (congrArg p (LinearMap.congr_fun hfT a)).trans
      (LinearMap.congr_fun hpf (TA.val a))
  have hTC : trace SC = trace TC := by
    change trace ⟨s.comp (g.comp TB.val), _⟩ = trace TC
    rw [trace_comp_of_hasNoetherianRange
      (g.comp TB.val) (TB.property.comp_left g) s]
    congr 1
    apply Subtype.ext
    ext c
    change g (TB.val (s c)) = TC.val c
    exact (LinearMap.congr_fun hgT (s c)).trans
      (congrArg TC.val (LinearMap.congr_fun hgs c))
  calc
    trace TB = trace (SA + SC) := congrArg trace hsum
    _ = trace SA + trace SC := map_add trace SA SC
    _ = trace TA + trace TC := congrArg₂ (· + ·) hTA hTC

end Langlands.FiniteRankEnd
