import Langlands.CommutativeAlgebra.MinimalFiniteFreeCover
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.RingTheory.Noetherian.Basic

/-! # Iterated minimal finite free covers -/

universe u

namespace Langlands.CommutativeAlgebra

open CategoryTheory

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- A surjection onto a projective module with kernel in the maximal-ideal
multiple of a finite source is injective. -/
theorem injective_of_surjective_of_minimal_kernel
    {F M : Type*} [AddCommGroup F] [Module R F] [Module.Finite R F]
    [AddCommGroup M] [Module R M] [Module.Projective R M]
    (f : F →ₗ[R] M) (hsurj : Function.Surjective f)
    (hker : LinearMap.ker f ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R F)) :
    Function.Injective f := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f (LinearMap.id : M →ₗ[R] M) hsurj
  let g : F →ₗ[R] LinearMap.ker f :=
    (LinearMap.id - s.comp f).codRestrict (LinearMap.ker f) (by
      intro x
      change f (x - s (f x)) = 0
      have h := LinearMap.congr_fun hs (f x)
      simpa using sub_eq_zero.mpr h.symm)
  have hg (x : LinearMap.ker f) : g x = x := by
    apply Subtype.ext
    simp [g, LinearMap.mem_ker.mp x.property]
  have hgsurj : Function.Surjective g := fun x ↦ ⟨x, hg x⟩
  have : Module.Finite R (LinearMap.ker f) := Module.Finite.of_surjective g hgsurj
  have hsmul : (⊤ : Submodule R (LinearMap.ker f)) ≤
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R (LinearMap.ker f)) := by
    intro x _
    have h := Submodule.mem_map_of_mem (f := g) (hker x.property)
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hgsurj] at h
    simpa only [hg] using h
  have hbot : (⊤ : Submodule R (LinearMap.ker f)) ≤ ⊥ :=
    Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
      (by rw [IsLocalRing.jacobson_eq_maximalIdeal]; exact bot_ne_top)
      (by simpa only [bot_sup_eq] using hsmul)
  rw [← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot]
  rw [← Submodule.subsingleton_iff R, ← subsingleton_iff_bot_eq_top]
  exact top_unique hbot

variable (R) [IsNoetherianRing R]

/-- The kernel of the chosen minimal finite free cover, as a finite module. -/
noncomputable abbrev nextMinimalSyzygy (M : FGModuleCat.{u} R) : FGModuleCat.{u} R :=
  FGModuleCat.of R (LinearMap.ker (minimalFiniteFreeCover R M).map)

/-- The successive minimal syzygies, with the module itself in degree zero. -/
@[reducible] noncomputable def minimalSyzygy (M : FGModuleCat.{u} R) : ℕ → FGModuleCat.{u} R
  | 0 => M
  | n + 1 => nextMinimalSyzygy R (minimalSyzygy M n)

/-- The minimal finite free cover in degree `n`. -/
noncomputable abbrev minimalSyzygyCover (M : FGModuleCat.{u} R) (n : ℕ) :
    MinimalFiniteFreeCover R (minimalSyzygy R M n) :=
  minimalFiniteFreeCover R (minimalSyzygy R M n)

/-- The free module in degree `n` of the minimal resolution. -/
abbrev minimalResolutionModule (M : FGModuleCat.{u} R) (n : ℕ) :=
  Fin (minimalSyzygyCover R M n).rank →₀ R

/-- The differential from degree `n+1` to degree `n`. -/
noncomputable def minimalResolutionDifferential (M : FGModuleCat.{u} R) (n : ℕ) :
    minimalResolutionModule R M (n + 1) →ₗ[R] minimalResolutionModule R M n :=
  (LinearMap.ker (minimalSyzygyCover R M n).map).subtype.comp
    (minimalSyzygyCover R M (n + 1)).map

variable (M : FGModuleCat.{u} R)

theorem minimalResolutionDifferential_comp (n : ℕ) :
    (minimalResolutionDifferential R M n).comp
      (minimalResolutionDifferential R M (n + 1)) = 0 := by
  apply LinearMap.ext
  intro x
  simp only [minimalResolutionDifferential, LinearMap.comp_apply,
    Submodule.subtype_apply, LinearMap.map_coe_ker, map_zero, LinearMap.zero_apply]

theorem minimalResolutionDifferential_range (n : ℕ) :
    LinearMap.range (minimalResolutionDifferential R M n) =
      LinearMap.ker (minimalSyzygyCover R M n).map := by
  rw [minimalResolutionDifferential, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (minimalSyzygyCover R M (n + 1)).surjective,
    Submodule.map_top, Submodule.range_subtype]

theorem minimalResolutionDifferential_minimal (n : ℕ) :
    LinearMap.range (minimalResolutionDifferential R M n) ≤
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R (minimalResolutionModule R M n)) := by
  rw [minimalResolutionDifferential_range]
  exact (minimalSyzygyCover R M n).minimal

/-- The cover short complex in degree `n`, with its kernel in degree `n+1`. -/
noncomputable def minimalResolutionShortComplex (n : ℕ) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk
    (X₁ := minimalSyzygy R M (n + 1))
    (X₂ := minimalResolutionModule R M n)
    (X₃ := minimalSyzygy R M n)
    (LinearMap.ker (minimalSyzygyCover R M n).map).subtype
    (minimalSyzygyCover R M n).map (by
      apply LinearMap.ext
      intro x
      exact x.property)

theorem minimalResolutionShortComplex_shortExact (n : ℕ) :
    (minimalResolutionShortComplex R M n).ShortExact where
  exact := by
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact Submodule.range_subtype _
  mono_f := (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (minimalSyzygyCover R M n).surjective

theorem minimalSyzygy_hasProjectiveDimensionLT_iff (n m : ℕ) :
    HasProjectiveDimensionLT M.obj (n + m + 1) ↔
      HasProjectiveDimensionLT (minimalSyzygy R M n).obj (m + 1) := by
  induction n generalizing m with
  | zero => simp only [Nat.zero_add, minimalSyzygy]
  | succ n ih =>
    have h := (ih (m + 1)).trans
      ((minimalResolutionShortComplex_shortExact R M n).hasProjectiveDimensionLT_X₃_iff m
        (by
          change Projective (ModuleCat.of R (minimalResolutionModule R M n))
          infer_instance))
    simpa only [minimalResolutionShortComplex, ShortComplex.moduleCatMk,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

theorem minimalSyzygy_projective_of_hasProjectiveDimensionLT (n : ℕ)
    (h : HasProjectiveDimensionLT M.obj (n + 1)) :
    Module.Projective R (minimalSyzygy R M n) := by
  have h' := (minimalSyzygy_hasProjectiveDimensionLT_iff R M n 0).mp h
  exact (IsProjective.iff_projective _).mpr
    (projective_iff_hasProjectiveDimensionLT_one.mpr h')

theorem minimalSyzygy_subsingleton_of_hasProjectiveDimensionLT (n : ℕ)
    (h : HasProjectiveDimensionLT M.obj (n + 1)) :
    Subsingleton (minimalSyzygy R M (n + 1)) := by
  have := minimalSyzygy_projective_of_hasProjectiveDimensionLT R M n h
  have hinj := injective_of_surjective_of_minimal_kernel
    (minimalSyzygyCover R M n).map
    (minimalSyzygyCover R M n).surjective
    (minimalSyzygyCover R M n).minimal
  exact Submodule.subsingleton_iff_eq_bot.mpr (LinearMap.ker_eq_bot.mpr hinj)

end Langlands.CommutativeAlgebra
