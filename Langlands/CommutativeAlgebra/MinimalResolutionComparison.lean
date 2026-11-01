import Langlands.CommutativeAlgebra.MinimalFiniteFreeResolution

/-! # Split comparisons with iterated minimal free covers -/

universe u

namespace Langlands.CommutativeAlgebra

open CategoryTheory TensorProduct

variable {R : Type u} [CommRing R] [IsLocalRing R]

theorem lTensor_residueField_injective_of_preimage
    {A B : Type*} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (f : A →ₗ[R] B)
    (h : ∀ x, f x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R B) →
      x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R A)) :
    Function.Injective (f.lTensor (IsLocalRing.ResidueField R)) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro z hz
  obtain ⟨x, rfl⟩ := TensorProduct.mk_surjective R A
    (IsLocalRing.ResidueField R) Ideal.Quotient.mk_surjective z
  change (f.lTensor (IsLocalRing.ResidueField R))
    ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x) = 0 at hz
  have hfx : f x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R B) := by
    rw [← LinearMap.ker_tensorProductMk]
    change (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] f x = 0
    simpa only [LinearMap.lTensor_tmul] using hz
  have hx := h x hfx
  rw [← LinearMap.ker_tensorProductMk] at hx
  exact hx

theorem split_injective_of_preimage_maximalIdeal_smul
    {A B : Type*} [AddCommGroup A] [Module R A] [Module.Finite R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.Free R B]
    (f : A →ₗ[R] B)
    (h : ∀ x, f x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R B) →
      x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R A)) :
    ∃ s : B →ₗ[R] A, s.comp f = LinearMap.id :=
  (IsLocalRing.split_injective_iff_lTensor_residueField_injective f).mpr
    (lTensor_residueField_injective_of_preimage f h)

omit [IsLocalRing R] in
lemma map_mem_ideal_smul_of_range_le
    {A B : Type*} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    (I : Ideal R) (f : A →ₗ[R] B) (P : Submodule R B)
    (hf : LinearMap.range f ≤ P) {x : A}
    (hx : x ∈ I • (⊤ : Submodule R A)) : f x ∈ I • P := by
  have h := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul'', Submodule.map_top] at h
  exact smul_mono_right I hf h

omit [IsLocalRing R] in
lemma map_mem_ideal_smul_smul_top
    {A B : Type*} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    (I : Ideal R) (f : A →ₗ[R] B) {x : A}
    (hx : x ∈ I • (I • (⊤ : Submodule R A))) :
    f x ∈ I • (I • (⊤ : Submodule R B)) := by
  have h := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul'', Submodule.map_smul'', Submodule.map_top] at h
  have hle : I • (I • LinearMap.range f) ≤
      I • (I • (⊤ : Submodule R B)) :=
    smul_mono_right I (smul_mono_right I le_top)
  exact hle h

variable (R) [IsNoetherianRing R] (M : FGModuleCat.{u} R)
variable (C : ℕ → Type u) [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
variable (d : ∀ n, C (n + 1) →ₗ[R] C n)

/-- A comparison into a minimal free resolution is split injective in every
degree if its degree-zero map is and its source differential detects membership
in the maximal-ideal multiple by membership in its square. -/
theorem split_injective_minimalResolutionComparison
    [∀ n, Module.Finite R (C n)]
    (a : ∀ n, C n →ₗ[R] minimalResolutionModule R M n)
    (ha : ∀ n, (minimalResolutionDifferential R M n).comp (a (n + 1)) =
      (a n).comp (d n))
    (hzero : ∃ s : minimalResolutionModule R M 0 →ₗ[R] C 0,
      s.comp (a 0) = LinearMap.id)
    (hdetect : ∀ n x, d n x ∈ IsLocalRing.maximalIdeal R •
      (IsLocalRing.maximalIdeal R • (⊤ : Submodule R (C n))) →
      x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (C (n + 1)))) :
    ∀ n, ∃ s : minimalResolutionModule R M n →ₗ[R] C n,
      s.comp (a n) = LinearMap.id := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih
    apply split_injective_of_preimage_maximalIdeal_smul
    intro x hx
    apply hdetect n x
    have hm := map_mem_ideal_smul_of_range_le (IsLocalRing.maximalIdeal R)
      (minimalResolutionDifferential R M n)
      (IsLocalRing.maximalIdeal R • (⊤ : Submodule R (minimalResolutionModule R M n)))
      (minimalResolutionDifferential_minimal R M n) hx
    have hax := LinearMap.congr_fun (ha n) x
    simp only [LinearMap.comp_apply] at hax
    rw [hax] at hm
    have h := map_mem_ideal_smul_smul_top (IsLocalRing.maximalIdeal R) s hm
    have hsx := LinearMap.congr_fun hs (d n x)
    change s (a n (d n x)) = d n x at hsx
    rwa [hsx] at h

theorem minimalResolutionModule_subsingleton_of_syzygy_subsingleton (n : ℕ)
    [Subsingleton (minimalSyzygy R M n)] :
    Subsingleton (minimalResolutionModule R M n) := by
  have hinj := injective_of_surjective_of_minimal_kernel
    (minimalSyzygyCover R M n).map
    (minimalSyzygyCover R M n).surjective
    (minimalSyzygyCover R M n).minimal
  exact hinj.subsingleton

theorem minimalResolutionModule_subsingleton_of_hasProjectiveDimensionLT (n : ℕ)
    (h : HasProjectiveDimensionLT M.obj n) :
    Subsingleton (minimalResolutionModule R M n) := by
  cases n with
  | zero =>
    have : Subsingleton M := ModuleCat.isZero_iff_subsingleton.mp
      ((hasProjectiveDimensionLT_zero_iff_isZero M.obj).mp h)
    exact minimalResolutionModule_subsingleton_of_syzygy_subsingleton R M 0
  | succ n =>
    have := minimalSyzygy_subsingleton_of_hasProjectiveDimensionLT R M n h
    exact minimalResolutionModule_subsingleton_of_syzygy_subsingleton R M (n + 1)

/-- A nonzero source in a split comparison forces the numerical lower bound. -/
theorem projectiveDimension_ge_of_split_minimalResolutionComparison
    (n : ℕ) [Nontrivial (C n)]
    (a : C n →ₗ[R] minimalResolutionModule R M n)
    (ha : ∃ s : minimalResolutionModule R M n →ₗ[R] C n, s.comp a = LinearMap.id) :
    (n : WithBot ℕ∞) ≤ projectiveDimension M.obj := by
  rw [projectiveDimension_ge_iff]
  intro h
  have := minimalResolutionModule_subsingleton_of_hasProjectiveDimensionLT R M n h
  obtain ⟨s, hs⟩ := ha
  have hinj : Function.Injective a :=
    Function.LeftInverse.injective (fun x ↦ LinearMap.congr_fun hs x)
  have : Subsingleton (C n) := hinj.subsingleton
  exact not_subsingleton (C n) this

/-- A comparison map in one degree together with its cycle condition. -/
structure MinimalResolutionComparisonStep (n : ℕ) where
  map : C n →ₗ[R] minimalResolutionModule R M n
  cycle : ((minimalSyzygyCover R M n).map.comp map).comp (d n) = 0

variable [∀ n, Module.Projective R (C n)]

/-- Lift a map from a projective source along the chosen cover. -/
noncomputable def liftToMinimalResolutionModule (n : ℕ)
    (f : C n →ₗ[R] minimalSyzygy R M n) :
    C n →ₗ[R] minimalResolutionModule R M n :=
  Classical.choose (Module.projective_lifting_property
    (minimalSyzygyCover R M n).map f (minimalSyzygyCover R M n).surjective)

@[simp]
theorem cover_comp_liftToMinimalResolutionModule (n : ℕ)
    (f : C n →ₗ[R] minimalSyzygy R M n) :
    (minimalSyzygyCover R M n).map.comp (liftToMinimalResolutionModule R M C n f) = f :=
  Classical.choose_spec (Module.projective_lifting_property
    (minimalSyzygyCover R M n).map f (minimalSyzygyCover R M n).surjective)

variable (ε : C 0 →ₗ[R] M) (hε : ε.comp (d 0) = 0)
variable (hdd : ∀ n, (d n).comp (d (n + 1)) = 0)

/-- Lift the augmentation into degree zero of the minimal resolution. -/
noncomputable def MinimalResolutionComparisonStep.initial :
    MinimalResolutionComparisonStep R M C d 0 where
  map := liftToMinimalResolutionModule R M C 0 ε
  cycle := by rw [cover_comp_liftToMinimalResolutionModule]; exact hε

omit ε hε in
/-- Extend a comparison by lifting a cycle into the next free cover. -/
noncomputable def MinimalResolutionComparisonStep.next (n : ℕ)
    (s : MinimalResolutionComparisonStep R M C d n) :
    MinimalResolutionComparisonStep R M C d (n + 1) where
  map := liftToMinimalResolutionModule R M C (n + 1)
    ((s.map.comp (d n)).codRestrict (LinearMap.ker (minimalSyzygyCover R M n).map)
      (by
        intro x
        exact LinearMap.congr_fun s.cycle x))
  cycle := by
    rw [cover_comp_liftToMinimalResolutionModule]
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change s.map (d n (d (n + 1) x)) = 0
    have hx : d n (d (n + 1) x) = 0 := LinearMap.congr_fun (hdd n) x
    rw [hx, map_zero]

omit ε hε in
theorem MinimalResolutionComparisonStep.next_comm (n : ℕ)
    (s : MinimalResolutionComparisonStep R M C d n) :
    (minimalResolutionDifferential R M n).comp
      (s.next R M C d hdd n).map = s.map.comp (d n) := by
  rw [minimalResolutionDifferential, LinearMap.comp_assoc,
    MinimalResolutionComparisonStep.next, cover_comp_liftToMinimalResolutionModule]
  rfl

/-- A degreewise comparison into the minimal free resolution, obtained by
projective lifting; the source complex need not be exact. -/
noncomputable def minimalResolutionComparisonStep :
    (n : ℕ) → MinimalResolutionComparisonStep R M C d n
  | 0 => MinimalResolutionComparisonStep.initial R M C d ε hε
  | n + 1 => (minimalResolutionComparisonStep n).next R M C d hdd n

/-- The map in a degree of the chosen comparison. -/
noncomputable def minimalResolutionComparison (n : ℕ) :
    C n →ₗ[R] minimalResolutionModule R M n :=
  (minimalResolutionComparisonStep R M C d ε hε hdd n).map

theorem minimalResolutionComparison_zero :
    (minimalSyzygyCover R M 0).map.comp
      (minimalResolutionComparison R M C d ε hε hdd 0) = ε := by
  exact cover_comp_liftToMinimalResolutionModule R M C 0 ε

theorem minimalResolutionComparison_comm (n : ℕ) :
    (minimalResolutionDifferential R M n).comp
      (minimalResolutionComparison R M C d ε hε hdd (n + 1)) =
      (minimalResolutionComparison R M C d ε hε hdd n).comp (d n) :=
  MinimalResolutionComparisonStep.next_comm R M C d hdd n
    (minimalResolutionComparisonStep R M C d ε hε hdd n)

theorem minimalResolutionComparison_split [∀ n, Module.Finite R (C n)]
    (hεinj : Function.Injective (ε.lTensor (IsLocalRing.ResidueField R)))
    (hdetect : ∀ n x, d n x ∈ IsLocalRing.maximalIdeal R •
      (IsLocalRing.maximalIdeal R • (⊤ : Submodule R (C n))) →
      x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (C (n + 1)))) :
    ∀ n, ∃ s : minimalResolutionModule R M n →ₗ[R] C n,
      s.comp (minimalResolutionComparison R M C d ε hε hdd n) = LinearMap.id := by
  apply split_injective_minimalResolutionComparison R M C d
    (minimalResolutionComparison R M C d ε hε hdd)
    (minimalResolutionComparison_comm R M C d ε hε hdd) _ hdetect
  apply (IsLocalRing.split_injective_iff_lTensor_residueField_injective _).mpr
  have hinj : Function.Injective
      (((minimalSyzygyCover R M 0).map.comp
        (minimalResolutionComparison R M C d ε hε hdd 0)).lTensor
          (IsLocalRing.ResidueField R)) := by
    rw [minimalResolutionComparison_zero]
    exact hεinj
  rw [LinearMap.lTensor_comp] at hinj
  intro x y hxy
  apply hinj
  exact congrArg ((minimalSyzygyCover R M 0).map.lTensor (IsLocalRing.ResidueField R)) hxy

include hε hdd in
/-- A finite projective source complex with the detection property gives
a lower bound on projective dimension in every nonzero degree. -/
theorem projectiveDimension_ge_of_projectiveComplex
    [∀ n, Module.Finite R (C n)]
    (hεinj : Function.Injective (ε.lTensor (IsLocalRing.ResidueField R)))
    (hdetect : ∀ n x, d n x ∈ IsLocalRing.maximalIdeal R •
      (IsLocalRing.maximalIdeal R • (⊤ : Submodule R (C n))) →
      x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (C (n + 1))))
    (n : ℕ) [Nontrivial (C n)] :
    (n : WithBot ℕ∞) ≤ projectiveDimension M.obj :=
  projectiveDimension_ge_of_split_minimalResolutionComparison R M C n
    (minimalResolutionComparison R M C d ε hε hdd n)
    (minimalResolutionComparison_split R M C d ε hε hdd hεinj hdetect n)

end Langlands.CommutativeAlgebra
