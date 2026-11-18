import Langlands.AlgebraicGeometry.FactorialAffineComplement

/-! # Hartogs extension across a point with factorial stalk -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.FactorialHartogsExtension

variable {X : Scheme.{u}}

/-- A chain `y₀ ⤳ y₁ ⤳ z` of proper generizations gives a nonzero prime of the stalk at `z`
that is not maximal. -/
theorem exists_prime_of_generization_chain {z y₀ y₁ : X} (h₀₁ : y₀ ⤳ y₁) (h₁z : y₁ ⤳ z)
    (hne₀₁ : y₀ ≠ y₁) (hne₁z : y₁ ≠ z) :
    ∃ q : Ideal (X.presheaf.stalk z), q.IsPrime ∧ q ≠ ⊥ ∧
      q ≠ IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
  let O := X.presheaf.stalk z
  let φ := X.fromSpecStalk z
  have hemb : IsEmbedding φ := φ.isEmbedding
  have hφc : φ (IsLocalRing.closedPoint O) = z := Scheme.fromSpecStalk_closedPoint
  have hrange : ∀ y : X, y ⤳ z → ∃ p, φ p = y := fun y hy ↦ by
    have : y ∈ Set.range φ := by
      rw [Scheme.range_fromSpecStalk]
      exact hy
    exact this
  obtain ⟨p₁, rfl⟩ := hrange y₁ h₁z
  obtain ⟨p₀, rfl⟩ := hrange y₀ (h₀₁.trans h₁z)
  have hle : p₀ ⤳ p₁ := hemb.specializes_iff.mp h₀₁
  have hlt : p₀.asIdeal < p₁.asIdeal :=
    lt_of_le_of_ne ((PrimeSpectrum.le_iff_specializes _ _).mpr hle)
      (fun h ↦ hne₀₁ (congrArg φ (PrimeSpectrum.ext h)))
  refine ⟨p₁.asIdeal, p₁.isPrime, ne_bot_of_gt hlt, fun h ↦ hne₁z ?_⟩
  have hp₁ : p₁ = IsLocalRing.closedPoint O := PrimeSpectrum.ext h
  exact (congrArg φ hp₁).trans hφc

variable [IsIntegral X]

theorem genericPoint_mem {U : X.Opens} {y : X} (hy : y ∈ U) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨y, trivial, hy⟩

/-- **Hartogs condition.** If `W` is the complement of a point `z`, then every section on
`W` becomes regular at `z` after multiplication by a power of any nonzero nonunit germ at
`z`, in the function field. -/
theorem forall_pow_mul {W : X.Opens} [Nonempty W] {z : X} (hW : ∀ y : X, y ∉ W ↔ y = z)
    (s : Γ(X, W)) (f : X.presheaf.stalk z) (hf : f ∈ IsLocalRing.maximalIdeal _)
    (hf0 : f ≠ 0) :
    ∃ (k : ℕ) (a : X.presheaf.stalk z),
      algebraMap _ X.functionField f ^ k * X.germToFunctionField W s =
        algebraMap _ X.functionField a := by
  obtain ⟨V, hzV, g, hg⟩ := X.presheaf.exists_germ_eq f
  obtain ⟨_, ⟨A, hA, rfl⟩, hzA, hAV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hzV V.isOpen
  have hAV' : A ≤ V := hAV
  let gA : Γ(X, A) := X.presheaf.map (homOfLE hAV').op g
  have hgA : X.presheaf.germ A z hzA gA = f := by
    change X.presheaf.germ A z hzA (X.presheaf.map (homOfLE hAV').op g) = f
    rw [TopCat.Presheaf.germ_res_apply]
    exact hg
  have : Nonempty A := ⟨⟨z, hzA⟩⟩
  have hDW : X.basicOpen gA ≤ W := by
    intro y hy
    by_contra hyW
    obtain rfl := (hW y).mp hyW
    have hu := (X.mem_basicOpen gA y hzA).mp hy
    rw [hgA] at hu
    exact (IsLocalRing.mem_maximalIdeal _).mp hf hu
  have hgenA : genericPoint X ∈ A := genericPoint_mem hzA
  have hfK : algebraMap _ X.functionField f = X.germToFunctionField A gA := by
    rw [← hgA, Scheme.algebraMap_germ_eq_germToFunctionField]
  have hgen : genericPoint X ∈ X.basicOpen gA := by
    rw [X.mem_basicOpen gA _ hgenA, isUnit_iff_ne_zero]
    change X.germToFunctionField A gA ≠ 0
    rw [← hfK]
    intro h
    exact hf0 ((map_eq_zero_iff _ (IsFractionRing.injective _ X.functionField)).mp h)
  have : Nonempty (X.basicOpen gA) := ⟨⟨_, hgen⟩⟩
  have := hA.isLocalization_basicOpen gA
  obtain ⟨⟨a', _, ⟨k, rfl⟩⟩, hk⟩ :=
    IsLocalization.surj (Submonoid.powers gA) (X.presheaf.map (homOfLE hDW).op s)
  refine ⟨k, X.presheaf.germ A z hzA a', ?_⟩
  have h1 := congrArg (X.germToFunctionField (X.basicOpen gA)) hk
  simp only [map_mul, map_pow] at h1
  have e1 : X.germToFunctionField (X.basicOpen gA) (X.presheaf.map (homOfLE hDW).op s) =
      X.germToFunctionField W s := TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have e2 : ∀ c : Γ(X, A), X.germToFunctionField (X.basicOpen gA)
      (algebraMap Γ(X, A) Γ(X, X.basicOpen gA) c) = X.germToFunctionField A c :=
    fun c ↦ TopCat.Presheaf.germ_res_apply _ _ _ _ _
  rw [e1, e2, e2] at h1
  rw [Scheme.algebraMap_germ_eq_germToFunctionField, hfK, mul_comm, ← h1]

/-- **Hartogs extension.** Let `X` be an integral scheme, `z` a point whose stalk is
factorial and which has a chain `y₀ ⤳ y₁ ⤳ z` of proper generizations, and `W` the
complement of `z`. Then every section of the structure sheaf on `W` extends to `X`. -/
theorem restrict_surjective_of_generization_chain {W : X.Opens} {z y₀ y₁ : X}
    (hW : ∀ y : X, y ∉ W ↔ y = z) (h₀₁ : y₀ ⤳ y₁) (h₁z : y₁ ⤳ z) (hne₀₁ : y₀ ≠ y₁)
    (hne₁z : y₁ ≠ z) [UniqueFactorizationMonoid (X.presheaf.stalk z)] :
    Function.Surjective (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op) := by
  intro s
  obtain ⟨q, hq, hq0, hqm⟩ := exists_prime_of_generization_chain h₀₁ h₁z hne₀₁ hne₁z
  have hy₁W : y₁ ∈ W := by
    by_contra h
    exact hne₁z ((hW y₁).mp h)
  have : Nonempty W := ⟨⟨y₁, hy₁W⟩⟩
  obtain ⟨a, ha⟩ :=
    Langlands.CommutativeAlgebra.FactorialLocalHartogs.exists_eq_of_forall_pow_mul
      (K := X.functionField) hq hq0 hqm (X.germToFunctionField W s)
      (fun f hf hf0 ↦ forall_pow_mul hW s f hf hf0)
  obtain ⟨V, hzV, t, ht⟩ := X.presheaf.exists_germ_eq a
  have : Nonempty V := ⟨⟨z, hzV⟩⟩
  have htK : X.germToFunctionField V t = X.germToFunctionField W s := by
    rw [← ha, ← ht, Scheme.algebraMap_germ_eq_germToFunctionField]
  have key : ∀ (O : X.Opens) (hO : genericPoint X ∈ O) (i : O ⟶ W) (j : O ⟶ V),
      X.presheaf.map i.op s = X.presheaf.map j.op t := by
    intro O hO i j
    have : Nonempty O := ⟨⟨_, hO⟩⟩
    apply X.germToFunctionField_injective O
    change X.presheaf.germ O _ _ (X.presheaf.map i.op s) =
      X.presheaf.germ O _ _ (X.presheaf.map j.op t)
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    exact htK.symm
  have hgW : genericPoint X ∈ W := genericPoint_mem hy₁W
  have hgV : genericPoint X ∈ V := genericPoint_mem hzV
  let U : Bool → X.Opens := fun b ↦ cond b W V
  let sf : ∀ b, ToType (X.sheaf.1.obj (op (U b))) := fun b ↦
    Bool.rec (motive := fun b ↦ ToType (X.sheaf.1.obj (op (U b)))) t s b
  have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 U sf := by
    rintro (_ | _) (_ | _)
    · rfl
    · exact (key (V ⊓ W) ⟨hgV, hgW⟩ _ _).symm
    · exact key (W ⊓ V) ⟨hgW, hgV⟩ _ _
    · rfl
  have hcover : (⊤ : X.Opens) ≤ iSup U := by
    intro y _
    rw [Opens.mem_iSup]
    by_cases hy : y ∈ W
    · exact ⟨true, hy⟩
    · exact ⟨false, (hW y).mp hy ▸ hzV⟩
  obtain ⟨σ, hσ, -⟩ :=
    X.sheaf.existsUnique_gluing' U ⊤ (fun _ ↦ homOfLE le_top) hcover sf hcomp
  exact ⟨σ, hσ true⟩

end Langlands.AlgebraicGeometry.FactorialHartogsExtension
