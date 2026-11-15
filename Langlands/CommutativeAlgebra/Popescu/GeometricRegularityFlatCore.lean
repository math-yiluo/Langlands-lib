import Mathlib

/-! # Linear independence in `𝔪/𝔪²` from injectivity of maps on `H₁` of cotangent complexes -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

namespace GeometricRegularity

open IsLocalRing

open scoped TensorProduct

/-- The extension `A → κ(A)` of a local ring onto its residue field, with underlying ring `A`.
Its conormal module is `𝔪/𝔪²` and its `H₁` is all of it, since `Ω_{A/A} = 0`. -/
noncomputable abbrev residueExtension (A : Type u) [CommRing A] [IsLocalRing A] :
    Algebra.Extension.{u} A (ResidueField A) where
  Ring := A
  σ x := (residue_surjective x).choose
  algebraMap_σ x := (residue_surjective x).choose_spec

section residueExtension

variable (A : Type u) [CommRing A] [IsLocalRing A]

theorem residueExtension_ker : (residueExtension A).ker = maximalIdeal A := by
  ext x
  rw [RingHom.mem_ker]
  exact residue_eq_zero_iff x

variable {A} in
theorem mem_residueExtension_ker {x : A} (hx : x ∈ maximalIdeal A) :
    x ∈ (residueExtension A).ker := by
  rw [residueExtension_ker]
  exact hx

variable {A} in
theorem residueExtension_mk_eq_zero_iff {x : A} (hx : x ∈ (residueExtension A).ker) :
    Algebra.Extension.Cotangent.mk (P := residueExtension A) ⟨x, hx⟩ = 0 ↔
      x ∈ maximalIdeal A ^ 2 := by
  rw [Algebra.Extension.Cotangent.mk_eq_zero_iff]
  show x ∈ (residueExtension A).ker ^ 2 ↔ _
  rw [residueExtension_ker]

variable {A} in
theorem residueExtension_sum_mk {ι : Type*} [Fintype ι] (b x : ι → A)
    (hx : ∀ i, x i ∈ maximalIdeal A) :
    ∑ i, residue A (b i) • Algebra.Extension.Cotangent.mk (P := residueExtension A)
        ⟨x i, mem_residueExtension_ker (hx i)⟩ =
      Algebra.Extension.Cotangent.mk (P := residueExtension A)
        ⟨∑ i, b i * x i, mem_residueExtension_ker
          (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hx i))⟩ := by
  have h1 : (⟨∑ i, b i * x i, mem_residueExtension_ker
      (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hx i))⟩ : (residueExtension A).ker) =
      ∑ i, b i • (⟨x i, mem_residueExtension_ker (hx i)⟩ : (residueExtension A).ker) := by
    ext
    simp [smul_eq_mul]
  rw [h1, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  exact algebraMap_smul (ResidueField A) (b i) _

/-- Every element of the conormal module of `A → κ(A)` lies in `H₁`. -/
theorem residueExtension_h1Cotangentι_surjective :
    Function.Surjective (residueExtension A).h1Cotangentι := by
  have : Subsingleton Ω[A⁄A] :=
    KaehlerDifferential.subsingleton_of_surjective (R := A) (S := A) fun x => ⟨x, rfl⟩
  intro z
  exact ⟨(⟨z, LinearMap.mem_ker.mpr (Subsingleton.elim _ _)⟩ :
    LinearMap.ker (residueExtension A).cotangentComplex), rfl⟩

/-- `H₁(L_{κ(A)/A})` is identified with `H₁` of the extension `A → κ(A)`. -/
theorem residueExtension_map_defaultHom_bijective :
    Function.Bijective (Algebra.Extension.H1Cotangent.map
      (Algebra.Extension.defaultHom _ _ (residueExtension A))) := by
  let g : (residueExtension A).Hom (Algebra.Generators.self A (ResidueField A)).toExtension :=
    { toRingHom := algebraMap A (MvPolynomial (ResidueField A) A)
      toRingHom_algebraMap := fun x => rfl
      algebraMap_toRingHom := fun x => by
        exact (Algebra.Generators.algebraMap_apply (P := Algebra.Generators.self A (ResidueField A))
          (MvPolynomial.C x)).trans (by rw [MvPolynomial.aeval_C]; rfl) }
  exact (Algebra.Extension.H1Cotangent.equiv (Algebra.Extension.defaultHom _ _ _) g).bijective

end residueExtension

/-- Jacobi–Zariski: if `T ⊗_S Ω_{S/R} → Ω_{T/R}` is injective, then `H₁(L_{T/R}) → H₁(L_{T/S})`
is surjective. -/
theorem h1Cotangent_map_surjective {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (h : Function.Injective (KaehlerDifferential.mapBaseChange R S T)) :
    Function.Surjective (Algebra.H1Cotangent.map R S T T) := by
  intro y
  have h1 : Algebra.H1Cotangent.δ R S T y = 0 := h (by
    rw [map_zero]
    exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T).apply_apply_eq_zero y)
  exact (Algebra.H1Cotangent.exact_map_δ R S T y).mp h1

section core

variable {k A₀ A : Type u} [Field k] [CommRing A₀] [CommRing A] [IsLocalRing A₀] [IsLocalRing A]
  [Algebra k A₀] [Algebra k A] [Algebra A₀ A] [IsScalarTower k A₀ A]
  [IsLocalHom (algebraMap A₀ A)]

variable (A₀ A) in
/-- The hom of extensions `(A₀ → κ(A₀)) → (A → κ(A))` given by `A₀ → A`. -/
noncomputable def residueExtensionHom : (residueExtension A₀).Hom (residueExtension A) where
  toRingHom := algebraMap A₀ A
  toRingHom_algebraMap _ := rfl
  algebraMap_toRingHom _ := rfl

variable (k) in
/-- The two composites `H₁(L_{κ₀/k}) → 𝔪/𝔪²`, through `H₁(L_{κ₀/A₀})` and through
`H₁(L_{κ/k}) → H₁(L_{κ/A})`, agree. -/
theorem h1_path_eq (y : Algebra.H1Cotangent k (ResidueField A₀)) :
    Algebra.Extension.H1Cotangent.map (residueExtensionHom A₀ A)
      (Algebra.Extension.H1Cotangent.map (Algebra.Extension.defaultHom _ _ (residueExtension A₀))
        (Algebra.H1Cotangent.map k A₀ (ResidueField A₀) (ResidueField A₀) y)) =
    Algebra.Extension.H1Cotangent.map (Algebra.Extension.defaultHom _ _ (residueExtension A))
      (Algebra.H1Cotangent.map k A (ResidueField A) (ResidueField A)
        (Algebra.H1Cotangent.map k k (ResidueField A₀) (ResidueField A) y)) := by
  simp only [Algebra.H1Cotangent.map]
  rw [← Algebra.Extension.H1Cotangent.map_comp_apply,
    ← Algebra.Extension.H1Cotangent.map_comp_apply,
    ← Algebra.Extension.H1Cotangent.map_comp_apply,
    ← Algebra.Extension.H1Cotangent.map_comp_apply]
  exact LinearMap.congr_fun (Algebra.Extension.H1Cotangent.map_eq _ _) y

/-- **Core of 07E6.** Let `A₀ → A` be a local homomorphism of local `k`-algebras with residue
fields `κ₀ → κ`. Assume
* `H₁(L_{κ/k}) → H₁(L_{κ/A})` is injective,
* `κ ⊗_{κ₀} H₁(L_{κ₀/k}) → H₁(L_{κ/k})` is injective,
* `κ₀ ⊗_{A₀} Ω_{A₀/k} → Ω_{κ₀/k}` is injective.
If `x_i ∈ 𝔪_{A₀}` have linearly independent classes in `𝔪_{A₀}/𝔪_{A₀}²` (stated through
coefficients), then so do their images in `𝔪_A/𝔪_A²`. -/
theorem cotangent_independent
    (hK3 : Function.Injective (Algebra.H1Cotangent.map k A (ResidueField A) (ResidueField A)))
    (hK2 : Function.Injective ((Algebra.H1Cotangent.map k k (ResidueField A₀)
      (ResidueField A)).liftBaseChange (ResidueField A)))
    (hΩ : Function.Injective (KaehlerDifferential.mapBaseChange k A₀ (ResidueField A₀)))
    {ι : Type*} [Fintype ι] (x : ι → A₀) (hx : ∀ i, x i ∈ maximalIdeal A₀)
    (hx₀ : ∀ b : ι → A₀, ∑ i, b i * x i ∈ maximalIdeal A₀ ^ 2 → ∀ i, b i ∈ maximalIdeal A₀)
    (a : ι → A) (ha : ∑ i, a i * algebraMap A₀ A (x i) ∈ maximalIdeal A ^ 2) (i : ι) :
    a i ∈ maximalIdeal A := by
  classical
  have hx' : ∀ j, algebraMap A₀ A (x j) ∈ maximalIdeal A := fun j =>
    map_nonunit (algebraMap A₀ A) (x j) (hx j)
  -- the `κ₀`-linear map `θ₀ : H₁(L_{κ₀/k}) → 𝔪₀/𝔪₀²`
  let θ₀ : Algebra.H1Cotangent k (ResidueField A₀) →ₗ[ResidueField A₀]
      (residueExtension A₀).Cotangent :=
    (residueExtension A₀).h1Cotangentι ∘ₗ
      Algebra.Extension.H1Cotangent.map (Algebra.Extension.defaultHom _ _ (residueExtension A₀)) ∘ₗ
      Algebra.H1Cotangent.map k A₀ (ResidueField A₀) (ResidueField A₀)
  have hθ₀ : ∀ z, ∃ h, θ₀ h = z := by
    intro z
    obtain ⟨w₁, rfl⟩ := residueExtension_h1Cotangentι_surjective A₀ z
    obtain ⟨w₂, rfl⟩ := (residueExtension_map_defaultHom_bijective A₀).2 w₁
    obtain ⟨h, rfl⟩ := h1Cotangent_map_surjective hΩ w₂
    exact ⟨h, rfl⟩
  choose h hh using fun j => hθ₀
    (Algebra.Extension.Cotangent.mk ⟨x j, mem_residueExtension_ker (hx j)⟩)
  -- the images of the `h j` in `𝔪/𝔪²`
  have himg : ∀ j, (residueExtension A).h1Cotangentι
      (Algebra.Extension.H1Cotangent.map (Algebra.Extension.defaultHom _ _ (residueExtension A))
        (Algebra.H1Cotangent.map k A (ResidueField A) (ResidueField A)
          (Algebra.H1Cotangent.map k k (ResidueField A₀) (ResidueField A) (h j)))) =
      Algebra.Extension.Cotangent.mk ⟨algebraMap A₀ A (x j), mem_residueExtension_ker (hx' j)⟩ := by
    intro j
    rw [← h1_path_eq k (h j)]
    change Algebra.Extension.Cotangent.map (residueExtensionHom A₀ A) (θ₀ (h j)) = _
    rw [hh j, Algebra.Extension.Cotangent.map_mk]
    rfl
  -- the element `w = ∑ ā_j ⊗ h_j` vanishes
  let w : ResidueField A ⊗[ResidueField A₀] Algebra.H1Cotangent k (ResidueField A₀) :=
    ∑ j, residue A (a j) ⊗ₜ h j
  have hw : w = 0 := by
    apply hK2
    apply hK3
    apply (residueExtension_map_defaultHom_bijective A).1
    apply (residueExtension A).h1Cotangentι_injective
    simp only [map_zero]
    simp only [w, map_sum, LinearMap.liftBaseChange_tmul, map_smul, himg]
    rw [residueExtension_sum_mk a _ hx', residueExtension_mk_eq_zero_iff]
    exact ha
  -- the classes of the `x j` are linearly independent in `𝔪₀/𝔪₀²`
  have hli₀ : LinearIndependent (ResidueField A₀) fun j =>
      Algebra.Extension.Cotangent.mk (P := residueExtension A₀)
        ⟨x j, mem_residueExtension_ker (hx j)⟩ := by
    rw [Fintype.linearIndependent_iff]
    intro e he j
    choose b hb using fun j => residue_surjective (R := A₀) (e j)
    have h1 : ∑ j, residue A₀ (b j) • Algebra.Extension.Cotangent.mk (P := residueExtension A₀)
        ⟨x j, mem_residueExtension_ker (hx j)⟩ = 0 := by
      simp only [hb]
      exact he
    rw [residueExtension_sum_mk b x hx, residueExtension_mk_eq_zero_iff] at h1
    rw [← hb j]
    exact (residue_eq_zero_iff _).mpr (hx₀ b h1 j)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective
    (Finsupp.linearCombination (ResidueField A₀) fun j =>
      Algebra.Extension.Cotangent.mk (P := residueExtension A₀)
        ⟨x j, mem_residueExtension_ker (hx j)⟩) (LinearMap.ker_eq_bot.mpr hli₀)
  have hgv : ∀ j, g (Algebra.Extension.Cotangent.mk (P := residueExtension A₀)
      ⟨x j, mem_residueExtension_ker (hx j)⟩) = Finsupp.single j 1 := by
    intro j
    have := LinearMap.congr_fun hg (Finsupp.single j 1)
    simpa [Finsupp.linearCombination_single] using this
  -- evaluate the `i`-th coordinate
  let Φ : Algebra.H1Cotangent k (ResidueField A₀) →ₗ[ResidueField A₀] ResidueField A :=
    (Algebra.linearMap (ResidueField A₀) (ResidueField A)) ∘ₗ
      (Finsupp.lapply i) ∘ₗ g ∘ₗ θ₀
  have hΦ : ∀ j, Φ (h j) = algebraMap (ResidueField A₀) (ResidueField A)
      (Finsupp.single j (1 : ResidueField A₀) i) := by
    intro j
    simp only [Φ, LinearMap.comp_apply, hh j, hgv j, Finsupp.lapply_apply,
      Algebra.linearMap_apply]
  have h2 := congrArg (Φ.liftBaseChange (ResidueField A)) hw
  simp only [w, map_sum, LinearMap.liftBaseChange_tmul, map_zero, hΦ] at h2
  rw [Finset.sum_eq_single i (fun j _ hji => by
      simp [hji])
    (fun hi => absurd (Finset.mem_univ i) hi), Finsupp.single_eq_same, map_one,
    smul_eq_mul, mul_one] at h2
  exact (residue_eq_zero_iff _).mp h2

end core

end GeometricRegularity

end Langlands.CommutativeAlgebra.Popescu
