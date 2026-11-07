import Langlands.Algebra.TorusChartRing
import Langlands.Algebra.HopfPointWeightLocus

/-! # Existence of a torus chart around a field point -/

noncomputable section

universe u

open TensorProduct

namespace Langlands.Algebra.TorusChartExistence

open HopfPointExtension HopfPointBridge HopfPointTwist FiniteBialgebraHom TorusChartAlgebra
  HopfPointClosedLocus LatticeConfiguration InvariantPrincipalOpen HopfPointRigidity
  HopfPointWeightWindow HopfPointWeightLocus TorusChartRing

section Lattice

variable {r : Type*} [Fintype r] [DecidableEq r]

/-- Bounded sums of a box lie in a larger box. -/
theorem boundedSums_box_subset (n : ℕ) : ∀ N : ℕ,
    boundedSums (box r n : Set (r → ℤ)) N ⊆ (box r (N * n) : Set (r → ℤ))
  | 0 => by
    rintro x rfl
    simp [mem_box]
  | N + 1 => by
    rintro x (hx | ⟨y, hy, z, hz, rfl⟩)
    · have := boundedSums_box_subset n N hx
      simp only [Finset.mem_coe, mem_box] at this ⊢
      intro j
      have := this j
      have : (N : ℤ) * n ≤ ((N + 1 : ℕ) : ℤ) * n := by push_cast; nlinarith
      push_cast at *
      linarith
    · have hy' := boundedSums_box_subset n N hy
      simp only [Finset.mem_coe, mem_box] at hy' hz ⊢
      intro j
      have h1 := hy' j
      have h2 := hz j
      have h3 := abs_add_le (y j) (z j)
      simp only [Pi.add_apply]
      push_cast at *
      nlinarith

/-- A finite set of lattice vectors lies in some box. -/
theorem exists_box (T : Finset (r → ℤ)) : ∃ n : ℕ, (T : Set (r → ℤ)) ⊆ (box r n : Set _) := by
  classical
  refine ⟨∑ χ ∈ T, ∑ j, (χ j).natAbs, fun χ hχ => ?_⟩
  simp only [Finset.mem_coe, mem_box] at hχ ⊢
  intro j
  have h1 : (χ j).natAbs ≤ ∑ j, (χ j).natAbs :=
    Finset.single_le_sum (f := fun j => (χ j).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
  have h2 : ∑ j, (χ j).natAbs ≤ ∑ χ ∈ T, ∑ j, (χ j).natAbs :=
    Finset.single_le_sum (f := fun χ => ∑ j, (χ j).natAbs) (fun _ _ => Nat.zero_le _) hχ
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h1.trans h2

end Lattice

section Points

variable {R : Type*} [CommRing R] {C : Type*} [CommRing C] [Algebra R C]
  {K : Type*} [Field K] [Algebra R K]

/-- A field point factors through the residue field of its kernel. -/
theorem exists_residueLift (y : C →ₐ[R] K) :
    ∃ (_ : (RingHom.ker y).IsPrime) (ι : (RingHom.ker y).ResidueField →ₐ[R] K),
      ι.comp (IsScalarTower.toAlgHom R C (RingHom.ker y).ResidueField) = y := by
  have hP : (RingHom.ker y).IsPrime := RingHom.ker_isPrime _
  refine ⟨hP, Ideal.ResidueField.liftₐ (RingHom.ker y) y le_rfl ?_,
    Ideal.ResidueField.liftₐ_comp_toAlgHom _ _ _ _⟩
  intro x hx
  simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
  intro h
  exact hx (by simpa [RingHom.mem_ker] using h)

/-- A point inverting `f` factors through the localization at `f`. -/
theorem exists_lift_away (y : C →ₐ[R] K) {f : C} (hf : y f ≠ 0) :
    ∃ y' : Localization.Away f →ₐ[R] K,
      y'.comp (IsScalarTower.toAlgHom R C (Localization.Away f)) = y := by
  have hunit : ∀ z : Submonoid.powers f, IsUnit (y z) := by
    rintro ⟨z, k, rfl⟩
    simpa using (isUnit_iff_ne_zero.mpr hf).pow k
  refine ⟨IsLocalization.liftAlgHom (M := Submonoid.powers f) hunit, ?_⟩
  apply AlgHom.ext
  intro w
  simp [IsLocalization.lift_eq]

/-- An element of `C_f` is a fraction with denominator a power of `f`. -/
theorem exists_numerator (f : C) (c : Localization.Away f) :
    ∃ (w : C) (k : ℕ), c * algebraMap C _ (f ^ k) = algebraMap C _ w := by
  obtain ⟨⟨w, ⟨s, k, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers f) c
  exact ⟨w, k, h⟩

end Points

section Localizations

variable {R : Type*} [CommRing R] {C : Type*} [CommRing C] [Algebra R C]
  {D : Type*} [CommRing D] [Algebra R D]

theorem mapAlgHom_comp_mapAlgHom {E : Type*} [CommRing E] [Algebra R E] {M : Type*}
    [AddCommGroup M] (g : C →ₐ[R] D) (h : D →ₐ[R] E) :
    (AddMonoidAlgebra.mapAlgHom M h).comp (AddMonoidAlgebra.mapAlgHom M g) =
      AddMonoidAlgebra.mapAlgHom M (h.comp g) := by
  apply AlgHom.ext
  intro x
  apply AddMonoidAlgebra.coeff_injective
  ext b
  simp [AddMonoidAlgebra.coeff_mapAlgHom]

/-- A map inverting `c` factors through the localization at `c`. -/
theorem exists_factor_away (ρ : C →ₐ[R] D) {c : C} (hc : IsUnit (ρ c)) :
    ∃ ρ' : Localization.Away c →ₐ[R] D,
      ρ'.comp (IsScalarTower.toAlgHom R C (Localization.Away c)) = ρ := by
  have hunit : ∀ z : Submonoid.powers c, IsUnit (ρ z) := by
    rintro ⟨z, k, rfl⟩
    simpa using hc.pow k
  refine ⟨IsLocalization.liftAlgHom (M := Submonoid.powers c) hunit, ?_⟩
  apply AlgHom.ext
  intro w
  simp [IsLocalization.lift_eq]

/-- The localization at `f₁` maps to the localization at a multiple of `f₁`. -/
theorem exists_away_dvd (f₁ w : C) :
    ∃ ρ : Localization.Away f₁ →ₐ[R] Localization.Away (f₁ * w),
      ρ.comp (IsScalarTower.toAlgHom R C (Localization.Away f₁)) =
        IsScalarTower.toAlgHom R C (Localization.Away (f₁ * w)) := by
  apply exists_factor_away
  apply isUnit_of_dvd_unit (map_dvd _ (dvd_mul_right f₁ w))
  exact IsLocalization.Away.algebraMap_isUnit _

end Localizations

section Invariant

variable {R : Type*} [CommRing R] {W : Type*} [CommRing W] [Algebra R W]
  {Γ : Type*} [Group Γ] [Fintype Γ]

/-- An invariant element whose principal open contains a given point and is covered by the
translates of a principal open containing the orbit. -/
theorem exists_invariant_cover (σ : Γ →* (W ≃ₐ[R] W)) {f : W} (p₀ : Ideal W) [p₀.IsPrime]
    (hf : f ∉ p₀) : ∃ N : W, (∀ γ, σ γ N = N) ∧ N ∉ p₀ ∧
      ∀ P : Ideal W, P.IsPrime → N ∉ P → ∃ γ, σ γ f ∉ P := by
  classical
  let J : Ideal W := Ideal.span (Set.range fun γ => σ γ f)
  let P : Γ → Ideal W := fun γ => Ideal.comap (σ γ : W →+* W) p₀
  have hJ : ∀ γ ∈ (Finset.univ : Finset Γ), ¬ J ≤ P γ := by
    intro γ _ hle
    have hmem : σ γ⁻¹ f ∈ J := Ideal.subset_span ⟨γ⁻¹, rfl⟩
    have := hle hmem
    simp only [P, Ideal.mem_comap] at this
    have e : (σ γ : W →+* W) (σ γ⁻¹ f) = f := by
      change σ γ (σ γ⁻¹ f) = f
      rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [e] at this
    exact hf this
  obtain ⟨g, hgJ, hgP⟩ := exists_mem_forall_not_mem Finset.univ P
    (fun γ _ => Ideal.comap_isPrime _ _) J hJ
  refine ⟨norm σ g, norm_invariant σ g, norm_not_mem σ (fun γ => ?_), fun Q hQ hNQ => ?_⟩
  · have := hgP γ (Finset.mem_univ γ)
    simpa [P, Ideal.mem_comap] using this
  · by_contra! h
    have hle : J ≤ Q := by
      rw [Ideal.span_le]
      rintro _ ⟨γ, rfl⟩
      exact h γ
    exact hNQ (Ideal.mem_of_dvd _ (dvd_norm σ g) (hle hgJ))

end Invariant

section Window

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [HopfAlgebra R A]
  [Algebra.FinitePresentation R A] (r : Type u) [Fintype r] [DecidableEq r] (m : ℕ) [NeZero m]
  {σ' : Type u} (gen : σ' → A) (n : ℕ) (V : Submodule R A) (δ : V →ₗ[R] V ⊗[R] A) (N₀ : ℕ)

/-- A chart datum whose window extension has its weights in the box, with reduction
modulo `m` injective on bounded sums of the box. -/
structure WindowDatum extends Datum R A r m gen n where
  weights : WeightsIn δ toDatum.α (box r n : Set (r → ℤ))
  injOn : Set.InjOn (red r m) (boundedSums (box r n : Set (r → ℤ)) N₀)

end Window

section Extension

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [HopfAlgebra R A]
  [Algebra.FinitePresentation R A] {r : Type u} [Fintype r] [DecidableEq r] {m : ℕ} [NeZero m]
  {K : Type u} [Field K] [Algebra R K]

omit [DecidableEq r] in
/-- The point of `W` attached to a Hopf point of `μ_m^r`. -/
theorem exists_point_of_hopfPoint {K : Type u} [CommRing K] [Algebra R K]
    {β : A →ₐ[R] AddMonoidAlgebra K (r → ZMod m)}
    (hβ : IsHopfPoint β) : ∃ y : W R A r m →ₐ[R] K, pointOf R A r m y = β := by
  refine ⟨(homEquiv R A (AddMonoidAlgebra R (r → ZMod m)) K).symm
    ⟨ofGroupAlgebra β, isHopfPoint_ofGroupAlgebra hβ⟩, ?_⟩
  rw [pointOf, ← univ_point, Equiv.apply_symm_apply, toGroupAlgebra_ofGroupAlgebra]

end Extension

section Window2

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [HopfAlgebra R A]
  [Algebra.FinitePresentation R A] {r : Type u} [Fintype r] [DecidableEq r] {m : ℕ} [NeZero m]
  {K : Type u} [Field K] [Algebra R K]
  {V : Submodule R A} [Module.Finite R V] {δ : V →ₗ[R] V ⊗[R] A}
  {σ' : Type u} {gen : σ' → A} {N₀ n : ℕ}

/-- The window extension around a field point of `W`. -/
theorem exists_window_extension (hδ : IsCoassoc δ)
    (hι : (Coalgebra.comul (R := R) (A := A)) ∘ₗ V.subtype = V.subtype.rTensor A ∘ₗ δ)
    (hgenV : ∀ i, gen i ∈ V) (hP : IsBoundedPresentation (R := R) gen N₀) (hN₀ : 1 ≤ N₀)
    (hinj : Set.InjOn (red r m) (boundedSums (box r n : Set (r → ℤ)) N₀))
    {α₀ : A →ₐ[R] AddMonoidAlgebra K (r → ℤ)} (hα₀ : IsHopfPoint α₀)
    (hs₀ : Function.Surjective (scalarExt α₀)) (hw₀ : WeightsIn δ α₀ (box r n : Set (r → ℤ)))
    (y₀ : W R A r m →ₐ[R] K)
    (hy₀ : pointOf R A r m y₀ = (AddMonoidAlgebra.mapDomainAlgHom R K (red r m)).comp α₀) :
    ∃ (f : W R A r m) (α : A →ₐ[R] AddMonoidAlgebra (Localization.Away f) (r → ℤ))
      (y : Localization.Away f →ₐ[R] K),
      IsHopfPoint α ∧ (∀ i, ↑(α (gen i)).coeff.support ⊆ (box r n : Set (r → ℤ))) ∧
      (AddMonoidAlgebra.mapDomainAlgHom R _ (red r m)).comp α =
        pointOf R A r m (IsScalarTower.toAlgHom R (W R A r m) (Localization.Away f)) ∧
      Function.Surjective (scalarExt α) ∧ WeightsIn δ α (box r n : Set (r → ℤ)) ∧
      y.comp (IsScalarTower.toAlgHom R (W R A r m) (Localization.Away f)) = y₀ ∧
      (AddMonoidAlgebra.mapAlgHom (r → ℤ) y).comp α = α₀ := by
  classical
  -- weights of the universal point at the residue field of `y₀`
  obtain ⟨hP₀, ι₀, hι₀⟩ := exists_residueLift y₀
  have hwβ : WeightsIn δ ((AddMonoidAlgebra.mapDomainAlgHom R K (red r m)).comp α₀)
      ((red r m) '' (box r n : Set (r → ℤ))) := weightsIn_mapDomain δ (red r m) hw₀
  have hwW : WeightsIn δ ((AddMonoidAlgebra.mapAlgHom (r → ZMod m)
      (IsScalarTower.toAlgHom R (W R A r m) (RingHom.ker y₀).ResidueField)).comp
        (univ R A r m)) ((red r m) '' (box r n : Set (r → ℤ))) := by
    apply weightsIn_of_mapAlgHom δ ι₀ (rTensor_injective_of_field ι₀)
    rw [← AlgHom.comp_assoc, mapAlgHom_comp_mapAlgHom, hι₀]
    rw [← hy₀] at hwβ
    exact hwβ
  -- the extension over a principal open
  obtain ⟨f₁, hf₁, α₁, ⟨hα₁, hsupp₁, hred₁⟩, -⟩ := HopfPointWindowExtension.exists_away_extension V δ hδ hι hgenV hP hN₀
    (red r m) hinj (isHopfPoint_univ R A r m) (RingHom.ker y₀) hwW
  have hy₀f₁ : y₀ f₁ ≠ 0 := fun h => hf₁ (by simpa [RingHom.mem_ker] using h)
  obtain ⟨y₁, hy₁⟩ := exists_lift_away y₀ hy₀f₁
  -- the extension specializes to `α₀`
  have hα₁K : (AddMonoidAlgebra.mapAlgHom (r → ℤ) y₁).comp α₁ = α₀ := by
    have hgs : ∀ i, ↑(((AddMonoidAlgebra.mapDomainAlgHom R K (red r m)).comp α₀) (gen i)).coeff.support
        ⊆ (red r m) '' (box r n : Set (r → ℤ)) := by
      intro i
      exact support_mapDomainAlgHom_subset (R := R) (red r m)
        (support_subset_of_weightsIn δ α₀ hw₀ V.subtype hι ⟨gen i, hgenV i⟩)
    obtain ⟨α', -, huniq⟩ := existsUnique_hopfPoint_extension hP hN₀ (red r m) hinj
      (hα₀.mapDomain (red r m)) hgs
    have h1 := huniq ((AddMonoidAlgebra.mapAlgHom (r → ℤ) y₁).comp α₁)
      ⟨HopfPointWindowExtension.IsHopfPoint.mapAlgHom y₁ hα₁,
        fun i => (support_mapAlgHom_subset y₁ _).trans (hsupp₁ i), by
          rw [← AlgHom.comp_assoc, ← HopfPointWindowExtension.mapAlgHom_comp_mapDomain,
            AlgHom.comp_assoc, hred₁, ← hy₀, ← hy₁]
          exact (pointOf_comp _ _).symm⟩
    have h2 := huniq α₀ ⟨hα₀, fun i => support_subset_of_weightsIn δ α₀ hw₀ V.subtype hι
      ⟨gen i, hgenV i⟩, rfl⟩
    rw [h1, h2]
  have hy₁' : ∀ x, y₁ (algebraMap (W R A r m) (Localization.Away f₁) x) = y₀ x :=
    fun x => congrArg (fun F => F x) hy₁
  -- weights near the point
  obtain ⟨hP₁, ι₁, hι₁⟩ := exists_residueLift y₁
  have hw₁ : WeightsIn δ ((AddMonoidAlgebra.mapAlgHom (r → ℤ)
      (IsScalarTower.toAlgHom R (Localization.Away f₁) (RingHom.ker y₁).ResidueField)).comp α₁)
      (box r n : Set (r → ℤ)) := by
    apply weightsIn_of_mapAlgHom δ ι₁ (rTensor_injective_of_field ι₁)
    rw [← AlgHom.comp_assoc, mapAlgHom_comp_mapAlgHom, hι₁, hα₁K]
    exact hw₀
  obtain ⟨c₂, hc₂, hW₂⟩ := exists_away_weightsIn δ hδ hα₁ (box r n : Set (r → ℤ))
    (RingHom.ker y₁) hw₁
  have hy₁c₂ : y₁ c₂ ≠ 0 := fun h => hc₂ (by simpa [RingHom.mem_ker] using h)
  -- the closed-immersion locus near the point
  obtain ⟨c₃, hy₁c₃, hS₃⟩ := exists_away_surjective_of_field hα₁ y₁ (by rw [hα₁K]; exact hs₀)
  -- a single principal open of `W`
  obtain ⟨w, k, hw⟩ := exists_numerator f₁ (c₂ * c₃)
  have hy₀w : y₀ w ≠ 0 := by
    have e := congrArg y₁ hw
    rw [map_mul, map_mul, hy₁', hy₁', map_pow] at e
    rw [← e]
    exact mul_ne_zero (mul_ne_zero hy₁c₂ hy₁c₃) (pow_ne_zero _ hy₀f₁)
  have hy₀f : y₀ (f₁ * w) ≠ 0 := by
    rw [map_mul]
    exact mul_ne_zero hy₀f₁ hy₀w
  obtain ⟨ρ, hρ⟩ := exists_away_dvd (R := R) f₁ w
  have hρ' : ∀ x, ρ (algebraMap (W R A r m) (Localization.Away f₁) x) =
      algebraMap (W R A r m) (Localization.Away (f₁ * w)) x :=
    fun x => congrArg (fun F => F x) hρ
  have hρc : IsUnit (ρ (c₂ * c₃)) := by
    have e := congrArg ρ hw
    rw [map_mul, hρ', hρ'] at e
    have hu : IsUnit (algebraMap (W R A r m) (Localization.Away (f₁ * w)) w) :=
      isUnit_of_dvd_unit (map_dvd _ (dvd_mul_left w f₁))
        (IsLocalization.Away.algebraMap_isUnit _)
    rw [← e] at hu
    exact isUnit_of_mul_isUnit_left hu
  rw [map_mul] at hρc
  obtain ⟨ρ₂, hρ₂⟩ := exists_factor_away ρ (isUnit_of_mul_isUnit_left hρc)
  obtain ⟨ρ₃, hρ₃⟩ := exists_factor_away ρ (isUnit_of_mul_isUnit_right hρc)
  obtain ⟨y, hy⟩ := exists_lift_away y₀ hy₀f
  have hyρ : y.comp ρ = y₁ := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers f₁)
    ext x
    have := congrArg (fun F => F x) hy
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at this
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom, AlgHom.comp_apply,
      hρ', this, hy₁']
  refine ⟨f₁ * w, (AddMonoidAlgebra.mapAlgHom (r → ℤ) ρ).comp α₁, y,
    HopfPointWindowExtension.IsHopfPoint.mapAlgHom ρ hα₁,
    fun i => (support_mapAlgHom_subset ρ _).trans (hsupp₁ i), ?_, ?_, ?_, hy, ?_⟩
  · rw [← AlgHom.comp_assoc, ← HopfPointWindowExtension.mapAlgHom_comp_mapDomain,
      AlgHom.comp_assoc, hred₁, ← hρ]
    exact (pointOf_comp _ _).symm
  · rw [← hρ₃, ← mapAlgHom_comp_mapAlgHom, AlgHom.comp_assoc]
    exact surjective_scalarExt_mapAlgHom ρ₃ hS₃
  · rw [← hρ₂, ← mapAlgHom_comp_mapAlgHom, AlgHom.comp_assoc]
    exact weightsIn_mapAlgHom δ ρ₂ hW₂
  · rw [← AlgHom.comp_assoc, mapAlgHom_comp_mapAlgHom, hyρ, hα₁K]

end Window2

section Main

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [HopfAlgebra R A]
  [Algebra.FinitePresentation R A] {r : Type u} [Fintype r] [DecidableEq r]
  {K : Type u} [Field K] [Algebra R K]
  {V : Submodule R A} [Module.Finite R V] {δ : V →ₗ[R] V ⊗[R] A}
  {σ' : Type u} {gen : σ' → A} {N₀ : ℕ}

/-- Every closed-immersion Hopf point of a split torus over a field lies on a window chart
datum. -/
theorem exists_windowDatum (hδ : IsCoassoc δ)
    (hι : (Coalgebra.comul (R := R) (A := A)) ∘ₗ V.subtype = V.subtype.rTensor A ∘ₗ δ)
    (hgenV : ∀ i, gen i ∈ V) (hgen : Algebra.adjoin R (Set.range gen) = ⊤)
    (hP : IsBoundedPresentation (R := R) gen N₀) (hN₀ : 1 ≤ N₀)
    {α₀ : A →ₐ[R] AddMonoidAlgebra K (r → ℤ)} (hα₀ : IsHopfPoint α₀)
    (hs₀ : Function.Surjective (scalarExt α₀)) :
    ∃ (n m : ℕ) (_ : NeZero m) (d : WindowDatum R A r m gen n V δ N₀)
      (y : Localization.Away d.f →ₐ[R] K),
      y (algebraMap (W R A r m) (Localization.Away d.f) d.N) ≠ 0 ∧
        (AddMonoidAlgebra.mapAlgHom (r → ℤ) y).comp d.α = α₀ := by
  classical
  obtain ⟨T₀, hT₀⟩ := exists_finite_weightsIn δ α₀
  obtain ⟨n, hn⟩ := exists_box T₀
  have hw₀ : WeightsIn δ α₀ (box r n : Set (r → ℤ)) := fun l hl => hT₀ l (fun h => hl (hn h))
  obtain ⟨m, hm, hm2⟩ : ∃ m : ℕ, rigidityBound r n ≤ m ∧ 2 * (N₀ * n) < m :=
    ⟨max (rigidityBound r n) (2 * (N₀ * n) + 1), le_max_left _ _,
      lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)⟩
  have hm0 : NeZero m := ⟨by omega⟩
  have hinj : Set.InjOn (red r m) (boundedSums (box r n : Set (r → ℤ)) N₀) :=
    (injOn_red_box hm2).mono (boundedSums_box_subset n N₀)
  obtain ⟨y₀, hy₀⟩ := exists_point_of_hopfPoint (A := A) (m := m) (hα₀.mapDomain (red r m))
  obtain ⟨f, α, y, hα, hsupp, hred, hsurj, hw, hy, hspec⟩ :=
    exists_window_extension hδ hι hgenV hP hN₀ hinj hα₀ hs₀ hw₀ y₀ hy₀
  have hy' : ∀ x, y (algebraMap (W R A r m) (Localization.Away f) x) = y₀ x :=
    fun x => congrArg (fun F => F x) hy
  have hP₀ : (RingHom.ker y₀).IsPrime := RingHom.ker_isPrime _
  have hf : f ∉ RingHom.ker y₀ := by
    intro h
    rw [RingHom.mem_ker, ← hy'] at h
    exact (IsLocalization.Away.algebraMap_isUnit f).map y |>.ne_zero h
  have := Fintype.ofFinite (Γ r m)
  obtain ⟨N, hNinv, hNp, hcover⟩ := exists_invariant_cover (act R A r m) (RingHom.ker y₀) hf
  let d : WindowDatum R A r m gen n V δ N₀ :=
    { bound := hm
      adjoin_gen := hgen
      f := f
      N := N
      α := α
      isHopfPoint := hα
      support := hsupp
      red_comp := hred
      surjective := hsurj
      invariant := hNinv
      cover := hcover
      weights := hw
      injOn := hinj }
  refine ⟨n, m, hm0, d, y, ?_, hspec⟩
  change y (algebraMap (W R A r m) (Localization.Away f) N) ≠ 0
  rw [hy']
  intro h
  exact hNp (by simpa [RingHom.mem_ker] using h)

end Main

end Langlands.Algebra.TorusChartExistence
