import Langlands.Algebra.HarishChandra.BorelIndependence

/-! # The split Cartan subalgebra of a Levi subalgebra

Let `𝔥` be a split Cartan subalgebra of a finite-dimensional complex Lie algebra `𝔤`, let
`X₁ ∈ 𝔥`, and let `ι : 𝔪 → 𝔤` be an injective map of Lie algebras with range the centralizer
`ker ad X₁`. Then `ι⁻¹(𝔥)` is a split Cartan subalgebra of `𝔪`, isomorphic to `𝔥` through `ι`.
Its roots are the roots of `𝔤` vanishing at `X₁`, composed with this isomorphism. -/

noncomputable section

universe v w

set_option autoImplicit false

namespace Langlands.Algebra.HarishChandra

open LieModule

section Levi

variable {L : Type v} [LieRing L] [LieAlgebra ℂ L] {H : LieSubalgebra ℂ L}
  {M : Type w} [LieRing M] [LieAlgebra ℂ M] (ι : M →ₗ⁅ℂ⁆ L) (X₁ : H)

variable (H) in
/-- The restriction of `ι` to `ι⁻¹(𝔥)`, as a linear map to `𝔥`. -/
def comapCartanMap : H.comap ι →ₗ[ℂ] H :=
  (ι.toLinearMap.comp (H.comap ι).toSubmodule.subtype).codRestrict H.toSubmodule
    (fun m => m.2)

variable (H) in
@[simp]
theorem comapCartanMap_apply (m : H.comap ι) : (comapCartanMap H ι m : L) = ι m := rfl

variable {ι}

theorem comapCartanMap_injective (hinj : Function.Injective ι) :
    Function.Injective (comapCartanMap H ι) := fun _ _ h =>
  Subtype.ext (hinj (congrArg Subtype.val h))

theorem cartan_le_range (hab : IsLieAbelian H)
    (hrange : LinearMap.range ι.toLinearMap = LinearMap.ker (LieAlgebra.ad ℂ L (X₁ : L)))
    (h : H) : (h : L) ∈ LinearMap.range ι.toLinearMap := by
  rw [hrange, LinearMap.mem_ker, LieAlgebra.ad_apply]
  have := congrArg Subtype.val (hab.1 X₁ h)
  rw [LieSubalgebra.coe_bracket] at this
  simpa using this

theorem comapCartanMap_surjective (hab : IsLieAbelian H)
    (hrange : LinearMap.range ι.toLinearMap = LinearMap.ker (LieAlgebra.ad ℂ L (X₁ : L))) :
    Function.Surjective (comapCartanMap H ι) := by
  intro h
  obtain ⟨m, hm⟩ := cartan_le_range X₁ hab hrange h
  refine ⟨⟨m, ?_⟩, Subtype.ext hm⟩
  change ι m ∈ H
  rw [show ι m = ι.toLinearMap m from rfl, hm]
  exact h.2

/-- The isomorphism `ι⁻¹(𝔥) ≃ 𝔥` induced by `ι`. -/
def comapCartanEquiv (hinj : Function.Injective ι) (hab : IsLieAbelian H)
    (hrange : LinearMap.range ι.toLinearMap = LinearMap.ker (LieAlgebra.ad ℂ L (X₁ : L))) :
    H.comap ι ≃ₗ[ℂ] H :=
  LinearEquiv.ofBijective (comapCartanMap H ι)
    ⟨comapCartanMap_injective hinj, comapCartanMap_surjective X₁ hab hrange⟩

@[simp]
theorem comapCartanEquiv_apply (hinj : Function.Injective ι) (hab : IsLieAbelian H)
    (hrange : LinearMap.range ι.toLinearMap = LinearMap.ker (LieAlgebra.ad ℂ L (X₁ : L)))
    (m : H.comap ι) : (comapCartanEquiv X₁ hinj hab hrange m : L) = ι m := rfl

/-- Weight vectors of `𝔪` for `ψ ∘ ι` are the vectors mapped to weight vectors of `𝔤` for `ψ`. -/
theorem mem_weightSpace_comp_iff (hinj : Function.Injective ι) (hab : IsLieAbelian H)
    (hrange : LinearMap.range ι.toLinearMap = LinearMap.ker (LieAlgebra.ad ℂ L (X₁ : L)))
    (ψ : H → ℂ) (x : M) :
    x ∈ weightSpace M (ψ ∘ comapCartanMap H ι) ↔ ι x ∈ weightSpace L ψ := by
  rw [mem_weightSpace, mem_weightSpace]
  constructor
  · intro hx h
    obtain ⟨m, rfl⟩ := comapCartanMap_surjective X₁ hab hrange h
    have := congrArg ι (hx m)
    rw [LieSubalgebra.coe_bracket_of_module, LieHom.map_lie, map_smul] at this
    rw [LieSubalgebra.coe_bracket_of_module]
    exact this
  · intro hx m
    apply hinj
    have := hx (comapCartanMap H ι m)
    rw [LieSubalgebra.coe_bracket_of_module] at this ⊢
    rw [LieHom.map_lie, map_smul]
    exact this

theorem weightSpace_ne_bot_of_comp (hinj : Function.Injective ι) (hab : IsLieAbelian H)
    (hrange : LinearMap.range ι.toLinearMap = LinearMap.ker (LieAlgebra.ad ℂ L (X₁ : L)))
    {ψ : H → ℂ} (h : weightSpace M (ψ ∘ comapCartanMap H ι) ≠ ⊥) : weightSpace L ψ ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := exists_ne_zero_of_weightSpace_ne_bot h
  refine weightSpace_ne_bot_of_mem ((mem_weightSpace_comp_iff X₁ hinj hab hrange ψ x).mp hx) ?_
  intro h0
  exact hx0 (hinj (h0.trans (map_zero ι).symm))

/-- A weight vector of `𝔤` whose weight vanishes at `X₁` lies in the range of `ι`. -/
theorem mem_range_of_mem_weightSpace
    (hrange : LinearMap.range ι.toLinearMap = LinearMap.ker (LieAlgebra.ad ℂ L (X₁ : L)))
    {ψ : H → ℂ} (hψ : ψ X₁ = 0) {y : L} (hy : y ∈ weightSpace L ψ) :
    y ∈ LinearMap.range ι.toLinearMap := by
  rw [hrange, LinearMap.mem_ker, LieAlgebra.ad_apply]
  have := (mem_weightSpace _ _).mp hy X₁
  rw [hψ, zero_smul] at this
  exact this

/-- A weight of `𝔤` with a weight vector in the range of `ι` vanishes at `X₁`. -/
theorem weight_eq_zero_of_mem_range
    (hrange : LinearMap.range ι.toLinearMap = LinearMap.ker (LieAlgebra.ad ℂ L (X₁ : L)))
    {ψ : H → ℂ} {y : L} (hy : y ∈ weightSpace L ψ) (hy0 : y ≠ 0)
    (hyr : y ∈ LinearMap.range ι.toLinearMap) : ψ X₁ = 0 := by
  rw [hrange, LinearMap.mem_ker, LieAlgebra.ad_apply] at hyr
  have := (mem_weightSpace _ _).mp hy X₁
  change ⁅(X₁ : L), y⁆ = ψ X₁ • y at this
  rw [hyr] at this
  exact (smul_eq_zero.mp this.symm).resolve_right hy0

section Comparison

variable (hinj : Function.Injective ι) (hab : IsLieAbelian H)
  (hrange : LinearMap.range ι.toLinearMap = LinearMap.ker (LieAlgebra.ad ℂ L (X₁ : L)))
include hinj hab hrange

theorem comp_symm_comp (χ : H.comap ι → ℂ) :
    χ = (χ ∘ (comapCartanEquiv X₁ hinj hab hrange).symm) ∘ comapCartanMap H ι := by
  funext m
  simp only [Function.comp_apply]
  congr 1
  exact ((comapCartanEquiv X₁ hinj hab hrange).symm_apply_apply m).symm

/-- Weight vectors of `𝔪` for `χ` are the vectors mapped to weight vectors of `𝔤` for the
transported weight. -/
theorem mem_weightSpace_iff_symm (χ : H.comap ι → ℂ) (x : M) :
    x ∈ weightSpace M χ ↔
      ι x ∈ weightSpace L (χ ∘ (comapCartanEquiv X₁ hinj hab hrange).symm) := by
  conv_lhs => rw [comp_symm_comp X₁ hinj hab hrange χ]
  exact mem_weightSpace_comp_iff X₁ hinj hab hrange _ x

theorem weightSpace_symm_ne_bot {χ : H.comap ι → ℂ} (h : weightSpace M χ ≠ ⊥) :
    weightSpace L (χ ∘ (comapCartanEquiv X₁ hinj hab hrange).symm) ≠ ⊥ :=
  weightSpace_ne_bot_of_comp X₁ hinj hab hrange (by rwa [← comp_symm_comp X₁ hinj hab hrange χ])

theorem weight_symm_ne_zero {χ : H.comap ι → ℂ} (h : χ ≠ 0) :
    χ ∘ (comapCartanEquiv X₁ hinj hab hrange).symm ≠ 0 := fun h0 => by
  apply h
  rw [comp_symm_comp X₁ hinj hab hrange χ, h0]
  rfl

/-- The weights of `𝔪` vanish at `X₁`. -/
theorem weight_symm_apply_eq_zero {χ : H.comap ι → ℂ} (h : weightSpace M χ ≠ ⊥) :
    (χ ∘ (comapCartanEquiv X₁ hinj hab hrange).symm) X₁ = 0 := by
  obtain ⟨x, hx, hx0⟩ := exists_ne_zero_of_weightSpace_ne_bot h
  exact weight_eq_zero_of_mem_range X₁ hrange
    ((mem_weightSpace_iff_symm X₁ hinj hab hrange χ x).mp hx)
    (fun h0 => hx0 (hinj (h0.trans (map_zero ι).symm))) ⟨x, rfl⟩

end Comparison

variable [FiniteDimensional ℂ L]

/-- **Transfer of split Cartan subalgebras.** `ι⁻¹(𝔥)` is a split Cartan subalgebra of `𝔪`. -/
theorem IsSplitCartan.comap (hC : IsSplitCartan H) (hinj : Function.Injective ι)
    (hrange : LinearMap.range ι.toLinearMap = LinearMap.ker (LieAlgebra.ad ℂ L (X₁ : L))) :
    IsSplitCartan (H.comap ι) := by
  have hab := hC.isLieAbelian
  let φ := comapCartanEquiv X₁ hinj hab hrange
  have hφ : ∀ χ : H.comap ι → ℂ, χ = (χ ∘ φ.symm) ∘ comapCartanMap H ι :=
    comp_symm_comp X₁ hinj hab hrange
  have hiff : ∀ (χ : H.comap ι → ℂ) (x : M),
      x ∈ weightSpace M χ ↔ ι x ∈ weightSpace L (χ ∘ φ.symm) :=
    mem_weightSpace_iff_symm X₁ hinj hab hrange
  have hbot : ∀ χ : H.comap ι → ℂ, weightSpace M χ ≠ ⊥ → weightSpace L (χ ∘ φ.symm) ≠ ⊥ :=
    fun _ h => weightSpace_symm_ne_bot X₁ hinj hab hrange h
  have hne : ∀ χ : H.comap ι → ℂ, χ ≠ 0 → χ ∘ φ.symm ≠ 0 :=
    fun _ h => weight_symm_ne_zero X₁ hinj hab hrange h
  have hzero : ∀ χ : H.comap ι → ℂ, weightSpace M χ ≠ ⊥ → (χ ∘ φ.symm) X₁ = 0 :=
    fun _ h => weight_symm_apply_eq_zero X₁ hinj hab hrange h
  have hpre : ∀ (ψ : H → ℂ) (hψ : ψ X₁ = 0) (y : L) (hy : y ∈ weightSpace L ψ),
      ∃ x : M, ι x = y ∧ x ∈ weightSpace M (ψ ∘ comapCartanMap H ι) := by
    intro ψ hψ y hy
    obtain ⟨x, rfl⟩ := mem_range_of_mem_weightSpace X₁ hrange hψ hy
    exact ⟨x, rfl, (mem_weightSpace_comp_iff X₁ hinj hab hrange ψ x).mpr hy⟩
  obtain ⟨B⟩ := hC.nonempty_weightBasis
  have _ : FiniteDimensional ℂ M := FiniteDimensional.of_injective ι.toLinearMap hinj
  refine ⟨⟨fun x y => Subtype.ext (hinj ?_)⟩, ?_, ?_, ?_, ?_, ?_⟩
  · have := congrArg Subtype.val (hab.1 (comapCartanMap H ι x) (comapCartanMap H ι y))
    rw [LieSubalgebra.coe_bracket] at this
    rw [LieSubalgebra.coe_bracket, LieHom.map_lie]
    simpa using this
  · -- the weight spaces span
    rw [eq_top_iff]
    intro x _
    have hx : ι x ∈ LinearMap.ker (LieAlgebra.ad ℂ L (X₁ : L)) := by
      rw [← hrange]
      exact ⟨x, rfl⟩
    have hcoord : ∀ a ∈ (B.b.repr (ι x)).support, B.w a X₁ = 0 := by
      intro a ha
      have h1 := repr_lie_basis B.b (fun a => ⇑(B.w a)) (fun a h => (mem_weightSpace _ _).mp
        (B.mem a) h) X₁ (ι x) a
      have hx' : ⁅(X₁ : L), ι x⁆ = 0 := by simpa using LinearMap.mem_ker.mp hx
      rw [hx', map_zero, Finsupp.zero_apply] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_right (Finsupp.mem_support_iff.mp ha)
    have hsum : ι x = ∑ a ∈ (B.b.repr (ι x)).support, B.b.repr (ι x) a • B.b a := by
      conv_lhs => rw [← B.b.linearCombination_repr (ι x)]
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
    choose! m hm hmw using fun a (ha : a ∈ (B.b.repr (ι x)).support) =>
      hpre (⇑(B.w a)) (hcoord a ha) (B.b a) (B.mem a)
    have hx' : x = ∑ a ∈ (B.b.repr (ι x)).support, B.b.repr (ι x) a • m a := by
      apply hinj
      rw [map_sum]
      conv_lhs => rw [hsum]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [map_smul, hm a ha]
    rw [hx']
    refine Submodule.sum_mem _ fun a ha => Submodule.smul_mem _ _ ?_
    exact (le_iSup (fun χ : H.comap ι → ℂ => weightSpace M χ)
      (⇑(B.w a) ∘ comapCartanMap H ι)) (hmw a ha)
  · -- the zero weight space
    ext x
    change x ∈ weightSpace M (0 : H.comap ι → ℂ) ↔ ι x ∈ H
    rw [hiff]
    have h0 : (0 : H.comap ι → ℂ) ∘ φ.symm = 0 := rfl
    rw [h0]
    change ι x ∈ (weightSpace L (0 : H → ℂ) : Submodule ℂ L) ↔ ι x ∈ H
    rw [hC.weightSpace_zero]
    rfl
  · -- root spaces are lines
    intro χ h0 hb
    have hrank := hC.finrank_weightSpace _ (hne χ h0) (hbot χ hb)
    obtain ⟨x, hx, hx0⟩ := exists_ne_zero_of_weightSpace_ne_bot hb
    have hle : Module.finrank ℂ (weightSpace M χ) ≤ 1 := by
      rw [← hrank]
      refine LinearMap.finrank_le_finrank_of_injective
        (f := (ι.toLinearMap.comp (weightSpace M χ : Submodule ℂ M).subtype).codRestrict
          (weightSpace L (χ ∘ φ.symm) : Submodule ℂ L) (fun y => (hiff χ y).mp y.2)) ?_
      intro y y' hyy
      exact Subtype.ext (hinj (congrArg Subtype.val hyy))
    have hpos : 0 < Module.finrank ℂ (weightSpace M χ) :=
      Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨x, hx⟩, fun h => hx0 (congrArg Subtype.val h)⟩
    omega
  · -- `𝔰𝔩₂`-triples
    intro χ h0 hb
    obtain ⟨e, he, f, hf, h, hef, hval⟩ := hC.exists_sl2 _ (hne χ h0) (hbot χ hb)
    have hz := hzero χ hb
    obtain ⟨e', rfl, he'⟩ := hpre _ hz e he
    have hzf : (-(χ ∘ φ.symm)) X₁ = 0 := by rw [Pi.neg_apply, hz, neg_zero]
    obtain ⟨f', rfl, hf'⟩ := hpre _ hzf f hf
    refine ⟨e', by rwa [hφ χ], f', ?_, φ.symm h, ?_, ?_⟩
    · have : -χ = (-(χ ∘ φ.symm)) ∘ comapCartanMap H ι := by
        funext m
        simp only [Pi.neg_apply, Function.comp_apply]
        congr 1
        exact congrArg χ (φ.symm_apply_apply m).symm
      rwa [this]
    · apply hinj
      rw [LieHom.map_lie, hef]
      exact (congrArg Subtype.val (φ.apply_symm_apply h)).symm
    · simpa using hval
  · -- reducedness
    intro χ h0 hb c hc hcb
    refine hC.reduced _ (hne χ h0) (hbot χ hb) c hc ?_
    have := hbot (c • χ) hcb
    exact this

end Levi

end Langlands.Algebra.HarishChandra
