/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules


/-!
# Tensor products of twisting sheaves on a projective spectrum

Free generators of the twisting sheaves over basic opens, and `𝒪(m) ⊗ 𝒪(n) ≅ 𝒪(m + n)`
(`AlgebraicGeometry.Proj.nonempty_tensorObj_twist_iso`).

## Implementation details

On `D₊(f)` both `𝒪(a) ⊗ 𝒪(b)` and `𝒪(a + b)` are free, with free generators `fᵃ ⊗ fᵇ` and
`fᵃ⁺ᵇ` having the same transition functions, so the two modules are isomorphic by
`Scheme.Modules.nonempty_iso_of_isFreeGenerator`.

## TODO

- Construct the canonical isomorphism sending `e^{(a)} ⊗ e^{(b)}` to `e^{(a+b)}`.
-/

@[expose] public section

noncomputable section
universe u

open CategoryTheory Opposite TopologicalSpace TopCat HomogeneousLocalization

namespace AlgebraicGeometry

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜] (m : ℤ)

namespace Proj

open ProjectiveSpectrum.Twist

section FreeGenerator

variable {𝒜 m}

/-- Sections of `𝒪(m)` restrict pointwise. -/
lemma twist_presheaf_map_apply {U V : (Proj 𝒜).Opens} (h : V ≤ U) (s : Γ(twist 𝒜 m, U))
    (x : V) : ((twist 𝒜 m).presheaf.map (homOfLE h).op s).1 x = s.1 ⟨x.1, h x.2⟩ :=
  rfl

/-- Sections of the structure sheaf act on sections of `𝒪(m)` by pointwise multiplication. -/
lemma coe_twist_smul_apply {U : (Proj 𝒜).Opens} (r : Γ(Proj 𝒜, U)) (s : Γ(twist 𝒜 m, U))
    (x : U) : ((r • s).1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
      (r.1 x).val * (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) :=
  rfl

/-- **A section of `𝒪(m)` with a pointwise inverse is a free generator**: if `ε` is a section of
`𝒪(m)` over `U` and `ε'` a section of `𝒪(-m)` over `U` with `ε ε' = 1` at every point, then every
section of `𝒪(m)` over an open `V ⊆ U` is uniquely `r • ε|_V`. -/
lemma isFreeGenerator_twist_of_mul_eq_one {U : (Proj 𝒜).Opens} (ε : Γ(twist 𝒜 m, U))
    (ε' : Γ(twist 𝒜 (-m), U))
    (h : ∀ x : U, (ε.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) * ε'.1 x = 1) :
    Scheme.Modules.IsFreeGenerator ε := by
  intro V hV
  constructor
  · intro r r' hrr
    refine Subtype.ext (funext fun x ↦ val_injective _ ?_)
    have hx := congrArg (fun s : Γ(twist 𝒜 m, V) ↦
      (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal)) hrr
    dsimp only at hx
    rw [coe_twist_smul_apply, coe_twist_smul_apply, twist_presheaf_map_apply] at hx
    have hx' := congrArg (· * (ε'.1 ⟨x.1, hV x.2⟩ :
      Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal)) hx
    dsimp only at hx'
    rwa [mul_assoc, mul_assoc, h, mul_one, mul_one] at hx'
  · intro t
    let ε'V := (twist 𝒜 (-m)).presheaf.map (homOfLE hV).op ε'
    refine ⟨sectionsZeroInv ⟨fun x ↦ ⟨t.1 x * ε'V.1 x, add_neg_cancel m ▸
      mul_mem_degreePart (t.1 x).2 (ε'V.1 x).2⟩, isLocallyFraction_mul (add_neg_cancel m) t.2
        ε'V.2⟩, ?_⟩
    refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
    rw [coe_twist_smul_apply, twist_presheaf_map_apply]
    have := zeroEquiv_sectionsZeroInv (U := Opposite.op V) ⟨fun x ↦ ⟨t.1 x * ε'V.1 x,
      add_neg_cancel m ▸ mul_mem_degreePart (t.1 x).2 (ε'V.1 x).2⟩,
        isLocallyFraction_mul (add_neg_cancel m) t.2 ε'V.2⟩ x
    have hv := congrArg Subtype.val this
    rw [degreePart.coe_zeroEquiv_apply] at hv
    rw [hv]
    change (t.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) *
      (ε'.1 ⟨x.1, hV x.2⟩ : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) *
      (ε.1 ⟨x.1, hV x.2⟩ : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) = _
    have hx := h ⟨x.1, hV x.2⟩
    rw [mul_comm] at hx
    rw [mul_assoc, hx, mul_one]

end FreeGenerator

section TensorObj

open MonoidalCategory Scheme.Modules

variable {𝒜} {f g : A}

/-- A power of a homogeneous element of degree `1` is homogeneous of degree its exponent. -/
lemma pow_mem_of_mem_one (hf : f ∈ 𝒜 1) (n : ℕ) : f ^ n ∈ 𝒜 n := by
  simpa using SetLike.pow_mem_graded n hf

/-- A power of `f` avoids every point of `D₊(f)`. -/
lemma pow_mem_primeCompl (x : Proj.basicOpen 𝒜 f) (n : ℕ) :
    f ^ n ∈ x.1.asHomogeneousIdeal.toIdeal.primeCompl :=
  fun h ↦ x.2 (x.1.isPrime.mem_of_pow_mem _ h)

variable (hf : f ∈ 𝒜 1)

/-- The value at a point of `D₊(f)` of the section `fᵐ` of `𝒪(m)`, for `f` homogeneous of
degree `1`: the fraction `f ^ m / 1` if `m ≥ 0`, and `1 / f ^ (-m)` if `m ≤ 0`. -/
def twistPowFun (x : Proj.basicOpen 𝒜 f) : fiber 𝒜 m x.1 :=
  degreePart.mk (m := m) ⟨f ^ m.toNat, pow_mem_of_mem_one hf _⟩
    ⟨f ^ (-m).toNat, pow_mem_of_mem_one hf _⟩ (pow_mem_primeCompl x _) (by omega)

/-- The section `fᵐ` of `𝒪(m)` over `D₊(f)`, for `f` homogeneous of degree `1`. -/
def twistPowSection : Γ(twist 𝒜 m, Proj.basicOpen 𝒜 f) :=
  ⟨twistPowFun m hf, isLocallyFraction_mk (by omega) ⟨f ^ m.toNat, pow_mem_of_mem_one hf _⟩
    ⟨f ^ (-m).toNat, pow_mem_of_mem_one hf _⟩ (pow_mem_primeCompl · _)⟩

/-- The value of the section `fᵐ` of `𝒪(m)` at a point of `D₊(f)`. -/
lemma val_twistPowSection_apply (x : Proj.basicOpen 𝒜 f) :
    ((twistPowSection m hf).1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
      Localization.mk (f ^ m.toNat) ⟨f ^ (-m).toNat, pow_mem_primeCompl x _⟩ :=
  degreePart.coe_mk _ _ _ (by omega)

/-- `fᵐ fⁿ = fᵐ⁺ⁿ` at every point of `D₊(f)`. -/
lemma val_twistPowSection_mul {n k : ℤ} (h : m + n = k) (x : Proj.basicOpen 𝒜 f) :
    ((twistPowSection m hf).1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) *
        (twistPowSection n hf).1 x = (twistPowSection k hf).1 x := by
  rw [val_twistPowSection_apply, val_twistPowSection_apply, val_twistPowSection_apply,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul, ← pow_add]
  congr 1
  omega

/-- `f⁰ = 1` at every point of `D₊(f)`. -/
lemma val_twistPowSection_zero (x : Proj.basicOpen 𝒜 f) :
    ((twistPowSection 0 hf).1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) = 1 := by
  rw [val_twistPowSection_apply]
  simp

/-- **The section `fᵐ` is a free generator of `𝒪(m)` on `D₊(f)`**, with inverse `f⁻ᵐ`. -/
lemma isFreeGenerator_twistPowSection : IsFreeGenerator (twistPowSection m hf) :=
  isFreeGenerator_twist_of_mul_eq_one _ (twistPowSection (-m) hf) fun x ↦
    (val_twistPowSection_mul m hf (add_neg_cancel m) x).trans (val_twistPowSection_zero hf x)

/-- If `fᵐ = c • gᵐ` and `fⁿ = d • gⁿ` on an open `W ⊆ D₊(f) ∩ D₊(g)`, then
`fᵐ⁺ⁿ = (c d) • gᵐ⁺ⁿ` on `W`. -/
lemma twistPowSection_map_eq_mul_smul (hg : g ∈ 𝒜 1) {a b : ℤ} {W : (Proj 𝒜).Opens}
    (hWf : W ≤ Proj.basicOpen 𝒜 f) (hWg : W ≤ Proj.basicOpen 𝒜 g) {c d : Γ(Proj 𝒜, W)}
    (hc : c • (twist 𝒜 a).presheaf.map (homOfLE hWg).op (twistPowSection a hg) =
      (twist 𝒜 a).presheaf.map (homOfLE hWf).op (twistPowSection a hf))
    (hd : d • (twist 𝒜 b).presheaf.map (homOfLE hWg).op (twistPowSection b hg) =
      (twist 𝒜 b).presheaf.map (homOfLE hWf).op (twistPowSection b hf)) :
    (c * d) • (twist 𝒜 (a + b)).presheaf.map (homOfLE hWg).op (twistPowSection (a + b) hg) =
      (twist 𝒜 (a + b)).presheaf.map (homOfLE hWf).op (twistPowSection (a + b) hf) := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  have hc' := congrArg (fun s : Γ(twist 𝒜 a, W) ↦
    (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal)) hc
  have hd' := congrArg (fun s : Γ(twist 𝒜 b, W) ↦
    (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal)) hd
  dsimp only at hc' hd'
  rw [coe_twist_smul_apply, twist_presheaf_map_apply, twist_presheaf_map_apply] at hc' hd'
  change ((c * d).1 x).val * ((twistPowSection (a + b) hg).1 ⟨x.1, hWg x.2⟩ :
      Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
    ((twistPowSection (a + b) hf).1 ⟨x.1, hWf x.2⟩ :
      Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal)
  rw [← val_twistPowSection_mul a hf rfl, ← val_twistPowSection_mul a hg rfl, ← hc', ← hd']
  change ((c.1 x * d.1 x)).val * _ = _
  rw [HomogeneousLocalization.val_mul]
  ring

variable (𝒜) in
/-- **Twists and tensor products**: when the basic open sets `D₊(f)` of the homogeneous elements
`f` of degree `1` cover `Proj 𝒜`, `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)`. -/
theorem nonempty_tensorObj_twist_iso (h : ∀ x : Proj 𝒜, ∃ f ∈ 𝒜 1, x ∈ Proj.basicOpen 𝒜 f)
    (a b : ℤ) : Nonempty (twist 𝒜 a ⊗ twist 𝒜 b ≅ twist 𝒜 (a + b)) := by
  let U (i : {f : A // f ∈ 𝒜 1}) : (Proj 𝒜).Opens := Proj.basicOpen 𝒜 i.1
  have hU : ⨆ i, U i = ⊤ := eq_top_iff.mpr fun x _ ↦ by
    obtain ⟨f, hf, hx⟩ := h x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, hf⟩, hx⟩
  refine (nonempty_iso_of_isFreeGenerator (M := twist 𝒜 (a + b)) hU
    (fun i ↦ isFreeGenerator_twistPowSection (a + b) i.2) (f := fun i ↦
      tmulSection (twistPowSection a i.2) (twistPowSection b i.2)) ?_
    fun i ↦ (isFreeGenerator_twistPowSection a i.2).tmulSection
      (isFreeGenerator_twistPowSection b i.2)).map Iso.symm
  rintro ⟨f, hf⟩ ⟨g, hg⟩ W hi hj α β hαβ
  obtain ⟨c, hc⟩ := ((isFreeGenerator_twistPowSection a hg).map hj).exists_smul_eq
    ((twist 𝒜 a).presheaf.map (homOfLE hi).op (twistPowSection a hf))
  obtain ⟨d, hd⟩ := ((isFreeGenerator_twistPowSection b hg).map hj).exists_smul_eq
    ((twist 𝒜 b).presheaf.map (homOfLE hi).op (twistPowSection b hf))
  have hcd := twistPowSection_map_eq_mul_smul hf hg hi hj hc hd
  have hβ : α * (c * d) = β := by
    refine ((isFreeGenerator_twistPowSection (a + b) hg).map hj).smul_left_injective ?_
    dsimp only
    rw [mul_smul, hcd]
    exact hαβ
  change α • (twist 𝒜 a ⊗ twist 𝒜 b).presheaf.map (homOfLE hi).op (tmulSection _ _) =
    β • (twist 𝒜 a ⊗ twist 𝒜 b).presheaf.map (homOfLE hj).op (tmulSection _ _)
  rw [tmulSection_map, tmulSection_map, ← hc, ← hd, smul_tmulSection, tmulSection_smul,
    smul_smul, smul_smul, ← hβ, mul_assoc]

end TensorObj

end Proj

end AlgebraicGeometry
