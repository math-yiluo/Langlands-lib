/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.Purity
public import WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy
public import WeilConjectures.WeilSheaf.FourierPlancherel

/-!
# The weight of the Fourier partner

Let `M` be a nonzero lisse Weil sheaf on a dense open `j : U₀ ↪ 𝔸¹_{k₀}`, punctually `ι`-pure of
weight `w`, and suppose that the Fourier transform of its middle extension is a middle extension,
`FT_ψ((j_*M)[1]) ≅ (j'_*M')[1]`, with `M'` lisse on a dense open `j' : U'₀ ↪ 𝔸¹_{k₀}` and
punctually `ι`-pure of weight `v`. Then `v = w + 1`.

The proof goes through the `L²`-weight parameter `‖K‖` of a Weil complex, the exponent of growth
of its trace energies `‖f_K‖²_m = ∑_{x ∈ 𝔸¹(𝔽_{qᵐ})} |ι t_K(x)|²`
(`AlgebraicGeometry.WeilComplex.l2Weight`):

* the Plancherel identity `‖f_{FT_ψ(K)}‖²_m = qᵐ ‖f_K‖²_m` gives `‖FT_ψ(K)‖ = ‖K‖ + 1`
  (`AlgebraicGeometry.WeilComplex.l2Weight_fourierTransform`);
* the shift `[1]` only changes the sign of the trace function, so `‖(j_*M)[1]‖ = ‖j_*M‖`;
* the middle extension does not change the `L²`-weight of a pure lisse sheaf, and the
  `L²`-weight of a nonzero pure lisse sheaf is its weight:
  `‖j_*M‖ = ‖M‖ = w` (`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.l2Weight_directImage`).

Hence `v = ‖j'_*M'‖ = ‖FT_ψ((j_*M)[1])‖ = ‖j_*M‖ + 1 = w + 1`. The sheaf `M'` is automatically
nonzero: otherwise `‖j'_*M'‖ = -∞`. The geometric input on the dense opens (affine, smooth
geometrically connected curves) is `WeilConjectures.DeligneLaumon.AffineLine.DenseOpen`.

## Main statements

- `AlgebraicGeometry.WeilComplex.l2Weight_fourierTransform`: `‖FT_ψ(K)‖ = ‖K‖ + 1`.
- `AlgebraicGeometry.eq_add_one_of_isFourierPartner`: `v = w + 1`.
- `AlgebraicGeometry.isPunctuallyPureOfWeight_add_one_of_isFourierPartner`: the Fourier partner of
  an irreducible nonexceptional sheaf pure of weight `w` is pure of weight `w + 1`.
- `AlgebraicGeometry.le_add_one_of_isFourierPartner`: the weight of the Fourier partner is at
  most `w + 1`.
-/

@[expose] public section

universe u

open CategoryTheory Filter

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilComplex

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The *`L²`-weight parameter* `‖K‖` of a Weil complex, the exponent of growth of its trace
energies `S_m = ‖f_K‖²_m` (`AlgebraicGeometry.WeilComplex.traceEnergy`):

`‖K‖ = sup {β ∈ ℝ | limsup_{m → ∞} S_m / q^{m(β + 1)} > 0}`,

the supremum of the empty set being `-∞`, the exponent `1` being the dimension of the curve on
which `K` is intended to live. The `limsup` is taken in `ℝ≥0∞`. This is the same formula as for
Weil sheaves, `AlgebraicGeometry.WeilSheaf.l2Weight`. (blueprint:
`definition-growth-squared-traces`) -/
noncomputable def l2Weight (ι : PadicAlgCl l →+* ℂ) (K : WeilComplex k₀ l X) : EReal :=
  ⨆ (β : ℝ) (_ : 0 < limsup (fun m : ℕ ↦ ENNReal.ofReal
    (K.traceEnergy ι m / (Nat.card k₀ : ℝ) ^ ((m : ℝ) * (β + 1)))) atTop), (β : EReal)

/-- Isomorphic Weil complexes have the same `L²`-weight. -/
theorem l2Weight_congr (ι : PadicAlgCl l →+* ℂ) {K L : WeilComplex k₀ l X} (e : K ≅ L) :
    K.l2Weight ι = L.l2Weight ι := by
  simp only [l2Weight, traceEnergy_congr ι e]

end WeilComplex

namespace WeilSheaf

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The trace energy of a Weil sheaf placed in degree `0` is that of the sheaf. -/
theorem traceEnergy_toComplex (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) (n : ℕ) :
    (toComplex.obj F).traceEnergy ι n = F.traceEnergy ι n := by
  simp only [WeilComplex.traceEnergy, traceEnergy, WeilComplex.traceFunction_toComplex]

/-- The `L²`-weight of a Weil sheaf placed in degree `0` is that of the sheaf. -/
theorem l2Weight_toComplex (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) :
    (toComplex.obj F).l2Weight ι = F.l2Weight ι := by
  simp only [WeilComplex.l2Weight, l2Weight, traceEnergy_toComplex]

/-- The trace energy of a Weil sheaf placed in degree `0` and shifted by one is that of the
sheaf: the shift only changes the sign of the trace function. -/
theorem traceEnergy_shift_toComplex (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) (n : ℕ) :
    ((toComplex.obj F)⟦(1 : ℤ)⟧).traceEnergy ι n = F.traceEnergy ι n := by
  simp only [WeilComplex.traceEnergy, traceEnergy, traceFunction_shift_toComplex, map_neg,
    norm_neg]

/-- The `L²`-weight of a Weil sheaf placed in degree `0` and shifted by one is that of the
sheaf. -/
theorem l2Weight_shift_toComplex (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) :
    ((toComplex.obj F)⟦(1 : ℤ)⟧).l2Weight ι = F.l2Weight ι := by
  simp only [WeilComplex.l2Weight, l2Weight, traceEnergy_shift_toComplex]

/-- The `L²`-weight of a zero Weil sheaf is `-∞`: its trace energies vanish. -/
theorem l2Weight_eq_bot_of_isZero (ι : PadicAlgCl l →+* ℂ) {F : WeilSheaf k₀ l X}
    (hF : Limits.IsZero F) : F.l2Weight ι = ⊥ := by
  refine le_bot_iff.1 (iSup₂_le fun β hβ ↦ ?_)
  simp [traceEnergy, traceFunction_eq_zero_of_isZero _ hF] at hβ

end WeilSheaf

namespace WeilComplex

/-- *The `L²`-weight shifts by one under the Fourier transform*: for a nontrivial `ψ` and a Weil
complex `K` on the affine line, `‖FT_ψ(K)‖ = ‖K‖ + 1`. By the Plancherel identity
`AlgebraicGeometry.WeilComplex.traceEnergy_fourierTransform`, the defining ratio of `FT_ψ(K)` at
`β` agrees with that of `K` at `β - 1` for every `m ≥ 1`, hence has the same `limsup`.
(blueprint: `corollary-plancherel--2`) -/
theorem l2Weight_fourierTransform (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1)
    (ι : PadicAlgCl l →+* ℂ) (K : WeilComplex k₀ l (affineLine k₀)) :
    ((fourierTransform ψ).obj K).l2Weight ι = K.l2Weight ι + 1 := by
  have hq0 : 0 < (Nat.card k₀ : ℝ) := by exact_mod_cast Nat.card_pos
  have key (β : ℝ) : limsup (fun m : ℕ ↦ ENNReal.ofReal
      (((fourierTransform ψ).obj K).traceEnergy ι m / (Nat.card k₀ : ℝ) ^ ((m : ℝ) * (β + 1))))
        atTop = limsup (fun m : ℕ ↦ ENNReal.ofReal
      (K.traceEnergy ι m / (Nat.card k₀ : ℝ) ^ ((m : ℝ) * ((β - 1) + 1)))) atTop := by
    refine limsup_congr (eventually_atTop.2 ⟨1, fun m hm ↦ congrArg ENNReal.ofReal ?_⟩)
    rw [traceEnergy_fourierTransform ψ hψ ι K hm, sub_add_cancel, mul_add, mul_one,
      Real.rpow_add hq0, Real.rpow_natCast]
    field_simp
  have h1 : ((1 : ℝ) : EReal) = 1 := rfl
  refine le_antisymm (iSup₂_le fun β hβ ↦ ?_) ?_
  · rw [key] at hβ
    calc (β : EReal) = ((β - 1 : ℝ) : EReal) + (1 : ℝ) := by norm_cast; ring
      _ ≤ K.l2Weight ι + 1 := by
        rw [h1]
        gcongr
        exact le_iSup₂_of_le (f := fun (γ : ℝ) _ ↦ (γ : EReal)) (β - 1) hβ le_rfl
  · rw [← h1, ← EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot 1)) (.inl (EReal.coe_ne_top 1))]
    refine iSup₂_le fun γ hγ ↦ ?_
    rw [EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot 1)) (.inl (EReal.coe_ne_top 1))]
    have hγ' : 0 < limsup (fun m : ℕ ↦ ENNReal.ofReal
        (((fourierTransform ψ).obj K).traceEnergy ι m /
          (Nat.card k₀ : ℝ) ^ ((m : ℝ) * ((γ + 1) + 1)))) atTop := by
      rwa [key, add_sub_cancel_right]
    exact_mod_cast le_iSup₂_of_le (f := fun (β : ℝ) _ ↦ (β : EReal)) (γ + 1) hγ' le_rfl

end WeilComplex

namespace WeilSheaf.LisseOnDenseOpen

/-- The `L²`-weight of the Fourier transform of the middle extension `(j_*M)[1]` of a nonzero
lisse sheaf `M`, punctually `ι`-pure of weight `w`, is `w + 1`. -/
theorem l2Weight_fourierTransform_middleExtension (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1)
    (ι : PadicAlgCl l →+* ℂ) (D : LisseOnDenseOpen k₀ l) (hM : ¬ Limits.IsZero D.sheaf) {w : ℝ}
    (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) :
    ((fourierTransform ψ).obj D.middleExtension).l2Weight ι = (w : EReal) + 1 := by
  obtain ⟨h1, h2⟩ := D.l2Weight_directImage ι hM hw
  rw [WeilComplex.l2Weight_fourierTransform ψ hψ, middleExtension, l2Weight_shift_toComplex, h1,
    h2]

end WeilSheaf.LisseOnDenseOpen

variable (ψ : AddChar k₀ (PadicAlgCl l))

/-- *Plancherel for a middle extension*: let `M` be a nonzero lisse sheaf on a dense open
`j : U₀ ↪ 𝔸¹_{k₀}`, punctually `ι`-pure of weight `w`, whose middle extension has a Fourier
partner `FT_ψ((j_*M)[1]) ≅ (j'_*M')[1]` with `M'` punctually `ι`-pure of weight `v`. Then
`v = w + 1`.

Both sides of the isomorphism have the same `L²`-weight; that of the transform is
`‖j_*M‖ + 1 = w + 1`, and that of `(j'_*M')[1]` is `‖j'_*M'‖ = v`. The sheaf `M'` is nonzero,
since otherwise `‖j'_*M'‖ = -∞`. The nonvanishing of `M`, implicit in the blueprint, is needed:
the zero sheaf is pure of every weight. (blueprint: `theorem-weight-fourier-transform`) -/
theorem eq_add_one_of_isFourierPartner (ι : PadicAlgCl l →+* ℂ) (hψ : ψ ≠ 1)
    (D D' : WeilSheaf.LisseOnDenseOpen k₀ l) (hM : ¬ Limits.IsZero D.sheaf) {w v : ℝ}
    (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) (hFT : D.IsFourierPartner ψ D')
    (hv : D'.sheaf.IsPunctuallyPureOfWeight ι v) :
    v = w + 1 := by
  obtain ⟨e⟩ := hFT
  have h := (WeilComplex.l2Weight_congr ι e).symm.trans
    (D.l2Weight_fourierTransform_middleExtension ψ hψ ι hM hw)
  rw [WeilSheaf.LisseOnDenseOpen.middleExtension, WeilSheaf.l2Weight_shift_toComplex] at h
  have hM' : ¬ Limits.IsZero D'.sheaf := fun h0 ↦ by
    rw [WeilSheaf.l2Weight_eq_bot_of_isZero (F := D'.directImage) ι
      ((WeilSheaf.directImage D'.j).map_isZero h0)] at h
    exact EReal.bot_ne_coe (w + 1) (h.trans (by norm_cast))
  obtain ⟨h1, h2⟩ := D'.l2Weight_directImage ι hM' hv
  rw [h1, h2] at h
  exact_mod_cast h

/-- The sheaf `M'` of a Fourier partner of a nonzero irreducible nonexceptional lisse sheaf `M`,
punctually `ι`-pure of weight `w`, is punctually `ι`-pure of weight exactly `w + 1`: it is pure of
some weight `v` by `AlgebraicGeometry.exists_isPunctuallyPureOfWeight_of_isFourierPartner`, and
`v = w + 1` by `AlgebraicGeometry.eq_add_one_of_isFourierPartner`.
(blueprint: `theorem-weight-fourier-transform`) -/
theorem isPunctuallyPureOfWeight_add_one_of_isFourierPartner (ι : PadicAlgCl l →+* ℂ)
    (hψ : ψ ≠ 1) (D D' : WeilSheaf.LisseOnDenseOpen k₀ l)
    (hD : D.sheaf.IsIrreducibleLisse)
    (hne : D.sheaf.IsNonexceptional ψ D.j) {w : ℝ}
    (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) (hFT : D.IsFourierPartner ψ D') :
    D'.sheaf.IsPunctuallyPureOfWeight ι (w + 1) := by
  obtain ⟨v, hv⟩ := exists_isPunctuallyPureOfWeight_of_isFourierPartner ψ ι hψ D D' hD hne hw hFT
  rwa [← eq_add_one_of_isFourierPartner ψ ι hψ D D' hD.2.1 hw hFT hv]

/-- If `M` is irreducible, nonexceptional and punctually `ι`-pure of weight `w`, and `ψ` is
nontrivial, then the transform of `(j_*M)[1]` is a middle extension `(j'_*M')[1]` with `M'`
irreducible and punctually `ι`-pure of weight `w + 1`.
(blueprint: `theorem-weight-fourier-transform`) -/
theorem exists_isFourierPartner_isPunctuallyPureOfWeight_add_one (ι : PadicAlgCl l →+* ℂ)
    (hψ : ψ ≠ 1) (D : WeilSheaf.LisseOnDenseOpen k₀ l) (hD : D.sheaf.IsIrreducibleLisse)
    (hne : D.sheaf.IsNonexceptional ψ D.j) {w : ℝ} (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) :
    ∃ D' : WeilSheaf.LisseOnDenseOpen k₀ l, D'.sheaf.IsIrreducibleLisse ∧
      D.IsFourierPartner ψ D' ∧ D'.sheaf.IsPunctuallyPureOfWeight ι (w + 1) := by
  obtain ⟨D', hD', hFT⟩ := exists_middleExtension_fourierTransform ψ hψ D hD hne
  exact ⟨D', hD', hFT,
    isPunctuallyPureOfWeight_add_one_of_isFourierPartner ψ ι hψ D D' hD hne hw hFT⟩

-- the nonexceptionality hypothesis is not needed for the bound
set_option linter.unusedVariables false in
/-- If `M` is irreducible, nonexceptional and pure of weight `w`, `ψ` is nontrivial, and the
sheaf `M'` of the Fourier partner of `M` is pure of weight `v`, then `v ≤ w + 1`; in fact
`v = w + 1` by `AlgebraicGeometry.eq_add_one_of_isFourierPartner`.
(blueprint: `theorem-weight-fourier-transform`) -/
theorem le_add_one_of_isFourierPartner (ι : PadicAlgCl l →+* ℂ) (hψ : ψ ≠ 1)
    (D D' : WeilSheaf.LisseOnDenseOpen k₀ l)
    (hD : D.sheaf.IsIrreducibleLisse)
    (hne : D.sheaf.IsNonexceptional ψ D.j) {w v : ℝ}
    (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) (hFT : D.IsFourierPartner ψ D')
    (hv : D'.sheaf.IsPunctuallyPureOfWeight ι v) :
    v ≤ w + 1 :=
  (eq_add_one_of_isFourierPartner ψ ι hψ D D' hD.2.1 hw hFT hv).le

end AlgebraicGeometry
