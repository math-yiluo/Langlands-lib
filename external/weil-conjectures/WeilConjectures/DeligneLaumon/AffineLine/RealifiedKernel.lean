/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.Concentration
public import WeilConjectures.DeligneLaumon.AffineLine.Defs
public import WeilConjectures.WeilSheaf.Dual
public import WeilConjectures.WeilSheaf.StalkConstantTwist
public import WeilConjectures.WeilSheaf.StalkExtensionByZero
public import WeilConjectures.WeilSheaf.StalkTensor
public import WeilConjectures.WeilSheaf.UpperStarPointwise
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.TracePow

/-!
# The realified kernel is `ι`-real

Let `j : U₀ ↪ 𝔸¹` be a dense open immersion and `M` a lisse Weil sheaf on `U₀`, punctually
`ι`-pure of weight `w`. For a unit `b` with `ι b = q ^ w` put `M† = M^∨ ⊗ 𝓑_b`. The
*realified kernel* on the Fourier square is

`𝒦 = pr₁^*(j_!M) ⊗ 𝒦_ψ ⊕ pr₁^*(j_!M†) ⊗ 𝒦_{ψ⁻¹}`.

At a closed point `z` over `x = pr₁ z ∈ U₀`, of degree `e` over `x`, the local eigenvalues of the
first summand are the `αᵉ λ`, where `α` runs through the eigenvalues of `Fₓ` on `M` and `λ` is
the eigenvalue of the Artin–Schreier kernel, of modulus one; those of the second summand are
the `(bᵐ α⁻¹)ᵉ λ⁻¹`, which are the complex conjugates since `|ι α|² = q^{m w}`. Over a point
outside `U₀` both stalks vanish. Hence the spectrum of `𝒦` at every closed point is stable
under complex conjugation: `𝒦` is `ι`-real.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.realifiedKernel`: the realified kernel.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isReal_realifiedKernel`
  (`lemma-twisted-envelope--1`): it is `ι`-real.
- `AlgebraicGeometry.WeilSheaf.exists_trace_frobeniusEnd_pow_stalk_fourierKernelTensor`: the
  traces of the local Frobenius of `𝒦_ψ ⊗ pr₁^* F` are `ψ(c) ^ (r n) tr (Fₓ ^ (e n))`.
- `WeilSheaf.IsPunctuallyPureOfWeight.map_trace_frobeniusEnd_pow_stalk_constantTwist_dual`:
  the twisted dual of a pure lisse sheaf has the conjugate traces.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **The local Frobenius of the Fourier kernel.** At a closed point `z` of the Fourier square,
the local Frobenius of `𝒦_ψ = μ^* ℒ_ψ` is multiplication by `ψ(c) ^ r`, for some `c ∈ k₀` and
`r ∈ ℕ` which do not depend on `ψ`: the stalk is a line, on which the Frobenius has the
characteristic polynomial of the `r`-th power of the local Frobenius of `ℒ_ψ` at `μ z`, which
is multiplication by `ψ(c)`
(`AlgebraicGeometry.WeilSheaf.exists_frobeniusEnd_stalk_artinSchreier`). -/
theorem exists_frobeniusEnd_stalk_fourierKernel (z : (affinePlane k₀).finitePoints) :
    ∃ (c : k₀) (r : ℕ), ∀ ψ : AddChar k₀ (PadicAlgCl l),
      ((fourierKernel ψ).stalk z).frobeniusEnd = ψ c ^ r • LinearMap.id := by
  obtain ⟨c, hc⟩ := exists_frobeniusEnd_stalk_artinSchreier (l := l) (1 : k₀)
    ⟨(affineSpacePair.pairing PUnit k₀).base z.1, Scheme.Hom.map_mem_finitePoints _ z.2⟩
  refine ⟨c, (affinePlane k₀ ↘ Spec (CommRingCat.of k₀)).degreeOver z.1 /
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).degreeOver
      ((affineSpacePair.pairing PUnit k₀).base z.1),
    fun ψ ↦ ?_⟩
  have hrank : Module.finrank (PadicAlgCl l) ((fourierKernel ψ).stalk z).carrier = 1 :=
    (finrank_stalk_upperStar _ _ z).trans (finrank_stalk_artinSchreier ψ 1 _)
  rw [LinearMap.eq_trace_smul_id_of_finrank_eq_one hrank ((fourierKernel ψ).stalk z).frobeniusEnd,
    ← pow_one ((fourierKernel ψ).stalk z).frobeniusEnd, fourierKernel,
    affineSpaceFourierKernel,
    LinearMap.trace_pow_eq_of_charpoly_eq (charpoly_frobeniusEnd_stalk_upperStar _ _ z) 1,
    pow_one, hc ψ, smul_pow, ← Module.End.one_eq_id, one_pow, map_smul, LinearMap.trace_one,
    finrank_stalk_artinSchreier, Nat.cast_one, smul_eq_mul, mul_one]

/-- **The traces of the local Frobenius of the kernel sheaf `𝒦_ψ ⊗ pr₁^* F`.** At a closed
point `z` of the Fourier square over the closed point `x = pr₁ z` of the line, the trace of the
`n`-th power of the local Frobenius of `𝒦_ψ ⊗ pr₁^* F` is `ψ(c) ^ (r n) tr (Fₓ ^ (e n))`, with
`c`, `r` and `e` independent of `ψ` and `F`: the stalk is `Hom(𝒦_ψ^∨, (pr₁^* F)_z)`
(`AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_tensorObj`), the Frobenius of the line
`(𝒦_ψ^∨)_z` is multiplication by `ψ(c) ^ (-r)`
(`AlgebraicGeometry.WeilSheaf.exists_frobeniusEnd_stalk_fourierKernel`), and the local
Frobenius of `pr₁^* F` at `z` has the characteristic polynomial of `Fₓ ^ e`. -/
theorem exists_trace_frobeniusEnd_pow_stalk_fourierKernelTensor
    (z : (affinePlane k₀).finitePoints) :
    ∃ (c : k₀) (r e : ℕ), ∀ (ψ : AddChar k₀ (PadicAlgCl l))
      (F : WeilSheaf k₀ l (affineLine k₀)) (n : ℕ),
      LinearMap.trace (PadicAlgCl l) _ (((fourierKernelTensor ψ F).stalk z).frobeniusEnd ^ n) =
        ψ c ^ (r * n) * LinearMap.trace (PadicAlgCl l) _
          ((F.stalk ⟨(affinePlane.fst k₀).base z.1,
            Scheme.Hom.map_mem_finitePoints _ z.2⟩).frobeniusEnd ^ (e * n)) := by
  obtain ⟨c, r, hc⟩ := exists_frobeniusEnd_stalk_fourierKernel (l := l) z
  refine ⟨c, r, (affinePlane k₀ ↘ Spec (CommRingCat.of k₀)).degreeOver z.1 /
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).degreeOver ((affinePlane.fst k₀).base z.1),
    fun ψ F n ↦ ?_⟩
  have hK := isLisse_fourierKernel ψ
  have hrank : Module.finrank (PadicAlgCl l) ((fourierKernel ψ).stalk z).carrier = 1 :=
    (finrank_stalk_upperStar _ _ z).trans (finrank_stalk_artinSchreier ψ 1 _)
  obtain ⟨e₁⟩ := nonempty_equiv_stalk_tensorObj hK ((upperStar (affinePlane.fst k₀)).obj F) z
  obtain ⟨e₂⟩ := nonempty_equiv_stalk_dual hK z
  have hrankD : Module.finrank (PadicAlgCl l) (((fourierKernel ψ).dual hK).stalk z).carrier =
      1 :=
    e₂.toLinearEquiv.finrank_eq.trans (Subspace.dual_finrank_eq.trans hrank)
  have hD : (((fourierKernel ψ).dual hK).stalk z).frobeniusEnd =
      (ψ c ^ r)⁻¹ • LinearMap.id := by
    refine LinearMap.ext fun x ↦ e₂.toLinearEquiv.injective ((e₂.map_frobenius x).trans ?_)
    rw [LinearMap.smul_apply, LinearMap.id_apply, map_smul, FrobeniusModule.dual_frobenius_apply]
    refine LinearMap.ext fun y ↦ ?_
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe,
      FrobeniusModule.frobenius_symm_apply_of_finrank_eq_one hrank (hc ψ), map_smul,
      LinearMap.smul_apply]
  have hne : (ψ c ^ r)⁻¹⁻¹ ≠ 0 :=
    inv_ne_zero (FrobeniusModule.ne_zero_of_frobeniusEnd_eq_smul hrankD hD)
  rw [← e₁.trace_frobeniusEnd_pow,
    ← (FrobeniusModule.linearHomEquivRescale (N := ((upperStar (affinePlane.fst k₀)).obj F).stalk z)
      hrankD hD).trace_frobeniusEnd_pow,
    FrobeniusModule.trace_frobeniusEnd_pow_rescale _ hne, inv_inv,
    LinearMap.trace_pow_eq_of_charpoly_eq (charpoly_frobeniusEnd_stalk_upperStar _ _ z) n,
    ← pow_mul, ← pow_mul]

/-- **The twisted dual of a pure sheaf has the conjugate traces.** If `G` is lisse and
punctually `ι`-pure of weight `w` and `ι b = q ^ w`, then at every closed point `x` the traces
of the powers of the local Frobenius of `G^∨ ⊗ 𝓑_b` are the complex conjugates of those of `G`:
the stalk of `G^∨ ⊗ 𝓑_b` at `x` is the dual of that of `G` with the Frobenius rescaled by
`b ^ deg x`, and `ι (b ^ deg x) = q_x ^ w`
(`FrobeniusModule.IsPureOfWeight.map_trace_frobeniusEnd_pow_rescale_dual`). -/
theorem IsPunctuallyPureOfWeight.map_trace_frobeniusEnd_pow_stalk_constantTwist_dual
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] {ι : PadicAlgCl l →+* ℂ}
    {G : WeilSheaf k₀ l X} {w : ℝ} (hG : G.IsPunctuallyPureOfWeight ι w) (hG' : G.IsLisse)
    {b : (PadicAlgCl l)ˣ} (hb : ι b = (((Nat.card k₀ : ℝ) ^ w : ℝ) : ℂ)) (x : X.finitePoints)
    (m : ℕ) :
    ι (LinearMap.trace (PadicAlgCl l) _
        ((((G.dual hG').constantTwist b).stalk x).frobeniusEnd ^ m)) =
      starRingEnd ℂ (ι (LinearMap.trace (PadicAlgCl l) _ ((G.stalk x).frobeniusEnd ^ m))) := by
  obtain ⟨e₁⟩ := (G.dual hG').nonempty_equiv_stalk_constantTwist b x
  obtain ⟨e₂⟩ := nonempty_equiv_stalk_dual hG' x
  have hq : 0 < (X ↘ Spec (CommRingCat.of k₀)).residueCard x.1 := pow_pos Nat.card_pos _
  have hc : ι ((b : PadicAlgCl l) ^ (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1) =
      ((((X ↘ Spec (CommRingCat.of k₀)).residueCard x.1 : ℝ) ^ w : ℝ) : ℂ) := by
    rw [map_pow, hb, Scheme.Hom.residueCard, Nat.cast_pow, ← Complex.ofReal_pow,
      ← Real.rpow_mul_natCast (Nat.cast_nonneg _), ← Real.rpow_natCast_mul (Nat.cast_nonneg _),
      mul_comm]
  rw [← e₁.trace_frobeniusEnd_pow, ← (e₂.rescale _).trace_frobeniusEnd_pow]
  exact (hG x).map_trace_frobeniusEnd_pow_rescale_dual hq hc m

end AlgebraicGeometry.WeilSheaf

namespace AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen

attribute [local instance] Abelian.hasFiniteBiproducts

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The *twisted dual* `M† = M^∨ ⊗ 𝓑_b` of the lisse sheaf `M` of `D`, as a datum on the same
dense open. -/
noncomputable def twistedDual (D : LisseOnDenseOpen k₀ l) (b : (PadicAlgCl l)ˣ) :
    LisseOnDenseOpen k₀ l :=
  { D with
    sheaf := (D.sheaf.dual D.lisse).constantTwist b
    lisse := isLisse_constantTwist.2 (D.lisse.dual) }

/-- The *realified kernel* `pr₁^*(j_!M) ⊗ 𝒦_ψ ⊕ pr₁^*(j_!M†) ⊗ 𝒦_{ψ⁻¹}` on the Fourier square,
`M† = M^∨ ⊗ 𝓑_b` being the twisted dual. (blueprint: `lemma-twisted-envelope--1`) -/
noncomputable def realifiedKernel (ψ : AddChar k₀ (PadicAlgCl l)) (D : LisseOnDenseOpen k₀ l)
    (b : (PadicAlgCl l)ˣ) : WeilSheaf k₀ l (affinePlane k₀) :=
  fourierKernelTensor ψ D.extensionByZero ⊞
    fourierKernelTensor ψ⁻¹ (D.twistedDual b).extensionByZero

/-- **The twisted dual has the conjugate traces.** If `M` is punctually `ι`-pure of weight `w`
and `ι b = q ^ w`, then at every closed point `x` of the line the traces of the powers of the
local Frobenius of `j_!M† = j_!(M^∨ ⊗ 𝓑_b)` are the complex conjugates of those of `j_!M`.
(blueprint: `lemma-twisted-envelope--1`, step 1) -/
theorem map_trace_frobeniusEnd_pow_stalk_extensionByZero_twistedDual
    (ι : PadicAlgCl l →+* ℂ) (D : LisseOnDenseOpen k₀ l) {w : ℝ}
    (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) {b : (PadicAlgCl l)ˣ}
    (hb : ι b = (((Nat.card k₀ : ℝ) ^ w : ℝ) : ℂ)) (x : (affineLine k₀).finitePoints) (m : ℕ) :
    ι (LinearMap.trace (PadicAlgCl l) _
        (((D.twistedDual b).extensionByZero.stalk x).frobeniusEnd ^ m)) =
      starRingEnd ℂ (ι (LinearMap.trace (PadicAlgCl l) _
        ((D.extensionByZero.stalk x).frobeniusEnd ^ m))) := by
  by_cases hx : x.1 ∈ Set.range D.j.base
  · obtain ⟨z, hz⟩ := hx
    have hz' : z ∈ D.U.finitePoints :=
      (Scheme.Hom.mem_finitePoints_iff_of_isIso D.j z).1 (hz ▸ x.2)
    obtain rfl : x = ⟨D.j.base z, (Scheme.Hom.mem_finitePoints_iff_of_isIso D.j z).2 hz'⟩ :=
      Subtype.ext hz.symm
    obtain ⟨e₁⟩ : Nonempty ((D.extensionByZero.stalk ⟨D.j.base z, _⟩).Equiv
        (D.sheaf.stalk ⟨z, hz'⟩)) :=
      nonempty_equiv_stalk_extensionByZero D.j D.sheaf ⟨z, hz'⟩
    obtain ⟨e₂⟩ : Nonempty (((D.twistedDual b).extensionByZero.stalk ⟨D.j.base z, _⟩).Equiv
        ((D.twistedDual b).sheaf.stalk ⟨z, hz'⟩)) :=
      nonempty_equiv_stalk_extensionByZero (D.twistedDual b).j (D.twistedDual b).sheaf ⟨z, hz'⟩
    rw [← e₁.trace_frobeniusEnd_pow, ← e₂.trace_frobeniusEnd_pow]
    exact hw.map_trace_frobeniusEnd_pow_stalk_constantTwist_dual D.lisse hb ⟨z, hz'⟩ m
  · have : Subsingleton (D.extensionByZero.stalk x).carrier :=
      subsingleton_stalk_extensionByZero D.j D.sheaf x hx
    have : Subsingleton ((D.twistedDual b).extensionByZero.stalk x).carrier :=
      subsingleton_stalk_extensionByZero (D.twistedDual b).j (D.twistedDual b).sheaf x hx
    rw [FrobeniusModule.trace_frobeniusEnd_pow_eq_zero_of_subsingleton,
      FrobeniusModule.trace_frobeniusEnd_pow_eq_zero_of_subsingleton, map_zero, map_zero]

/-- **The realified kernel is `ι`-real.** If `M` is punctually `ι`-pure of weight `w` and
`ι b = q ^ w`, then the realified kernel `pr₁^*(j_!M) ⊗ 𝒦_ψ ⊕ pr₁^*(j_!M†) ⊗ 𝒦_{ψ⁻¹}` is
`ι`-real: at every closed point its local eigenvalues are stable under complex conjugation.
Only the purity of `M` is used. (blueprint: `lemma-twisted-envelope--1`) -/
theorem isReal_realifiedKernel (ψ : AddChar k₀ (PadicAlgCl l)) (ι : PadicAlgCl l →+* ℂ)
    (D : LisseOnDenseOpen k₀ l) {w : ℝ} (hw : D.sheaf.IsPunctuallyPureOfWeight ι w)
    {b : (PadicAlgCl l)ˣ} (hb : ι b = (((Nat.card k₀ : ℝ) ^ w : ℝ) : ℂ)) :
    (realifiedKernel ψ D b).IsReal ι := by
  intro z
  obtain ⟨c, r, e, h⟩ := exists_trace_frobeniusEnd_pow_stalk_fourierKernelTensor (l := l) z
  obtain ⟨eb⟩ := nonempty_equiv_stalk_biprod (fourierKernelTensor ψ D.extensionByZero)
    (fourierKernelTensor ψ⁻¹ (D.twistedDual b).extensionByZero) z
  refine FrobeniusModule.IsReal.of_localPolynomial_eq
    (FrobeniusModule.isReal_prod_of_map_trace_frobeniusEnd_pow fun n ↦ ?_) eb.localPolynomial_eq
  rw [h, h, map_mul, map_mul, map_mul, map_pow ι, map_pow ι, map_pow (starRingEnd ℂ),
    AddChar.inv_apply', map_inv₀,
    Complex.inv_eq_conj (AddChar.norm_map_apply_eq_one ψ ι c),
    map_trace_frobeniusEnd_pow_stalk_extensionByZero_twistedDual ι D hw hb]

end AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen
