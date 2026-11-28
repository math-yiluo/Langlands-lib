# A supercuspidal selection test for `GL_{m+1}` over a local field

Lean module: `Langlands.Representation.AffineGeneric.SelectionTest`, namespace
`Langlands.AffineGeneric`.

Let `F` be a nonarchimedean local field with finite residue field `k`, `ϖ : Fˣ`, `ψ` a
complex additive character of `k` and `A ∈ k`. Write `f_{ψ,r} = affineGenericTest ϖ ψ r` for
the test function `1_{I⁺} · ψ(λ_r)` of `Langlands.Representation.AffineGeneric.TestFunction`.
Write `aᵢ(Y) = coord ϖ Y i`, `D(g) = coordProd ϖ g = ∏ᵢ aᵢ(g - 1)` and
`Kl = kloosterman ψ (m + 1) A`.

## Elements of `I⁺` with prescribed coordinates

- `exists_mem_groupCoord_eq`: for a uniformizer `ϖ` and every `a : Fin (m + 1) → k` there is
  `γ ∈ I⁺` with `groupCoord ϖ γ i = aᵢ` for all `i`. Take `γ = 1 + Y`, where `Y` has entries
  `(weight ϖ i)⁻¹ cᵢ` at `(i, ρ i)` and `0` elsewhere, with `cᵢ` an integral lift of `aᵢ`; then
  `Y ∈ 𝔓` and `exists_mem_iwahoriRadical_coe_eq` applies.
- `isLocallyConstant_coordProd`: `D` is locally constant on `GL_{m+1}(F)`.

## The averaged test function

- `normOneTuples m`: the finite set of `r : Fin (m + 1) → k` with `r₁ ⋯ r_{m+1} = 1`;
  `ne_zero_of_mem_normOneTuples`: all entries of such `r` are nonzero.
- `selectionTest ϖ ψ A = Kl⁻¹ • Σ_{r ∈ normOneTuples m} f_{ψ,r}`, an element of
  `SchwartzBruhat (GeneralLinear (m + 1) F)`; `selectionTest_apply` gives its values.
- `selectionTest_apply_of_not_mem`: it vanishes off `I⁺`.
- `selectionTest_apply_of_mem`: if `Kl ≠ 0`, `A ≠ 0`, `g ∈ I⁺` and `D(g) = A`, then
  `selectionTest ϖ ψ A g = 1`. All coordinates of `g` are nonzero since their product is `A`,
  and `sum_prod_eq_one` gives `Σ_{r} ψ(Σᵢ rᵢ aᵢ(g - 1)) = Kl`.
- `affineGenericTest_one_of_mem`, `affineGenericTest_one_of_not_mem`: for the trivial
  character and `r = 0`, `affineGenericTest ϖ 1 0` is the indicator function of `I⁺`.

## The three properties

Assume `ϖ` is a uniformizer.

- `hasVanishingConstantTerms_selectionTest`: if `ψ ≠ 1`, `selectionTest ϖ ψ A` has vanishing
  constant terms, by `hasVanishingConstantTerms_testFunction` for each `r ∈ normOneTuples m`,
  `hasVanishingConstantTerms_sum` and `HasVanishingConstantTerms.const_mul`.
- `isSupercuspidal_of_distribution_selectionTest_ne_zero`: if `ψ ≠ 1` and the distribution
  character `Character.distribution μ π hπ` of an irreducible admissible `π` does not vanish at
  `selectionTest ϖ ψ A`, then `π` is supercuspidal. The distribution character is linear, so
  it does not vanish at some `f_{ψ,r}` with `r ∈ normOneTuples m`, and
  `isSupercuspidal_of_distribution_ne_zero` applies.
- `isOpen_selectionSet`, `selectionSet_nonempty`: the set `U = {γ ∈ I⁺ | D(γ) = A}` is open
  (`I⁺` is open and `D` is locally constant) and nonempty (`exists_mem_groupCoord_eq` with
  coordinates `(A, 1, …, 1)`).
- `orbitalIntegral_selectionTest_ne_zero`: if `F` has characteristic zero, `Kl ≠ 0`, `A ≠ 0` and
  `γ ∈ U`, then `orbitalIntegral γ νγ (selectionTest ϖ ψ A) ≠ 0` for every Haar measure `μ` on
  `GL_{m+1}(F)` with its Borel σ-algebra, every right-invariant Haar measure `μγ` on the
  centralizer `glCentralizer γ` and every quotient measure `νγ` compatible with them
  (`IsCompatible`).

**Proof of orbital nonvanishing.** `γ` is regular semisimple by
`isRegularSemisimple_of_coordProd_ne_zero`, since `D(γ) = A ≠ 0`. For every `x`, if
`x⁻¹ γ x ∈ I⁺`, then `D(x⁻¹ γ x) = D(γ) = A` (`coordProd_conj`), so `selectionTest` takes the
value `1` there (`selectionTest_apply_of_mem`); otherwise it takes the value `0`. Hence
`selectionTest ϖ ψ A (x⁻¹ γ x) = 1_{I⁺}(x⁻¹ γ x)` for all `x`. The two orbit functions on
`G_γ \ G` agree (`twistedOrbitFunction_mk`), so the orbital integral of `selectionTest ϖ ψ A`
at `γ` equals that of the indicator function `affineGenericTest ϖ 1 0` of `I⁺`. That function is
nonnegative and equals `1` at `γ`, so its orbital integral is positive by
`Langlands.BaseChange.orbitalIntegralPositivity`.

## The general theorem

`exists_supercuspidalSelectionTest F m`: for a nonarchimedean local field `F` of characteristic
zero, with `GL_{m+1}(F)` given its Borel σ-algebra and the Hausdorff, locally compact and totally
disconnected structures `LocalFieldTopology.generalLinear_t2Space`,
`generalLinear_locallyCompactSpace` and `generalLinear_totallyDisconnectedSpace`, there is
`φ ∈ C_c^∞(GL_{m+1}(F))` such that

1. `φ` has vanishing constant terms;
2. every irreducible admissible representation (carrier in `Type uW`) whose distribution
   character does not vanish at `φ` for some Haar measure is supercuspidal;
3. there is a nonempty open `U ⊆ GL_{m+1}(F)` such that the orbital integral of `φ` at every
   `γ ∈ U` is nonzero for every Haar measure on `GL_{m+1}(F)`, every right Haar measure on the
   centralizer of `γ` and every compatible quotient measure.

The proof chooses a uniformizer (`Iwasawa.exists_isUniformizingElement`), a nontrivial
character `ψ` of the finite residue field (`exists_addChar_ne_one`) and `A ≠ 0` with
`Kl_{m+1}(ψ, A) ≠ 0` (`exists_kloosterman_ne_zero`), and takes `φ = selectionTest ϖ ψ A` and
`U = {γ ∈ I⁺ | D(γ) = A}`.

## Origin

`exists_supercuspidalSelectionTest` is the content of
`Langlands.TraceFormula.GeneralLinearSupercuspidalSelectionTestStatement` for an arbitrary
nonarchimedean local field of characteristic zero; the Markdown page of that statement
(`Langlands/TraceFormula/GeneralLinearLocalSelectionTestStatement.md`) gives its sources.
The proof uses a uniformizer `ϖ` and a nontrivial additive character `ψ`. Every
`r ∈ normOneTuples m` has nonzero entries, so for `m ≥ 1` each `ψ ∘ λ_r` is an affine generic
character of `I⁺`. See [Genericity](Genericity.md#origin) for the source formulas. For `m = 0`
the only tuple is `r = (1)` and `λ_r(g) = res(ϖ⁻¹ (g - 1))` on `I⁺ = 1 + 𝔭`, the
principal-unit homomorphism to `k`.
