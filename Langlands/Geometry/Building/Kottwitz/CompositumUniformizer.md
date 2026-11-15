# Uniformizers of composita with the maximal unramified extension

This internal helper module supplies the local-field input for the proof of
KP Corollary 11.1.9 (`inducedTorusKottwitzRationalSurjectivity`). Write `F` for a
nonarchimedean local field, `Ω = SeparableClosure F`, `K = UnramifiedClosure F`
(the inertia fixed field `LocalGalois.Separable.inertiaFixedField F`), and
`|·| = LocalGalois.Separable.sepClosureValuation F` for the spectral valuation on `Ω`.
For an intermediate field `E` of `Ω/F` it proves that the compositum `K ⊔ E` has
no more absolute values than `E`. Hence a finite extension of `K` inside
`K ⊔ E` that contains `E` has a uniformizer in `E`.

The module adds no assertion from the literature. It is a derived helper, needed
because the source treats as obvious the fact that `E·K/E` is unramified. Its
argument adapts the Library's proof of `LocalGalois.Separable.fixedFieldValuesFromBase`
(module `Langlands.Galois.Local.SeparableUnramifiedArithmeticProof`), which is
the case `E = F`.

## Declarations

All declarations are in the namespace
`Langlands.Geometry.Building.Kottwitz.CompositumUniformizer`. The module uses
the Library's local instances `localNormedField F` etc. The `NontriviallyNormedField`
instance is declared with low priority so that it does not override the given
`Field F` structure when intermediate fields are elaborated.

* `sepClosureValuation_map`: `|σ x| = |x|` for every `σ : Ω ≃ₐ[F] Ω`. Proof:
  `spectralNorm_eq_of_equiv`.
* `mem_integers_iff`: `x` lies in the valuation ring
  `extensionIntegers F Ω` iff `|x| ≤ 1`.
* `exists_value_aeval_teich`: for an intermediate field `E`, a primitive root of
  unity `ζ` of order `q^M - 1` in the integers of `Ω` (`q` the residue
  cardinality of `F`, `M > 0`), and `g ∈ E[X]` with
  `natDegree g < natDegree (minpoly E ζ)`, there is `a ∈ E` with
  `|g(ζ)| = |a|`. In fact `a` is a coefficient of `g` of largest absolute value.
* `exists_teich_of_mem_sup`: every `x ∈ K ⊔ E` lies in `E(ζ)` for such a `ζ`.
* `exists_value_of_mem_sup`: every `x ∈ K ⊔ E` has `|x| = |a|` for some `a ∈ E`.
* `exists_uniformizer_of_le_sup`: let `M : IntermediateField K Ω` be finite over
  `K`, with every element of `M` in `K ⊔ E` and `E ⊆ M`. Then some `a ∈ E` has
  `normalizedIntermediateValuation F M a = ofAdd (-1)`, so `a` is a uniformizer
  of `M`.

## Proofs

`exists_value_aeval_teich`. The zero polynomial is trivial. Otherwise choose a
coefficient `c = g_j` of maximal absolute value and put `h = c⁻¹ g`. All
coefficients of `h` are integral, so `h` lifts to `g₀` over the integers `𝔸`
of `Ω`, and `g₀` has coefficient `1` in degree `j`. Then `|h(ζ)| ≤ 1`. Suppose
`|h(ζ)| < 1`. Every root `β` of `minpoly E ζ` is `σ ζ` for some
`σ ∈ Gal(Ω/E)` (`minpoly.exists_algEquiv_of_root'`; `Ω/E` is Galois). Galois
invariance of `|·|` then gives `|h(β)| = |h(ζ)| < 1`. So the residue of `β` is a
root of the nonzero residue polynomial `H = g₀ mod 𝔪`. Two such roots are
`(q^M-1)`-th roots of unity whose residues agree, and
`eq_of_pow_eq_one_of_sub_mem` with `teichOrder_isUnit` shows they are equal.
So `H` has at least `natDegree (minpoly E ζ)` roots
(`card_rootSet_eq_natDegree`, separability and normality of `Ω/E`). That is
more than `natDegree H ≤ natDegree g`, contradicting `ncard_rootSet_le`. Hence
`|h(ζ)| = 1`, and `|g(ζ)| = |c|`.

`exists_teich_of_mem_sup`. `K ≤ F(teichSet F)` (`inertiaFixedField_le_adjoin`),
so `K ⊔ E` lies in `E(teichSet F)` (`restrictScalars_adjoin_eq_sup`). An element
lies in the adjunction of a finite subset. Finitely many Teichmüller roots have a
common order (`exists_common_teich`), so they lie in `F(ζ)` for one primitive
root `ζ` (`exists_teich`, `mem_adjoin_of_pow_eq_one`), hence in `E(ζ)`.

`exists_value_of_mem_sup` writes `x ∈ E(ζ)` with the power basis of `E(ζ)/E`
as `g(ζ)`, where `natDegree g < natDegree (minpoly E ζ)`, and applies
`exists_value_aeval_teich`.

`exists_uniformizer_of_le_sup`. The normalized valuation of `M` is surjective,
so some `z ∈ M` has value `ofAdd (-1)`. By the previous result `|z| = |a|` for
some `a ∈ E`. The normalized valuation is equivalent to the spectral valuation
(`normalizedIntermediateValuation_spec'`), so `a` has the same normalized value.
