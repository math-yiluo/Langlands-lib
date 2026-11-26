# Traces through the stable image of an Iwahori compression

The module `Langlands.Representation.Jacquet.IwahoriContractionTrace` proves one
theorem, `Langlands.Jacquet.trace_compressedAction_mul_of_iwahoriContraction`. It
lets a trace on the fixed vectors of a compact open subgroup be computed on the
corresponding fixed space of the Jacquet coinvariants.

## Statement

Let `G` be a topological group, `ρ` a smooth complex representation of `G` on `V`,
`K` a compact open subgroup and `N`, `M`, `Nbar` subgroups with `M` normalizing
`N`. Suppose `g` satisfies the abstract Iwahori contraction conditions
`Jacquet.IsIwahoriContraction K N M Nbar g` and that `V^K` is finite dimensional.
Write `C = Jacquet.compressedAction ρ hρ K hK g`, the endomorphism
`v ↦ e_K(ρ(g)v)` of `V^K`, and

`p = Jacquet.fixedJacquetMap ρ N M hMN K : V^K → (V_N)^{K ∩ M}`

for the quotient map into the coinvariants fixed by `K ∩ M`. Let `X` be an
endomorphism of `V^K` commuting with `C`, and let `Z` be an endomorphism of
`(V_N)^{K ∩ M}` with `p(C(X x)) = Z(p x)` for every `x` in `V^K`. Then

`trace_{V^K}(C X) = trace_{(V_N)^{K ∩ M}}(Z)`.

The group and carrier universes are independent.

## Proof

The published `Jacquet.powerKernelSup_isCompl_stableImage` splits `V^K` as the
sum of the power-kernel supremum `P` of `C` and the stable image `S`, the
intersection of the ranges of the powers of `C`. Mathlib's
`LinearMap.eventually_iSup_ker_pow_eq` gives `n` with `P = ker C^n`. Because `X`
commutes with `C`, both `X` and `C` map `P` into `P` and `S` into `S`, and so
does `C X`.

The two summands form an internal direct sum indexed by `Bool`
(`DirectSum.isInternal_submodule_iff_isCompl`). Mathlib's
`LinearMap.trace_eq_sum_trace_restrict` therefore writes the trace of `C X` as
the sum of the traces of its restrictions to `P` and `S`.

- On `P`, `(C X)^n = C^n X^n` vanishes, since `X^n` preserves `P = ker C^n`. The
  restriction is nilpotent, so its trace is a nilpotent complex number
  (`LinearMap.isNilpotent_trace_of_isNilpotent`), hence zero.
- On `S`, the published `Jacquet.stableImageJacquetMap_bijective_of_iwahoriContraction`
  makes the restriction of `p` to `S` a linear equivalence `e` onto
  `(V_N)^{K ∩ M}`. The hypothesis on `Z` says that `e` conjugates the
  restriction of `C X` to `Z`. Mathlib's `LinearMap.trace_conj'` gives equality
  of the traces.

## Provenance

This is derived from the Fitting decomposition and the stable-image form of
Jacquet's lemma in the module
`Langlands.Representation.Jacquet.IwahoriContractionAdmissibility`. Those
results follow David Renard, *Représentations des groupes réductifs p-adiques*,
VI.6.1. The trace identity is an input to a compression proof of
Henniart–Lemaire, *Changement de base et induction automorphe pour GLₙ en
caractéristique non nulle*, Mém. SMF 124 (2011), I.5.3, Proposition, printed
pp. 31–32 (PDF pp. 39–40). The printed proof instead integrates over an
orbital chart, computes its Jacobian, and concludes with the lemma of I.5.2.
