# General-field families for Shahidi's intertwining integral

This module defines flat families in the actual general-field induction and
the scalar integrals that will be used to state rational continuation. It
proves their reading through the actual intertwining operator on its
existing convergence domain. No convergence or continuation theorem is
assumed or proved.

## Source and provenance

The original is Shahidi, *Fourier transforms of intertwining operators and
Plancherel measures for GL(n)*, Amer. J. Math. 106 (1984), 67–111,
registered as `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.
Printed page 70 fixes the integral maximal compact subgroup `K_r`; printed
page 72, equation (0.1), gives

`A(s,π,w)f(g) = ∫ f(w u' g) du'`.

The following sentence describes rational dependence on `q⁻ˢ` without
specifying how sections at different parameters are identified. As in the
published p-adic `IntertwiningStatements` interface, this module uses the
compact-picture interpretation: a flat family has parameter-independent
restriction to the integral maximal compact subgroup. This is a **derived**
interpretation, not a verbatim source definition.

Worker 99 adapted Worker 11's published p-adic family definitions and scalar
operator-reading lemma. The new definitions use the existing general
`SourceSpace`, `sourceEval`, `TargetSpace`, `targetEval` and
`intertwiningInduced`. The p-adic declarations are unchanged. The normalized
induction and its documented printed exponent issue are inherited from
`Induction`: the factor twists are `|det|^(s/2)` and `|det|^(-s/2)`.

## Objects and definitions

All declarations lie in `Langlands.Shahidi`. The definitions allow a field
`F` with a topology making it a topological ring and a real absolute value
`abv` satisfying `IsOpenNormOne abv`. Positive ranks are specified by
`hm : 0 < m` and `hn : 0 < n`. The factor representations act on arbitrary
algebraic complex modules, whose common universe is independent of the
field universe. There is no norm or topology assumption on those modules.

`generalMaximalCompact F r` is
`GeneralLinearGroup.integralSubgroup (Fin r) (valuation F).integer`.
Its elements and their inverses have all entries in the valuation ring.
The subgroup definition needs only a valued field. Its name refers to the
intended local-field application; compactness or maximality is not
asserted for a general valued field in this module.

`IsGeneralFlatFamily abv hopen hm hn π₁ π₂ f` is the Prop-valued predicate
on an actual family `f : ∀ s : ℂ, SourceSpace abv hopen hm hn s π₁ π₂`
that its evaluations at every element of `generalMaximalCompact F (m+n)`
are equal for every pair of parameters. It uses the same tensor carrier
for the values of all sections. Flatness neither asserts existence of
such families with any prescribed restriction nor assumes convergence.

For a measurable field, a measure `μ` on `n × m` matrices, an actual family
`f`, a group element `g`, and a smooth functional `ℓ` on
`pairRepresentation hm hn π₁ π₂`, `generalIntertwiningCoefficient` is

`s ↦ ∫ a, ℓ(f_s(w_(m,n) u'(a) g)) dμ(a)`.

The coordinates `a` range over the exchanged upper radical, exactly as in
`IntertwiningIntegral`. The value is an ordinary complex Bochner integral,
which is a total definition even without integrability. Its interpretation
as a pairing with the operator is claimed only under convergence. The
coefficient definition needs neither flatness nor a valuation.

## Proved operator reading

`generalIntertwiningCoefficient_eq` takes:

- smooth factor representations;
- a left-invariant measure `μ`, with measurable field addition and
  multiplication;
- `CompactOpenCofinal` for the actual two-block Levi;
- the published Jacobian law `IsModulusScaling hm hn abv μ`;
- a parameter `s` with `f s` in the actual `sourceDomain`.

Its conclusion identifies the scalar integral with
`ℓ(pairFlip.symm (targetEval (intertwiningInduced ⟨f s, hs⟩) g))`.
The tensor flip is necessary because the target values have the reversed
factor order. The implemented proof is the symmetry of the published
`intertwiningInduced_eval` specialized to `⟨f s, hs⟩`. It adds no analytic
assumption beyond those of the existing operator and does not require
flatness.

## Scope

These are general-field definitions; in particular they introduce no
characteristic-zero restriction. Analytic statements using them must impose
the local-field hypotheses, normalized absolute value and residue
cardinality, appropriate Haar choices, and irreducibility/admissibility
separately. This module does not derive local-field Levi cofinality or
normalized Haar scaling; the operator-reading lemma displays those
conditions explicitly.

There is no assertion here about existence of flat extensions, an
Iwasawa decomposition, identification of smooth induction with the
source's compact-finite model, rationality away from the maximal compact,
or a common rational denominator. Those matters are separate from these
definitions and their conditional operator reading.
