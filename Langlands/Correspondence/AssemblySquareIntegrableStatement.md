# Essentially square-integrable assembly images

Author: Worker 1700.

This module states one proposition, `AssemblySquareIntegrablePreimageStatement`.
It is a statement only. Nothing is proved, and no correspondence is assumed.

## Statement

`AssemblySquareIntegrablePreimageStatement F` says the following. Take any
supercuspidal map `c0`, any rank `n`, any Frobenius-semisimple Weil–Deligne
parameter class `D` of rank `n`, and any automorphic object `A` of rank `n`.
Suppose `IsAssembledFrom F c0 D (automorphicClassOf F A)` holds (see
`AssemblyRelation`) and `A.obj.representation` is essentially square-integrable
(the published `IsEssentiallySquareIntegrable` for the canonical topological
data of `F`). Then `D` is indecomposable: `IsIndecomposableParameterClass F D`
from `AssemblyLFactorStatement`, so some representative of `D` is
indecomposable in the published block sense.

The map `c0` is arbitrary. The statement assumes neither bijectivity, nor
well-definedness of the assembly, nor any L-factor property. The field and
the parameter and automorphic carrier universes `uF`, `uP`, `uA` are
independent.

## Provenance (derived)

The statement is derived from Henniart 2002, §§2.6–2.9 (printed pp. 595–596,
PDF pp. 9–10). Henniart does not state it in this form.

- §2.6: `(ρ, n) ↦ St_n(ρ)` is a bijection from supercuspidal classes times
  positive integers onto the set `A_2` of essentially square-integrable
  classes, where `St_n(ρ)` is the unique irreducible quotient of
  `i(ρ, νρ, …, ν^(n-1) ρ)` (Henniart cites Zelevinsky 1980, 9.3).
- §2.7: the extension `π_2 : G_2 → A_2` sends an indecomposable parameter
  `ρ ⊗ Sp(n)` to `St_n(π_0(ρ))`.
- §2.8: sending a nonzero multiset `π_1 + … + π_r` of elements of `A_2` to
  the Langlands quotient `J(π_1, …, π_r)` is a bijection
  `N[A_2] − {0} → A`. Singletons map to themselves, so the essentially
  square-integrable classes are exactly the images of one-element multisets.
- §2.9: the full map `π` on `G` is obtained from `π_2` through the
  decomposition of a parameter into indecomposables (2.2) and the
  classification of 2.8.

In the notation of `IsAssembledFrom`, the parameter is
`D = ⊕_i σ_i ⊗ Sp(m_i + 1)` and the class is the Langlands head of the
multisegment of the segments `[c0 σ_i, ν^(m_i) c0 σ_i]`. By 2.6 and 2.8, this
head is essentially square-integrable only if the multisegment has one
segment. Then `r = 1`, and `D` is the single block `σ_1 ⊗ Sp(m_1 + 1)` with
`σ_1` irreducible, which is indecomposable. This argument uses no property of
`c0` beyond its values being supercuspidal classes of the right rank.

## Use

This is the ingredient that Henniart's proof of Theorem 1.8 (§4.5, printed
p. 600, PDF p. 14) needs in order to test against essentially
square-integrable classes. With a bijective assembly `c`, every essentially
square-integrable class of rank `r` is `c(D')` for some `D'`, and this
statement makes `D'` indecomposable. The lower-rank L-factor hypothesis of
`AssemblyLCharacterizationStatement` is assumed only for indecomposable `D'`.
