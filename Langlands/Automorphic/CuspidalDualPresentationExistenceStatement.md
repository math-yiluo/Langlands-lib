# Spectral presentation existence for a supplied cuspidal contragredient

Author: Worker 192.

`Langlands.Automorphic.CuspidalDualPresentationExistenceStatement.{uF, uP, uQ}`
is a Prop-valued definition for a later proof. It states exactly:

```lean
∀ (F : Type uF) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  (r : ℕ) (T T' : CuspidalOperatorRealization F r),
  T'.realization.IsContragredientOf T.realization →
  CuspidalSpectralPresentation.{uF, uP} T →
  Nonempty (CuspidalSpectralPresentation.{uF, uQ} T')
```

Here `AdeleQuotient` is in `Langlands.Global`, and the other mathematical
declarations are in `Langlands.Automorphic`. The number field is arbitrary,
with the Library's explicit compactness instance for its additive adelic
quotient. The group has positive rank `r + 1`, including rank one.

The existing [cuspidal operator realization](CuspidalOperatorRealization.md)
already contains full-operator irreducibility and vanishing of actual proper
constant terms. The supplied `T'` is itself such a cuspidal realization.
The statement does not construct a contragredient realization.
The reused [contragredient relation](Contragredient.md) identifies `T'` with
the finite-smooth, infinite-compact-finite dual of `T` by a perfect complex
bilinear pairing. It retains the actual finite and compact translations and
the negative-transpose real Lie algebra action.

A supplied [spectral presentation](CuspidalSpectralPresentation.md) contains a
nonzero finite-adelic-invariant slice inside the actual finite form image, a
genuine restricted tensor presentation by bundled smooth local factors, and
almost-everywhere normalized spherical Hecke data. Its reference vectors are
nonzero and integral-fixed away from the finite tensor exceptional set.
The spectral exceptional set contains the tensor exceptional set; outside it
the existing presentation data include irreducibility, admissibility and
whole-fixed-space Hecke equations. The selected slice need not be
finite-dimensional and need not equal the full finite restriction of the
cuspidal object.

The only conclusion is that some such presentation of the supplied `T'`
exists. There is no additional conclusion relating its local factors,
exceptional sets or spectra to the supplied input presentation. In particular,
the statement adds no irreducibility or admissibility conclusion at every
finite place. The universes `uF`, `uP` and `uQ` are independent: the input and
output local-factor carriers lie in `Type uP` and `Type uQ`, respectively.
The output universe may be chosen independently even when `uQ = 0`. This is
part of the existence target, not a resizing premise. No unitarity,
irreducibility, admissibility, countable-dimension, factorization,
local-duality or universe-shrinking premise is added to the displayed
quantifiers and supplied structures.

The published
`Langlands.Automorphic.CuspidalContragredientPresentationExistenceStatement`
in [CuspidalContragredientStatement](CuspidalContragredientStatement.md)
has a `HasUnitaryCentralCharacter T` premise and concludes that an output
presentation has irreducible admissible actual local components at **every**
finite place. This statement omits that premise and that extra conclusion.
It therefore supplies the presentation-existence interface needed for a
possibly nonunitary contragredient class.

## Derived provenance and remaining proof

This is a derived interface expressing the standard principle that the
contragredient of a cuspidal automorphic representation factors as the
restricted tensor product of its local smooth duals. It is not a verbatim
quotation of any one source theorem, and the Lean file proves no such
factorization or existence assertion.

The original source passages used for this provenance were read directly:

| Source | Precise passage | Role |
| --- | --- | --- |
| D. Flath, *Decomposition of representations into tensor products* (1979), registered as `flath-1979-tensor-products` | §§2–3, printed pp.180–182, one-based PDF pp.176–178 of the retained Corvallis Part I | Restricted tensor products, Theorem 2 for irreducible admissible representations of restricted products, and Theorem 3 with its number-field `(g, K)` convention. |
| I. N. Bernstein and A. V. Zelevinsky, *Representations of the group GL(n,F) where F is a non-Archimedean local field* (1976), `bernstein-zelevinsky-1976-representations-gln` | §2.13–2.16, printed and one-based PDF pp.19–20 | The smooth part of the inverse-element algebraic dual, admissible biduality and preservation of irreducibility, and compatibility of admissible smooth duals with finite tensor products. |
| G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un corps p-adique* (2000), `henniart-2000-simple-proof` | §2.2, printed p.444, one-based PDF p.6 | Association is preserved by contragredients; this motivates the consuming class-association application rather than constructing a presentation. |

These sources do not by themselves construct the Library's actual embedded
finite slice or its normalized spectral data. A proof must compare the
supplied full-operator pairing with the restricted dual of a factorization,
separate the finite action from its infinite-factor multiplicity, realize a
nonzero finite slice in the supplied actual `T'`, and assemble the reference
vectors and almost-everywhere Hecke data. It must also realize the local
factors in the independently prescribed universe and transport all
presentation data through those equivalences. These are proof obligations
of the derived target, not additional supplied hypotheses or results proved
in this module. Local-dual compatibility with any particular pair of
presentations remains a separate assertion.
