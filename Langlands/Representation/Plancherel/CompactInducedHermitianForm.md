# Actual normalized induced forms with compact Haar probability

This module constructs an invariant positive Hermitian form on the actual
normalized induced representation by integrating the inducing form against
the existing Haar probability on a supplied compact open subgroup `K`.
It uses the same literal measure as compact normalized-induction duality and
coefficients, and proves the form's integral formula with spherical Haar
probability as well. It also proves positive rescaling and equivariant
pullback compatibility.

## Source and provenance

The source conventions are Waldspurger, *La formule de Plancherel pour les
groupes p-adiques (d'après Harish-Chandra)* (2003): I.1, printed p.240 /
PDF p.6, fixes Haar normalizations on compact intersections and the actual
`G = P K` decomposition; V.2, printed p.293 / PDF p.59, the paragraph before
Lemma V.2.2, integrates a positive Hermitian inducing form to obtain the
induced form. The first argument is conjugate-linear.

This is a derived construction from the existing positive integration
constructor, the existing `CompactInduction.measure` with its proved
`measure_scalar` law, the actual normalized pairing covariance, and the
proved equality `measure_eq_normalizedHaar`. No scalar right-invariance or
normalization identity is added as an analytic input.

The earlier `Aubert.General.compactQuotientNormalizedInductionForm` selects
an arbitrary Bruhat measure. This module constructs a distinct form using
explicit compact Haar probability. It neither identifies those measures nor
silently replaces the earlier form. The choice is explicit in the definition
and every computation theorem. Comparisons between the arbitrary Bruhat and
compact-normalized forms remain separate.

## Hypotheses and actual objects

`G : Type uG` is a locally compact, second countable nonarchimedean topological
group with a Borel measurable space. This module needs no additional
Hausdorff assumption. The actual subgroups `P`, `M`, `U` have a supplied
`h : IsSemidirectDecomposition P M U`; `P` and `U` are closed and `P` is
locally compact. The ambient modular character is trivial, and the full
modular character of `P` equals
`HaarModulus.closedRestrictCharacter U hU P h.le_normalizer` for every
`q : P`.

`K : OpenSubgroup G` has compact underlying set, and the actual decomposition
is supplied in the form

```lean
∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k.
```

The theorem does not realize these geometric facts for reductive rational
points or identify a supplied `K` with the source's special compact subgroup.
It requires no continuity of the Levi projection. Compactness of `P \ G`
is not a further input; the actual `P K` decomposition is used directly.

The inducing object is `A : SmoothRep.{0, uG, uV} ℂ M` with an actual
`InvariantPositiveForm A.representation`. Neither admissibility,
irreducibility, compact-open cofinality on `M`, finite length nor global finite
dimension is assumed. The group and original carrier universes are
independent. The original complex carrier has no norm, topology or completion.
The pullback comparison allows a second carrier universe `uW` independent of
both `uG` and `uV`.

## Scalar law for the actual pairings

All declarations are in `Langlands.Plancherel.CompactInduction`.
`hermitianPairing_scalar` proves integrability and right-translation
invariance of

```text
k ↦ b.inner (f(k g)) (j(k g))
```

against the existing `measure K hK`, for every actual normalized induced pair
`f`, `j` and every `g : G`. The existing
`normalizedInduction_pairing_covariant` gives full-modulus covariance of this
scalar pairing from the positive half-modulus covariance of both induced
functions. The displayed parabolic modular identity converts it into exactly
the covariance required by the proved `measure_scalar` theorem. Local
constancy follows from `Induction.pairing_isLocallyConstant`. Thus both the
integrability and the scalar integral equality are derived for the actual
pairings, rather than supplied by a caller.

## The compact probability form

`invariantPositiveForm` applies the existing
`Induction.integralInvariantPositiveForm` to the actual normalized induced
functions and `measure K hK`. This measure is the already constructed comap of
ambient Haar normalized to give `K` mass one; its existing Haar instance gives
positive mass on nonempty open sets. The actual `P K` decomposition supplies
the coverage required for definiteness. The preceding scalar law supplies
integrability and action invariance. Positivity, definiteness, sesquilinearity
and conjugate symmetry are inherited from the proved generic integration
constructor, with no new completeness or representation-theoretic assumptions.

`invariantPositiveForm_inner` is its defining equality

```text
⟨f,j⟩ = ∫ k : K, b.inner (f(k)) (j(k)) d(measure K hK).
```

The same `Induction.eval` on the same original normalized induced functions
appears in the definition and the equality. The form is not on a replacement
compact carrier.

`invariantPositiveForm_inner_normalizedHaar` rewrites that integral using the
already proved exact equality

```text
measure K hK = HarishChandraSchwartz.normalizedHaar (K : Subgroup G).
```

The compact-space instance needed to write spherical Haar is derived from
`hK`; it is not an additional compactness or normalization assumption. There
is no unknown scalar in this equality. The form therefore uses exactly the
same compact probability normalization as the existing duality, coefficient
and spherical integral constructions.

## Rescaling and pullback

`invariantPositiveForm_rescale` proves equality of the whole actual induced
forms after multiplying the inducing form by a strictly positive real scalar.
Extensionality, the integral computation and `integral_const_mul` move that
scalar through the integral. Both sides use precisely the same measure.

`invariantPositiveForm_ofEquiv` proves that inducing an actual pulled-back
form `b.ofEquiv e` agrees with pulling the induced form back by the actual
`normalizedInductionEquivOfEquiv h hU e`. The proof unfolds the two integrals
against the same compact measure; the induced equivalence applies `e`
pointwise. It neither assumes that arbitrary forms are isometric nor asserts
independence of every representation equivalence.

## Retained obligations

The choice and general rational-point realization of the geometric hypotheses
and the source special compact subgroup remain separate. The arbitrary Bruhat
form has not been compared to this compact probability form. Tensoring with
induction of the actual dual, proving the corresponding duality is an
isometry, inserting the actual inverse formal degree, representative and
compact-choice comparisons, and smooth spectral-family forms remain further
assembly steps. The Plancherel theorem and all seven whole-task completion
conditions remain open.
