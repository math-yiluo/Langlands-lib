# Actual cuspidal contragredients and their local components

Authors: Worker 1815 and Worker 1728.

This module defines three propositions and their conjunction
`Langlands.Automorphic.CuspidalContragredientStatement.{uF, uP, uQ}`.
They are targets for later proofs. No existence or compatibility assertion is
proved here. The formulations are derived from the cusp, duality and
factorization sources below; none is attributed verbatim to Flath's theorem
or to a local duality theorem.

## Common objects and original actions

Every proposition quantifies over every `F : Type uF` with `Field F`,
`NumberField F` and `CompactSpace (Langlands.Global.AdeleQuotient F)`, and
every `r : ℕ`. This compactness instance is the existing additive adelic
quotient convention used for constant terms. The group rank is `r + 1`, so
rank one (`r = 0`) is included. There is no CM or ramification restriction.

`T : CuspidalOperatorRealization F r` is an actual embedded space of
cuspidal automorphic functions, irreducible for its full operator action.
The operators are finite adelic right translations, standard infinite compact
right translations and the genuine enveloping differential action. They are
not replaced by a spectral system. The full action, its restriction to the
finite adelic group, and its restriction to a single local group are distinct.

The reused predicate
`Langlands.ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T`
means that some continuous idele-class character `χ` with values in `ℂˣ`
satisfies `‖(χ x : ℂ)‖ = 1` for every `x`, and that the actual forms of `T`
transform by `χ`. Its namespace does not add a Weil representation or an
association hypothesis.

The relation `T'.realization.IsContragredientOf T.realization` is the
existing full-operator relation from [Contragredient](Contragredient.md).
It requires a complex bilinear pairing `B : T.Space → T'.Space → ℂ`
invariant under simultaneous finite and compact translations, with

```text
B (T(X) y) x + B y (T'(X) x) = 0
```

for every real Lie algebra element `X`. The partial map `x ↦ B (·) x` must
be injective and have image exactly all algebraic functionals on `T.Space`
that are smooth for the finite adelic action and finite for the infinite
compact action. Thus nondegeneracy alone does not suffice. The induced dual
actions are `l ↦ l ∘ T(g⁻¹)` and `l ↦ -l ∘ T(X)`. No spectral or numerical
condition replaces this relation.

## The three exact propositions

`CuspidalUnitaryContragredientExistenceStatement.{uF}` quantifies over every
such `F`, `r` and `T`. Its sole additional premise is
`HasUnitaryCentralCharacter T`. Its conclusion is

```text
∃ T' : CuspidalOperatorRealization F r,
  T'.realization.IsContragredientOf T.realization ∧
  HasUnitaryCentralCharacter T'.
```

The output is an actual cuspidal realization of the same positive rank. This
first assertion has only the universe `uF`; it has no presentation premise.
It does not select a central character or assert its equality to a specified
inverse character, although the inverse character motivates the formulation.

`CuspidalContragredientPresentationExistenceStatement.{uF, uP, uQ}`
quantifies over every such `F`, `r`, supplied `T` and `T'`, a proof of
`HasUnitaryCentralCharacter T`, the supplied relation
`T'.realization.IsContragredientOf T.realization`, and every supplied
`P : CuspidalSpectralPresentation.{uF, uP} T`. It concludes

```text
∃ P' : CuspidalSpectralPresentation.{uF, uQ} T',
  ∀ v : FinitePlace F,
    (P'.localComponent v).IsIrreducible ∧
    (P'.localComponent v).IsAdmissible.
```

In particular the output presentation is existential data, with its genuine
nonzero finite slice inside the actual finite image of `T'`, a restricted
tensor product, a finite tensor exceptional set with integral-fixed nonzero
reference vectors outside it, and the existing almost-everywhere
`UnramifiedData`. The latter includes normalized spherical Hecke spectra
on the entire fixed spaces outside a finite spectral exceptional set. The
extra conclusion requires irreducibility and admissibility at **all** finite
places, including both exceptional sets. There is no supplied output
presentation, factorization, local-duality, countable-dimension or
universe-shrinking premise. Unitarity of the central character of `T'` is not
an extra premise or extra conclusion of this second proposition.
The supplied input `P` has no irreducibility or admissibility premise on its
local components.

`CuspidalContragredientLocalCompatibilityStatement.{uF, uP, uQ}`
quantifies over every such `F`, `r`, `T`, `T'`, the supplied full-operator
contragredient relation, **every** pair
`P : CuspidalSpectralPresentation.{uF, uP} T` and
`P' : CuspidalSpectralPresentation.{uF, uQ} T'`, every finite place `v`,
and every supplied proof `hI`, `hA`, `hI'`, `hA'` of irreducibility and
admissibility of the respective actual local components. Put

```text
rho  = ((P.localComponent v).padicObject hI hA).obj.representation
rho' = ((P'.localComponent v).padicObject hI' hA').obj.representation.
```

The conclusion is exactly
`Nonempty (rho'.Equiv (Langlands.smoothContragredient rho))`: a genuine
bijective complex-linear intertwiner from the second original local action
to the smooth dual of the first. There is no unitarity, weak association,
equality of finite slices, equality of spectra or selected-presentation
premise. The place need not avoid either exceptional set. The supplied
irreducibility and admissibility concern this place; the proposition does
not require these proofs at other places of either presentation.

For this conclusion the statement installs
`(Langlands.Global.CompletionPadic.padicField v).canonicalTopologicalData.topology`,
as in the published local unitarity statement. The [p-adic object
adapter](PadicLocalCategory.md) preserves the embedded form carrier and the
actual action of `GL_(r+1)(F_v)`, while using its canonical p-adic matrix
topology. The statement also installs the existing
`canonicalGeneralLinearTopology (r + 1)` and
`canonicalGeneralLinearTopologicalGroup (r + 1)`, which supply this matrix
topology and its proved continuity of multiplication and inversion. These
are canonical structures, not additional hypotheses.
[Smooth contragredience](../Representation/Smooth/Contragredient/Definitions.md)
means the smooth-vector submodule of the algebraic dual with action
`(g l)(x) = l (rho(g⁻¹) x)`. It imposes no vector-space topology and uses
neither the full algebraic dual as carrier nor a numerical duality test.

The three universes are independent, with no inequalities between them.
The factor carriers of `P` and `P'` lie in `uP` and `uQ`, respectively.
The actual embedded local form carriers, and hence both `padicObject`
carriers, remain in `uF`. In the second assertion even `uQ = 0` is allowed
regardless of `uF` and `uP`. This is an existence requirement, not a claim
that the existing adapter resizes arbitrary carriers.

## Original sources and derived provenance

The retained originals listed here were read directly, together with all five
pages of the registered October 2026 Getz--Hahn errata.

| Source | Exact passage | Literal source content used |
| --- | --- | --- |
| Borel--Jacquet, *Automorphic forms and automorphic representations* (1979), registered as `borel-jacquet-1979-automorphic` | §§4.4--4.6, printed pp.196--197, retained Part I PDF pages 191--192 (one-based); §4.5 and §4.6 in particular | Cusp growth and square-integrability comparison with a central character, admissibility of automorphic representations, and the discrete cuspidal L² decomposition with finite multiplicities and identification of its admissible vectors with cusp forms. |
| Getz--Hahn, *An Introduction to Automorphic Representations* (2024), `getz-hahn-2024-automorphic-representations` | §5.4, Definition 5.4.1 and Lemma 5.4.2, printed pp.143--145, PDF pages 158--160 | The inverse-element action on smooth functionals, admissible duality and biduality, and the invariant Hermitian-form description of the Hermitian dual. |
| Same book | §§5.6--5.7, especially Theorem 5.7.1, printed pp.149--153, PDF pages 164--168 | Restricted tensor products and Flath existence and uniqueness for an irreducible admissible finite adelic representation. |
| Same book | §6.3, Theorem 6.3.4, Lemma 6.3.6 and Theorem 6.3.7, printed pp.164--166, PDF pages 178--180 | Joint admissibility, finite/infinite separation with unique irreducible factors, and all-place factorization with unique irreducible admissible local factors. |
| Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un corps p-adique* (2000), `henniart-2000-simple-proof` | §2.2, printed p.444, PDF page 6 | Association is preserved by contragredients; this is consuming context, not a construction of an actual cuspidal dual. |

The source fingerprints are, respectively,
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`,
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`
(for all three book rows), and
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
The errata source is `getz-hahn-2024-errata-2026-10`, fingerprint
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`.
It lists no correction to §§5.4, 5.6--5.7 or 6.3. Its §4.4 correction requires
continuity of finite-dimensional compact actions in the canonical topology;
its correction about connectedness in §4.6 prevents using an unrestricted
compact-group infinitesimal-character assertion. Those corrections must be
respected in the future full-operator comparison proof.

The following explains the additional mathematics behind the targets. It
records a derivation route and the outstanding proof work, not implemented
Lean proofs or literal quotations from these sources.

For the first assertion, start with the unitary central character of `T`.
The cusp L² comparison places its functions in the square-integrable space
modulo the rational points and adelic center. Pointwise complex conjugation
gives a candidate actual cusp space with conjugate central character, equal
to the inverse character in this unitary case. Constant-term vanishing
passes through conjugation. The candidate bilinear pairing is
`B(f, conjugate(h)) = integral f * conjugate(h)` on that quotient. Its
integrand is central-invariant. Translation invariance and differentiation
give the two group identities and the real Lie algebra negative-transpose
identity. Joint admissibility at finite levels and compact types is the
route from a nondegenerate L² pairing to surjectivity onto precisely the
finite-smooth compact-finite algebraic dual. Given such a functional, choose
a compact open subgroup fixing it for the finite action and the finitely
many infinite compact types in its compact orbit. Finite-level averaging
and compact-type projections make the functional factor through the
corresponding joint block. Joint admissibility makes that block
finite-dimensional, and the positive L² form identifies its conjugate with
its full linear dual. Invariance of the form makes the projections compatible
with this pairing, so the representing vector gives the functional on the
whole module. The projections, their continuity on the actual compact-type
spaces and their compatibility with the embedded stable core remain to be
proved. One must also verify the differential identity and full-operator
irreducibility of the conjugate space. Borel--Jacquet supplies the analytic
and admissibility inputs, not this Lean realization construction. The
existing transport lemmas alone do not construct it.

For the second assertion, the cusp admissibility comparison and finite/infinite
separation apply to the supplied actual `T'`. Under
`T' ≅ T'_infinity tensor T'_finite`, fixing a nonzero infinite-factor vector
embeds one irreducible admissible finite factor as a nonzero actual finite
slice. Flath then factors that finite representation into irreducible
admissible local factors. The genuine tensor equivalence must be composed
with this embedding, rather than declared onto the whole finite restriction.
The almost-everywhere spectral fields require further compatibility with
the Library's normalization. The input `P` need not have irreducible local
components, so its spherical data must be compared through multiplicities.
At a place outside the relevant finite exceptional sets, its nonzero
integral-fixed vector embeds through its finite slice into `M tensor L_v`,
where the local group acts trivially on `M` and `L_v` is the irreducible
factor of `T`. Choosing a basis of `M`, some coordinate projection to `L_v`
is nonzero on that vector. This local intertwiner preserves integral-fixed
vectors and commutes with the normalized spherical Hecke operators. Hence
the whole-fixed-space Hecke equations supplied by `P` hold on its nonzero
image. The one-dimensional spherical fixed space of the irreducible
unramified factor then has those same eigenvalues. Smooth duality gives
the inverse Satake parameters for the dual factor. Constructing the
projections, checking the fixed-space and Hecke compatibilities, and
assembling the resulting output data remain part of this existence target.
No irreducibility of the supplied input components is added. Neither Flath
alone nor a numerical system supplies a spectral presentation.

The arbitrary output universe is also a derived implementation requirement.
The published Library theorem
`Langlands.padicIrreducibleSmoothSmallRealization.{uF, uW, uQ}` in
[SmallRealizationProof](../Representation/Smooth/SmallRealizationProof.md)
already provides an equivalent irreducible smooth local representation in
any independently prescribed `Type uQ`, including `uQ = 0`. Apply it to
`CompletionPadic.padicField v`, its canonical topological data and rank
`r + 1`. Its proof uses the countable spanning orbit of a nonzero smooth
vector, a basis within that orbit and reindexing into the desired universe;
it needs no admissibility or supplied countability or resizing witness.
This internal theorem is not attributed to the cited literature. Future
work must preserve admissibility through those equivalences and assemble
them into the reference vectors, genuine restricted tensor equivalence and
spectral data of the output presentation. The scalar field `ℂ` already lies
in `Type 0`, independently of the number-field carrier universe. This
statement adds no small-model premise.

For the third assertion, first compare each actual full module with the
finite/infinite and all-place factorizations of §6.3. After forgetting the
infinite action, the full carrier has multiplicity from the infinite
factor; it need not be an irreducible finite representation. At a fixed
finite place the locally restricted carrier has the form `M tensor L_v`,
where the local group acts trivially on `M` and `L_v` is the irreducible local
factor. A basis of `M` expresses this as an algebraic direct sum of copies
of `L_v`. The actual local component of any supplied presentation embeds
equivariantly into this carrier through its finite slice. For a nonzero
vector in an irreducible such component, some coordinate projection to
`L_v` is nonzero. Its restriction to the component is an intertwiner;
irreducibility of the component and `L_v` makes it injective and
surjective. Thus every admitted irreducible component has the same local
factor class. This argument applies separately to `P` and `P'`, uses no
irreducibility at other places, and identifies no two embedded slices. It
is the needed comparison beyond uniqueness for two tensor presentations
of one fixed finite representation.

Next, the full invariant perfect pairing identifies the second full module
with the finite-smooth compact-finite dual of the first. At a fixed finite
level and finitely many compact types, the factors in the corresponding
joint blocks are finite-dimensional. Their ordinary tensor-dual comparison,
followed by passage through these levels and types, is the route to
restricted-dual factorization. Admissible local duality then identifies
their local factor classes as contragredients at every finite place.
Restricting the bilinear pairing to two arbitrarily chosen embedded slices
need not itself give a perfect pairing; the factor and isotypic comparisons
are essential. Finally compose the actual-component-to-factor equivalences
with local duality, using contravariant transport on smooth duals, and the
existing canonical topology comparison. This yields the displayed genuine
equivalence of the original actions. It uses no global unitary structure
and excludes no exceptional place. Full-module factorization, restricted-dual
comparison and coordinate-projection constructions remain mathematical
proof obligations.

## Boundary with association and other work

The conjunction is the first proposition and the conjunction of the second
and third, in that order. It adds no theorem proving any conjunct. The
existing `AssociatedContragredientStatement` and its imports are unchanged.
That target assumes a dual realization or class is supplied and includes a
possibly nonunitary class formulation with an output presentation. The
unitary existence targets here do not establish that full class assertion.
Generic finite factorization and fixed-representation tensor-factor
uniqueness can support later proofs but do not provide an actual cusp dual
or the comparison of arbitrary finite slices in two full realizations.
Local unitarity, local genericity and associated factor comparisons retain
their separate proof obligations.
