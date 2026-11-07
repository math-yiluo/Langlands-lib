# Actual cuspidal presentations irreducible at every finite place

Authors: Worker 1793.

This module defines two propositions for later proofs:

- `Langlands.Automorphic.CuspidalIrreducibleAdmissibleFiniteSliceExistenceStatement.{u}`,
  an intermediate assertion about actual finite slices;
- `Langlands.Automorphic.CuspidalAllLocalIrreduciblePresentationExistenceStatement.{u, uQ}`,
  the principal assertion about auxiliary spectral presentations.

Neither is proved here, and neither is assumed by the other. Both are derived
formulations: the cited sources prove the corresponding results for abstract
irreducible admissible modules, not for the Library structures. The proof route
and its outstanding obligations are recorded below.

## Common objects

Both propositions quantify over every `F : Type u` with `Field F`,
`NumberField F` and `CompactSpace (Langlands.Global.AdeleQuotient F)`, and over
every `r : ℕ`. The group is `GL_(r+1)`, so rank one (`r = 0`) is included. The
compactness instance is the existing additive adelic quotient convention used
for constant terms. There is no CM, ramification, central character or
unitarity hypothesis.

`S : CuspidalOperatorRealization F r` is an actual subspace of the stable
automorphic form space. It is invariant under, and irreducible for, the whole
concrete operator algebra: finite adelic right translations, right translations
by the standard infinite compact subgroup, and the genuine enveloping-algebra
differential action. Its vectors have vanishing proper constant terms. The
underlying forms have finite level, are finite under the standard infinite
compact subgroup, are center-finite, and have polynomial growth. Irreducibility
concerns this full action, not its restriction to the finite adelic group.

## The intermediate proposition

`CuspidalIrreducibleAdmissibleFiniteSliceExistenceStatement.{u}` concludes,
for every such `F`, `r` and `S`,

```text
∃ A : S.FiniteSlice,
  A.subspace.IsIrreducible ∧
  Langlands.IsAdmissible A.subspace.representation.
```

An `S.FiniteSlice` is an actual subspace `A.subspace` of automorphic forms,
invariant under finite adelic right translation, contained in the image
`S.realization.toFiniteRealization` of the full realization, and different
from `⊥`. `A.subspace.representation` is the restricted right-translation
action of `GL_(r+1)` of the finite adeles on these actual forms.
`IsIrreducible` is Mathlib's `Representation.IsIrreducible`: the lattice of
subrepresentations is simple, so in particular the carrier is nonzero.
`Langlands.IsAdmissible` is the Library's Casselman convention: every vector
is fixed by some open subgroup, and for every open subgroup the fixed vectors
form a finite-dimensional complex space. Both properties are conclusions, not
premises. The slice need not be the whole finite image
`CuspidalOperatorRealization.FiniteSlice.whole S`, which is in general not
irreducible for the finite adelic group alone.

## The principal proposition

`CuspidalAllLocalIrreduciblePresentationExistenceStatement.{u, uQ}` quantifies
over every such `F`, `r`, `S` and every supplied
`_P : CuspidalSpectralPresentation.{u, uQ} S`. It concludes

```text
∃ Q : CuspidalSpectralPresentation.{u, u} S,
  ∀ v : FinitePlace F,
    (Q.localComponent v).IsIrreducible ∧
    (Q.localComponent v).IsAdmissible.
```

The output `Q` is a complete instance of the existing
[spectral presentation structure](CuspidalSpectralPresentation.md) on the same
`S`. It therefore contains:

- an actual nonzero finite slice `Q.finiteSlice` inside the finite image of `S`;
- smooth local factors `Q.localFactor v` of `GL_(r+1)(F_v)`, with carriers in
  universe `u`;
- a finite tensor exceptional set and reference vectors fixed by the actual
  integral subgroup outside it;
- a genuine equivariant linear equivalence from the slice to the restricted
  tensor product of these factors, pulled back along the adelic matrix
  equivalence;
- a finite spectral exceptional set with the existing `UnramifiedData`. Outside
  it the factors are irreducible and admissible, and the normalized spherical
  Hecke spectrum holds on the entire spherical fixed space of the embedded
  local component.

`Q.localComponent v` is the actual embedded copy of the factor at `v` inside
automorphic forms: the local factor tensored with a fixed nonzero complementary
tail vector. Its `IsIrreducible` and `IsAdmissible` are those of
[the presented local category](PresentedLocalCategory.md): irreducibility and
admissibility of the actual right-translation action of `GL_(r+1)(F_v)` on that
embedded subspace. The conclusion holds at **every** finite place, including
both exceptional sets of `Q`. Almost-everywhere irreducibility, which is
already part of every presentation, is not sufficient.

The supplied `_P` is an unused hypothesis, as the objective requires, and the
conclusion does not mention it. It need not have irreducible components at any
exceptional place, and `Q` is not required to share its slice, factors,
exceptional sets or spectra. Nothing is asserted about every supplied
presentation; the assertion is the existence of a suitable auxiliary on the
same actual `S`. `_P` and its universe `uQ` remain available unchanged to
downstream comparisons. Its presence makes the proposition no stronger than
the same assertion without `_P`.

The two universes are independent. The original presentation has factors in
`uQ`, possibly `uQ = 0` or `uQ` larger than `u`. The auxiliary factors lie in
the form-space universe `u`, where Flath factorization produces them. No
resizing into `uQ` is asserted. All embedded local components lie in `u` in
either case.

## How the intermediate proposition yields the principal one

Given `A` from the intermediate proposition, pull its action back to the
restricted product of the local groups along
`Langlands.Global.FiniteAdelicGL.restrictedProductEquiv`, with the integral
subgroups `localIntegral F (r + 1) v`. These are compact open, and their
spherical Hecke algebras are commutative (Library
`Langlands.Unramified.sphericalHeckeAlgebra_mul_comm`, still to be connected to the measure
convention of the Flath statement). The published theorem
`Langlands.flathRestrictedProductExistence` then gives irreducible admissible
local representations on carriers in the universe of `A.subspace.Space`,
namely `u`. It also gives a finite set `E`, nonzero integral-fixed reference
vectors off `E`, and an equivalence of `A.subspace.representation` with the
restricted product representation.

Take `Q.finiteSlice := A`, smooth local factors from these representations
(admissible representations are smooth), `Q.tensorExceptional := E`, and the
tensor presentation obtained by composing the Flath equivalence with the
identification of the restricted product with
`Langlands.Global.FiniteAdelicGL.tensorRepresentation`. That identification is
the same pullback along `restrictedProductEquiv`. Put `Q.exceptional := E` and
`Q.unramified := FiniteTensorPresentation.unramifiedData` from
[the unramified construction](PresentedUnramifiedConstruction.md). It needs
irreducibility and admissibility off `E`, and constructs the normalized spectra
from the actual embedded components. The equivalences
`localComponent_isIrreducible_iff` and `localComponent_isAdmissible_iff`
transfer irreducibility and admissibility of every Flath factor to
`Q.localComponent v` at every `v`. The intermediate proposition is the
genuinely new global input. The packaging steps use only existing Library
constructions together with the comparison obligations named here.

## Original sources and derived provenance

| Source | Exact passage | Content used |
| --- | --- | --- |
| Getz--Hahn, *An Introduction to Automorphic Representations* (2024), `getz-hahn-2024-automorphic-representations` | §5.7, Theorem 5.7.1 (Flath), printed p.152, PDF page 167 | Every irreducible admissible representation of `G(A^∞)` is a restricted tensor product of irreducible admissible local representations, unique up to isomorphism. |
| Same book | §6.3, Theorem 6.3.4, printed pp.164--165, PDF pages 178--179 | For an ideal `J` of finite codimension in `Z(g)`, the space `A(J)` of automorphic forms annihilated by `J` is an admissible `(g, K_∞) × G(A^∞)`-module. |
| Same book | §6.3, Lemma 6.3.6 and Theorem 6.3.7 with its proof, printed pp.165--166, PDF pages 179--180 | An irreducible admissible `(g, K_∞) × G(A^∞)`-module is `π_∞ ⊗ π^∞` with irreducible admissible factors (the lemma is left as Exercise 6.7), and then factors at all places by Flath. |
| Same book | §6.6, Theorems 6.6.1--6.6.2, printed pp.170--171, PDF pages 184--185 | Hilbert route: for an irreducible unitary representation of `G(A_F)`, the `K`-finite vectors form an irreducible admissible module that factors as `π_∞ ⊗ π^∞`. |
| Same book | §9.7, Theorem 9.7.1, Lemma 9.7.2 and Theorem 9.7.3, printed pp.264--265, PDF pages 276--277 | Hilbert route: cusp forms on `A_G\G(A_F)` are rapidly decreasing, lie in `L²_cusp`, and the cuspidal automorphic representations correspond to discrete cuspidal summands. |

The book fingerprint is
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`. The
October 2026 errata `getz-hahn-2024-errata-2026-10`, fingerprint
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`, were read
in full. They list no correction to §5.7 or §6.3. In §6.6 they correct
`(π_∞, V_fin)` to `(π, V_fin)` at the top of p.171, and a reference in the
proof of Theorem 6.6.2. In §4.6 they require `K` connected before deducing that
`Z(g)` commutes with `K` and that infinitesimal characters exist, with an
`O_2(ℝ)` counterexample. In §4.4 they require continuity of the
finite-dimensional compact actions. The route below respects the §4.6
correction explicitly.

The rest of this section records a derivation route and the outstanding proof
work. It is neither an implemented Lean proof nor a quotation.

**Algebraic full-operator route (chosen).** Fix a nonzero `f` in `S`. The form
`f` is center-finite, so its annihilator `J` in `Z(g)` has finite codimension.
The full action of `Z(g)` on actual forms commutes with finite translations and
with the differential action. It also commutes with translations by the
disconnected standard compact group `K_∞`. The reason is that `Z(g)` is fixed by
the adjoint action of `G(F_∞)`, which factors through the connected complex
group, a product of copies of `GL_(r+1)(ℂ)`. This is a property of the actual
derivative action, and it avoids the abstract `(g, K)` counterexample in the
errata. Hence `J` annihilates the full-operator submodule generated by `f`,
which is all of `S` by irreducibility. Thus `S ⊆ A(J)`, and Theorem 6.3.4 makes
`S` admissible. Lemma 6.3.6 gives `S ≅ π_∞ ⊗ π^∞`. For a nonzero vector `x` of
`π_∞`, the image of `x ⊗ π^∞` is an actual nonzero finite-translation-invariant
subspace of `S`. Its image in automorphic forms is the required slice `A`. It is
isomorphic to `π^∞`, hence irreducible and admissible. For an arbitrary open
subgroup, its fixed space lies in the fixed space of a compact open subgroup,
which matches the Library's all-open-subgroups convention.

This route uses neither a unitary central character nor cuspidality. It needs
three comparisons with the book:

- Library center-finiteness, standard compact finiteness and polynomial growth
  against the book's `A(J)`;
- the standard infinite compact subgroup against a maximal compact `K_∞`;
- the concrete operator-algebra irreducibility against irreducibility as a
  `(g, K_∞) × G(A^∞)`-module.

It also needs a proof of Harish-Chandra finiteness (Theorem 6.3.4 via Theorem
6.2.6 and reduction theory) and of Lemma 6.3.6. The published archimedean
slice-finiteness results transport center and compact finiteness of
archimedean slices. They do not give finite-adelic admissibility. The
cuspidality of `S` is inherited by `A`
(`CuspidalOperatorRealization.FiniteSlice.isCuspidal`) and hence by
`Q.localComponent v`, but it is not used for existence.

**Hilbert route (not used).** Theorems 6.6.1--6.6.2 and 9.7.3 work with
irreducible unitary subrepresentations of `L²_cusp` on `A_G\G(A_F)`. To use them
for an arbitrary actual `S` one would twist by a power of `|det|` to make the
central character trivial on `A_G` and unitary. The Library has
determinant-twist adapters for presentations. One would then embed the twisted
forms in `L²_cusp` by rapid decrease, compare the resulting discrete summand
with the original algebraic module, and untwist. Since the algebraic route
needs none of this, the principal proposition carries no central-character
premise. Unitary central character is not added as a hypothesis.
