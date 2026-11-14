# Automorphy of the constituents of cuspidally induced representations, at the finite places

Author: Worker 3657. Statement contribution to task
`34b81620-20d7-4059-9b08-6bedd1c1c029`, revision 1.

**Scope.** This module states one proposition and proves nothing:

- `Langlands.Global.CuspidalInducedConstituentAutomorphyStatement`.

The module is `Langlands.Global.Factors.CuspidalInducedConstituentAutomorphyStatement`.
The proposition is the first half of Getz–Hahn (2024), Theorem 10.7.1
(Langlands), for `GL_n` and at the finite places, combined with Langlands'
description of the constituents (Langlands 1979, Lemma 1). Take cuspidal
automorphic representations `π_1, …, π_k` of `GL_(n_i)(𝔸_F)` with
`∑ n_i = n`. At every finite place `v` choose an irreducible subquotient
`A_v` of the normalized induced representation `i(π_(1,v), …, π_(k,v))`, with
`A_v` unramified for almost all `v`. Then some irreducible automorphic
representation of `GL_n(𝔸_F)` has component `A_v` at every finite place `v`.
The Lean conclusion says that `A_v` embeds into the restriction of that
representation to `GL_n(F_v)`.

The module defines one `local instance` and nothing else: the canonical
topology on `GL_n(F_v)`, as in `CuspidalInducingDataRigidityStatement`.
Without it, Lean picks the `Units` topology of the matrix ring, and the
`representation` field of a canonical object does not elaborate. Everything
else is Library vocabulary:

- `CuspidalOperatorRealization`, `CuspidalSpectralPresentation`
  (`Langlands/Automorphic/CuspidalOperatorRealization.lean`);
- `CuspidalPairFunctionalEquation.HasIrreducibleAdmissibleComponents`
  (`Langlands/Global/Factors/CuspidalPairFactorData.lean`);
- `LocalRealization.padicObject` (`Langlands/Automorphic/PadicLocalCategory.lean`);
- `PadicField.canonicalNormalizedProductInduced`
  (`Langlands/Representation/Induction/BlockFactors.lean`);
- `Correspondence.AutomorphicObject`, `Correspondence.sphericalSubgroup` and
  `Correspondence.IsSubquotientOf`
  (`Langlands/Correspondence/AutomorphicRelations.lean`,
  `Langlands/Correspondence/UnramifiedNormalization.lean`);
- `Langlands.fixedVectors` (`Langlands/Representation/Smooth/Definitions.lean`);
- `Automorphic.IrreducibleOperatorSubquotient`
  (`Langlands/Automorphic/IrreducibleOperatorSubquotient.lean`) and
  `OperatorSubquotient.localRepresentation`
  (`Langlands/Automorphic/OperatorSubquotient.lean`).

**Why it is here.** L4 of this task's contract asks for the isobaric
construction of GH 10.7.5–10.7.6, and its context names GH 10.2.3–10.7.6 as
the roadmap range. GH's proof of Theorem 10.7.5 uses Theorem 10.7.1 and the
description of constituents after it. The Library has no global induced
representation and no statement that its constituents are automorphic. This
statement is the global input of the 10.7.5 proof, in a form that the
Library can state: the finite components of a constituent are prescribed and
an automorphic subquotient with those components is asserted. As the
contract notes, not every such automorphic subquotient is isobaric; this
statement does not say it is.

**Proof target.** A later proof task should prove the Library statement
`Langlands.Global.CuspidalInducedConstituentAutomorphyStatement`. Its
universe parameters are `u` (the number field and every local carrier) and
`uQ` (the factor universe of the spectral presentations).

## 1. Sources

"p." is the printed page and "PDF" the one-based page of the registered file.

| Source ID | SHA-256 | Locators used |
|---|---|---|
| `getz-hahn-2024-automorphic-representations` | `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507` | `I(σ, λ)` and its local factors, p.271 (PDF 283); (10.34), Thm 10.7.1 and the remark on Lemma 1, pp.286–287 (PDF 298–299); `π_i = \|det\|^(λ_i) π_i^1`, p.288 (PDF 300) |
| `langlands-1979-notion-automorphic-representation` | `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5` | `Ind σ`, constituents, `π°_v`, Lemma 1 and its proof, p.203 (PDF 198); Prop 2, p.204 (PDF 199); proof that constituents are automorphic, Lemmas 7–9, pp.205–207 (PDF 200–202) |
| `borel-jacquet-1979-automorphic` | `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5` | automorphic forms, §4.2, pp.194–195 (PDF 189–190); automorphic representations, §4.6, p.196 (PDF 191) |

The last two sources are consecutive papers in the same registered file, the
Corvallis volume, Part I. Its printed page is the PDF page plus 5. GH cite
Langlands' paper as "the appendix to [BJ79]"; its title is *On the notion of
an automorphic representation. A supplement to the preceding paper*.

**What the sources state.** GH p.286: "Given a cuspidal automorphic
representation `σ` of `M(𝔸_F)`, we form the induced representation `I(σ, λ)`
(10.34) as in (10.1). For the proof of the following theorem, see the
appendix to [BJ79]:

> **Theorem 10.7.1 (Langlands)** Any irreducible subquotient of `I(σ, λ)` is
> an automorphic representation, and every automorphic representation is of
> this form."

GH continue (pp.286–287): "in [BJ79, Appendix, Lemma 1] Langlands observes
that the subquotients of `I(σ, λ)` can be described as follows. For all but
finitely many `v` the representation `σ_v` is unramified and `I(σ_v, λ)` has
a unique irreducible unramified subquotient `π°_v`. The irreducible
subquotients of `I(σ, λ)` are the representations of the form `⊗'_v π_v`,
where `π_v` is an irreducible subquotient of `I(σ_v, λ)` for all `v` and
`π_v ≅ π°_v` for almost every `v`." On p.271 the action of `I(σ, λ)` carries
the factor `e^⟨H_P(xg), λ + ρ_P⟩`, so the induction is normalized, and
`I(σ, λ) ≅ ⊗'_v I(σ_v, λ)`.

Langlands p.203: for a parabolic `P` with Levi factor `M` and a cuspidal
representation `σ = ⊗σ_v` of `M(𝔸)`, `Ind σ = ⊗_v Ind σ_v`, and "an
irreducible subquotient of this representation is said to be a constituent
of it". "For almost all `v`, `Ind σ_v` has exactly one constituent `π°_v`
containing the trivial representation of `G(O_v)`."

> LEMMA 1. The constituents of `Ind σ` are the representations `π = ⊗π_v`
> where `π_v` is a constituent of `Ind σ_v` and `π_v = π°_v` for almost all `v`.

The proof begins "That any such representation is a constituent is clear."
P.204:

> PROPOSITION 2. A representation `π` of `G(𝔸)` is an automorphic
> representation if and only if `π` is a constituent of `Ind σ` for some `P`
> and some `σ`.

BJ79 §4.6, p.196: "An irreducible representation of `ℋ` is automorphic … if
it is isomorphic to a subquotient of a representation of `ℋ` in the space of
automorphic forms on `G(𝔸)`." Here `ℋ` is the global Hecke algebra, built
from `G(𝔸_f)` and the pair `(𝔤, K_∞)`.

## 2. The declaration

`CuspidalInducedConstituentAutomorphyStatement` says the following. Let:

- `F` be a number field with `[CompactSpace (AdeleQuotient F)]`, the instance
  needed by `CuspidalOperatorRealization`;
- `r, k : ℕ` and `m : Fin k → ℕ` with `hm : ∑ i, (m i + 1) = r + 1`;
- `T i : CuspidalOperatorRealization F (m i)`, actual cuspidal realizations of
  `GL_(m i + 1)` over `F`;
- `P i` be spectral presentations of `T i`, with factors in universe `uQ`;
- `h i` say that every finite local component of `P i` is irreducible and
  admissible (`HasIrreducibleAdmissibleComponents`);
- `A v : AutomorphicObject.{u, u} (padicField v) r.succPNat`, for every finite
  place `v`, an irreducible admissible smooth representation of
  `GL_(r+1)(F_v)` with carrier in universe `u`;
- `S : Finset (FinitePlace F)` be a finite set of finite places.

Write `σ_(i,v)` for the canonical object
`((P i).localComponent v).padicObject (h i v).1 (h i v).2` of
`AutomorphicObject (padicField v)`, and `B` for the block shape
`⟨k, fun i => m i + 1, _, hm⟩`. Suppose:

1. for every finite place `v`, `A v` is a subquotient (`IsSubquotientOf`) of
   `(padicField v).canonicalNormalizedProductInduced B (fun i => σ_(i,v).obj.representation)`;
2. for every finite place `v ∉ S`, `A v` has a nonzero vector fixed by
   `sphericalSubgroup (padicField v) r`, that is by `GL_(r+1)(O_v)`.

Then there is `Q : IrreducibleOperatorSubquotient F r` such that for every
finite place `v` there is an injective intertwining map from `A v` to
`Q.subquotient.localRepresentation v`, the restriction of `Q` to
`GL_(r+1)(F_v)`.

## 3. Hypotheses and conclusion, matched with the sources

- **Cuspidal data and `λ`.** As in `CuspidalInducingDataRigidityStatement`
  §3, `T i` is a cuspidal `π_i` of `GL_(n_i)(𝔸_F)`, `n_i = m i + 1`, with no
  condition on the split centre. By GH p.288, `π_i = |det|^(λ_i) π_i^1` with
  `π_i^1` cuspidal on `A_(GL_(n_i)) \ GL_(n_i)(𝔸_F)`. GH's `σ = ⊗_i π_i^1` and
  `λ = (λ_1, …, λ_k)` give a normalized `I(σ, λ)` whose local factor at `v` is
  the normalized induction of the `π_(i,v)`. Langlands' `σ` is any cuspidal
  representation of `M(𝔸)`, here `⊗_i π_i`. So the Lean data, with `λ`
  absorbed, are GH's and Langlands' data for `G = GL_(r+1)` and the standard
  parabolic of type `(n_1, …, n_k)`. Only standard block parabolics occur;
  every parabolic of `GL_n` is conjugate to one.
- **Local components.** `(P i).localComponent v` is the actual embedded factor
  at `v` of a spectral presentation, the `σ_(i,v)` (GH) or `π_(i,v)` above.
  `LocalRealization.padicObject` views it in the correspondence category with
  its original action (see `CuspidalStrongMultiplicityOneStatement`). The
  statement is not vacuous: for `uQ = u` every cuspidal realization has a
  presentation satisfying `h`
  (`cuspidalIrreducibleAdmissibleFiniteSliceExistence` and
  `CuspidalOperatorRealization.exists_presentation_of_finiteSlice`, cited in
  `CuspidalInducingDataRigidityStatement` §3).
- **Hypothesis 1.** `canonicalNormalizedProductInduced B` is normalized smooth
  induction from the standard upper block parabolic with blocks
  `m 0 + 1, …, m (k-1) + 1` (`BlockFactors.lean`), GH's local `I(σ_v, λ)` and
  Langlands' `Ind σ_v`. `IsSubquotientOf ρ A` says that a subrepresentation
  of `ρ` maps onto `A`. With `A v` irreducible, hypothesis 1 says that `A v`
  is a constituent of `Ind σ_v` in Langlands' sense, at every finite place.
- **Hypothesis 2 is "`A_v ≅ π°_v` for almost all `v`".** The following is
  background and is not asserted. If `σ_(i,v)` is unramified for all `i`,
  then by the Iwasawa decomposition the `GL_(r+1)(O_v)`-fixed vectors of
  `i(σ_(1,v), …, σ_(k,v))` form a line, and taking fixed vectors of a compact
  open subgroup is exact. So exactly one constituent is spherical, Langlands'
  `π°_v`, and a constituent `A_v` is spherical exactly when `A_v ≅ π°_v`. If
  some `σ_(i,v)` is ramified, the induced representation has no nonzero
  `GL_(r+1)(O_v)`-fixed vector and no constituent is spherical. As
  `σ_(i,v)` is unramified for almost all `v` (GH p.286), "`A_v` spherical for
  almost all finite `v`" and "`A_v ≅ π°_v` for almost all finite `v`" are the
  same condition. The Lean `S` is a finite exceptional set for it.
- **The infinite places.** The Lean statement fixes nothing at the infinite
  places. To read it off GH 10.7.1, choose at each infinite place `w` an
  irreducible subquotient `π_w` of `I(σ_w, λ)`; one exists, since the
  `(𝔤, K_w)`-module of `I(σ_w, λ)` has finite length (background). Then
  `π = (⊗_w π_w) ⊗ (⊗'_(v finite) A_v)` is a constituent of `I(σ, λ)` by the
  easy direction of Lemma 1, and automorphic by Theorem 10.7.1.
- **The conclusion `Q`.** By BJ79 §4.6, `π` is isomorphic to a quotient
  `V / U` of `ℋ`-invariant subspaces `U ⊆ V` of the space of automorphic
  forms. Library automorphic forms are those of BJ79 §4.2
  (`Langlands/Automorphic/Forms.md`). `ℋ`-invariance is invariance under
  `GL_(r+1)(𝔸_f)`, `K_∞` and the enveloping algebra. So `V` lies in the
  largest such invariant subspace, `StableAutomorphicFunctions`
  (`OperatorCore.md`), and the pair `(V, U)` is an `OperatorSubquotient`.
  Irreducibility as an `ℋ`-module is irreducibility under the whole operator
  algebra, so `(V, U)` is an `IrreducibleOperatorSubquotient F r`, the
  Library's irreducible automorphic representation. Restricted to
  `GL_(r+1)(F_v)`, `π` is `A_v ⊗ (⊗'_(w ≠ v) π_w)` with the group acting on
  the first factor. Fixing a nonzero vector `y` of the second factor,
  `x ↦ x ⊗ y` embeds `A_v` into that restriction. Composed with `π ≅ V / U`,
  this gives the injective intertwining maps of the conclusion, for one `Q`
  and all finite `v` at once.
- **What the conclusion pins down.** Given background facts (an irreducible
  automorphic `Q` is admissible and is a restricted tensor product, Flath),
  the restriction of `Q` to `GL_(r+1)(F_v)` is `Q_v`-isotypic. So the
  conclusion says `Q_v ≅ A_v` for every finite `v`: the finite part of `Q` is
  `⊗'_(v finite) A_v`. This reformulation is not asserted.
- **Universes.** `A v` has its carrier in universe `u`, the universe of `F`.
  A constituent of the local induced representation is a quotient of a
  subspace of its carrier, which lies in universe `u`, so every constituent
  has a representative of this kind.

So the Lean statement follows from GH Theorem 10.7.1 with Lemma 1 and the
background facts above. It is weaker than the sources in the ways listed in
§6.

## 4. Relation to other statements

- **`CuspidalIsobaricRealizationStatement`** (GH 10.7.5). Accepted by review
  as candidate `287a6e56`; it is not in the Library at commit `aad41a6e`,
  and this module does not import it. It has the same setup and asks for a
  `Q` whose restriction to each `GL_(r+1)(F_v)` contains the local isobaric
  sum `⊞_i σ_(i,v)`. GH's proof of 10.7.5 is: the local isobaric sum is a
  constituent of `i(σ_(1,v), …, σ_(k,v))` (GH Theorem 10.6.4) and is
  unramified for almost all `v` (GH Theorem 10.6.3); then Theorem 10.7.1
  applies. With `A_v := ⊞_i σ_(i,v)`, the present statement is that last
  step.
- **`CuspidalInducingDataRigidityStatement`** (GH 10.7.2). It compares two
  families of cuspidal data with a common spherical constituent at almost all
  places. With the present statement, GH Corollary 10.7.3 says that the `Q`
  obtained here determines `(T i)` up to permutation and isomorphism. That
  corollary is not stated.
- **Eisenstein series.** The Library's general-reductive Eisenstein
  statements, `Langlands.Global.EisensteinMeromorphicContinuationStatement`
  (`Langlands/Global/AdelicEisensteinContinuationStatement.lean`) and its
  neighbours in `Langlands/Global/AdelicEisenstein*`, are the analytic input
  of Langlands' proof (§5). They are not used by this statement.

## 5. Proof route (for the proof task; not part of the statement)

Langlands proves the direction stated here on pp.205–207. Fix an
irreducible representation `κ` of `K` contained in `π`; it suffices to show
that the `κ`-isotypic part of `π` is a constituent of the space of
automorphic forms of type `κ`, as a module over `ℋ_κ = ε_κ ℋ ε_κ`. Each `μ` in
the complexified lattice `L_ℂ` of rational characters of `M` gives a character
`ξ_μ` of `M(𝔸)`. The `κ`-isotypic parts `I_μ` of `Ind (ξ_μ σ)` are
identified with `I = I_0`. Near `μ = 0` an Eisenstein series, multiplied by a
product of linear functions, is holomorphic, takes values in automorphic
forms, intertwines the `ℋ` actions, and its derivatives in `μ` stay
automorphic. Germs of degree `d` at `0` of holomorphic sections form an
`ℋ_κ`-module `I_d`, mapped by the Eisenstein series into power series with
automorphic coefficients (Langlands' map `λ`, unrelated to GH's `λ`). Lemma 7:
for `d` large, the kernel of this map is contained in the kernel of
`I_d → I_0 = I`. The proof replaces the Eisenstein series by its constant
terms along the parabolics associate to `P`, reduces to finitely many
evaluation points (Lemma 8), and concludes with a lemma on holomorphic
families of linear maps between finite-dimensional spaces that are injective
on an open set (Lemma 9). The Jordan–Hölder theorem then gives the
proposition.

The step from the global constituent to the finite-place form here is the
argument of §3: Lemma 1's easy direction, choice of archimedean
constituents, and the tensor embedding.

## 6. Not asserted

- the converse half of GH 10.7.1 and of Langlands' Proposition 2: that every
  automorphic representation is a constituent of some `I(σ, λ)`;
- anything at the infinite places; in particular one cannot prescribe the
  archimedean components of `Q`;
- that `Q` is a constituent of the global induced representation, which is not
  in the Library;
- that `Q_v ≅ A_v`, admissibility of `Q`, or that the restriction of `Q` to
  `GL_(r+1)(F_v)` is isotypic (§3);
- uniqueness of `Q`;
- the hard direction of Lemma 1 (every constituent of the global induced
  representation is a restricted tensor product of local constituents);
- parabolics of groups other than `GL_n`, or non-standard parabolics;
- presentations in a universe `uQ ≠ u` are allowed by the statement, but the
  non-vacuity remark of §3 is for `uQ = u` only.

## 7. Provenance

This is a source statement: the "constituents are automorphic" half of GH
Theorem 10.7.1 (Langlands' Proposition 2), for `GL_n`, combined with the easy
direction of Langlands' Lemma 1. The following choices belong to this
formalization:

- the cuspidal data are arbitrary cuspidal realizations, with `λ` absorbed
  (§3, as in `CuspidalInducingDataRigidityStatement`);
- "almost all `π_v ≅ π°_v`" is replaced by "almost all `A_v` spherical",
  equivalent by the background argument of §3;
- "is automorphic" is replaced by the existence of an irreducible automorphic
  subquotient `Q` whose restriction to each `GL_(r+1)(F_v)`, `v` finite,
  contains `A_v`;
- only the finite places are covered.

The Lean file was checked with `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, with no errors and no warnings. The
declaration is a `def` returning `Prop`, with universe parameters `u` and
`uQ` and axioms `propext`, `Classical.choice`, `Quot.sound`.
