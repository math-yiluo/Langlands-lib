# Rigidity of cuspidal inducing data from unramified local components

Author: Worker 3657. Statement contribution to task
`34b81620-20d7-4059-9b08-6bedd1c1c029`, revision 1.

**Scope.** This module states one proposition and proves nothing:

- `Langlands.Global.CuspidalInducingDataRigidityStatement`.

The module is `Langlands.Global.Factors.CuspidalInducingDataRigidityStatement`.
The proposition is the representation-theoretic form of Jacquet–Shalika (1981),
*Euler products II*, Theorem (4.4), as restated in Getz–Hahn (2024), Theorem
10.7.2. Take two lists of cuspidal automorphic representations whose ranks
add up to the same `n`. Suppose that at almost all places their normalized
induced representations of `GL_n` have the same unramified subquotient. Then
the two lists have the same length and agree up to a permutation.

The module defines one `local instance` and nothing else. The instance is the
canonical topology on `GL_n(F_v)`, the one already used by the correspondence
category `Correspondence.AutomorphicObject (padicField v)`. Without it, Lean
picks the `Units` topology of the matrix ring, and the `representation` field
of a canonical object does not elaborate. Everything else is Library
vocabulary:

- `CuspidalOperatorRealization`, `CuspidalSpectralPresentation`,
  `PositiveRankCuspidalClass` (`Langlands/Automorphic/CuspidalOperatorRealization.lean`);
- `CuspidalPairFunctionalEquation.HasIrreducibleAdmissibleComponents` and
  `CuspidalPairFunctionalEquation.localClass`
  (`Langlands/Global/Factors/CuspidalPairFactorData.lean`);
- `LocalRealization.padicObject` (`Langlands/Automorphic/PadicLocalCategory.lean`);
- `PadicField.canonicalNormalizedProductInduced`
  (`Langlands/Representation/Induction/BlockFactors.lean`);
- `Correspondence.AutomorphicObject`, `Correspondence.IsSphericalClass`,
  `Correspondence.sphericalSubgroup` and `Correspondence.IsSubquotientOf`
  (`Langlands/Correspondence/AutomorphicRelations.lean` and
  `Langlands/Correspondence/UnramifiedNormalization.lean`).

The local components and their classes are the same ones used by the
published pair L-function statements and by the strong multiplicity one
statement `CuspidalStrongMultiplicityOneStatement`, accepted by review.

**Why it is here.** The program ledger
`notes/automorphic/global-program-coverage.md` lists the
representation-theoretic form of Getz–Hahn 10.7.2 as an L4 target with no
public statement. The list is in the closing paragraph of the section "13
November 2026 Getz–Hahn 11.7.1 poles, Lemma 11.8.1 and the H3 reduction". The
ledger row names task `91266440` as the owner of the L4 units. That task does
not exist in this project (`inspect` returns not found), and 10.7.2 is in the
L4 list of this task's contract. The Library has only the numerical
constituent-recovery step of JS II (4.4), which compares unramified spectra
(§5 below).

**Proof target.** A later proof task should prove the Library statement
`Langlands.Global.CuspidalInducingDataRigidityStatement`. Its universe
parameters are `u` (the number field, and every local carrier) and `uQ` (the
factor universe of the spectral presentations).

## 1. Sources

"p." is the printed page and "PDF" the one-based page of the registered file.

| Source ID | Short name | Locators used |
|---|---|---|
| `getz-hahn-2024-automorphic-representations` | GH | `I(σ, λ)` and its local factors, p.271 (PDF 283); Thm 10.7.1 and the unramified subquotient `π°_v`, pp.286–287 (PDF 298–299); Thm 10.7.2 and Cor 10.7.3, p.287 (PDF 299); the twist `π_i = \|det\|^(λ_i) π_i^1`, p.288 (PDF 300) |
| `jacquet-shalika-1981-euler-ii` | JS II | (4.3) and the parabolic `P`, p.807 (PDF 32); (2)–(5) and "associate pairs", p.808 (PDF 33); Thm (4.4) and its proof, p.809 (PDF 34) |

JS II is Jacquet–Shalika, *On Euler products and the classification of
automorphic forms II*, Amer. J. Math. 103 (1981), 777–815. Its registered file
has no text layer, so the pages were read as rendered images. The printed page
is the PDF page plus 775.

**What the sources state.** GH p.287 sets up the theorem as follows. Let
`∑_(i=1)^k n_i = ∑_(j=1)^(k') n'_j = n`. Let `σ_i` (resp. `σ'_j`) be cuspidal
automorphic representations of `A_(GL_(n_i)) \ GL_(n_i)(𝔸_F)` (resp. of
`A_(GL_(n'_j)) \ GL_(n'_j)(𝔸_F)`). Let `σ = ⊗_i σ_i` and `σ' = ⊗_j σ'_j`. The
induced representations `I(σ, λ)` and `I(σ', λ')` are formed with respect to the
standard parabolics `P` and `P'` of types `(n_1, …, n_k)` and
`(n'_1, …, n'_(k'))`. Then:

> **Theorem 10.7.2 (Jacquet and Shalika)** Let `S` be a finite set of places of
> `F` including the infinite places such that `I(σ, λ)` and `I(σ', λ')` are
> unramified outside of `S`. If the irreducible unramified subquotients of
> `I(σ_v, λ)` and `I(σ'_v, λ')` are isomorphic for `v ∉ S` then `k = k'` and
> there is a permutation `τ` of the set of `k` elements such that
> `σ_i ≅ σ'_(τ(i))` and `λ_i = λ'_(τ(i))`.

GH cites it as "[JS81a, Theorem 4.4]". The action of `I(σ, λ)` on p.271 has
the factor `e^⟨H_P(xg), λ + ρ_P⟩`, so the induction is normalized. On the same
page GH factor `I(σ, λ) ≅ ⊗'_v I(σ_v, λ)`, with the local factors defined in
§8.1 in the non-archimedean case. GH pp.286–287 (citing Langlands, appendix to
[BJ79], Lemma 1) say that for almost all `v` the representation `σ_v` is
unramified and `I(σ_v, λ)` has a unique irreducible unramified subquotient
`π°_v`. GH p.288: for each cuspidal `π_i` of `GL_(n_i)(𝔸_F)` there is a unique
cuspidal `π_i^1` of `A_(GL_(n_i)) \ GL_(n_i)(𝔸_F)` with
`π_i(g) = |det g|^(λ_i) π_i^1(g)` for some `λ_i ∈ ℂ`.

JS II (4.3), p.807: `P` is a standard parabolic subgroup of `G_r` of type
`(r_1, …, r_u)`. P.808: for `1 ≤ j ≤ u`, `σ_j` is an automorphic cuspidal
representation of `GL(m_j, 𝔸)`. At each place `σ_v = ⊗_j σ_(jv)` induces
`ξ_v = Ind(G_v, P_v; σ_v)` (formula (2)). `Q` of type `(s_1, …, s_w)` and `τ_j`
give `η_v = Ind(G_v, Q_v; τ_v)` (formula (4)). The pairs `(σ, P)` and `(τ, Q)`
are called *associate* if `u = w` and there is a permutation `φ` of
`{1, …, u}` with `s_j = r_(φ(j))` and `τ_j ≃ σ_(φ(j))`. P.809:

> (4.4) THEOREM. Let `P`, `Q`, `σ_j` and `τ_k` be as above. Let `S` be a finite
> set of places containing all the places at infinity. Suppose that for
> `v ∉ S` the representations `σ_(jv)` and `τ_(kv)` are unramified and that the
> representations `ξ_v` and `η_v` of `G_v` they induce have the same unramified
> component. Then the pairs `(σ, P)` and `(τ, Q)` are associate.

JS II does not restrict `σ_j` to be trivial on the split centre. The proof of
(4.2) on p.807 writes the cuspidal representations as `π_j ⊗ α^(t_j)` with
`π_j` unitary and `t_j` real. The proof of (4.4) on p.809 says that "the class
associated to the unramified component of `ξ_v` … is nothing other than
`⊕_j A_(jv)`", where `A_(jv)` is the Satake class of `σ_(jv)`. That holds for
normalized induction. These pages of JS II do not print the normalization;
GH's `I(σ, λ)` is normalized explicitly.

## 2. The declaration

`CuspidalInducingDataRigidityStatement` says the following. Let:

- `F` be a number field with `[CompactSpace (AdeleQuotient F)]`, the instance
  needed by `CuspidalOperatorRealization`;
- `r, k, k' : ℕ`, `m : Fin k → ℕ` and `m' : Fin k' → ℕ`, with
  `hm : ∑ i, (m i + 1) = r + 1` and `hm' : ∑ j, (m' j + 1) = r + 1`;
- `T i : CuspidalOperatorRealization F (m i)` and
  `T' j : CuspidalOperatorRealization F (m' j)`, actual cuspidal realizations of
  `GL_(m i + 1)` and `GL_(m' j + 1)` over `F`;
- `P i` and `P' j` be spectral presentations of `T i` and `T' j`, with factors in
  universe `uQ`;
- `h i`, `h' j` say that every finite local component of `P i` (resp. `P' j`)
  is irreducible and admissible (`HasIrreducibleAdmissibleComponents`);
- `S : Finset (FinitePlace F)` be a finite set of finite places.

Suppose that for every finite place `v ∉ S`:

1. every `localClass (P i) (h i) v` and every `localClass (P' j) (h' j) v` is
   spherical (`Correspondence.IsSphericalClass`);
2. there is `A : AutomorphicObject.{u, u} (padicField v) r.succPNat`, an
   irreducible admissible smooth representation of `GL_(r+1)(F_v)`, such that
   - `A` has a nonzero vector fixed by `sphericalSubgroup (padicField v) r`,
     that is by `GL_(r+1)(O_v)`;
   - `A` is a subquotient (`IsSubquotientOf`) of
     `(padicField v).canonicalNormalizedProductInduced B σ_v`, where `B` is the
     block shape `⟨k, fun i => m i + 1, _, hm⟩` and `σ_v i` is the
     representation of the canonical object
     `((P i).localComponent v).padicObject (h i v).1 (h i v).2`;
   - `A` is a subquotient of the same construction for `B'`, `P'` and `h'`.

Then there is `e : Fin k ≃ Fin k'` such that for every `i`,
`⟨m i, (T i).isoClass⟩ = ⟨m' (e i), (T' (e i)).isoClass⟩` in
`PositiveRankCuspidalClass F`.

## 3. Hypotheses and their match with the sources

- **Cuspidal representations and `λ`.** `CuspidalOperatorRealization F m` is an
  actual irreducible cuspidal subspace of automorphic forms on `GL_(m+1)`,
  with all finite, compact and differential operators. No condition is put on
  the split centre `A_GL` or on the central character. So `T i` is a
  cuspidal `π_i` of `GL_(n_i)(𝔸_F)`, `n_i = m i + 1`, in the sense of JS II
  and of GH p.288. By GH p.288, `π_i = |det|^(λ_i) ⊗ π_i^1` for a unique
  cuspidal `π_i^1` of `A_(GL_(n_i)) \ GL_(n_i)(𝔸_F)` and some `λ_i ∈ ℂ`. With
  normalized induction, `I(π^1, λ)_v` is the normalized induction of the local
  components `π_(iv)`. So the GH data `(σ_i, λ_i)` and the Lean data `T i`
  determine each other, and GH's conclusion `σ_i ≅ σ'_(τ(i))`,
  `λ_i = λ'_(τ(i))` says `π_i ≅ π'_(τ(i))`. The Lean statement takes this
  form, which is JS II's form: arbitrary cuspidal `σ_j`, no separate `λ`.
- **The local components.** As in `CuspidalStrongMultiplicityOneStatement`, a
  spectral presentation `P i` of `T i` is a nonzero finite-adelic-invariant
  subspace with an equivalence to a restricted tensor product of supplied
  local factors. `(P i).localComponent v` is the actual embedded factor at `v`,
  the `σ_(iv)` of the sources. Under `h i`, `LocalRealization.padicObject`
  views it as an object of `Correspondence.AutomorphicObject (padicField v)`,
  a smooth representation of `GL_(m i + 1)(F_v)` for the canonical p-adic
  topology. Its `representation` is the actual local action, unchanged.
- **Unramified components.** By `LocalRealization.padicClass_isSpherical_iff`
  (`Langlands/Automorphic/PadicLocalCategory.lean`), condition 1 says exactly
  that `(P i).localComponent v` has a nonzero vector fixed by
  `GL_(m i + 1)(O_v)`, that is, `σ_(iv)` is unramified. This is JS II's
  hypothesis "`σ_(jv)` and `τ_(kv)` are unramified". GH instead assumes
  `I(σ, λ)` unramified outside `S`. For irreducible `σ_(iv)` this is the same
  condition, by the Iwasawa decomposition `G_v = P_v K_v`. That equivalence is
  background; the statement uses JS II's form.
- **The induced representations.** `canonicalNormalizedProductInduced B σ_v` is
  `i(σ_(1,v), …, σ_(k,v))`: the smooth vectors of the space of functions on
  `GL_(r+1)(F_v)` with `f(pg) = δ_P(p)^(1/2) (σ_(1,v)(m_1) ⊗ ⋯ ⊗ σ_(k,v)(m_k)) f(g)`
  for the standard upper block parabolic `P` with block sizes
  `m 0 + 1, …, m (k-1) + 1` in this order (`normalizedProductInduced_covariant`
  in `BlockFactors.lean`). This is GH's local `I(σ_v, λ)` for `P` of type
  `(n_1, …, n_k)`, after `λ` is absorbed as above, and JS II's
  `ξ_v = Ind(G_v, P_v; σ_v)` read as normalized induction (§1).
- **The same unramified subquotient.** GH speaks of "the irreducible unramified
  subquotients" and JS II of "the same unramified component". The Lean
  hypothesis asks for one irreducible admissible `A` with a nonzero
  `GL_(r+1)(O_v)`-fixed vector that is a subquotient of both induced
  representations. `IsSubquotientOf ρ A` means that a subrepresentation of `ρ`
  maps onto `A` by an intertwining map. For unramified data the two forms are
  equivalent. An induced representation `i(σ_(1,v), …, σ_(k,v))` of unramified
  irreducible admissible representations has a one-dimensional space of
  `GL_(r+1)(O_v)`-fixed vectors and finite length. Taking fixed vectors under a
  compact open subgroup is exact. So it has exactly one spherical irreducible
  subquotient up to isomorphism, GH's `π°_v` (GH pp.286–287). If the two
  `π°_v` are isomorphic, either one serves as `A`. It lives in universe `u`,
  as a quotient of a subspace of the induced carrier, which is in universe `u`.
  Conversely, `A` is isomorphic to both `π°_v`. This equivalence is background
  and is not asserted.
- **The infinite places.** GH's and JS II's `S` contain the infinite places,
  and nothing is assumed there. The Lean `S` holds finite places only and
  nothing is assumed at the infinite places. Taking the finite places of the
  source `S` gives the Lean `S`, and conversely the Lean `S` together with the
  infinite places is a source `S`.
- **The ranks.** Each block has size `m i + 1 ≥ 1`, as in the sources. The two
  sums `hm`, `hm'` are GH's `∑ n_i = ∑ n'_j = n` with `n = r + 1`. The
  conclusion needs no separate `k = k'`: it is part of `e : Fin k ≃ Fin k'`.
- **The statement is not vacuous.** For `uQ = u`, every cuspidal realization
  has a presentation with irreducible admissible components, by the proved
  `cuspidalIrreducibleAdmissibleFiniteSliceExistence`
  (`Langlands/Automorphic/CuspidalAdmissible/Existence.lean`) and
  `CuspidalOperatorRealization.exists_presentation_of_finiteSlice`
  (`Langlands/Automorphic/CuspidalSlicePresentation.lean`). These are the
  facts cited in `CuspidalStrongMultiplicityOneStatement`.

## 4. The conclusion

`PositiveRankCuspidalClass F` is the dependent pair type
`Σ r, CuspidalOperatorRealization.IsoClass F r`. The equality
`⟨m i, (T i).isoClass⟩ = ⟨m' (e i), (T' (e i)).isoClass⟩` says that
`m' (e i) = m i` and that, at this common rank, `T i` and `T' (e i)` have the
same full operator class. By `PositiveRankCuspidalClass.ofFixedRank_isoClass_eq_iff`
and `CuspidalOperatorRealization.isoClass_eq_iff`, that means a linear
equivalence of the carriers intertwining all finite, compact and differential
operators: `π_i ≅ π'_(e(i))`. With `τ = e` this is GH's conclusion `k = k'`,
`σ_i ≅ σ'_(τ(i))`, `λ_i = λ'_(τ(i))`, read through the first bullet of §3. With
`φ = e⁻¹` it is JS II's "the pairs `(σ, P)` and `(τ, Q)` are associate".

Equivalently, the two multisets `{⟨m i, (T i).isoClass⟩}` and
`{⟨m' j, (T' j).isoClass⟩}` of positive-rank cuspidal classes are equal. Such
multisets are the Library's `Langlands.Automorphic.IsobaricData F`
(`Langlands/Automorphic/IsobaricData.lean`). The statement does not use that
type.

## 5. Relation to other statements

- **`CuspidalSpectralRigidityStatement`**
  (`Langlands/Automorphic/Unramified/CuspidalSpectralRigidityStatement.lean`).
  Its `CuspidalPowerTraceConstituentRecoveryStatement` is described there as
  "the numerical constituent-recovery step in JS81 Theorem 4.4". It has the
  same conclusion shape `∃ e : Fin p ≃ Fin q, ∀ i, c i = d (e i)`, but its
  hypothesis compares supplied spectral systems by power traces, as in
  formula (2) of the proof of (4.4). `CuspidalEulerConstituentRecoveryStatement`
  compares Euler polynomials instead. This statement is not a specialization
  of either. A proof must link the local induced representations to the
  spectra (§6).
- **`CuspidalStrongMultiplicityOneStatement`** (GH 11.7.2), accepted by review.
  With `k = k' = 1` this statement concerns one cuspidal realization on each
  side of the same rank. A one-block normalized induction is equivalent to
  the representation itself, so the hypothesis then compares the unramified
  local components. Neither statement is derived from the other here.

## 6. Proof route (for the proof task; not part of the statement)

JS II's route, p.809. At `v ∉ S`, let `A_(iv)` be the Satake class of
`σ_(iv)`. The unique spherical subquotient of `i(σ_(1,v), …, σ_(k,v))` has the
Satake class `⊕_i A_(iv)`. So the hypothesis gives `⊕_i A_(iv) = ⊕_j B_(jv)`
as unordered spectra. Hence the power traces agree:
`∑_i σ_i(v^n) = ∑_j σ'_j(v^n)` for all `v ∉ S` and `n ≥ 1`. Then the linear
independence of JS II (4.2) gives the permutation. In Library terms:

- the Satake class of a spherical local component: the spectral systems of
  the presentations (`P.spectralSystem.eigenvalues v`), and the spherical
  spectrum vocabulary `HasSphericalSpectrum` and `IsSphericalConstituent`
  (`Langlands/Representation/Unramified/PrincipalSeries.lean`,
  `SphericalClassificationStatement.lean`);
- the induced spectrum: the spherical subquotient of a block-induced
  representation of unramified blocks has the concatenated spectrum. This
  needs induction in stages to a principal series, and it is not yet in the
  Library;
- the numerical step: `CuspidalPowerTraceConstituentRecoveryStatement`, or
  `CuspidalEulerConstituentRecoveryStatement` after passing to Euler
  polynomials.

The rigidity statements are not proved in the Library at this time.

## 7. Not asserted

- GH Corollary 10.7.3, which concerns a global irreducible subquotient of both
  `I(σ, λ)` and `I(σ', λ')`;
- the isobaric sum or its irreducibility (GH Theorem 10.7.5, Definition 10.7.6);
- the existence or uniqueness of the spherical subquotient (§3);
- independence of the local components from the presentations;
- equality of `T i` and `T' (e i)` as subspaces of the cusp forms;
- anything at the infinite places;
- presentations in a universe `uQ ≠ u`.

## 8. Provenance

This is a source statement: JS II Theorem (4.4) in GH's form Theorem 10.7.2.
The following choices belong to this formalization:

- the cuspidal data are arbitrary cuspidal realizations, with `λ` absorbed
  (§3, JS II's form);
- `S` holds finite places only (§3);
- the local components are read through spectral presentations, as in the
  published pair statements;
- "the same unramified subquotient" is the existence of one common spherical
  irreducible subquotient (§3, equivalent for unramified data).

The Lean file was checked with `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, with no errors and no warnings. The
declaration is a `def` returning `Prop`, with universe parameters `u` and `uQ`
and axioms `propext`, `Classical.choice`, `Quot.sound`.
