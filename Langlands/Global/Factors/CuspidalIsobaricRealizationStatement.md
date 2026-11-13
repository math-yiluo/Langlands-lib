# Automorphy of isobaric sums of cuspidal representations, at the finite places

Author: Worker 3657. Statement contribution to task
`34b81620-20d7-4059-9b08-6bedd1c1c029`, revision 1.

**Scope.** This module states one proposition and proves nothing:

- `Langlands.Global.CuspidalIsobaricRealizationStatement`.

The module is `Langlands.Global.Factors.CuspidalIsobaricRealizationStatement`.
The proposition is Getz–Hahn (2024), Theorem 10.7.5, at the finite places. Take
cuspidal automorphic representations `π_1, …, π_k` of `GL_(n_i)(𝔸_F)` with
`∑ n_i = n`. Then there is an irreducible automorphic representation of
`GL_n(𝔸_F)` whose component at every finite place `v` is the local isobaric
sum `π_(1,v) ⊞ ⋯ ⊞ π_(k,v)`. That local isobaric sum is also a subquotient of
the normalized induced representation `i(π_(1,v), …, π_(k,v))`.

The same contribution adds the definition module
`Langlands.Representation.Classification.IsobaricSum`
(`Langlands/Representation/Classification/IsobaricSum.lean` and `.md`), with
the local relation `PadicField.TopologicalData.IsIsobaricSum`. The statement
module defines one `local instance`: the canonical topology on `GL_n(F_v)`, as
in `CuspidalInducingDataRigidityStatement`. Everything else is Library
vocabulary:

- `CuspidalOperatorRealization`, `CuspidalSpectralPresentation`
  (`Langlands/Automorphic/CuspidalOperatorRealization.lean`);
- `CuspidalPairFunctionalEquation.HasIrreducibleAdmissibleComponents`
  (`Langlands/Global/Factors/CuspidalPairFactorData.lean`);
- `LocalRealization.padicObject` (`Langlands/Automorphic/PadicLocalCategory.lean`);
- `PadicField.canonicalNormalizedProductInduced`
  (`Langlands/Representation/Induction/BlockFactors.lean`);
- `Correspondence.AutomorphicObject` and `Correspondence.IsSubquotientOf`
  (`Langlands/Correspondence/AutomorphicRelations.lean`,
  `Langlands/Correspondence/UnramifiedNormalization.lean`);
- `Automorphic.IrreducibleOperatorSubquotient`
  (`Langlands/Automorphic/IrreducibleOperatorSubquotient.lean`) and
  `OperatorSubquotient.localRepresentation`
  (`Langlands/Automorphic/OperatorSubquotient.lean`).

**Why it is here.** Getz–Hahn 10.7.5 is in the L4 list of this task's
contract. The program ledger `notes/automorphic/global-program-coverage.md`
has no public statement for it. The Library already has the data side of
isobaric representations, the multisets `Automorphic.IsobaricData F` of
positive-rank cuspidal classes, but no statement that such data are realized
by automorphic representations.

**Proof target.** A later proof task should prove the Library statement
`Langlands.Global.CuspidalIsobaricRealizationStatement`. Its universe
parameters are `u` (the number field, every local carrier and the
multisegments) and `uQ` (the factor universe of the spectral presentations).

## 1. Sources

"p." is the printed page and "PDF" the one-based page of the registered file.

| Source ID | SHA-256 | Locators used |
|---|---|---|
| `getz-hahn-2024-automorphic-representations` | `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507` | local isobaric sum, Thm 10.6.1, (10.33), pp.284–285 (PDF 296–297); Thm 10.6.3, p.285 (PDF 297); Thm 10.6.4 and Thm 10.7.1, p.286 (PDF 298); `π_i = \|det\|^(λ_i) π_i^1`, Thm 10.7.5 and its proof, Def 10.7.6, p.288 (PDF 300) |
| `kudla-1994-local-langlands-nonarchimedean` | `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b` | segment form of the Langlands classification, Thm 1.2.5, pp.370–371 (PDF 380–381); used through `IsIsobaricSum` |
| `zelevinsky-1980-induced-ii` | `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac` | associativity of products, §1.7, pp.172–173 (PDF 9–10); Thm 1.9, commutativity of the representation ring, p.174 (PDF 11) |

**What GH state.** On p.288 GH fix cuspidal automorphic representations
`π_i` of `GL_(n_i)(𝔸_F)`, `1 ≤ i ≤ k`. For each, `π_i^1` is the unique
cuspidal automorphic representation of `A_(GL_(n_i)) \ GL_(n_i)(𝔸_F)` with
`π_i(g) = |det g|^(λ_i) π_i^1(g)` for some `λ_i ∈ ℂ`. "After rearranging the
`π_i` we can assume (10.30) holds", that is `Re(λ_1) ≥ ⋯ ≥ Re(λ_k)`. With `P`
the standard parabolic of type `(n_1, …, n_k)` and `λ = (λ_1, …, λ_k)`, GH form
`I(⊗_(i=1)^k π_i^1, λ)`, and "by Theorem 10.7.1 any irreducible subquotient of
this representation is automorphic". Then:

> **Theorem 10.7.5** The representation
> `⊞_(i=1)^k π_i := ⊗'_v (⊞_(i=1)^k π_(iv))` (10.35)
> is an irreducible subquotient of `I(⊗_(i=1)^k π_i^1, λ)`, hence automorphic.

The proof: the `π_(iv)` are generic (GH Theorem 11.3.6) and essentially
unitary. So for all `v`, `⊞_i π_(iv)` is an irreducible subquotient of
`I(⊗_i π_(iv)^1, λ)` by Theorem 10.6.4, and it is unramified for almost all `v`
by Theorem 10.6.3. The discussion after Theorem 10.7.1 (Langlands, appendix to
[BJ79]) on irreducible subquotients of `I(σ, λ)` then gives the theorem. The
local isobaric sum `⊞_i π_(iv)` is GH's `J` of §10.6, extended to arbitrary
irreducible representations by (10.33); see `IsobaricSum.md` §1. Definition
10.7.6 (pp.288–289) then calls an automorphic representation isobaric if it is
isomorphic to some `⊞_i π_i` with all `π_i` cuspidal.

## 2. The declaration

`CuspidalIsobaricRealizationStatement` says the following. Let:

- `F` be a number field with `[CompactSpace (AdeleQuotient F)]`, the instance
  needed by `CuspidalOperatorRealization`;
- `r, k : ℕ` and `m : Fin k → ℕ` with `hm : ∑ i, (m i + 1) = r + 1`;
- `T i : CuspidalOperatorRealization F (m i)`, actual cuspidal realizations of
  `GL_(m i + 1)` over `F`;
- `P i` be spectral presentations of `T i`, with factors in universe `uQ`;
- `h i` say that every finite local component of `P i` is irreducible and
  admissible (`HasIrreducibleAdmissibleComponents`).

Write `σ_(i,v)` for the canonical object
`((P i).localComponent v).padicObject (h i v).1 (h i v).2` of
`AutomorphicObject (padicField v)`. Then there is
`Q : IrreducibleOperatorSubquotient F r` such that for every finite place `v`
there is `A : AutomorphicObject.{u, u} (padicField v) r.succPNat`, an
irreducible admissible smooth representation of `GL_(r+1)(F_v)`, with:

1. `(padicField v).canonicalTopologicalData.IsIsobaricSum (fun i => σ_(i,v).obj) A.obj`:
   `A` is the isobaric sum `σ_(1,v) ⊞ ⋯ ⊞ σ_(k,v)`;
2. `A` is a subquotient (`IsSubquotientOf`) of
   `(padicField v).canonicalNormalizedProductInduced B (fun i => σ_(i,v).obj.representation)`,
   where `B` is the block shape `⟨k, fun i => m i + 1, _, hm⟩`;
3. there is an injective intertwining map from `A` to
   `Q.subquotient.localRepresentation v`, the restriction of `Q` to
   `GL_(r+1)(F_v)`.

## 3. Hypotheses and conclusion, matched with GH

- **Cuspidal representations and `λ`.** As in
  `CuspidalInducingDataRigidityStatement` §3, `T i` is a cuspidal `π_i` of
  `GL_(n_i)(𝔸_F)` with `n_i = m i + 1`, with no condition on the split centre.
  It is GH's `π_i` of p.288, not `π_i^1`. With normalized induction, the local
  factor of `I(⊗π_i^1, λ)` at `v` is the normalized induction of the
  `π_(iv) = |det|^(λ_i) π_(iv)^1`. So GH's `I(⊗_i π_(iv)^1, λ)` is
  `i(σ_(1,v), …, σ_(k,v))`.
- **Local components.** `(P i).localComponent v` is the actual embedded
  factor at `v` of a spectral presentation, GH's `π_(iv)`;
  `LocalRealization.padicObject` views it in the correspondence category with
  its original action (see `CuspidalStrongMultiplicityOneStatement`). The
  hypothesis `h` is the one of the published pair statements. The statement
  is not vacuous: for `uQ = u` every cuspidal realization has such a
  presentation (`cuspidalIrreducibleAdmissibleFiniteSliceExistence` and
  `CuspidalOperatorRealization.exists_presentation_of_finiteSlice`, cited in
  `CuspidalInducingDataRigidityStatement` §3).
- **Condition 1, the local isobaric sum.** By `IsobaricSum.md` §3, given
  Kudla's Theorem 1.2.5, condition 1 holds exactly when `A ≅ ⊞_i π_(iv)` in
  GH's sense. The multisegments live in universe `u`.
- **Condition 2, the induced representation.** `canonicalNormalizedProductInduced`
  is normalized smooth induction from the standard upper block parabolic with
  blocks `m 0 + 1, …, m (k-1) + 1` in this order. GH order the blocks by
  (10.30); the Lean statement keeps the given order. Zelevinsky (1980),
  Theorem 1.9: "The ring `R` is commutative. In other words if `π_1`, `π_2` …
  are of finite length then `π_1 × π_2` and `π_2 × π_1` have the same
  composition factors." With the associativity of products (Zelevinsky §1.7),
  the composition factors of `i(σ_1, …, σ_k)`, for blocks of finite length, do
  not depend on the order of the blocks. An irreducible representation is a
  subquotient of a finite-length representation exactly when it is one of its
  composition factors. So condition 2 is GH's local statement "irreducible
  subquotient of `I(⊗π_(iv)^1, λ)`" (from Theorem 10.6.4), for any order. This
  order-independence is background; it is not asserted.
- **Condition 3 and `Q`.** `IrreducibleOperatorSubquotient F r` is an actual
  invariant subspace of automorphic forms on `GL_(r+1)` modulo an invariant
  subspace, irreducible under the whole operator algebra: finite adelic
  translations, the standard maximal compact at infinity and the enveloping
  algebra (`IrreducibleOperatorSubquotient.md`). This is the Library's form of
  an irreducible automorphic representation, GH's "automorphic". GH's theorem
  gives such a `Q` isomorphic to `⊗'_w (⊞_i π_(iw))`. Its restriction to
  `GL_(r+1)(F_v)` is a direct sum of copies of `⊞_i π_(iv)`, so condition 3
  holds with `A ≅ ⊞_i π_(iv)` realized inside `Q`; such an `A` has its carrier
  in universe `u`. Conversely, given background facts (an irreducible
  automorphic `Q` is admissible and factors as a restricted tensor product,
  Flath), its restriction to `GL_(r+1)(F_v)` is `Q_v`-isotypic. So condition 3
  says `Q_v ≅ A`, and conditions 1 and 3 say that the finite part of `Q` is
  `⊗'_(v finite) (⊞_i π_(iv))`.
- **The places.** GH's statement covers all places. The Lean statement covers
  the finite places, all of them, and says nothing at the infinite places.

So the Lean statement follows from GH Theorem 10.7.5 and the background facts
above. It is weaker than GH in three ways, recorded in §6.

## 4. Relation to other statements

- **`CuspidalInducingDataRigidityStatement`** (GH 10.7.2), accepted by review.
  It shares the setup. At the places where all `σ_(i,v)` are unramified, the
  spherical subquotient of `i(σ_(1,v), …, σ_(k,v))` is `⊞_i σ_(i,v)` (GH Theorem
  10.6.3). So 10.7.2 says that the unramified local components of `Q` at almost
  all places determine the cuspidal data up to permutation. GH use this after
  Definition 10.7.6 to extend `⊞` to isobaric representations. That
  consequence is not stated here.
- **`Automorphic.IsobaricData F`** (`Langlands/Automorphic/IsobaricData.lean`):
  the multiset `{⟨m i, (T i).isoClass⟩}` is the isobaric datum of the family.
  This statement realizes it at the finite places.
- **`CuspidalIsobaricPoleOrderStatement`** (GH Lemma 11.8.1) uses GH's
  convention that the L-function of an isobaric sum is a product of pair
  L-functions. It does not use `IsIsobaricSum`, and neither statement is
  derived from the other.

## 5. Proof route (for the proof task; not part of the statement)

GH's route has three inputs:

- local genericity of cuspidal components (GH Theorem 11.3.6). The Library has
  `Automorphic.CuspidalLocalGenericityStatement` and its proved
  unitary-central-character form `Automorphic.cuspidalUnitaryLocalGenericity`
  (`Langlands/Automorphic/CuspidalUnitaryLocalGenericity.lean`);
- the local subquotient theorem for essentially unitary generic blocks (GH
  Theorem 10.6.4, through Moeglin–Waldspurger 1989 §1.2(3)), plus the
  identification of the head of a multisegment with GH's `J` (Kudla 1.2.5);
- Langlands' theorem that irreducible subquotients of the global `I(σ, λ)` are
  automorphic (GH Theorem 10.7.1, appendix to Borel–Jacquet 1979), with its
  description of those subquotients. The Library has no global parabolically
  induced representation or Eisenstein series for this purpose.

The second and third inputs are not in the Library at this time.

## 6. Not asserted

- anything at the infinite places, including the archimedean isobaric sum;
- that `Q` is a subquotient of the global induced representation
  `I(⊗π_i^1, λ)`, which is not in the Library;
- admissibility of `Q`, or that the restriction of `Q` to `GL_(r+1)(F_v)` is
  isotypic;
- uniqueness of `Q`, of `A` or of the multisegments;
- independence of the local components from the presentations;
- GH Definition 10.7.6. GH note on p.289 that not all automorphic
  representations are isobaric (Exercise 10.8). A predicate "isobaric"
  phrased through the finite places alone would be too weak. For example, let
  `F` have a real place `w`. By GH Theorem 10.7.1, the irreducible subquotient
  of the global `I(1 ⊗ 1, (1/2, -1/2))` of `GL_2` that is the
  infinite-dimensional constituent of the local induced representation at `w`
  and the trivial representation at every other place is automorphic. Its finite part is that of the trivial representation
  `|·|^(1/2) ⊞ |·|^(-1/2)`. It is not isobaric: by Theorem 10.7.2 any cuspidal
  data for it would be `{|·|^(1/2), |·|^(-1/2)}`, whose isobaric sum is trivial
  at `w`. The data side is `Automorphic.IsobaricData`;
- presentations in a universe `uQ ≠ u`.

## 7. Provenance

This is a source statement: GH Theorem 10.7.5. The following choices belong
to this formalization:

- the local isobaric sum is the derived relation `IsIsobaricSum` in Kudla's
  segment form (`IsobaricSum.md` §3);
- the cuspidal data are arbitrary cuspidal realizations, with `λ` absorbed
  (§3, as in `CuspidalInducingDataRigidityStatement`);
- "an irreducible subquotient of `I(⊗π_i^1, λ)`, hence automorphic" is
  replaced by the existence of an irreducible automorphic subquotient `Q`
  whose restriction to each `GL_(r+1)(F_v)`, `v` finite, contains `⊞_i π_(iv)`,
  together with the local subquotient property (§3);
- only the finite places are covered.

The Lean files were checked with `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, with no errors and no warnings. The
declaration is a `def` returning `Prop`, with universe parameters `u` and `uQ`
and axioms `propext`, `Classical.choice`, `Quot.sound`.
