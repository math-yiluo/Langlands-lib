# Galois conjugation and weak transfer of isobaric constituent data

Worker 12 authored this definition unit for task
`91266440-3276-48dc-ab77-8d1c1fa386e8`. It extends Worker 8's published
`Langlands.Automorphic.IsobaricData` with the operations that the Arthur–Clozel
statements of `IsobaricCyclicTransferStatement` need. The `IsobaricData` Markdown
leaves "Galois actions and twists on isobaric data … to the statement modules that use
them". Nothing here asserts that any lift, induction or attached spectral system exists.

Isobaric data `D : IsobaricData F` are a finite multiset of actual cuspidal classes of
positive rank (`PositiveRankCuspidalClass F`). They stand for the representation
`Π₁ × ⋯ × Π_b` induced from the cuspidal data `Π₁ ⊗ ⋯ ⊗ Π_b` (Arthur–Clozel III,
Definition 4.1). `D.rank` is the sum of the ranks. `D.HasSpectralSystem s` says that `s`
agrees, outside a finite set of places, with the direct sum of spectral systems attached to
the constituents through actual spectral presentations.

## Invariance of the numerical transfer relations

In namespace `Langlands.Unramified.SpectralSystem`, for number fields `F`, `E` with
`[Algebra F E]`:

- `SameEulerPolynomials.eventually_above`: if two systems over `E` have the same Euler
  polynomials outside a finite set of places of `E`, then for all places `v` of `F`
  outside a finite set, the second system is defined at every `w | v` and the Euler
  polynomials agree there. The proof turns the cofinite agreement into an explicit finite
  set and applies the published `eventually_avoidsAbove`.
- `IsArithmeticWeakBaseChangeOf.of_sameEulerPolynomials`: the published relation
  `t.IsArithmeticWeakBaseChangeOf s` is preserved when `s` and `t` are replaced by
  systems with the same Euler polynomials outside finite sets. The relation compares
  eigenvalue multisets. Equal Euler polynomials give equal multisets by the published
  `Eigenvalues.eulerPolynomial_injective`.
- `inducedEulerPolynomial_congr`: the published induced Euler polynomial at `v` depends
  only on the Euler polynomials at the places above `v`.
- `IsArithmeticWeakInductionOf.of_sameEulerPolynomials`: the same invariance for the
  published weak-induction relation.

## Galois conjugation of isobaric data

Let `F` be a field, `E` a number field with `[Algebra F E]` and
`[CompactSpace (AdeleQuotient E)]`, and `σ : E ≃ₐ[F] E`.

- `galoisConj σ D = D.map (PositiveRankCuspidalClass.galoisConj σ)` replaces every
  constituent `c` by its conjugate `c ∘ σ⁻¹`. It keeps multiplicities, and each conjugate
  keeps its rank. The class-level `PositiveRankCuspidalClass.galoisConj` is the published
  Galois action of `OperatorArithmeticTransportClasses` on mixed positive-rank classes.
  Conjugating the induced representation `Π₁ × ⋯ × Π_b` by `σ` gives
  `Π₁^σ × ⋯ × Π_b^σ`, which is why the operation acts on constituents. The convention
  `c ∘ σ⁻¹` is that of `ArithmeticTransportRelation`.
- Proved laws: `galoisConj_zero`, `galoisConj_add`,
  `galoisConj_ofCuspidal` (`(ofCuspidal c)^σ = ofCuspidal c^σ`), `rank_galoisConj`,
  `galoisConj_one` and `galoisConj_mul`. `galoisAction` packages them as an installable
  `MulAction (E ≃ₐ[F] E) (IsobaricData E)`. It is marked `@[instance_reducible]`, and no
  global instance is installed.
- `IsGaloisStable σ D` means `galoisConj σ D = D`. This is the source's "`Π` is
  `σ`-stable" for representations induced from cuspidal data. By Arthur–Clozel (2.4)
  (Jacquet–Shalika), such a representation determines its cuspidal data up to order.

With `[FiniteDimensional F E]`, so that `Gal(E/F)` is finite:

- `galoisOrbit F c` is the multiset of the conjugates `c^τ`, one for each
  `τ ∈ E ≃ₐ[F] E`. For `E/F` cyclic with generator `σ` of order `ℓ`, it is the data of
  `Π₁ × Π₁^σ × ⋯ × Π₁^{σ^{ℓ-1}}` in Theorem 4.2(b), (e) and Lemma 6.4.
- `rank_galoisOrbit`: its rank is `|Gal(E/F)| · c.rank`. Under `[IsGalois F E]`,
  `rank_galoisOrbit_of_isGalois` gives `[E : F] · c.rank`, by Mathlib's
  `IsGalois.card_aut_eq_finrank`.
- `isGaloisStable_galoisOrbit`: the orbit is stable under every automorphism. The proof
  reindexes the multiset over the group by left multiplication, using
  `Multiset.map_univ_val_equiv`.

## Weak transfer of isobaric data

Let `F`, `E` be number fields in universes `uF`, `uE`, with `[Algebra F E]` and both
adele quotients compact. The universes `uV`, `uW` are those of the spectral presentations
on the two sides.

- `IsWeakBaseChangeOf DE DF` means three things: `DE.rank = DF.rank`; there are systems
  `s` attached to `DF` and `t` attached to `DE`; and `t`, transported to rank `DF.rank` by
  the rank equation, is an arithmetic weak base change of `s` in the sense of the
  published `SpectralSystem.IsArithmeticWeakBaseChangeOf`. This is Arthur–Clozel III,
  Definition 1.1 (`t_{π,v}^{f_v} = t_{Π,w}` for almost all `v` and all `w | v`), for the
  representations induced from the two data. Their Hecke matrices at almost all places
  are the direct sums of those of the constituents.
- `IsWeakInductionOf DF DE` means that some system attached to `DF` is the arithmetic weak
  induction (published `SpectralSystem.IsArithmeticWeakInductionOf`) of some system
  attached to `DE`. This is Definition 6.1, formulas (6.1)–(6.2), as in the published
  cuspidal relation. The published relation includes the rank equation, and
  `IsWeakInductionOf.rank_eq` extracts `DF.rank = DE.rank · [E : F]`.
  `IsWeakBaseChangeOf.rank_eq` extracts the rank equation of base change.
- `isWeakBaseChangeOf_ofCuspidal_iff` and `isWeakInductionOf_ofCuspidal_iff`: for the data
  of single cuspidal classes, the relations are exactly the published class relations
  `IsoClass.IsWeakBaseChangeOf` and `IsoClass.IsWeakInductionOf` of
  `Automorphic.Unramified.WeakTransfer`. The proofs pass between systems attached to
  `ofCuspidal c` and systems attached to `c` with the published
  `HasSpectralSystem.exists_ofCuspidal` and `hasSpectralSystem_ofCuspidal_of`. They then
  use the invariance lemmas above.

Both relations are existential over attached systems, as are the published cuspidal
relations. If all systems attached to the same data have the same Euler polynomials
outside a finite set, the invariance lemmas show that the choice of witnesses does not
matter. That fact follows from the uniqueness of local components. It is neither stated
nor used here.

## Source correspondence

J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the
Trace Formula*, Annals of Mathematics Studies 120 (1989), literature ID
`arthur-clozel-1989-base-change`, SHA256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`, PDF page = printed
page + 14. Read from the original: Chapter III, Definition 1.1 (printed p.199), (2.4)
(printed p.200), Definition 4.1 and the notation `Π₁ × ⋯ × Π_b` before Theorem 4.2
(printed p.202), and Definition 6.1 with (6.1)–(6.2) (printed pp.215–216).

The constructions are internal. They compose published objects and identify them with the
source's notions as described above.

## Scope

No isobaric or induced representation is constructed, and no existence, uniqueness or
compatibility of transfers is asserted. Twists of isobaric data are not defined. The
statements that use these relations are in
`Langlands.Automorphic.Unramified.IsobaricCyclicTransferStatement`.
