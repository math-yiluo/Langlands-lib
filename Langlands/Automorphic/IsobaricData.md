# Isobaric constituent data

Worker 8 authored this definition unit for task
`6c50b2fd-cb4a-47b3-8f5d-d464916d69fb`. All declarations lie in the namespace
`Langlands.Automorphic`. The module defines the *constituent data* of an isobaric
automorphic representation `Π₁ ⊞ ⋯ ⊞ Π_b` of `GL_n` over a number field, and its unitarity
condition. Arthur–Clozel write such a representation, induced from cuspidal data, as
`Π₁ × ⋯ × Π_b`. The module also defines the numerical spectral systems attached to the
data through actual spectral presentations of the constituents.

The data are distinct from any realization. The module constructs no induced, isobaric
or automorphic representation, and it asserts no existence, irreducibility or uniqueness.

## Setting

`F : Type uF` is a number field with `[CompactSpace (AdeleQuotient F)]`, the standing
hypothesis of the published cuspidal classes. `PositiveRankCuspidalClass F` is the published
type `Σ r, CuspidalOperatorRealization.IsoClass F r` of actual cuspidal isomorphism classes of
`GL_{r+1}` over `F`, with `rank c = r + 1`.

## Declarations

### The data and their rank

- `IsobaricData F` is `Multiset (PositiveRankCuspidalClass F)`: finitely many actual cuspidal
  classes, with repetitions, unordered. Isobaric sum is multiset addition, and the empty
  multiset is the data of `GL_0`.
- `IsobaricData.rank D` is the sum of the ranks of the constituents, the `n` of `GL_n`.
  `rank_eq_sum` restates the definition. `rank_zero`, `rank_add`, `rank_cons` and
  `rank_singleton` compute it, and `rank_pos_iff` says that the rank is positive exactly for
  nonempty data.
- `IsobaricData.ofCuspidal c` is the singleton `{c}`, the data of one cuspidal class, with
  `rank_ofCuspidal : (ofCuspidal c).rank = c.rank`.

### Unitarity

- `IsobaricData.IsUnitary D`: every constituent `c` is unitarizable. This means the published
  `OperatorRealization.IsoClass.IsUnitarizable` of `c.2.toOperatorClass`: an actual
  representative carries a positive definite invariant Hermitian form. `isUnitary_zero`,
  `isUnitary_add` and `isUnitary_ofCuspidal` compute it.

### Attached spectral systems

`IsobaricData.HasSpectralSystem D s`, for a published spectral system
`s : SpectralSystem (FinitePlace F) D.rank`, requires the following data:

- an enumeration `σ : Fin k → PositiveRankCuspidalClass F` of the constituents with their
  multiplicities, so that `Finset.univ.val.map σ = D`;
- spectral systems `t j` of rank `(σ j).rank`, each attached to the class `σ j` by the published
  `PositiveRankCuspidalClass.HasSpectralSystem`, through some actual spectral presentation
  of some actual representative.

It then requires that the published numerical sum `SpectralSystem.finiteSum t` and `s` have
the same Euler polynomials outside a finite set (`SameEulerPolynomials`). At such a place
the Euler polynomial of `s` is the product of those of the constituents. Each constituent
attachment is existential, and the universe `uV` of the presentations' local factors is an
independent universe parameter of `HasSpectralSystem`, as in the cuspidal relation.

Proved properties:

- `HasSpectralSystem.of_sameEulerPolynomials`: attachment depends only on the Euler
  polynomials outside a finite set;
- `sameEulerPolynomials_finiteSum_one`: a one-term finite sum has the Euler polynomials of its
  term;
- `hasSpectralSystem_ofCuspidal_of` and `HasSpectralSystem.exists_ofCuspidal`: a system is
  attached to `ofCuspidal c` exactly when it has, outside a finite set, the Euler polynomials
  of a system attached to `c`.

## Source correspondence

- J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
  Formula*, Ann. of Math. Stud. 120 (1989), literature ID `arthur-clozel-1989-base-change`,
  SHA256 `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`. The PDF page is
  the printed page plus 14. The following passages were read.
  - Chapter 3, Definition 4.1, printed p.202 (PDF p.216): an automorphic representation `π`
    of `G(𝔸)` is *induced from cuspidal* if it is induced from a cuspidal unitary
    representation `σ` of `M(𝔸)` for an `F`-parabolic `P = MN`. It is then unitary and
    irreducible.
  - The paragraph before Theorem 4.2, same page: for automorphic `Π_i` of `GL(a, 𝔸)`,
    `Π₁ × ⋯ × Π_b` denotes the representation induced from `Π₁ ⊗ ⋯ ⊗ Π_b ⊗ 1` on the
    parabolic of type `(a, …, a)`.
  - §2, (2.4), printed p.200 (PDF p.214): two cuspidal data `(M, π)` and `(L, σ)` with the
    same Hecke matrices at almost all places are conjugate. This is Jacquet–Shalika's
    theorem, and it is why the multiset of cuspidal classes determines an induced-from-cuspidal
    representation. It is cited for orientation only, not used or proved.
- G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un corps
  p-adique*, Invent. Math. 139 (2000), literature ID `henniart-2000-simple-proof`, SHA256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`, §2.2, printed p.444
  (PDF p.6): an isobaric automorphic representation `Π` associated with a representation `S`
  of `W_F` is unique up to isomorphism, by Jacquet–Shalika rigidity.

### Derived formulation

1. **Data, not realization.** An isobaric (or induced from cuspidal) representation is
   recorded here by its multiset of cuspidal constituents. Arthur–Clozel (2.4) shows that,
   for induced-from-cuspidal representations, this multiset determines the representation up
   to isomorphism. The realized induced representation on automorphic forms is a separate
   construction and is not provided here.
2. **Arbitrary ranks and twists.** Constituents may have different ranks, which covers
   Arthur–Clozel's `Π₁ × ⋯ × Π_b` of equal ranks and general Levi subgroups. They need not be
   unitary. The unitary case of Definition 4.1 is the separate predicate `IsUnitary`.
3. **Hecke matrices.** At almost every place the Hecke matrix of `Π₁ × ⋯ × Π_b` is the
   block-diagonal sum of those of the `Π_i`. So its Euler polynomial
   `det(1 - X t_v)` is the product of the constituents' Euler polynomials. The attached
   systems record exactly these polynomials outside a finite set. They are compared by
   `SameEulerPolynomials`, not by equality of systems, because weak association concerns
   almost every place only.
4. **Ordering.** Multisets are unordered, as isobaric sums are up to isomorphism. The
   attachment chooses an enumeration `σ`. The Euler polynomial product does not depend on it.

## Scope

The module does not construct the induced representation `Π₁ × ⋯ × Π_b`. It also does not
prove that this representation is irreducible or isobaric, that the data are determined by
an attached system (Jacquet–Shalika), or that every multiset has an attached system. Galois
actions and twists on isobaric data are left to the statement modules that use them.
