# Actual Cayley presentations of type-`G₂` group schemes: proof

Authors: Worker 161 and Worker 920.

`Langlands.GroupScheme.typeG2CayleyPresentation` proves the published
proposition `Langlands.GroupScheme.TypeG2CayleyPresentationStatement`
exactly, at every universe `u`, with no additional premise. The proof is
one line:

`typeG2CayleyPresentation_of_splitCayleyAutomorphismPinning splitCayleyAutomorphismPinning`.

It applies the reduction theorem to the proof of the split-model statement.
The statement is unchanged. Its scope is every field `K` in every
characteristic, including two and three, and every affine, locally finite
type, simply connected, absolutely almost-simple group scheme `G` over
`Spec K` whose actual Cartan matrix is `G₂` under a numbering of its
simple vertices. The conclusion gives an actual `CayleyDatum K` `c` and a
closed immersion `iG : G ⟶ GL₈`. On every test scheme, nonreduced ones
included, the range of `iG` is exactly the set of invertible matrices that
fix the identity and preserve the extended multiplication. This
comparison goes through `GeneralLinear.pointsEquiv`. No local-field,
split-rank, isotropy, perfection or characteristic hypothesis is used.
No local rank-one Tits-index statement, local rank-one classification or
local Kneser–Tits result is used.

## The two ingredients

1. **The split model.**
   `Langlands.GroupScheme.splitCayleyAutomorphismPinning :
   SplitCayleyAutomorphismPinningStatement.{u}`, in
   `Composition/SplitCayleyAutomorphism/Pinning.lean` (Worker 920). It
   concerns the actual automorphism group scheme of Zorn's split Cayley
   datum over every field. It shows that this group scheme has trivial
   scheme-theoretic centre and a split pinning. The pinning has full
   coroot span and Cartan matrix `G₂`. The statement and the split datum
   are in `Composition/SplitCayleyAutomorphismPinningStatement`,
   `Composition/SplitCayley` and `Composition/CayleyAutomorphismGroup`. The
   proof modules, in dependency order, each have their own Markdown:
   - `RootGroups`: the twelve root groups and the two-dimensional torus,
     as explicit automorphisms over every commutative ring.
   - `Derivations`: derivations and the Lie algebra over dual numbers.
   - `Interface`: algebraic generation and rigidity statements.
   - `Points`: points and Lie algebra of the automorphism group scheme.
   - `Maps`: root and torus morphisms of schemes.
   - `Smooth`: smoothness.
   - `BaseChange`: base change of the automorphism group scheme.
   - `Torus`: the maximal split torus and its roots.
   - `Generation`: generation of the automorphisms by root and torus
     elements.
   - `Connected`: connectedness.
   - `RadicalAlgebra`: stable subspaces and rigidity modulo the unit for
     Zorn's algebra.
   - `Radical`: connected reductivity.
   - `Center`: trivial centre.
   - `Pinning`: the root datum, the base `{l₂₁, u₁}`, the `G₂` Cartan
     matrix and the full coroot span.
2. **The reduction.**
   `Langlands.GroupScheme.typeG2CayleyPresentation_of_splitCayleyAutomorphismPinning :
   SplitCayleyAutomorphismPinningStatement.{u} →
   TypeG2CayleyPresentationStatement.{u}`, in
   `SimplyConnected/TypeG2CayleyPresentationReduction.lean` (Worker 161).
   - A finite Galois extension `L/K` splits `G`.
   - Rigidity of the `G₂` Cartan matrix makes the star action trivial.
   - A pinned isomorphism over `L` compares `G` with the split
     automorphism group.
   - The trivial centre makes the identity an adjoint quotient. The
     published trivial-star twisting theorem then gives an inner
     discrepancy cocycle with values in the split automorphism group.
   - `SimplyConnected/TypeG2CayleyDescent` descends it to an actual Cayley
     datum `c` over `K` and an isomorphism `G ≅ c.automorphismGroup` of
     group schemes over `Spec K`. It uses Hilbert 90 for `GL₈`
     (`LinearAlgebra/GeneralLinearGaloisFixedBasis`), the twisted datum of
     `Composition/CayleyGaloisTwist`, norm invariance
     (`Composition/SplitCayleyNormInvariance`) and fpqc descent of local
     isomorphisms.
   - Composing with the closed inclusion `c.automorphismInclusion`, whose
     representation property is proved in `CayleyAutomorphismGroup`, gives
     `iG`.

Each supporting module's Markdown explains its own declarations and
sources.

## Source

Knus, Merkurjev, Rost and Tignol, *The Book of Involutions* (1998),
registered as `knus-merkurjev-rost-tignol-1998-book-of-involutions`.
- Theorem 26.19, printed p.373 / PDF p.396: Cayley algebras and type-`G₂`
  groups correspond over an arbitrary field.
- Theorem 25.14, printed p.360 / PDF p.383: the split model.
- Theorem 33.17, printed pp.459–460 / PDF pp.482–483: eight-dimensional
  unital composition algebras are Cayley algebras.

The Lean proof follows the source's strategy of descending the
multiplication tensor of the split model. The implementation is the
coordinate, scheme-level route described above, not a transcription.
