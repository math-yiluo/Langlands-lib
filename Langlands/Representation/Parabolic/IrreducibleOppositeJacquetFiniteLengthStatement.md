# Finite length of opposite Jacquet modules of irreducible admissible input

Author: Worker 203. Worker 363 specified the target for the discrete-series
opposite Jacquet quotient criterion. The statement form follows the
published opposite finite-generation statement.

The closed proposition
`Langlands.Parabolic.IrreducibleOppositeJacquetFiniteLengthStatement.{uF,uV}`
says the following. Take an irreducible admissible complex representation
of a positive-rank p-adic general linear group. Its actual normalized
opposite Jacquet representation has finite length as a module over the
complex group algebra of the actual product block Levi. This pair only
defines the proposition. Its proof is a separate obligation.

## Exact statement

Fix a prime `p` through `[Fact p.Prime]`, a finite extension
`F : PadicField.{uF} p` and a compatible `T : F.TopologicalData`, and
install `T.topology`. For every natural rank `n` with `0 < n`, every
`B : GeneralLinear.BlockShape n`, every carrier `V : Type uV` with
`[AddCommGroup V] [Module ℂ V]`, and every
`π : Representation ℂ (GeneralLinear n F.Carrier) V`, the only
hypotheses are

```text
Representation.IsIrreducible π
IsAdmissible π
```

and the conclusion is exactly

```text
IsFiniteLength (MonoidAlgebra ℂ (B.Levi F.Carrier))
  (CuspidalJacquetMultiplicity.oppositeJacquet T B (Rep.of π)).ρ.asModule.
```

The pieces of this statement mean the following.

- Mathlib's `Representation.IsIrreducible π` is
  `IsSimpleOrder (Subrepresentation π)`. So the subrepresentation lattice
  has exactly two elements, and in particular `V` is nonzero.
  Irreducibility is algebraic: no topology on `V` is involved.
- `IsAdmissible π`, from `Langlands.Representation.Smooth.Definitions`,
  means that `π` is smooth and that the fixed vectors of every open
  subgroup form a finitely generated complex module. Fixed vectors are
  finite-dimensional because `ℂ` is a field.
- Mathlib's `IsFiniteLength R M` is defined inductively. A module has
  finite length if it is subsingleton, or if it has a submodule of finite
  length with simple quotient. By `Mathlib.RingTheory.FiniteLength`, this
  is equivalent to having a composition series from `⊥` to `⊤`, and to
  being both Noetherian and Artinian.

The zero module has finite length, so the conclusion holds automatically
when the opposite Jacquet quotient is zero. The proposition does not
assume that the quotient is nonzero.

The statement has no other premise. In particular it assumes no scalar
central character, temperedness, square integrability, unitarity,
finite-dimensional carrier, chosen generating set, opposite finite
generation, or finite length of anything. It also assumes no tensor
factorization of representations of the product Levi. The field universe
`uF` and the carrier universe `uV` are independent. Rank zero is excluded
by `0 < n`, as the consumer requires.

## Actual opposite quotient and normalization

The target is the published
`CuspidalJacquetMultiplicity.oppositeJacquet T B (Rep.of π)` from
`Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement`.
It is neither an upper Jacquet module nor an upper Jacquet module with
an inverted twist. Its underlying space is the coinvariant quotient of
`V` by the complex span of

```text
π(u) v - v,  u ∈ B.oppositeUnipotentSubgroup F.Carrier.
```

The embedded block Levi `B.leviSubgroup F.Carrier` normalizes the
opposite radical, so it acts on this quotient. The action is then
transported to the product Levi `B.Levi F.Carrier` through
`B.leviEquiv F.Carrier`. Write `δ_B` for the published upper block modulus
`T.leviModulus B` transported to the embedded Levi. The construction
passes the inverse `δ_B⁻¹` to `Jacquet.normalizedActionOfModulus`. That
function scales by the inverse square root of the modulus it receives
(`Jacquet.normalizedActionOfModulus_mk`). So for `m : B.Levi F.Carrier`
the action is

```text
m · [v] = δ_B(m)^(1/2) [π(B.leviEmbedding F.Carrier m) v].
```

The normalizing factor is therefore the positive half of the upper
modulus, which is the inverse half of the opposite modulus.
`Langlands.GLTemperedDiscreteSeriesJacquetQuotientStatement` uses the
same carrier and action, written out in full.

## Sources

Two registered originals were read for this pair.

1. A. J. Silberger, *Introduction to harmonic analysis on reductive
   p-adic groups* (1979), Theorem 5.4.1.6, printed p.291 (PDF p.297),
   with its proof ending on printed p.292. Source
   `silberger-1979-harmonic-analysis`, SHA256
   `b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
   Page 291 was also checked as an image. The theorem, which Silberger
   attributes to Howe, says the following. If an admissible
   representation of `G` is a `G`-module of finite type, it has a finite
   composition series. The proof reduces to the cyclic case and uses
   induction through the Jacquet modules `V/V(P_i)` of the maximal
   standard parabolics. It uses that these modules are admissible and
   finitely generated.
2. W. Casselman, *Introduction to the theory of admissible
   representations of p-adic reductive groups*, draft of 1 May 1995.
   Source `casselman-1995-admissible-representations`, SHA256
   `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
   The parts read were:
   - §1.4, p.13: the standing assumptions. `k` is a nonarchimedean local
     field and `G` is a connected reductive group over `k`.
   - Proposition 3.2.1, p.33: `V(N)` is the span of the vectors
     `π(n)v − v`.
   - Theorem 3.3.1, p.35: for every parabolic `P = MN`, the Jacquet
     module of a finitely generated representation is finitely generated.
     The Jacquet module of an admissible representation is admissible.
   - Theorem 6.3.10, pp.60–61: every finitely generated admissible
     representation of `G` has finite length.

No errata file for either source exists in the project notes, the
current Library notes, or the literature collection.

## Derivation of the specialization

Neither source states this exact specialization. It follows from them
by the steps below. The steps also outline a natural proof route.

1. An irreducible representation is nonzero. Any nonzero vector
   generates it, so it is cyclic and in particular finitely generated
   over `MonoidAlgebra ℂ (GeneralLinear n F.Carrier)`.
2. The opposite block parabolic is a parabolic subgroup of `GL_n(F)`.
   Conjugation by `B.reverseMatrix` carries the upper parabolic for
   `B.reverse` onto it. The published lemmas
   `GeneralLinear.BlockShape.reverseMatrix_conj_mem_oppositeParabolic_iff`
   and `GeneralLinear.BlockShape.reverse_unipotentSubgroup_map_conj` in
   `Langlands.Group.GL.ReverseBlocks` record this. So Casselman's
   Theorem 3.3.1 applies with `N` the opposite radical: the unnormalized
   coinvariant quotient is a finitely generated admissible representation
   of the Levi.
3. The product Levi `∏ GL_{n_i}(F)` is the group of `F`-points of a
   connected reductive group. Casselman's Theorem 6.3.10, or Silberger's
   Theorem 5.4.1.6, applied to this Levi shows that the unnormalized
   quotient has finite length in the category of smooth representations.
4. Every invariant subspace or quotient of a smooth representation is
   smooth. So composition series of smooth representations are the same
   as composition series of modules over the complex group algebra, and
   Mathlib's `IsFiniteLength` is the matching notion.
5. Normalizing multiplies the action of each Levi element by a nonzero
   complex scalar. This does not change which subspaces are invariant.
   Transport along the group isomorphism `B.leviEquiv F.Carrier` also
   preserves the lattice of invariant subspaces. Finite length therefore
   passes to the bundled representation `oppositeJacquet`.

Steps 1, 4 and 5 are elementary and are not quoted from either source.

Library commit `e67c1a57` already proves step 2 for this bundled action.
`Langlands.Parabolic.isAdmissible_standardOppositeJacquet` gives
admissibility, and `Langlands.Parabolic.oppositeJacquetFiniteGeneration`
gives finite generation. They are in the modules
`Langlands.Representation.Parabolic.StandardOppositeJacquetAdmissibilityProof`
and `Langlands.Representation.Parabolic.OppositeJacquetFiniteGenerationProof`.

For step 3, the same commit proves
`Langlands.Parabolic.normalizedJacquetFiniteLength`, in
`Langlands.Representation.Classification.FiniteLengthProof`. That theorem
covers standard upper normalized Jacquet modules only. It does not apply
to the opposite action without a comparison of groups, actions and moduli.
The same module proves
`Langlands.FiniteLengthAssembly.finiteLength_of_refinedJacquet`. That
lemma reduces finite length of an admissible, finitely generated
product-Levi representation to finite length of its proper refined
Jacquet modules. No Library theorem at this commit gives finite length of
every finitely generated admissible representation of a product block
Levi.

## Proof boundary

The only new declaration is the closed `Prop`-valued definition above.
This pair proves neither finite length nor finite generation of the
opposite quotient. It also does not prove or complete the consuming
discrete-series quotient criterion.

A proof of this proposition must not use that consuming criterion, its
summand proof, or any Langlands-classification or exhaustion result
that depends on it. It must also not use downstream results about finite
type or finite length of induced representations whose own proofs rely
on GL finite length.
