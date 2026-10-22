# Positive-rank quasicuspidal embedding

Author: Worker 238.

`Langlands.CuspidalSupport.normalizedQuasicuspidalEmbedding` proves the
published `Langlands.CuspidalSupport.NormalizedQuasicuspidalEmbeddingTheorem.{uF,uV} F T n`
for every prime `p`, `F : PadicField.{uF} p`, `T : F.TopologicalData` and
`n : ℕ`. It applies `normalizedQuasicuspidalEmbedding_of`, which proves the
target from the proposition `MinimalNonzeroJacquetTheorem.{uF,uV}` (nonzero
quasicuspidal Jacquet descent for arbitrary nontrivial smooth input), to the
published descent theorem `minimalNonzeroJacquet` from
`Langlands.Representation.CuspidalSupport.MinimalJacquetProof`. Compactness of
`P \ G` is the published theorem `Parabolic.parabolicQuotientCompact`.
The field and representation-carrier universes are independent. The positive
rank hypothesis `0 < n` of the target is not used. No admissibility, finite
length or finite generation hypothesis appears.

## Source

Bernstein and Zelevinsky (1976), Chapter II, Proposition 3.19: an irreducible
representation `ω` embeds in a representation induced from an irreducible
quasicuspidal representation. The source takes a minimal nonzero Jacquet module,
shows it is finitely generated, takes an irreducible quotient and applies
Frobenius reciprocity. The target uses the BZ77 normalization: the inducing
representation is `σ` inflated through `leviProjection` and twisted by
`T.parabolicHalfModulus B`, and the Jacquet module is the actual normalized
Jacquet functor `T.normalizedJacquetFunctor B`.

## Implemented proof

1. An irreducible representation has a nontrivial carrier
   (`nontrivial_of_isIrreducible`), so the descent hypothesis gives a block
   shape `B` whose normalized Jacquet object `J` is nontrivial and
   `IsLeviQuasicuspidal`.

2. `jacquetMk_parabolic`: for `g` in the parabolic, the Jacquet quotient map
   sends `ω g v` to `δ(g)^{1/2}` times the normalized Levi action of the Levi
   projection of `g` on the class of `v`. This follows from the Levi
   decomposition `g = u · m` of the parabolic (`unipotentPart`), invariance of
   Jacquet classes under the unipotent radical, and the published inverse
   half-modulus formula for the normalized action.

3. `exists_finset_generating`: choose a nonzero vector `v₀`; by irreducibility
   its orbit spans `ω` (`mem_span_orbit`). Its stabilizer contains an open
   subgroup `K`. Compactness of `P \ G` (`Parabolic.parabolicQuotientCompact`)
   gives finitely many double-coset
   representatives `t` with `G = ⋃ P t K`
   (`Induction.exists_finset_doubleCoset_cover`). By step 2 the classes of
   `ω t v₀` generate every class of `ω g v₀` under the Levi action, so they
   generate `J` as a representation.

4. `exists_isCoatom_subrepresentation`: a finite generating set makes the
   carrier a finitely generated module over the group algebra. Mathlib's
   coatomic submodule lattice of a finitely generated module, transported along
   `Subrepresentation.subrepresentationSubmoduleOrderIso`, gives a maximal
   proper subrepresentation `S` of the nonzero representation `J`.

5. `σ` is the actual smooth quotient `SmoothRep.quotient J S`, in the same
   carrier universe. `isIrreducible_of_isCoatom` shows that a surjective
   intertwiner whose kernel is a coatom has irreducible target.
   `coinvariants_subsingleton_of_surjective` shows that vanishing coinvariants
   for every proper refined unipotent radical pass from `J` to its quotient,
   so `σ` is Levi quasicuspidal.

6. Reciprocity in the needed direction is built directly. `orbitMap` sends
   `v` to the function `g ↦ q(r_P(ω g v))`, where `r_P` is the Jacquet
   quotient map and `q : J → σ` the quotient. Step 2 is exactly its covariance
   under the twisted inflated action of the parabolic. `inducedMap` restricts
   it to smooth vectors with `smoothLift`, using smoothness of `ω`.
   `inducedMap_eval_one` evaluates it at the identity to `q(r_P v)`.

7. The induced intertwiner from the irreducible `ω` is injective or zero
   (`Representation.IsIrreducible.injective_or_eq_zero`). Since `S` is proper,
   some class `r_P v` lies outside `S`, so `q(r_P v) ≠ 0`, and evaluation at the
   identity shows the intertwiner is nonzero. Hence it is injective.

## Lattice helpers

The helpers in the `Lattice` and `Irreducible` sections hold for an arbitrary
group and complex carriers. They are general facts used in steps 3 to 5.
