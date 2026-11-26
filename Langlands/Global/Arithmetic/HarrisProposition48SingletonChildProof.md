# Proof: the equal-rank singleton child in Harris, Proposition 4.8

Module `Langlands.Global.Arithmetic.HarrisProposition48SingletonChildProof`. The theorem

```lean
theorem Langlands.Global.Harris.proposition48SingletonChildNormalization :
    Proposition48SingletonChildNormalizationStatement.{uF, uV}
```

proves `Proposition48SingletonChildNormalizationStatement` (module
`HarrisProposition48SingletonChildStatement`) at arbitrary universes `uF` (the local field) and
`uV` (the local carriers). Unfolded, the statement is

```lean
∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
  Q.IsAuxiliaryValid → Q.IsPrimeCyclicStep D → Nat.card (Q.MackeyIndex D) = 1 →
  ∀ (R : Proposition48Problem.{uF}) (ν : HeckeCharacter R.E)
    (χs : FieldCharacter R.F R.F') (r : ℕ) (S T : CuspidalOperatorRealization R.E r),
    Q.IsAuxiliaryMackeyChild D 1 R → Module.finrank R.E R.E' = Q.mackeyRank D 1 →
    R.IsAuxiliaryParityNormalization (Module.finrank Q.E Q.E' - 1) ν χs →
    R.IsUntwistedSolution.{uF, uV} ν S T →
    Module.finrank R.E R.E' = Module.finrank Q.E Q.E' ∧ ν = 1 ∧
    S.isoClass = T.isoClass ∧ R.IsSolution.{uF, uV} S.isoClass
```

In words: let `Q` be auxiliary-valid and let `D` be an intermediate field of `L/E` with a single
double coset `Gal(L/D) \ Gal(L/E) / Gal(L/E')`. Let `R` be a problem whose rank `[R.E' : R.E]`
is the Mackey rank `[D · E' : D]` at the identity coset. Let `ν, χs` be a parity normalization of
`R` for the parent parity `[E' : E] − 1`. Let `S, T` be an untwisted solution of `R` for `ν`. Then
`R` has the parent rank, `ν = 1`, the classes of `S` and `T` agree, and the class of the raw
realization `S` has all four properties of `R.IsSolution`.

## Proof as implemented

Write `G = Gal(L/E)`, `H = Gal(L/D) = D.fixingSubgroup` and `K' = Gal(L/E'')`, the fixing subgroup
of the copy `E'' = Q.conjugateField 1` of `E'` in `L`.

1. **Group theory** (`relIndex_eq_index_of_forall_eq_mul`). If every element of a group `G` is a
   product `x * y` with `x ∈ H` and `y ∈ K`, then `K.relIndex H = K.index`, that is,
   `[H : H ∩ K] = [G : K]`. The proof lets `H` act on `G ⧸ K`. The stabilizer of the trivial
   coset is `K.subgroupOf H`, by `QuotientGroup.eq`. Its orbit is all of `G ⧸ K`: write `g = x * y`
   and note `x • [1] = [x * y]`. Then `MulAction.index_stabilizer` gives the claim.
2. **Field theory** (`finrank_sup_left_eq_of_forall_eq_mul`). Let `L/E` be finite Galois and let
   `D, K` be intermediate fields with `G = Gal(L/D) · Gal(L/K)`. Then `[D ⊔ K : D] = [K : E]`,
   where `D ⊔ K` is a `D`-algebra by the inclusion, as in `Proposition48Problem.mackeyRank`. The
   tower law `Module.finrank_mul_finrank` for `D ⊆ D ⊔ K ⊆ L` and
   `IsGalois.card_fixingSubgroup_eq_finrank` give `[D ⊔ K : D] · |H ⊓ K'| = |H|`, using
   `IntermediateField.fixingSubgroup_sup` for `Gal(L/(D ⊔ K)) = H ⊓ K'`. Next,
   `Subgroup.relIndex_mul_card` and step 1 give `[G : K'] · |H ⊓ K'| = |H|`. Cancel the positive
   factor `|H ⊓ K'|` and use `IntermediateField.finrank_eq_fixingSubgroup_index`,
   `[K : E] = [G : K']`.
3. **Mackey rank** (`Proposition48Problem.mackeyRank_one_eq_of_card_mackeyIndex`). If `Q` is
   auxiliary-valid and `Nat.card (Q.MackeyIndex D) = 1`, then `Q.mackeyRank D 1 = [E' : E]`. The
   normal-closure clause of `IsAuxiliaryValid` makes `L/E` normal, hence Galois in characteristic
   zero. A type of cardinality one is a subsingleton, so the double coset of every `g` equals that
   of `1`. `DoubleCoset.eq` then writes `g = x * 1 * y` with `x ∈ H` and `y ∈ K'`. Step 2 gives
   `Q.mackeyRank D 1 = [E'' : E]`, and `AlgHom.equivFieldRange` identifies `E''` with `E'` over
   `E`.
4. **Main theorem.** The rank hypothesis and step 3 give
   `[R.E' : R.E] = Q.mackeyRank D 1 = [E' : E]`. The parities `[E' : E] − 1` and
   `[R.E' : R.E] − 1` are then equal. The third clause of `IsAuxiliaryParityNormalization` gives
   `ν = 1`. The last clause of `IsUntwistedSolution` is
   `OperatorRealization.IsDeterminantMultiple 1 S.realization T.realization`. By
   `OperatorRealization.isDeterminantMultiple_one_iff` this is the equality
   `S.realization = T.realization`. The other two fields of `CuspidalOperatorRealization` are
   propositions, so `S = T`. Hence `S.isoClass = T.isoClass`. The weak automorphic induction of
   `R.ξ`, conjugate self-duality and the supercuspidal component at `R.Ps.v` are clauses of
   `IsUntwistedSolution` for `S`. Regular algebraicity is its clause for `T = S`. Together they
   give `R.IsSolution S.isoClass`.

The proof does not use the hypotheses `Q.IsPrimeCyclicStep D` and `Q.IsAuxiliaryMackeyChild D 1 R`.
From `Q.IsAuxiliaryValid` it uses only the normal-closure clause.

## Declarations

- `relIndex_eq_index_of_forall_eq_mul` (theorem): `[H : H ∩ K] = [G : K]` when `G = H K`.
- `finrank_sup_left_eq_of_forall_eq_mul` (theorem): `[D ⊔ K : D] = [K : E]` in a finite Galois
  extension with `Gal(L/E) = Gal(L/D) · Gal(L/K)`.
- `Proposition48Problem.mackeyRank_one_eq_of_card_mackeyIndex` (theorem): a single Mackey double
  coset gives `Q.mackeyRank D 1 = [E' : E]`.
- `proposition48SingletonChildNormalization :
  Proposition48SingletonChildNormalizationStatement.{uF, uV}` (theorem).

All are in the namespace `Langlands.Global.Harris`.

## Provenance

M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field, n < p*, Invent. Math.
134 (1998), 177–210, registered as `harris-1998-local-langlands`. The proof of Proposition 4.8,
printed pp. 202–203, is the source. In the companion TeX `math_9611226v1.tex`, lines 1574–1614
parametrize the Mackey constituents of `Ind_{E'/E} ξ` restricted to `Gal(Ē/E_i)` by the double
cosets `A_i`. They give the constituent at `a` the rank `n(a,i) = [a(E') · E_i : E_i]` and the
inducing character `a(ξ) ∘ N_{a(E')·E_i/a(E')}`. Lines 1666–1674 treat the case where `A_{t−1}`
is a singleton `e` and identify `Π_{t−1}` with `Π(e, t−1)`. With a single double coset, the
restriction of `Ind_{E'/E} ξ` to `Gal(Ē/E_{t−1})` has one Mackey constituent. That constituent
therefore has the full dimension `[E' : E]`, which Harris leaves implicit. The Lean proof obtains
the corresponding equality of field degrees by the Galois-correspondence count above. The vanishing of the parity correction and the passage from the
determinant multiple to the raw realization concern the Library's explicit parity formulation
(`IsAuxiliaryParityNormalization`, `IsUntwistedSolution`), which Harris does not state verbatim.
