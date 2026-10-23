# Split-center dual exponents and their uniform nilpotence orders

Author: Worker 19.

This module constructs dual exponents on the full algebraic dual of the actual
normalized opposite Jacquet quotient of a complex representation of `GL_n(F)`.
It proves the quotient/source comparison at every finite nilpotence order. The
construction applies to arbitrary representations; it neither asserts finite
nilpotence nor supplies a weak-critical support theorem.

## Objects and quantifiers

For an arbitrary commutative ring `R`, commutative group `A`, and `R`-module
representation `ρ`, `commutativeTranspose ρ` acts on `Module.Dual R V` by

```
(a · φ)(v) = φ(ρ(a)v).
```

The construction composes the ordinary contragredient with inversion on `A`.
Commutativity makes this inversion a homomorphism and makes transposition a
representation. The inverse in the contragredient therefore cancels: this is
not the ordinary contragredient action. `commutativeTranspose_apply` proves the
displayed identity. `commutativeTranspose_defect_pow_apply` proves

```
((transpose(ρ(a)) - c I)^k φ)(v) = φ((ρ(a) - c I)^k v).
```

Ring, group and carrier universes are independent. These generic constructions
make no assumption of smoothness, admissibility, finite length or irreducibility.

`commutativeCentralCharacter` restricts a character `χ : A →* Rˣ` to the full
center of `A`. Since every element of `A` is central,
`commutativeCharacterSpace ρ χ k` is the actual invariant subrepresentation
consisting of the vectors `v` such that

```
forall a, (ρ(a) - χ(a) I)^k v = 0.
```

It reuses the published `centralCharacterSpace`, which has the invariant
subrepresentation structure needed here. Its underlying membership agrees
with the finite character spaces in `Exponents.Jacquet`; no independent
alternative convention is introduced. The proved membership lemmas give this
formula and identify the exponent-one space with the simultaneous eigenspace.
`generalizedCommutativeCharacterSpace` is the increasing union of these spaces.
Its membership lemma has quantifier order `exists k, forall a` for each vector.
`commutativeCharacterNilpotenceIndex` reuses the least uniform bound on this
whole generalized space, with value infinity if there is no finite bound.
Its finite-bound lemma states that the index is at most `k` exactly when the
whole generalized space is contained in its `k`-th stage.

For an arbitrary group `G` and subgroup `N`, `Jacquet.subgroupInvariantDual ρ N`
is the actual submodule of full-dual functionals satisfying
`φ(ρ(n)v) = φ(v)` for every `n ∈ N` and every `v`.
`Jacquet.coinvariantsDualEquiv` constructs a linear equivalence

```
(Coinvariants ρ N)* ≃ { φ ∈ V* | forall n ∈ N, forall v, φ(ρ(n)v) = φ(v) }.
```

The forward map composes with the actual coinvariant quotient map. The inverse
is its universal lift. The proofs use the quotient relations and quotient-map
surjectivity, so no duality equivalence is assumed as input. This uses the full
algebraic dual, without a smoothness restriction on its elements.

## The GL construction and normalization

Fix a prime `p`, a `PadicField p` in universe `uF`, compatible topological data
`T`, any rank `n`, any standard block shape `B`, and a bundled representation
`A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)`. The field and representation
carrier universes are independent. Let `Nbar` be the actual lower block
unipotent subgroup and write

```
q : A → A / span{ A.ρ(n)v - v | n ∈ Nbar }
a ↦ m(a) = B.leviEmbedding (B.blockScalarLevi a)
h(a) = T.leviHalfModulus B (B.blockScalarLevi a).
```

Here `a` ranges over `Fin B.length → F.Carrierˣ`. `h(a)` is a nonzero positive
complex scalar, the square root of the explicit upper full block modulus.
`splitCentreOppositeJacquet` restricts the existing actual opposite Jacquet
representation to these block scalars. It uses the inverse of the upper full
modulus as its supplied opposite modulus. `splitCentreOppositeJacquetMk` is
exactly `q` and is proved surjective. `splitCentreOppositeJacquet_mk` proves

```
ρ_J(a) q(v) = h(a) q(A.ρ(m(a)) v).
```

`splitCentreDualJacquet` is the transpose representation on the full algebraic
dual of this quotient. `splitCentreDualJacquetSourceEquiv` specializes the
quotient universal-property equivalence above. It sends `φ` to `φ₀ = φ ∘ q`,
an opposite-unipotent-invariant functional on `A`. The evaluation lemmas prove

```
(ρ_D(a) φ)(q(v)) = h(a) φ₀(A.ρ(m(a)) v).
```

They prove the positive upper half in this action from the imported inverse
upper-full-modulus normalization, including the square-root inversion. As in
the imported opposite-induction and opposite-Jacquet constructions, comparison
of the explicit block modulus with an analytic Haar modulus is a separate
representation-theoretic obligation.

## Source equations and the index

`splitCentreOppositeJacquet_defect_pow_mk` proves that powers of the normalized
character-defect operator commute with `q`.
`splitCentreDualJacquet_defect_pow_apply_mk` combines this with transposition
and proves, for every complex `c` and every natural `k`,

```
((ρ_D(a) - c I)^k φ)(q(v))
  = h(a)^k φ₀((A.ρ(m(a)) - h(a)^(-1)c I)^k v).
```

The proof is algebraic: induction on powers, linearity, factoring out the
nonzero scalar `h(a)`, and the scalar-power identity for endomorphisms.
Surjectivity of `q` and nonvanishing of `h(a)^k` give
`mem_dualJacquet_characterSpace_iff`: membership in the `k`-th dual character
space is equivalent to

```
forall a v, φ₀((A.ρ(m(a)) - h(a)^(-1)χ(a) I)^k v) = 0.
```

The equivalence uses the same `k`, uniformly in `a` and `v`. In particular,
`mem_dualJacquet_eigenspace_iff` proves the source eigen-equation

```
φ₀(A.ρ(m(a))v) = h(a)^(-1)χ(a) φ₀(v).
```

`IsDualJacquetExponent` requires that `χ` have open kernel and that its
exponent-one dual space be nonzero. By the linear equivalence above, this is
exactly occurrence of a nonzero opposite-invariant eigenfunctional with the
displayed source normalization. It does not replace this eigenfunctional
condition with generalized occurrence. `IsUnitaryDualJacquetExponent` adds
`norm(χ(a)) = 1` for every block scalar.

`dualJacquetExponentNilpotenceIndex` is the least uniform order on the full
generalized component of this dual action, using `ℕ∞`. Its finite-bound theorem
identifies bounds with inclusion in the corresponding finite space. Together
with the finite-space equivalence, this is the uniform nilpotence order of the
source component. A missing component has index zero; an unbounded component
has index infinity, as in the imported generic construction. No identification
with dimension or Jordan–Hölder multiplicity is asserted.

## Original source and scope

The original is A. J. Silberger, *Introduction to harmonic analysis on reductive
p-adic groups* (1979), section 2.4, printed pp.90–92 (PDF pp.96–98), especially
p.90's dual exponent and p.91's `d(χ)`. Registered source:
`silberger-1979-harmonic-analysis`; retained SHA-256:
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
These formula-bearing pages were checked in rendered original page images.

Silberger uses the full-dual functionals fixed by the opposite unipotent and
the transpose action with eigenvalue `δ_(Pbar)^(1/2)(a) χ(a)`. In the explicit
GL normalization above this is `h(a)^(-1)χ(a)`. The proved evaluation and
finite-space equivalences implement this passage to the normalized quotient.
On p.91 `d(χ)` is the maximum of the per-vector uniform nilpotence orders; p.92
identifies the minimal annihilating power and properness of the preceding
stage. If this maximum is finite, the least uniform bound constructed here
is that order. The source's irreducible admissibility assumptions yield finite
bounds and finite decomposition; these assertions are neither assumed nor
proved here. Allowing arbitrary representations and the values zero/infinity
is an explicitly derived algebraic extension of the source convention.

The group realization is restricted to standard block parabolics of `GL_n`.
No construction for arbitrary reductive groups is supplied. The generic
central spaces and their index are algebraic infrastructure documented in
`Exponents.Central` and `Exponents.NilpotenceIndex`. The identification of these
dual exponents with class exponents, the tempered weak-exponent comparison,
finite nilpotence under irreducible admissibility, and the strict weak-critical
support refinement remain separate obligations. In particular, norm-one dual
exponents are not declared to be weak class exponents by definition. The module
introduces no axiom and proves only its stated intrinsic construction laws.
