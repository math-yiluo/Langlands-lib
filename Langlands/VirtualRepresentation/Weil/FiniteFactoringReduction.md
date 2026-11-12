# Unramified twists of finite-factoring unitary Weil classes

Author: Worker 4803.

## Statement

`Langlands.VirtualRepresentation.LocalWeil.UnramifiedTwistFiniteFactoringStatement.{uK, uW}`:
for every prime `p`, every p-adic field `K : PadicField.{uK} p` and every class
`b` in the actual basis `LocalWeil.Basis.{uK, uW} K` of continuous irreducible
complex representations of the constructed local Weil group `W_K` (all
positive ranks, carriers in `Type uW`), there are

- a complex unit `z`,
- a class `b₀` of the unitary basis `LocalWeil.UnitaryBasis.{uK, uW} K`,
- a finite group `Q : Type uK` and a group homomorphism `q` from the absolute
  Galois group of `K` to `Q`,

such that the generator of `b₀` lies in
`LocalWeil.unitaryFiniteFactoringSupported K q` (the class `b₀` factors through
`q` composed with the projection `W_K → Gal(K̄/K)`), the twist of `b₀` by the
unramified character `Weil.Local.localUnramifiedCharacter K z` (the continuous
character `w ↦ z ^ deg(w)` taking the value `z` at geometric Frobenius) is `b`,
and, if `b` is itself a unitary class, `‖z‖ = 1`.

The theorem `unramifiedTwistFiniteFactoring` proves it with no hypotheses.

## Provenance

Derived. Henniart (2000), §4.4, printed p. 453 (PDF p. 15), begins with:
for every irreducible `σ` of dimension `n` there is an unramified character `χ`
of `K^×` such that `σ ⊗ (χ ∘ rec)⁻¹` has determinant of finite order. For an
irreducible representation finite order of the determinant is the same as
finite image (the second clause of the published
`Weil.Local.LocalWeilIrreducibleReductionFor`), so the statement above is that
first sentence written for the classes used by
`Henniart.StableMap.IsFiniteFactoring`: unitary classes factoring through a
finite quotient of the absolute Galois group. The unitary refinement records
the elementary fact that the twisting parameter of a unitary class has modulus
one. No assertion beyond the published local Weil representation theory is
assumed; the statement is proved here.

## Proof

**Finite image implies unitary** (`FiniteRepresentation.isUnitary_of_hasFiniteImage`).
For a representation `A` with finite image `S`, take the coordinate inner
product of `Module.finBasis ℂ A` and sum it over `S`. Hermitian symmetry,
additivity and conjugate linearity in the first variable hold termwise.
Definiteness uses the term of the identity endomorphism, which lies in `S`.
Invariance under `A g` follows by reindexing the sum along `T ↦ T * A g`, a
bijection of `S` with inverse `T ↦ T * A g⁻¹`.

**Modulus of twisting characters** (`FiniteRepresentation.norm_eq_one_of_equiv_twist`).
Let `A` be equivalent to the twist of `B` by `χ`, both preserving positive
definite Hermitian forms, and `B` nonzero. For `g`, choose an eigenvector `v`
of `B g` with eigenvalue `μ` (`Module.End.exists_eigenvalue`). Invariance of
the form gives `|μ|² = 1`. Transporting `v` through the equivalence gives an
eigenvector of `A g` with eigenvalue `χ(g) μ`, so `|χ(g) μ|² = 1` and
`‖χ g‖ = 1`. `Weil.norm_eq_one_of_isUnitaryClass_twist` applies this to an
irreducible class and its twist when both are unitary, using the published
`underlyingClass_twistBasisEquiv` and `twistClass_classOf`.

**Finite quotients** (`LocalWeil.exists_finiteQuotient_of_isLocalGaloisType`).
A representation `B` of Galois type has a continuous extension `τ` to the
absolute Galois group. That group is compact and nonarchimedean, so `τ` has
finite range by the published
`Weil.continuous_compact_nonarchimedean_representation_finite_range`. Let
`φ = τ.toHomUnits`. The quotient `Q = Gal ⧸ ker φ` lives in the field
universe. `kerLift φ`, followed by the inclusion of units, is an injective
representation of `Q` whose range is contained in that of `τ`, so `Q` is
finite. By construction this representation composed with the quotient map and
the projection `W_K → Gal` is `B`.

**Reduction** (`LocalWeil.exists_unramifiedTwist_finiteFactoring`). Choose a
representative `A` of `b`. The published `localWeilIrreducibleReductionFor`
gives `z` and a continuous irreducible `B` of finite image and Galois type with
`A` equivalent to the twist of `B` by `localUnramifiedCharacter K z`. Then `B`
has the rank of `A`, is unitary by the averaging lemma, and factors through a
finite quotient by the previous lemma. Its class `b₀` is the twist of `b` by the
character with value `z⁻¹`. This is checked with
`Weil.IrreducibleBasis.ext_underlyingClass` (classes of equal rank with equal
underlying representation classes are equal) and the published twist-class
identities.

**Modulus one** (`LocalWeil.norm_eq_one_of_isUnitaryClass`). If `b` is unitary,
apply the modulus lemma to `b` and its unitary twist `b₀` at the geometric
Frobenius lift, where the character takes the value `z⁻¹`.

`unramifiedTwistFiniteFactoring` assembles these and rewrites
`b₀ = twist(z⁻¹) b` as `twist(z) b₀ = b` using the published
`Weil.twistBasisEquiv_mul` and `Weil.twistBasisEquiv_one`.

Field and carrier universes are independent throughout.
