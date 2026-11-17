# Finite Galois full faithfulness for groups of multiplicative type: proof

Author: Worker 815.

This module proves
`Langlands.GroupScheme.MultiplicativeTypeGaloisFullFaithfulnessStatement.{u}`
(see [the statement](MultiplicativeTypeGaloisFullFaithfulnessStatement.md))
as the theorem
`Langlands.GroupScheme.multiplicativeTypeGaloisFullFaithfulness`, for every
universe `u`. The helper results live in the namespace
`Langlands.GroupScheme.MultiplicativeTypeGaloisFullFaithfulness`.

The statement is derived from Milne, *Algebraic Groups* (2017), Theorem 12.23.
The Lean proof does not follow Milne's route. It extends the split-torus
descent argument of [FiniteGaloisCharacterDescent](FiniteGaloisCharacterDescent.md)
to a target whose character group may have torsion. That argument needs only
one fact about the target over `L`: a homomorphism into it is determined by its
character pullback. The proof below establishes this fact for every group
isomorphic to some `D_L(M')`.

The proof does not use the hypotheses `[AddGroup.FG M]` and `[AddGroup.FG M']`.
The theorem's binder list still includes them, because it must match the
statement. The source isomorphism `i : T_L ≅ D_L(M)` is used only to construct
the homomorphism over `L`. Uniqueness and the Galois argument use only the
target isomorphism `i'`.

## 1. Homomorphisms into `D(Λ')` are determined by characters

Section `Split` works over an arbitrary commutative ring `R`.
`evalCharacter R Λ m` is the character of `D_R(Λ)` given by evaluation at
`m`. It comes from `DiagonalizableCharacterProof`.

- `evalCharacter_add`: `evalCharacter (a + b) = evalCharacter a + evalCharacter b`.
  The proof checks this on points over every test scheme `U`. It uses
  `comp_groupHom_add`, `evalCharacter_apply`, and the fact that the points
  equivalence of `D(Λ)` is multiplicative.
- `hom_ext_evalCharacter`: let `G` be any commutative group scheme over `R`,
  and let `f, g : G ⟶ D_R(Λ')`. If `f ≫ evalCharacter m = g ≫ evalCharacter m`
  for every `m : Λ'`, then `f = g`. The proof uses `hom_ext_points` and
  injectivity of `Diagonalizable.characterPointsEquiv`. A point of `D(Λ')` is
  a monoid map `Multiplicative Λ' →* Γ(U)ˣ`, and its value at `m` is the
  pullback of `evalCharacter m` along that point.
- `hom_ext_of_iso_diagonalizable`: let `i' : H ≅ D_R(Λ')` and `f, g : G ⟶ H`.
  If `f ≫ χ = g ≫ χ` for every actual character `χ` of `H`, then `f = g`.
  The proof cancels the mono `i'.hom` and applies the previous lemma to the
  characters `i'.hom ≫ evalCharacter m`.
- `restrictMap_comp_evalCharacter`: let `g : Λ' →+ Λ`. The homomorphism
  `D(g) : D(Λ) ⟶ D(Λ')` (`Diagonalizable.restrictMap R g`) satisfies
  `D(g) ≫ evalCharacter m' = evalCharacter (g m')`. On points this is
  `Diagonalizable.pointsEquiv_restrictMap`.

## 2. Existence over a field

Section `Field` works over a field `K`.

- `evalCharacterEquiv K Λ : Λ ≃+ characterLattice (D_K(Λ))` is evaluation,
  `m ↦ evalCharacter m`. It is additive by `evalCharacter_add`. It is
  bijective by the uniqueness and existence clauses of
  `NaturalUnits.ofCharacter χ |>.existsUnique` from
  `DiagonalizableCharacterProof`: over a field, each character of `D_K(Λ)`
  is evaluation at exactly one element of `Λ`. Torsion in `Λ` is allowed.
  `evalCharacterEquiv_apply` records the formula definitionally.
- `exists_hom_of_characterMap`: let `G ≅ D_K(M)` via `i` and `H ≅ D_K(M')`
  via `i'`. Every additive map `F : X(H) →+ X(G)` of actual character groups
  has the form `χ ↦ f ≫ χ` for some `f : G ⟶ H`. The proof first transports
  `F` to `Φ : X(D(M')) →+ X(D(M))`, `ψ ↦ i.inv ≫ F (i'.hom ≫ ψ)`. It then pulls
  `Φ` back through the two evaluation equivalences to obtain
  `g : M' →+ M`, and sets `f = i.hom ≫ D(g) ≫ i'.inv`. Let `χ` be a
  character of `H`, and write `i'.inv ≫ χ = evalCharacter m'`. Then
  `restrictMap_comp_evalCharacter` and the defining property of `g` give
  `f ≫ χ = i.hom ≫ Φ (evalCharacter m') = F χ`.

## 3. Galois compatibility

Section `Galois` has an arbitrary source `T` and a target `T'` with
`i' : T'_L ≅ D_L(M')`.

- `galoisHomTransport_eq_of_diagonalizable`: let `f : T_L ⟶ T'_L` satisfy
  `σ(f ≫ χ) = f ≫ σ χ` for all `σ` and `χ`. Then
  `galoisHomTransport σ f = f`. The proof applies
  `hom_ext_of_iso_diagonalizable i'`. Every character of `T'_L` has the form
  `σ ψ`, because `σ` acts bijectively
  (`Representation.apply_bijective`). Then `galoisHomTransport_comp`
  together with the hypothesis gives `galoisHomTransport σ f ≫ σ ψ = σ(f ≫ ψ) = f ≫ σ ψ`.
- `compatible_of_equivariant_characterPullback_of_diagonalizable`
  (assuming `[FiniteDimensional k L] [IsGalois k L]`): under the same
  hypothesis, `f` is compatible with the canonical descent data of `T` and
  `T'`. The proof applies `Descent.compatible_of_galois` and cancels the
  canonical transport isomorphism `descentBaseChangeIso`. This reduces the
  claim to the previous lemma. The argument is the same as
  `compatible_of_equivariant_characterPullback` in
  `FiniteGaloisCharacterDescent`, with the split-torus hypothesis replaced
  by `i'`.

## 4. The main theorem

Fix `k`, `L`, `T`, `T'`, `M`, `M'`, `i`, `i'` and `F`.

**Equivariance implies unique realization.** The morphism
`Spec L → Spec k` is flat, surjective and quasi-compact
(`fieldExtension_fpqc`). By `exists_hom_of_characterMap i i' F` there is
`f : T_L ⟶ T'_L` with `f ≫ χ = F χ` for every `χ`. Equivariance of `F` turns
into `σ(f ≫ χ) = f ≫ σ χ`, so `f` satisfies the descent condition of
Section 3. `Descent.FpqcHomDescent.hom` descends `f` to `a : T ⟶ T'`, and
`Descent.FpqcHomDescent.baseChange_hom` gives `a_L = f`. Hence
`a_L ≫ χ = F χ`. For uniqueness, suppose that `b` satisfies
`b_L ≫ χ = F χ = f ≫ χ` for all `χ`. Then `hom_ext_of_iso_diagonalizable i'`
gives `b_L = f`, and `Descent.FpqcHomDescent.unique` gives `b = a`.

**Realization implies equivariance.** Suppose that `a_L ≫ χ = F χ` for all
`χ`. Rewrite both sides of `F (σ χ) = σ (F χ)` with this equation. The claim
becomes `a_L ≫ σ χ = σ (a_L ≫ χ)`, which is
`characterLattice.galoisRepresentation_precompose` (from
`WeilRestrictionNormOneCharacters`).

## Imports

- `MultiplicativeTypeGaloisFullFaithfulnessStatement` (the target).
- `DiagonalizableCharacterProof` (`evalCharacter`, `evalCharacter_apply`,
  `NaturalUnits.ofCharacter`, and the points lemmas for `D(Λ)`).
- `FiniteGaloisCharacterDescent` (`galoisHomTransport`,
  `galoisHomTransport_comp`, `Descent.compatible_of_galois`, and, through
  its own imports, `Descent.FpqcHomDescent` and `fieldExtension_fpqc`).
- `WeilRestrictionNormOneCharacters`
  (`characterLattice.galoisRepresentation_precompose`).

The evaluation equivalence and its application formula reuse
`DiagonalizableCharacter.evalCharacterEquiv` and `evalCharacterEquiv_apply`
from `MultiplicativeTypeSplitCategory`. The underlying evaluation function
and the additive character group are unchanged.
