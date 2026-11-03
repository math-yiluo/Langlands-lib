# Restriction of the adjoint determinant character to a split torus

This module states, without proof, the root formula for the algebraic
character `det(Ad | Lie U)` of a parabolic `P(χ)`. Over a field, its
restriction to a split torus `T` mapping to `P(χ)` is the product of the
roots of `T` occurring in `Lie(U)`. Each root is raised to the dimension of
its weight space. In the additive notation for characters, the product
becomes a sum with multiplicities.

The only declaration is the Prop-valued definition
`Langlands.GroupScheme.Dynamic.AdjointDeterminantTorusRestrictionStatement`,
at a single universe level `u`.

## Setting

The statement quantifies over the following data.

- A field `k : Type u`, a group scheme `G` over `Spec k`, and an actual
  cocharacter `χ : (Gm (Spec k)).toGrp ⟶ G`.
- Representations `hP : (parabolic χ).IsRepresentedBy iP` with
  `iP : P ⟶ G` and `hU : (unipotent χ).IsRepresentedBy iU` with
  `iU : U ⟶ G` of the published dynamic subgroup functors `Dynamic.parabolic χ`
  and `Dynamic.unipotent χ`. Here `U.X.hom` is affine and `P.X.left` is
  affine.
- Finite coordinates `c : Lie.FiniteCoordinates U d` of `Lie(U)`, from
  `Langlands.GroupScheme.Lie.FiniteAction`. These are
  natural `A`-linear isomorphisms `Lie(U)(A) ≅ A^d` over all commutative
  `k`-algebras `A`.
- A commutative group scheme `T` over `Spec k` such that `T.toGrp` is split
  (`IsSplitTorus T.toGrp`: `T.toGrp` is isomorphic to `G_m^I` for a finite
  type `I`), and an arbitrary homomorphism `j : T.toGrp ⟶ P`.

The characteristic of `k` is arbitrary. `I` may be empty, so `T` may have
rank zero. `j` need not be a monomorphism. No reductivity, connectedness or
smoothness of `G` is assumed. In the main application `T` is a maximal split
torus `S` of the Levi factor, mapped to `P` through `Z(χ)`.

## The statement

Write `a = parabolicAdjointAction hP hU`, from
`Langlands.GroupScheme.Dynamic.AdjointDeterminant`. This is the action of `P`
on `U` by normalized conjugation `u ↦ p u p⁻¹`
(`Dynamic.parabolicAdjointAction_act_comp`). The statement has two parts.

1. `(a.lieRoots j).Finite`.
2. `characterRestrict j (adjointDeterminantCharacter hP hU c)` equals

   `∑ᶠ α ∈ a.lieRoots j,
      Module.finrank (CommRingCat.of k) (a.lieWeightSpace j α) •
        (rationalCharacters.equivCharacterLattice T).symm α`.

The ingredients are the following.

- `a.lieWeightSpace j α` is the weight space of `α : characterLattice T` in
  `Lie(U)(k)`, from `Langlands.GroupScheme.Lie.ActionWeights`. It consists of
  the `X` with `a.differential (j(t)) X_A = α(t) • X_A` for every commutative
  `k`-algebra `A` and every `t ∈ T(A)`. Here `X_A` is the image of `X` in
  `Lie(U)(A)` and `a.differential` is the differential of the action.
- `a.lieRoots j` is the set of nonzero `α` with nonzero weight space. No
  reducedness is imposed: if `α` and `2α` both occur, both are roots and
  both appear in the sum.
- `Module.finrank (CommRingCat.of k) (a.lieWeightSpace j α)` is the actual
  `k`-dimension of
  the weight space. This is the multiplicity of the root `α`.
- `adjointDeterminantCharacter hP hU c : rationalCharacters P`, from the same
  module, is the determinant character of `a` in the coordinates `c`
  (`AutomorphicAction.determinantCharacter`, from
  `Langlands.GroupScheme.Lie.ActionDeterminant`). Its restriction along
  `j` is `characterRestrict j`, namely `χ ↦ j ≫ χ`.
- `rationalCharacters.equivCharacterLattice T` is the published
  identification of the rational characters of `T.toGrp` with the character
  lattice of `T`. The sum is taken in the additive group
  `rationalCharacters T.toGrp`.

Characters are written additively, so `n • α` is the character `α^n` and the
finite sum is a product of characters. Part 1 makes the finite sum
meaningful. The weight `0` is excluded from `lieRoots`. Including it would not
change the sum, because `n • 0 = 0`. If `lieRoots` is empty, for example when
`T` has rank zero, the right side is the trivial character.

## Conjugation orientation

The action is `u ↦ p u p⁻¹`. The point `p` is the left factor and `p⁻¹` is
the right factor. A point `t` of `T` acts on the `α`-weight space of
`Lie(U)` by the scalar `α(t)`. So the determinant at `t` is
`∏_α α(t)^{dim W_α}`. If one used `p⁻¹ u p` instead, `t` would act on the
`α`-weight space by `α(t)⁻¹`, and every root would enter with the opposite
sign.

## Scope

The statement uses the actual `P(χ)` and `U(χ)` and the constructed
determinant character. No abstract character is supplied as a hypothesis. The
coordinates `c` are arbitrary; their existence is a separate structural
target. The statement assumes no weight decomposition of `Lie(U)`; that
decomposition, and the finiteness of the set of roots, are part of what
must be proved. It is not about the Levi factor as such; see
`AdjointDeterminantCentralizerRestrictionStatement`.

## Provenance

The source formula is in Renard, *Représentations des groupes réductifs
p-adiques* (version of 9 July 2026), §V.5.4, printed pp.126–127 / PDF
pp.132–133. It is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
For a parabolic `P = MN` of a reductive group over a nonarchimedean local
field `F`, and `a` in the split component `A`, the Lemma there gives

`δ_{P\G}(a) = ∏_{γ∈Σ(P)} |γ(a)^{m_γ+2m_{2γ}}|_F`,
`δ_P(a) = ∏_{γ∈Σ(P)} |γ(a)^{-(m_γ+2m_{2γ})}|_F`.

So Renard's modular function `δ_P` is the inverse of the absolute value of
the character in this statement, and `δ_{P\G}` is that absolute value. In
Renard, `Σ(P)` is the set of reduced positive roots of `A` (§V.3.4, printed
p.110 / PDF p.116). The multiplicities `m_γ` and `m_{2γ}` are introduced in
the proof of the preceding Proposition, for the minimal parabolic `P_∅`, as
the multiplicities of `γ` and `2γ` in `Σ'_∅`.

Our sum runs over all roots occurring in `Lie(U)`, nonreduced roots
included, each with its own weight space dimension. Group the roots on the
ray of a reduced root `γ`. If `nγ` has weight space dimension `m_{nγ}`, the
ray contributes `(∑_{n≥1} n m_{nγ}) • γ`. When only `γ` and `2γ` occur on the
ray, this is Renard's exponent `m_γ + 2m_{2γ}`. That holds for a minimal
parabolic and its maximal split torus `A_∅`, the setting in which Renard
introduces `m_γ` and `m_{2γ}`. There the roots of `A_∅` in `Lie(G)` form the
relative root system, possibly nonreduced (Renard §V.3.7, printed p.111 /
PDF p.117, records the root-system property for minimal parabolics, citing
its reference [7], cor. 5.8). In such a system the only positive multiples
of a reduced root `γ` that are roots are `γ` and `2γ`.

For a general parabolic and its split component, higher multiples can occur,
and the printed two-term exponent does not account for them. Take a split
group of type `G_2`, with short simple root `α` and long simple root `β`, and
the maximal parabolic whose Levi factor has simple root `β`. The roots in
`Lie(U)` are `α, α+β, 2α+β, 3α+β, 3α+2β` (the standard positive roots of
`G_2` other than `β`). On the one-dimensional split component `A` of the
Levi factor, `β` is trivial. With `γ` the restriction of `α`, these roots
restrict to `γ, γ, 2γ, 3γ, 3γ`. So `m_γ = 2`, `m_{2γ} = 1` and `m_{3γ} = 2`.
Our sum gives `2γ + 2γ + 6γ = 10γ`. The two-term expression gives
`(2 + 2·1)γ = 4γ`. These are different characters. The determinant of a
torus acting diagonally is the product of all its weights, each raised to the
dimension of its weight space, so the Lean statement takes this all-weight
form and keeps every multiple. It agrees with Renard's grouped formula
wherever only `γ` and `2γ` occur on each ray. Where higher multiples occur,
it differs from the printed two-term exponent.

Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra* (2003), §I.1, printed pp.238–241 / PDF pp.4–7, uses the same
setting. There `Σ(A_M)` is the set of roots of `A_M` in `Lie(G)`, `Σ(P)` is
the subset of roots positive for `P`, `Σ^red(P)` is the subset of reduced
roots, and `δ_P` is the module of `P`. It is registered as
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

The arbitrary-field packaging is internal and derived. The statement is an
identity of algebraic characters over any field, of any characteristic. The
torus may be any split torus with any homomorphism into `P`. Roots are
measured in `Lie(U)` through the differential of the conjugation action. The
expected proof decomposes `Lie(U)(k)` into weight spaces for the split torus
(compare the published `isInternal_weightSpace_of_isSplitTorus`) and takes
the determinant on each weight space. Absolute values, Haar measures, square
roots and the analytic modulus identities are not part of this statement.
