# `λ`-adic characters realizing Hecke characters

Author: Worker 34. This module defines the relation saying that a continuous
`λ`-adic character of `Gal(K̄/K)` realizes a complex Hecke character of `K`
through a field embedding `ι : L → ℂ`. Harris 1999 treats its character
`ν̄(π)` both as a Hecke character and as a `λ`-adic character, for example in
`[H^{n-1}[π] ⊗ ν̄(π)]^*` in Theorem 5.7(i). This relation connects the two
readings (see `Langlands/Galois/HarrisTwistingCharacter.md`). The module
proves no existence theorem: it does not construct the `λ`-adic character
attached to an algebraic Hecke character.

## Source and provenance

The relation is derived content, the rank-one case of the compatibility used
by the published `Langlands.Galois.CompatibleFamily`. The direction is fixed by
Harris's L-function conventions: M. Harris, *Galois properties of cohomological
automorphic forms on GL(n)*, J. Math. Kyoto Univ. 39-2 (1999), 299-318, §5,
printed p.313 (registered
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`; checked
against the page image). Harris considers "`λ`-adic representations `σ` of
`Gal(𝒦̄/𝒦)` which are unramified at all but finitely many places". In (5.6)
the local factor at an unramified place `w` is formed from "the eigenvalues of
`σ(Fr_w)` for any (geometric) Frobenius `w`". For a Hecke character `χ` the
matching Euler factor is `(1 - χ_w(ϖ_w) Nw^{-s})^{-1}` with a uniformizer
`ϖ_w`. So a lift of geometric Frobenius corresponds to a uniformizer.

## Definitions

Fix number fields `K` and `L` and a finite place `λ` of `L`. Throughout,
`L_λ` is the published actual completion `FiniteCompletion L λ`.

- `LambdaAdicCharacter K L λ` is the type of continuous homomorphisms
  `Gal(K̄/K) → L_λ^×`, from the actual absolute Galois group (Mathlib's
  `Field.absoluteGaloisGroup`). For `K` it only needs a `Field` instance.
- `ψ.atFinitePlace v` restricts `ψ` to the absolute Galois group of the
  completion `K_v`. It uses `Field.absoluteGaloisGroup.map` along the actual
  embedding `K → K_v`, the same map as the published
  `GaloisRepresentation.atFinitePlace`.
- `ψ.IsUnramifiedAt v` says that `ψ` is trivial on the published actual inertia
  subgroup `localInertia v`.
- `IsLambdaAdicRealization ι λ χ ψ`, for `ι : L →+* ℂ`, a Hecke character `χ`
  of `K` and `ψ` as above, says the following. There is a finite set `S` of
  finite places of `K`. For every finite place `v ∉ S` whose residue
  characteristic differs from that of `λ`:
  1. `χ` is unramified at `v` (the published `HeckeCharacter.IsUnramifiedAt`);
  2. `ψ` is unramified at `v`;
  3. there is `c ∈ L` such that `ι(c) = χ_v(ϖ)` for an actual uniformizer `ϖ`
     of `K_v` (valuation `WithZero.exp (-1)` in the Library's multiplicative
     convention), and `ψ(g) = c` in `L_λ` for an actual lift `g` of geometric
     Frobenius at `v` (the published `IsGeometricFrobeniusLift`).

  The value `c` is required to lie in `L`. This expresses that the Frobenius
  values of `ψ` are algebraic and correspond under `ι` to the values of `χ`.

## Proved properties

- `LambdaAdicCharacter.atFinitePlace_eq_of_geometricFrobenius`: at a place where
  `ψ` is unramified, all lifts of geometric Frobenius take the same value. Two
  lifts act equally on residues (the published
  `residueAction_eq_of_geometricFrobenius`), so their quotient lies in inertia.
- `IsLambdaAdicRealization.forall_lifts`: so in a realization the prescribed
  value holds for every lift of geometric Frobenius at every good place.
  Clause 3 only asks for one lift.
- `isLambdaAdicRealization_one` (nonvacuity): the trivial `λ`-adic character
  realizes the trivial Hecke character, with `S = ∅` and `c = 1`. The proof
  takes a uniformizer from Mathlib's surjectivity of the adic valuation
  (`valuedAdicCompletion_surjective`). It takes a lift of geometric Frobenius
  from the published `exists_geometricFrobeniusLift`.

## Remarks and boundaries

- Clause 3 asks for some uniformizer. Since `χ` is unramified at `v`, all
  uniformizers give the same value, but no lemma about this is proved here.
- Chebotarev density would imply that a realization is unique for given `χ`,
  `ι` and `λ`. That uniqueness is not proved here.
- The existence of a realization for algebraic Hecke characters is not stated or
  proved here. That is the classical construction going back to Weil, which
  needs global class field theory. The Library has the global Artin map only as
  a statement (`Langlands/Global/Arithmetic/ClassFieldStatement`).
