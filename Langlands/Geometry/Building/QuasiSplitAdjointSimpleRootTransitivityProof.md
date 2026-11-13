# Proof of simple-root transitivity of `Z(k)` in quasi-split adjoint groups

The theorem `quasiSplitAdjointSimpleRootTransitivity` proves the Library proposition
`QuasiSplitAdjointSimpleRootTransitivityStatement.{u}`. It uses no hypotheses beyond the
statement's own. Its route follows the argument sketched in the statement's Markdown, from
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), the proofs of Lemma 6.4.10 and
Proposition 6.6.2. The steps are as follows.

1. `Z` is a maximal torus. `T(k)` acts on each root group through root values.
2. The simple absolute roots form a basis of the character lattice of `T_K`, where `K/k` is a
   finite Galois splitting field of `Z`.
3. A Galois-equivariant assignment of character values comes from a point of `T(k)`.

The Lean proof does not use the induced-torus decomposition `T(k) = ∏ k_ã^×`. It uses
steps 2 and 3 instead.

## Helper modules

The proof uses six helper modules of this unit. Each has its own Markdown file.

- `Langlands.LinearAlgebra.AdjointRootDatum` and
  `Langlands.GroupScheme.Reductive.AdjointRootSpan`. Over a field, if a connected reductive
  group with split maximal torus has trivial center, its roots span the character lattice
  over `ℤ` (`IsAdjoint.rootSpan_eq_top`).
- `Langlands.Geometry.Building.RootGroupTorusValueAction`. A rational point `z` of the
  centralizer torus acts on `U_a(k)`, or on `U_a(k)/U_{2a}(k)`, through its root value. This
  gives the conjugation property and the commutation property for one relative root.
- `Langlands.GroupScheme.Torus.EquivariantCharacterValueDescent`
  (`exists_rationalPoint_characterValue_eq_of_equivariant`). Let `L/k` be Galois and let
  `T_L` be split. Every Galois-equivariant homomorphism `X^*(T_L) → Lˣ` is the family of
  character values of a rational point of `T`.
- `Langlands.GroupScheme.Rational.SimpleRootValueCharacter`
  (`exists_simpleRootValueCharacter`), with its companion
  `Langlands.GroupScheme.Rational.RootOrbitUnitValue` (`exists_rootOrbitValue`). Together
  they give the simple-root value step described below.

## Declarations in this module

- `exists_rationalPoint_rootOrbitCharacterValue` restates the descent theorem in terms of
  `rootOrbitCharacterValue`, the root values used in `RootGroupTorusValueAction`. It does
  this through `GaloisPointComparison.rationalCoeffEquiv` and `rootOrbitCharacterValue_coe`.
- `commute_of_rootOrbitCharacterValue_eq_one_of_fibers`. Let `b` be a relative root, and
  let `z ∈ T(k)` have root value `1` at every absolute root over `b` and over `2b`. Then
  `j(z)` commutes with every point of `U_b(k)`. The proof picks an absolute root `β` over
  `b`. Its Galois orbit is the whole restriction fiber
  (`rootOrbit_eq_restrictionFiber_of_torusCentralizer`). If `2b` is a relative root, it picks
  `β₂` over `2b` in the same way and applies the multipliable commutation lemma. Otherwise
  it applies the non-multipliable lemma. In both cases the relative root multiplicities
  `n • a` with `n ∉ {1, 2}` are excluded by the relative root system (`hmult`).
- `exists_simpleRoot_conj` proves clause 3 of the statement for one simple relative root
  `a`, in the setup `f ≫ j : S → T → G`. Take `u, u' ∈ U_a(k) ∖ U_{2a}(k)`.
  1. The conjugation lemmas of `RootGroupTorusValueAction` give a nonzero `c` in the field
     `k_β` of an absolute root `β` over `a`. Every `z ∈ T(k)` with root value `c` at `β`
     conjugates `u` into `u' · U_{2a}(k)`. For non-multipliable `a`, `U_{2a}(k)` is trivial
     and `w = 1`.
  2. The simple-root value step (below) gives a Galois-equivariant `φ : X^*(T_K) → Kˣ`.
     It has `φ(β) = c`, and `φ(γ) = 1` for every absolute root `γ` over `b` or over `2b`,
     where `b ≠ a` is another simple relative root.
  3. The descent theorem turns `φ` into a point `z ∈ T(k)` with these root values.
  4. `commute_of_rootOrbitCharacterValue_eq_one_of_fibers` and step 1 give the two
     properties of `z`.
- `quasiSplitAdjointSimpleRootTransitivity` proves the statement. Given `k`, `G`, `i` and
  `j` as in the statement:
  1. `i` factors as `s ≫ j` through the centralizer (`IsRepresentedBy.factorHom`).
  2. `Z` is a torus (`isTorus_of_quasiSplit_torusCentralizer`, with the Library proofs
     `quasiSplitTorusCentralizerExistence` and `maximalSplitTorusConjugacy`). `j` is a closed
     subgroup, and `j` is a maximal torus because the centralizer of `Z` is `Z` itself.
  3. `Z` splits over a finite Galois extension `K` (`torusFiniteGaloisSplitting`).
     `rootDatumExistence` gives a reduced root datum `P` of `(G_K, T_K)`.
  4. `G_K` is adjoint: it is connected reductive by the Library proof
     `connectedReductiveFieldExtensionStatement`, has finite center, and has trivial center
     (`center_eq_bot_baseChange`). So the roots of `P` span `X^*(T_K)`.
  5. The relative root system (`relativeRootSystem`) bounds the multiples of relative roots
     to `n ∈ {1, 2}`. A generic cocharacter `ν` of `S` gives the simple relative roots.
  6. `Δ` is the finite set of simple relative roots. Clause 1 holds because simple roots are
     positive roots. Clause 2 is `relativeRoots_subset_addSubgroupClosure_simpleRelativeRoots`,
     with negation stability from the relative root system. Clause 3 is
     `exists_simpleRoot_conj`.

## The simple-root value step

`exists_simpleRoot_conj` needs one more input. Let `a` be a simple relative root, `β` an
absolute root over `a`, and `c ∈ Kˣ` with `c ∈ k_β`. The input is a Galois-equivariant
`φ : X^*(T_K) →+ Additive Kˣ` with `φ(β) = c`. It must also satisfy `φ(γ) = 1` (additively
`0`) on the absolute roots `γ` over `b` and over `2b`, for every other simple relative
root `b`. This is `exists_simpleRootValueCharacter`. Its hypotheses are those available
inside `exists_simpleRoot_conj`: the torus setup, a reduced root datum `P` of `j_K`, and
`P.rootSpan ℤ = ⊤`. Its proof proceeds as follows.

1. The absolute roots over simple relative roots lie in the absolute base `B` of the
   regular cocharacter given by `ν`.
2. Because the roots span the lattice, `B` is an integral basis of `X^*(T_K)`.
3. `exists_rootOrbitValue` gives Galois-equivariant values on the roots: `c` at `β`, its
   Galois conjugates on the orbit of `β`, and `1` off that orbit. Extending these values
   along `B` gives `φ`.
4. A root over `b` or `2b` has coordinate `0` at every basis root over `a`. This follows by
   comparing Galois orbit sums and using that positive roots have nonnegative coordinates.

`SimpleRootValueCharacter.md` describes this proof in detail.

## Provenance

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Lemma 6.4.10 and its proof
(printed pp.227–228) and Proposition 6.6.2 with its proof (printed pp.231–232). There, for
adjoint quasi-split `G`, `Z = T` is an induced torus. The factor `k_ã^×` of `T(k)` attached
to the lifts of `a ∈ Δ` centralizes the other `U_b` and acts transitively on the nontrivial
elements of `U_a(k)` or `U_a(k)/U_{2a}(k)`. The Lean proof obtains the same elements of
`T(k)` from prescribed root values and Galois descent instead of the induced-torus
decomposition.
