# Realization of Galois modules by groups of multiplicative type: statement

Worker 3483.

`Langlands.GroupScheme.MultiplicativeTypeGaloisModuleRealizationStatement.{u}` is a
proposition definition. This module does not prove it.

## The statement

Let `k` and `L` be fields in the universe `u`, with `L` a finite Galois extension of
`k` (`[Algebra k L] [FiniteDimensional k L] [IsGalois k L]`). Let `M : Type u` be a
finitely generated abelian group (`AddGroup.FG M`), possibly with torsion, and let
`ρ : Representation ℤ (L ≃ₐ[k] L) M` be a `ℤ`-linear action of `Gal(L/k)` on `M`.
Write `T_L = (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T` and
`D_L(M) = Diagonalizable.groupScheme (CommRingCat.of L) M` (`Torus/Diagonalizable`). The
statement asserts that there exist

- a commutative group scheme `T` over `Spec k`,
- an isomorphism `i : T_L ≅ D_L(M)` of commutative group schemes over `Spec L`, and
- an additive isomorphism `e : M ≃+ X^*(T_L)` onto the characters of `T_L`
  (`characterLattice`, homomorphisms `T_L ⟶ 𝔾_m`),

such that

1. for every `m ∈ M`, every test scheme `U → Spec L` and every point `x` of `T_L` over
   `U`, the value of `e m` at `x` is `t(m)`, where `t` is the point `x ≫ i` of `D_L(M)`
   read as a homomorphism `M → Γ(U, 𝒪_U)ˣ` by `Diagonalizable.characterPointsEquiv`
   (`Torus/KernelDiagonalizable`); values of characters are read through
   `Gm.pointsEquiv`. So `e m` is the character `t ↦ t(m)` of `D_L(M)` transported to
   `T_L` along `i`;
2. `e (ρ σ m) = characterLattice.galoisRepresentation k L T σ (e m)` for all
   `σ ∈ Gal(L/k)` and `m ∈ M`, where `galoisRepresentation` (`Torus/LatticeGalois`) is
   the Galois action `(σ χ)(t) = σ (χ (σ⁻¹ t))` on the characters of `T_L`.

In words: every finitely generated `Gal(L/k)`-module is, compatibly with the
diagonalizable structure over `L`, the character module of a group over `k` that
becomes diagonalizable over `L`.

## Source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type over a
Field* (2017), source ID `milne-2017-algebraic-groups`, §12.g (printed pp.239–240,
PDF pp.255–256).

Printed p.239 (PDF p.255):

> Let Γ denote the Galois group of k_s/k endowed with the Krull topology. An action of
> Γ on a commutative group M is continuous for the discrete topology on M if every
> element of M is fixed by an open subgroup of Γ, i.e., M = ⋃_K M^{Gal(k_s/K)} where K
> runs through the finite extensions of k contained in k_s.
> For an algebraic group G, we let X^*(G) = X(G_{k_s}). In other words, X^*(G) consists
> of the characters of G defined over k_s.

Printed p.240 (PDF p.256):

> Let M be a finitely generated Z-module equipped with a continuous action of Γ. Let
> D(M_0) be the diagonalizable group over k_s attached to the Z-module M. The
> coordinate ring of D(M_0) is k_s[M], and the continuous action of Γ on M extends to
> a semilinear action on k_s[M]. We define D(M) to be the algebraic group over k with
> coordinate ring k[M]^Γ. It becomes isomorphic to D(M_0) over k_s, and so is of
> multiplicative type.

> THEOREM 12.23. The functor X^* is a contravariant equivalence from the category of
> algebraic groups of multiplicative type over k to the category of finitely
> generated Z-modules equipped with a continuous action of Γ (with quasi-inverse
> M ⇝ D(M)). Under the equivalence, short exact sequences correspond to short exact
> sequences.

Lemma 12.4 and the sentence after it (printed p.232, PDF p.248) give the
identification `X(D(M)) ≃ M` used in part 1:

> Thus X(D(M)) ≃ M. The character of D(M) corresponding to m ∈ M is
> D(M)(R) = Hom(M, R^×) → R^× = G_m(R), f ↦ f(m).

## Correspondence with the source

The Lean statement is the essential surjectivity part of Theorem 12.23, together with
the description of the realizing group over the splitting field, for actions that
factor through a finite Galois extension. It is a **derived** formulation.

- **Finite Galois level.** A continuous action of `Γ = Gal(k_s/k)` on a finitely
  generated `M` fixes each of finitely many generators on an open subgroup, so it
  factors through `Gal(L/k)` for a finite Galois `L/k` inside `k_s`. Conversely `ρ`
  inflates to a continuous action of `Γ`. The statement works at this level, with
  characters of `T_L` in place of characters of `T_{k_s}`.
- **Truth.** Apply Theorem 12.23 (with its quasi-inverse `D(M)`) to the inflated
  action. Milne's `D(M)` becomes isomorphic to `D(M_0)` over `k_s`; since
  `Gal(k_s/L)` acts trivially on `M`, it is already `D_L(M)` over `L`, and its
  characters over `L` are `M` with the given `Gal(L/k)`-action, the character attached
  to `m` being `t ↦ t(m)` (Lemma 12.4). This is the Lean conclusion.
- **The action.** Milne gives no formula for the action of `Γ` on `X^*(G)`; the
  Library's `characterLattice.galoisRepresentation` is the standard left action
  `(σ χ)(t) = σ (χ (σ⁻¹ t))` (`Torus/LatticeGalois.md`), and the derivation reads
  Theorem 12.23 with this action.
- **Torsion.** `M` may have torsion, including `p`-torsion in characteristic `p`, so
  `T` need not be smooth: for `M = ℤ/p` with trivial action in characteristic `p`,
  `T = μ_p`. The Library's `Diagonalizable.groupScheme` keeps all torsion.
- **Not formalized.** Functoriality, Milne's explicit quasi-inverse
  `Spec (k_s[M])^Γ`, and the clause on short exact sequences.

## Relation to the Library

- The published `TorusGaloisLatticeRealizationStatement`
  (`Torus/GaloisLatticeRealizationStatement`) is the torus case: there `M` is free of
  finite rank and `T_L` is required to be a split torus. The present statement
  allows torsion and records the diagonalizable structure of `T_L` through `i`.
- `IsMultiplicativeType` (`Torus/MultiplicativeType`) asks for an isomorphism of
  `T_K` with some `D_K(Λ)` over some field `K`. The group-scheme isomorphism
  underlying `i` provides this for `T.toGrp` with `K = L` and `Λ = M`.
- Possible building blocks for a proof: the route of the torus case (presenting `M`
  as a cokernel of permutation lattices, a homomorphism of Weil restrictions from the
  published `IsSplitTorus.existsUnique_hom_of_equivariant_characterMap`, and its
  kernel), together with `Diagonalizable.homKernelDiagonalizableIso`
  (`Torus/HomKernelDiagonalizable`), which identifies the kernel of a homomorphism of
  split tori with `D` of the cokernel of character pullback, torsion included.
- The published family-2 ledger (`notes/group-schemes/ledger-family-2-tori.md`,
  row D4) lists the Galois-module classification of multiplicative-type groups as a
  gap.
