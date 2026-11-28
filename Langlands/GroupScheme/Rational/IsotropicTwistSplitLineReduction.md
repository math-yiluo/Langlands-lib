# Isotropic inner twists and centralizers of split lines

Module: `Langlands.GroupScheme.Rational.IsotropicTwistSplitLineReduction`.

The module states one proposition, `IsotropicTwistSplitLineReductionStatement`. It contains
no theorem; the statement is not proved here.

## Notation

- `GaloisCocycle.cover K L` is the field cover `Spec L → Spec K`, and
  `GaloisCocycle.coverMap K L M : cover K M ⟶ cover K L` is the map of covers induced by a
  tower `K ⊆ L ⊆ M`. For a cocycle `ξ` on `cover K L`, `ξ.refine (coverMap K L M)` is its
  pullback to `cover K M`; on Galois covers this is inflation from `Gal(L/K)` to
  `Gal(M/K)`.
- `Cocycle G U` (module `TorsorCocycle`) assigns to any two points `a b : Z ⟶ U` over a
  test scheme `Z` a point `ξ(a, b)` of `G` over `Z`, naturally in `Z` and with
  `ξ(a, b) ξ(b, c) = ξ(a, c)`. For a point `g : U ⟶ G.X` the twist `ξ.twist g` is
  `(a, b) ↦ g(a)⁻¹ ξ(a, b) g(b)`, writing `g(a)` for `a ≫ g`; it is cohomologous to `ξ`.
- `LocalGroupIso G H U` (module `LocalGroupIso`) is a family of group isomorphisms
  `φ_a : G(Z) ≃ H(Z)`, one for each point `a : Z ⟶ U`, natural in `Z`. In other words it is
  an isomorphism of `G` and `H` after base change to `U`.
- `φ.HasDiscrepancy (AutomorphicAction.conjugation (𝟙 G)) ξ` says that
  `φ_b (ξ(b, c) x ξ(b, c)⁻¹) = φ_c (x)` for all points `b c : Z ⟶ U` and `x : Z ⟶ G.X`.
  Thus `H` is the twist of `G` by `ξ` acting by inner automorphisms, and `φ` is the
  identification of the two groups over the cover. For a finite Galois extension `L/K`,
  with `U = cover K L`, `b` the identity and `c` the automorphism `σ` of the cover, this is
  the usual description of the inner form of `G` defined by the Galois cocycle
  `σ ↦ ξ_σ`: the `K`-structure of `H` is `G` with the Galois action twisted by
  `Int(ξ_σ)`.
- `Gm (Spec K)` is the multiplicative group over `K` (module `Multiplicative`), and
  `IsClosedSubgroup μ` says that the homomorphism `μ` is a closed immersion. A closed copy of
  `𝔾_m` in a reductive `K`-group `H` is the same as a one-dimensional `K`-split subtorus;
  `H` has one exactly when it is `K`-isotropic.
- `torusCentralizer ν` (module `Rational/TorusCentralizer`) is the subgroup functor of
  points of `G` that commute, after every base change, with every point of the image of
  `ν`.
- `IsQuasiSplit G` (module `Reductive/QuasiSplit`) says that `G` is connected reductive and
  contains a Borel subgroup defined over the field.

## The statement

```lean
∀ (K : Type u) [Field K]
  (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom], IsQuasiSplit G →
  ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (ξ : Cocycle G (GaloisCocycle.cover K L))
    (H : GroupScheme (Spec (CommRingCat.of K)))
    (φ : LocalGroupIso G H (GaloisCocycle.cover K L)),
    IsAffineHom H.X.hom → φ.HasDiscrepancy (AutomorphicAction.conjugation (𝟙 G)) ξ →
    ∀ μ : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ H, IsClosedSubgroup μ →
      ∃ (M : Type u) (_ : Field M) (_ : Algebra K M) (_ : Algebra L M)
        (_ : IsScalarTower K L M) (_ : FiniteDimensional K M) (_ : IsGalois K M)
        (g : GaloisCocycle.cover K M ⟶ G.X)
        (ν : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ G),
        IsClosedSubgroup ν ∧
          ∀ {Z : Over (Spec (CommRingCat.of K))} (a b : Z ⟶ GaloisCocycle.cover K M),
            ((ξ.refine (GaloisCocycle.coverMap K L M)).twist g).toFun a b ∈
              (torusCentralizer ν).carrier Z
```

Let `G` be a quasi-split group over a field `K`, `L/K` a finite Galois extension and `ξ` a
cocycle of `G` on `Spec L → Spec K`. If the inner twist `H` of `G` by `ξ` is
`K`-isotropic, then `ξ` comes from the centralizer of a one-dimensional `K`-split torus of
`G`: on a finite Galois extension `M ⊇ L` of `K` there are a point `g ∈ G(M)` and a closed
copy `ν` of `𝔾_m` in `G`, defined over `K`, such that every value of the inflated cocycle,
twisted by `g`, centralizes `ν`. In Galois terms, the class of `ξ` in `H¹(K, G)` lies in
the image of `H¹(K, Z_G(ν))`.

## Mathematical content

Write `ν'` for the cocharacter of `G` over `L` obtained by transporting `μ` along `φ`,
that is `ν'(t) = φ_b⁻¹(μ(t))` over the point `b` of the cover. The discrepancy condition
applied to `x = φ_c⁻¹(μ(t))` gives `ξ(b, c) ν'_c(t) ξ(b, c)⁻¹ = ν'_b(t)`, since `μ` is
defined over `K`. Hence the geometric conjugacy class of `ν'` in `G` is stable under the
Galois group. If `ν` is a cocharacter of `G` defined over `K` and `g ∈ G(M)` satisfies
`ν'(t) = g ν(t) g⁻¹` over `M`, the displayed identity says exactly that
`g(b)⁻¹ ξ(b, c) g(c)` commutes with `ν(t)`, which is the conclusion. The cocharacter `ν` is
a closed immersion because its base change to `M` is conjugate to that of `μ`.

The existence of `ν` and `g` is the standard fact that, for a quasi-split group, a
Galois-stable conjugacy class of cocharacters contains a cocharacter defined over `K`: take
a Borel subgroup `B` defined over `K` and a maximal `K`-torus `T ⊆ B`. The class contains a
unique cocharacter of `T` that is dominant for `B`, and the Galois action on `X_*(T)`
preserves the `B`-dominant cone, so this cocharacter is Galois-fixed, hence defined over
`K`. A conjugating point lies in `G(K^sep)`, hence in `G(M)` for some finite Galois
extension `M` of `K` containing `L`. This dominant-cocharacter argument is the
justification of the statement over an arbitrary field `K`, as the Lean statement
quantifies.

Platonov–Rapinchuk work over perfect fields (convention of §2.1.1, printed p. 49), and in
that setting a different argument gives the same reduction for semisimple quasi-split `G`.
Proposition 6.19 (printed p. 339), whose hypotheses are those of Proposition 6.18 and whose
proof uses Steinberg's theorem for perfect fields (printed pp. 338–339), states that every
maximal `K`-torus `T` of `H` admits a `K`-embedding into `G` such that the class of `ξ`
lies in the image of `H¹(K, T)`. Applying it to a maximal `K`-torus containing the image
of `μ`, the cocycle takes values in the image of `T`, which centralizes the image of `μ`;
this is how the proof of Proposition 6.22 (printed p. 378) passes from an isotropic twist
to the centralizer of a split torus of the quasi-split group. That torus argument does not
cover imperfect fields such as `𝔽_p(t)`, which the Lean statement includes.

## Source

V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory* (1994), registered as
`platonov-rapinchuk-1994-algebraic-groups-number-theory`; printed page `p` is PDF page
`p + 10`. Section 2.1.1 (perfect-field convention, printed p. 49); Section 6.5,
Propositions 6.18 and 6.19 (printed pp. 338–339); Section 6.8, proof of Proposition 6.22
(printed p. 378). The book's results cover semisimple quasi-split groups over perfect
fields; the Lean statement is over an arbitrary field and for any quasi-split group, which
the dominant-cocharacter argument above justifies. It also uses a single split line rather
than a maximal `K`-split torus, an arbitrary finite Galois cover for the cocycle, and a
finite Galois refinement on which the conjugating point is defined.
