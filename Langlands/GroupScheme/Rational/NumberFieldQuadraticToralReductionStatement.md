# Statement: toral representatives of quadratic cocycles over number fields

`Langlands.GroupScheme.NumberFieldQuadraticToralReductionStatement.{u}` is a
`Prop`-valued definition with one universe parameter. The module states it and proves
nothing.

## Lean statement

```lean
def NumberFieldQuadraticToralReductionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F))),
    IsConnectedReductive G →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L],
      Module.finrank F L = 2 →
      ∀ ξ : Cocycle G (GaloisCocycle.cover F L),
        (∀ w : InfinitePlace F, w.IsReal →
          let b := algebraBaseMap F (Global.placeCompletion F (.inl w))
          let r := (Over.mapPullbackAdj b).counit.app (GaloisCocycle.cover F L)
          (ξ.baseChange b _ r).IsTrivial) →
        ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
          (η : Cocycle T.toGrp (GaloisCocycle.cover F L)),
          IsMaximalTorus i ∧
          (∀ w : InfinitePlace F, w.IsReal →
            let b := algebraBaseMap F (Global.placeCompletion F (.inl w))
            let r := (Over.mapPullbackAdj b).counit.app (GaloisCocycle.cover F L)
            (η.baseChange b _ r).IsTrivial) ∧
          ξ.Cohomologous (η.map i)
```

## Statement in words

Let `F` be a number field, `G` a connected reductive group over `F` and `L/F` a Galois
extension of degree two. Let `ξ` be a cocycle of `G` on the cover `Spec L → Spec F`
that becomes trivial at every real place of `F`. Then there are a maximal torus `T` of
`G` over `F` and a cocycle `η` of `T` on the same cover such that `η` is trivial at
every real place of `F` and the image of `η` in `G` is cohomologous to `ξ`.

## Objects and conventions

- `Cocycle G U` (module `TorsorCocycle`) is a natural family of points of `G` on pairs of
  points of the cover `U` over all test schemes, satisfying the cocycle identity.
  `GaloisCocycle.cover F L` is `Spec L` as a scheme over `Spec F` (module
  `GaloisCocycle`); for a Galois extension these cocycles are the ordinary Galois
  cocycles of `Gal(L/F)` with values in `G(L)`.
- `IsTrivial` means being a coboundary of a point of `G` over the cover.
  `ξ.Cohomologous ζ` (module `CocycleCohomology`) means that `ζ` is the twist of `ξ` by
  a point of `G` over the cover.
- `η.map i` is the image of `η` under the homomorphism `i`.
- At a real place `w`, `b` is `Spec F_w → Spec F` for the completion
  `Global.placeCompletion F (.inl w)`, the cover is pulled back to `Spec (F_w ⊗_F L)`,
  `r` is the projection of the pulled-back cover to `Spec L`, and `ξ.baseChange b _ r`
  (module `CocycleRelativeTrivialization`) is the base-changed cocycle. This is the
  real-place part of `Cocycle.LocallyTrivial` (module
  `Rational.NumberFieldHasseKernelReduction`).
- `IsMaximalTorus i` (module `Torus.Maximal`): `T` is a torus, `i` is a closed subgroup,
  and `i` factors through no strictly larger closed torus over `F`.

The hypothesis at a real place `w` split in `L` holds for every cocycle, since then the
pulled-back cover has a section; it is a real condition only at the real places that
become complex in `L`.

## Source

V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory*, Academic Press 1994,
registered as `platonov-rapinchuk-1994-algebraic-groups-number-theory` (SHA-256
`c333b953ca0ace6306663f648cd853a75da55023bf873e0ef2688d997216717f`; printed page `p` is
PDF page `p + 10`), Lemma 6.28 and its proof, printed pp. 369–370:

> Let G be a semisimple algebraic group defined over an arbitrary field K. Assume G
> contains a Borel subgroup B defined over a quadratic extension L/K, such that
> T = B ∩ σ(B) is a maximal K-torus of G (where σ is the generator of Gal(L/K)). Then
> any cocycle ξ in Z¹(L/K, G) is equivalent to some ξ' in Z¹(L/K, T). Moreover, if K
> is a number field and ξ in Z¹(L/K, G) represents an element of
> ker(H¹(K, G) → ∏_{v ∈ V_∞^K} H¹(K_v, G)), then also ξ' in Z¹(L/K, T) can be chosen
> to represent an element of ker(H¹(K, T) → ∏_{v ∈ V_∞^K} H¹(K_v, T)).

## Derivation (provenance: derived)

The statement differs from the source in three ways.

- *No Borel subgroup over `L`.* The source fixes the torus `T = B ∩ σ(B)` in advance and
  uses the open Bruhat cell. The statement lets the torus depend on the cocycle and
  drops the Borel hypothesis. The conclusion then follows from the regular-element
  argument of the Library's `quadraticToralRepresentatives` (module
  `Rational.GaloisTwistedPointDensity`), which treats the case of an algebraically
  closed quadratic extension, through the reduction
  `quadraticToralRepresentatives_of_stronglyRegularValue` (module
  `Rational.GaloisCocycleStronglyRegular`). Write the
  cocycle as `a ∈ G(L)` with `a σ(a) = 1`. The twisted values `f⁻¹ a σ(f)`,
  `f ∈ G(L)`, are Zariski dense in `G_L` (module `Rational.GaloisTwistedPointDensity`
  proves this when `L` is algebraically closed; the same Weil-restriction argument
  applies to a quadratic extension of an infinite field). Choose such a value `a'` that
  is strongly regular. Its centralizer is a maximal torus of `G_L`; the cocycle identity
  `σ(a') = a'⁻¹` makes it Galois stable, so it descends to a maximal torus `T` over `F`
  containing `a'`, and `a'` defines the cocycle `η`.
- *Real places only.* The source takes the kernel of localization at the archimedean
  places; the complex places impose no condition. The statement uses exactly the real
  places, in the hypothesis and in the conclusion.
- *Choice at the real places.* As in the second half of the source's proof, which uses
  weak approximation (Proposition 7.9) and the triviality of torus cocycles near `1`
  (Proposition 3.3), choose `f` close, at each real place `w` inert in `L`, to a point
  trivializing `ξ` over `F_w ⊗_F L ≅ ℂ`. Then `a'` is close to `1` in `G(ℂ)`, and a
  square root of `a'` taken in a fixed neighbourhood of `1` lies in the centralizer `T`
  and trivializes `η` at `w`. The required density of `G(L)` at the real places follows
  from real approximation for connected groups (J. S. Milne, *Algebraic Groups*, 2017,
  Theorem 25.70, printed p. 564, registered as `milne-2017-algebraic-groups`; the
  Library's `realApproximation` proves it over `ℚ`) applied to Weil restrictions.

The statement is restricted to number fields, where the real places are defined, and to
connected reductive groups; it asserts nothing about the Galois action on the characters
of `T`.
