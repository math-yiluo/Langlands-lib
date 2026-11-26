# Statement: anisotropic toral representatives of quadratic cocycles

Module: `Langlands.GroupScheme.Rational.NumberFieldQuadraticQuasiSplitToralReduction`.

`Langlands.GroupScheme.NumberFieldQuadraticQuasiSplitToralReductionStatement.{u}` is a
`Prop`-valued definition with one universe parameter. The module states it and proves
nothing.

## Lean statement

```lean
def NumberFieldQuadraticQuasiSplitToralReductionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G),
    (∀ π : d.Vertex ≃ d.Vertex,
      (∀ a b, d.cartan (π a) (π b) = d.cartan a b) → π = Equiv.refl d.Vertex) →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L],
      Module.finrank F L = 2 →
      IsQuasiSplit ((GroupScheme.baseChange (algebraBaseMap F L)).obj G) →
      ∀ ξ : Cocycle G (GaloisCocycle.cover F L),
        (∀ w : InfinitePlace F, w.IsReal →
          let b := algebraBaseMap F (Global.placeCompletion F (.inl w))
          let r := (Over.mapPullbackAdj b).counit.app (GaloisCocycle.cover F L)
          (ξ.baseChange b _ r).IsTrivial) →
        ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
          (η : Cocycle T.toGrp (GaloisCocycle.cover F L)),
          IsMaximalTorus i ∧
          IsSplitTorus ((GroupScheme.baseChange (algebraBaseMap F L)).obj T.toGrp) ∧
          IsAnisotropic T.toGrp ∧
          (∀ w : InfinitePlace F, w.IsReal →
            let b := algebraBaseMap F (Global.placeCompletion F (.inl w))
            let r := (Over.mapPullbackAdj b).counit.app (GaloisCocycle.cover F L)
            (η.baseChange b _ r).IsTrivial) ∧
          ξ.Cohomologous (η.map i)
```

## Statement in words

Let `F` be a number field and `G` a semisimple group over `F` whose Dynkin diagram, with
its Cartan integers, has no nontrivial symmetry. Let `L/F` be a Galois extension of
degree two such that `G` becomes quasi-split over `L`, and let `σ` generate
`Gal(L/F)`. Let `ξ` be a cocycle of `G` on the cover `Spec L → Spec F` that becomes
trivial at every real place of `F`. Then there are a maximal torus `T` of `G` over `F`
and a cocycle `η` of `T` on the same cover such that

- `T` splits over `L` and is anisotropic over `F`; equivalently, the Galois group acts
  on the character group `X(T)` through `Gal(L/F)`, with `σ` acting as `-1`;
- `η` is trivial at every real place of `F`;
- the image of `η` in `G` is cohomologous to `ξ`.

The equivalence in the first item: for a lattice `M` with an involution `σ`, the
element `m + σ(m)` is `σ`-fixed for every `m`, so `σ = -1` on `M` exactly when `M` has
no nonzero `σ`-fixed vector; and an `L`-split torus is anisotropic over `F` exactly when
its character group has no nonzero `Gal(L/F)`-fixed vector.

## Objects and conventions

- `TitsIndexData G` (module `Reductive.TitsIndex`) records, among other data, that `G`
  is semisimple (`d.isSemisimple`) and a Galois pinning over the separable closure of
  `F`. `d.Vertex` is the set of simple roots of this pinning and
  `d.cartan a b` is the Cartan integer of the simple roots `a` and `b`. The second
  hypothesis says that the only permutation of the simple roots preserving all Cartan
  integers is the identity. It holds for the simple types `A_1`, `B_n`, `C_n`
  (`n ≥ 2`), `E_7`, `E_8`, `F_4` and `G_2`: for the doubly and triply laced types the
  only symmetry of the underlying graph exchanges long and short roots and changes the
  Cartan integers. It fails for `A_n` (`n ≥ 2`), `D_n` (`n ≥ 4`) and `E_6`.
- `IsQuasiSplit H` (module `Reductive.QuasiSplit`) says that the connected reductive
  field group `H` contains a Borel subgroup defined over the field that remains Borel
  over the algebraic closure. `(GroupScheme.baseChange (algebraBaseMap F L)).obj G` is
  the base change `G_L`.
- `Cocycle G U` (module `TorsorCocycle`) is a natural family of points of `G` on pairs
  of points of the cover `U` over all test schemes, satisfying the cocycle identity.
  `GaloisCocycle.cover F L` is `Spec L` as a scheme over `Spec F` (module
  `GaloisCocycle`); for a Galois extension these cocycles are the ordinary Galois
  cocycles of `Gal(L/F)` with values in `G(L)`.
- `IsTrivial` means being the coboundary of a point of `G` over the cover.
  `ξ.Cohomologous ζ` (module `CocycleCohomology`) means that `ζ` is the twist of `ξ` by
  a point of `G` over the cover. `η.map i` is the image of `η` under `i`.
- At a real place `w`, `b` is `Spec F_w → Spec F` for the completion
  `Global.placeCompletion F (.inl w)`, the cover is pulled back to
  `Spec (F_w ⊗_F L)`, `r` is the projection of the pulled-back cover to `Spec L`, and
  `ξ.baseChange b _ r` (module `CocycleRelativeTrivialization`) is the base-changed
  cocycle. This is the real-place part of `Cocycle.LocallyTrivial` (module
  `Rational.NumberFieldHasseKernelReduction`). At a real place that splits in `L` the
  pulled-back cover has a section and the condition holds for every cocycle.
- `IsMaximalTorus i` (module `Torus.Maximal`): `T` is a torus, `i` is a closed
  subgroup, and `i` factors through no strictly larger closed torus over `F`.
- `IsSplitTorus H` (module `Torus.Split`): `H` is isomorphic to a split torus
  `splitTorus S I` for a finite index type `I`. `IsAnisotropic H` (module
  `Rational.SplitTorus`): the split rank of `H` is zero, that is, `H` contains no
  nontrivial closed split torus.

## Source

V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory*, Academic Press
1994, registered as `platonov-rapinchuk-1994-algebraic-groups-number-theory`
(SHA-256 `c333b953ca0ace6306663f648cd853a75da55023bf873e0ef2688d997216717f`; printed
page `p` is PDF page `p + 10`).

Lemma 6.17, printed p. 329:

> Let G be a semisimple algebraic group defined over an arbitrary field K of
> characteristic 0 and containing a Borel subgroup over a quadratic extension L/K,
> and let σ be a generator of Gal(L/K). Then there exists a Borel L-subgroup B of G
> such that B ∩ B^σ is a maximal K-torus of G.

Lemma 6.28 and its proof, printed pp. 369–370:

> Let G be a semisimple algebraic group defined over an arbitrary field K. Assume G
> contains a Borel subgroup B defined over a quadratic extension L/K, such that
> T = B ∩ σ(B) is a maximal K-torus of G (where σ is the generator of Gal(L/K)). Then
> any cocycle ξ in Z¹(L/K, G) is equivalent to some ξ' in Z¹(L/K, T). Moreover, if K
> is a number field and ξ in Z¹(L/K, G) represents an element of
> ker(H¹(K, G) → ∏_{v ∈ V_∞^K} H¹(K_v, G)), then also ξ' in Z¹(L/K, T) can be chosen
> to represent an element of ker(H¹(K, T) → ∏_{v ∈ V_∞^K} H¹(K_v, T)).

The proof of Lemma 6.28 notes that `T = B ∩ σ(B)` makes `σ(B)` the Borel subgroup
opposite to `B`. The computation of the Galois action on the characters of such a
torus follows the proof of Lemma 6.18 (printed p. 330, for `ℂ/ℝ`), where `σ` maps the
set of simple roots of `B` to its negative.

## Derivation (provenance: derived)

Apply Lemma 6.17 to `G` and `L` (a number field has characteristic zero, and `G_L`
is quasi-split) to obtain a Borel subgroup `B` of `G_L` with `T = B ∩ B^σ` a maximal
`F`-torus. Lemma 6.28 then gives the cocycle `η` of `T`, cohomologous in `G` to `ξ`
and trivial at the archimedean places. The complex places impose no condition, so the
statement uses exactly the real places, in its hypothesis and in its conclusion.

The two further properties of `T` come from the hypothesis on the Cartan integers.
Let `Π` be the set of simple roots of `G` with respect to `T` determined by `B`; over
the separable closure all pairs of a maximal torus and a Borel subgroup containing it
are conjugate, so the Cartan integers on `Π` are those of `d`, and a permutation of
`Π` preserving them is the identity.

- An element `τ` of the absolute Galois group fixing `L` maps `B` and `T` to
  themselves, so it permutes `Π` preserving Cartan integers, hence fixes every simple
  root. The roots span `X(T) ⊗ ℚ` because `G` is semisimple, so `τ` acts trivially on
  `X(T)`: the torus `T` splits over `L`.
- `B^σ` contains `T` and meets `B` exactly in `T`, so it is the Borel subgroup
  opposite to `B` and `σ` maps `Π` to `-Π`. Then `-σ` permutes `Π` preserving Cartan
  integers, so `σ = -1` on the roots and hence on `X(T)`. No nonzero character of `T`
  is Galois-fixed, so `T` is anisotropic over `F`.

The statement thus adds to Lemmas 6.17 and 6.28 the hypothesis that the diagram has no
symmetry, and records the resulting Galois action on `X(T)` in the conclusion instead
of the Borel subgroup `B`.
