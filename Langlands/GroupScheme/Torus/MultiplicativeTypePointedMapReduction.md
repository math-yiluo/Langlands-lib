# Pointed multiplicative-type maps from product-unit decomposition

Worker 504.

This derived unit proves the full conditional reduction
`Langlands.GroupScheme.MultiplicativeTypePointedMapReductionStatement.{u}`:

```lean
UnitsProductDecompositionStatement.{u} → MultiplicativeTypePointedMapStatement.{u}
```

Both sides are imported unchanged from the Library. The theorem
`multiplicativeTypePointedMap_of_unitsProductDecomposition` proves this implication
in every universe. It does not discharge the product-unit premise and therefore
does not by itself prove the unconditional pointed-morphism statement.

The reduction follows Milne, *Algebraic Groups* (2017), Proposition 12.49, printed
p.247, using Proposition 12.48, printed pp.246–247. The official 2017 errata
snapshot of 2 November 2026 lists no correction to either proposition. The
explicit implication is an internal formulation of the dependence in Milne's
proof; the helper lemmas give its scheme-valued-points and descent details.

The imported target quantifies over every field `k`, every group scheme `G` over
`Spec k` whose structure morphism is smooth and quasi-compact and whose underlying
space is connected, and every group scheme `T` with `IsMultiplicativeType T`.
For each scheme morphism `p : G.X ⟶ T.X` taking the identity section to the identity
section, the conclusion gives `f : G ⟶ T` with underlying morphism `p`. The source
is not required to be affine. The target may be nonsmooth, including finite groups
of multiplicative type. No hypotheses are added to this conclusion.

The implemented Lean proof proceeds as follows.

1. `PointedMapReduction.isMonHom_of_points` uses the published Yoneda construction
   `homOfPoints` to turn a pointed scheme map that is multiplicative on every
   group of scheme-valued points into an actual group-scheme morphism. Evaluating
   the resulting natural transformation on the identity morphism identifies its
   underlying scheme map with the original map.
2. `source_integral` applies the published domain-stalk theorem for smooth
   schemes over fields and the theorem that a connected locally Noetherian scheme
   with domain stalks is integral. Smoothness supplies local finite type and local
   Noetherianity. The published `fieldSeparated` supplies separatedness.
3. `gm_isMonHom` works over an algebraically closed field. It applies the explicit
   product-unit premise to the multiplication morphism followed by the pointed
   map to the multiplicative group. This gives two factors `a` and `b` with
   `p(xy) = a(x)b(y)` on every test scheme. The specializations at `(x,1)`, `(1,y)`
   and `(1,1)` give `p(x) = a(x)b(1)`, `p(y) = a(1)b(y)` and
   `a(1)b(1) = 1`. Commutativity of the multiplicative-group points now gives
   `p(xy) = p(x)p(y)`.
4. `diagonalizable_hom_ext` proves that coordinate characters distinguish maps
   into `D(Λ)`, by the injective character-valued points equivalence and the
   published formula for `DiagonalizableCharacter.evalCharacter`.
   `diagonalizable_isMonHom_algClosed` applies the multiplicative-group case to
   each coordinate character and uses this separation to prove multiplicativity.
   These helpers work for every abelian group `Λ`, without finite generation.
5. `source_geometricallyConnected` uses the unit section and the published theorem
   that a smooth connected scheme over a field with a rational section is
   geometrically connected. `source_baseChange` deduces that smoothness,
   quasi-compactness and connectedness hold after every field extension.
6. `diagonalizable_isMonHom` pulls back to `AlgebraicClosure k`, uses the published
   isomorphism `Diagonalizable.baseChangeIso` to identify the target with `D(Λ)`
   there, and invokes the algebraically closed case. `isMonHom_of_target_iso`
   transports the resulting group-law equations back through that isomorphism;
   the published faithful field-pullback theorem reflects them to `k`.
7. The main theorem extracts an arbitrary splitting field `K`, a finitely
   generated abelian group `Λ` and a group-scheme isomorphism `T_K ≅ D_K(Λ)` from
   `IsMultiplicativeType T`. It applies the arbitrary-field diagonalizable case
   over `K`, transports through the splitting isomorphism and reflects the
   group-law equations along the faithful pullback from `k` to `K`.
   Finally `Grp.homMk p` supplies the exact existential conclusion.

The two field descents are separate. They use no common splitting-field tower
and require no separability, finite degree or Galois hypotheses. The pointedness
equations after pullback use `pointed_morphism_algebraPullback`. All auxiliary
geometric and descent results are imported published theorems; no new axiom or
proof hole is introduced.

Sources: `milne-2017-algebraic-groups`, Proposition 12.49, printed p.247, and
Proposition 12.48, printed pp.246–247; and
`milne-2017-algebraic-groups-errata-2026-11-02`, Chapter 12.
