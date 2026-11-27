# The type `E_6` Hasse kernel on quadratic covers from a Levi subgroup

Module: `Langlands.GroupScheme.Rational.NumberFieldTypeE6QuadraticLeviReduction`.

The module states two propositions about simply connected absolutely almost-simple groups of
type `E_6` over number fields and proves one theorem:

- `NumberFieldTotallyComplexTypeE6DistinguishedVerticesStatement.{u}` (a `Prop`): over a
  totally complex number field, the vertices `α₂` and `α₄` of the Tits index are distinguished;
- `NumberFieldTypeE6QuadraticLeviHasseStatement.{u}` (a `Prop`): over a quadratic Galois
  extension `E/F` over which `α₂` and `α₄` are distinguished, a cocycle of the Levi subgroup
  `C = P ∩ σ(P)` of an opposite pair of minimal parabolic subgroups, trivial at the real
  places, has trivial image in `G`;
- `numberFieldTypeE6QuadraticHasse_of_minimalParabolicLevi` (a theorem): these two statements
  and `NumberFieldQuadraticOppositeMinimalParabolicLeviStatement` imply the published
  `NumberFieldTypeE6QuadraticHasseStatement`.

The two statements are not proved in this module, and neither is
`NumberFieldQuadraticOppositeMinimalParabolicLeviStatement`.

## Imports

- [`Rational.NumberFieldTypeE6HasseReduction`](NumberFieldTypeE6HasseReduction.md), for the
  target `NumberFieldTypeE6QuadraticHasseStatement`; through its imports it supplies
  `TitsIndexData` ([`Reductive.TitsIndex`](../Reductive/TitsIndex.md)), `IsSimplyConnected`,
  `IsAbsolutelyAlmostSimple`, `Cocycle.LocallyTrivial`, `Cocycle.IsTrivial.of_cohomologous`
  ([`Rational.NumberFieldHasseInflation`](NumberFieldHasseInflation.md)),
  `isSimplyConnectedFieldExtension` and `IsAbsolutelyAlmostSimple.baseChange_of_algebraicExtension`
  ([`Rational.QuasiSplitSplittingReduction`](QuasiSplitSplittingReduction.md)).
- [`Rational.NumberFieldQuadraticOppositeMinimalParabolicLevi`](NumberFieldQuadraticOppositeMinimalParabolicLevi.md),
  for `IsQuadraticOppositeMinimalParabolicLevi` and
  `NumberFieldQuadraticOppositeMinimalParabolicLeviStatement`.

## Lean statements

```lean
def NumberFieldTotallyComplexTypeE6DistinguishedVerticesStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K], IsTotallyComplex K →
    ∀ (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) →
    e.symm 1 ∈ d.distinguishedVertices ∧ e.symm 3 ∈ d.distinguishedVertices

def NumberFieldTypeE6QuadraticLeviHasseStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) →
    ∀ (E : Type u) [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E],
      (∀ [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap F E)).obj G).X.hom]
        [LocallyOfFiniteType ((GroupScheme.baseChange (algebraBaseMap F E)).obj G).X.hom]
        (d' : TitsIndexData ((GroupScheme.baseChange (algebraBaseMap F E)).obj G))
        (e' : d'.Vertex ≃ Fin 6),
        (∀ a b, d'.cartan a b = CartanMatrix.E 6 (e' a) (e' b)) →
        e'.symm 1 ∈ d'.distinguishedVertices ∧ e'.symm 3 ∈ d'.distinguishedVertices) →
      ∀ (C : GroupScheme (Spec (CommRingCat.of F))) (t : C ⟶ G),
        IsQuadraticOppositeMinimalParabolicLevi E t →
        ∀ δ : Cocycle C (GaloisCocycle.cover F E),
          (∀ w : InfinitePlace F, w.IsReal →
            (δ.baseChangePullback
              (algebraBaseMap F (Global.placeCompletion F (.inl w)))).IsTrivial) →
          (δ.map t).IsTrivial
```

## Conventions

- **The group.** As in `NumberFieldTypeE6QuadraticHasseStatement`, `G` is an affine,
  locally finite-type group scheme over `Spec F` (or `Spec K`) with `IsSimplyConnected G` and
  `IsAbsolutelyAlmostSimple G`, and `d : TitsIndexData G` is actual Tits index data with a
  bijection `e : d.Vertex ≃ Fin 6` carrying the Cartan pairings `d.cartan` to
  `CartanMatrix.E 6`. Nothing is assumed about the star action, so inner forms (`¹E_6`) and
  outer forms (`²E_6`) are both covered.
- **Numbering.** Mathlib's `CartanMatrix.E 6` has the edges `0–2`, `1–3`, `2–3`, `3–4`,
  `4–5`: it numbers the vertices as Bourbaki does, shifted by one, so vertex `i` is
  Bourbaki's `α_{i+1}`. The vertices `1` and `3` are `α₂` (the end of the short branch) and
  `α₄` (the branch vertex). The only nontrivial automorphism of the diagram exchanges `0 ↔ 5`
  and `2 ↔ 4` and fixes `1` and `3`; hence the conditions below do not depend on the choice
  of `e`.
- **Distinguished vertices.** `d.distinguishedVertices` is the complement of `d.zeroVertices`,
  the simple vertices whose roots restrict to zero on the maximal split torus of the index
  data. These are Tits's distinguished (circled) vertices.
- **The index hypothesis over `E`.** The base change
  `G_E = (GroupScheme.baseChange (algebraBaseMap F E)).obj G` has no registered instances
  `IsAffineHom` and `LocallyOfFiniteType`; the hypothesis of the second statement is
  quantified over them (they hold, by stability under base change), and then over all actual
  Tits index data `d'` of `G_E` and all numberings `e'` by `CartanMatrix.E 6`.
- **Levi subgroups of opposite minimal parabolics.** `IsQuadraticOppositeMinimalParabolicLevi E t`
  ([module](NumberFieldQuadraticOppositeMinimalParabolicLevi.md)) says that `E/F` has degree
  `2`, `t : C ⟶ G` is a closed subgroup over `F`, and for the nonidentity automorphism `σ`
  of `E/F` and some minimal parabolic subgroup `P` of `G_E` over `E`, `C_E` is a Levi
  subgroup of `P` and `C_E = P ∩ σ(P)` as subgroup functors of `G_E`.
- **Cocycles and real places.** `Cocycle C (GaloisCocycle.cover F E)` is a cocycle of `C` on
  the cover `Spec E → Spec F`; `δ.baseChangePullback (algebraBaseMap F F_w)` is its pullback
  to the full cover `Spec (F_w ⊗_F E) → Spec F_w` at the completion `F_w` at a real place
  `w`; `δ.map t` is its image in `G`; `IsTrivial` means being a coboundary.

## The first statement

`NumberFieldTotallyComplexTypeE6DistinguishedVerticesStatement`: let `K` be a totally complex
number field and `G` a simply connected absolutely almost-simple group of type `E_6` over `K`.
For every actual Tits index of `G` numbered by `CartanMatrix.E 6`, the vertices `1` and `3`
(Bourbaki's `α₂`, `α₄`) are distinguished.

**Source.** Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994), registered as
`platonov-rapinchuk-1994-algebraic-groups-number-theory` (SHA-256
`c333b953ca0ace6306663f648cd853a75da55023bf873e0ef2688d997216717f`; printed page `p` is the
one-based PDF page `p + 10`), §6.8:

- For type `¹E_6`, printed pp. 382–383: over a totally imaginary number field every such group
  is isotropic (Theorem 6.26, using `H¹(K, G₀) = 1` for the quasi-split form), and of the
  isotropic indices listed in (6.57) the one with anisotropic kernel of type `D_4` (circled
  vertices `α₁`, `α₆`) does not occur, "since all groups of this type are K-isotropic".
  "G is isotropic over L; moreover its index is either (b) or (c) in (6.57)" (printed
  p. 383): (b) has circled vertices `α₂`, `α₄` and anisotropic kernel of type `A₂ × A₂`, (c)
  is the split index.
- For type `²E_6`, printed p. 385: "the index of G over a totally imaginary number field L
  must be one of the following: [the index with circled vertices `α₂`, `α₄` and anisotropic
  kernel of type `A₂ × A₂`, and the quasi-split index] i.e., α₂ and α₄ must be distinguished
  vertices. We shall now prove this." The proof uses Theorem 6.20 and the vanishing of the
  cohomology of simply connected groups of type `²E_6` over totally imaginary number fields.

**Comparison (provenance: source).** The statement is the conclusion "α₂ and α₄ are
distinguished vertices" for both forms. It is stated for every actual Tits index `d` and
every numbering `e`; since all such indices of `G` are equivalent (Tits, §2.3) and every
automorphism of the `E_6` diagram fixes `1` and `3`, this is the same condition as for one
index.

## The second statement

`NumberFieldTypeE6QuadraticLeviHasseStatement`: let `G` be a simply connected absolutely
almost-simple group of type `E_6` over a number field `F`, and `E/F` a finite Galois
extension over which `α₂` and `α₄` are distinguished (for every actual Tits index of `G_E`).
Let `t : C ⟶ G` be a closed subgroup with `C_E = P ∩ σ(P)` a Levi subgroup of a minimal
parabolic subgroup `P` of `G_E`, `σ` the nonidentity automorphism of the quadratic extension
`E/F`. Then every cocycle `δ` of `C` on `Spec E → Spec F` that is trivial at every real place
of `F` has trivial image in `G`.

**Source.** Platonov and Rapinchuk, §6.8, printed pp. 383–385 (Hasse principle for `¹E_6`,
and for `²E_6` by the same argument once `α₂`, `α₄` are distinguished). There `P` is taken in
the class of the standard parabolic subgroup `P_Δ`, `Δ = Π ∖ {α₂, α₄}`, with
`C = P ∩ σ(P)` its reductive part, `H = [C, C]` simply connected of type `A₂ × A₂` (systems
`{α₁, α₃}` and `{α₅, α₆}`), "the centralizer B = Z_G(H) is a simply connected simple group
of type A₂ corresponding to the system {α₂, μ}" (`μ` the maximal root), `D = HB ⊇ C`, and
the following lemma. (In the comparison below the source's `C` is called `C₁`, and `C`
denotes the smaller Levi subgroup of the Lean statement.)

> LEMMA 6.33. If ξ ∈ H¹(L/K, D) and ξ ∈ ker(H¹(K, D) → ∏_{v ∈ V_∞^K} H¹(K_v, D)), then
> ξ = 1 in H¹(L/K, D).

The proof uses the central isogeny `1 → F → H × B → D → 1` with `F = H ∩ B`: the image of `ξ`
in `H²(K, F)` dies in `H²(L, F)`, and corestriction with `Cor ∘ Res = [L : K] = 2` kills it
"since |F| divides |Z(B)| = 3"; so `ξ` lifts to `ζ ∈ H¹(K, H × B)`; `H¹(K_v, F) = 1` at the
archimedean places makes `ζ` locally trivial there, and the Hasse principle for groups of type
`A₂` makes `ζ` trivial. (Below, the source's finite group `F = H ∩ B` is written `N`, to keep
`F` for the base field.)

**Comparison (provenance: derived).** The statement combines the construction on printed
pp. 383–384 with Lemma 6.33, with three differences.

- *Minimal parabolic.* The source starts from `P` in the class of `P_Δ`; here `P` is a minimal
  parabolic subgroup, as produced by `NumberFieldQuadraticOppositeMinimalParabolicLeviStatement`.
  The source's Levi subgroup is recovered in three steps.
  1. *Split torus and relative roots.* Let `S` be the maximal `E`-split subtorus of the
     identity component of the centre of `C_E`. As `P` is a minimal parabolic subgroup, `S`
     is a maximal `E`-split torus of `G_E` and `C_E = Z_{G_E}(S)`. As `C` is defined over
     `F`, `S` is `σ`-stable, so `σ` acts on the characters of `S` and on the relative roots
     `Φ(G_E, S)`. Since `P ∩ σ(P) = C_E` is a Levi subgroup of `P`, `σ(P)` is the parabolic
     subgroup opposite to `P` with respect to `C_E`.
  2. *Absolute roots.* Over an algebraic closure `F̄` of `F` containing `E`, choose a maximal
     torus `T` of `C` containing `S` and a Borel subgroup `B_C` of `C` containing `T`. Then
     `B₀ = B_C · R_u(P)` is a Borel subgroup of `G` contained in `P` and containing `T`, so
     every simple absolute root of `(G, T, B₀)` restricts to `S` as `0` or as a simple
     relative root of `(G_E, S, P)`. Let `σ̃ ∈ Gal(F̄/F)` extend `σ`. It maps `C` to itself,
     `(T, B_C)` to another torus and Borel subgroup pair of `C`, and `R_u(P)` to `R_u(σ(P))`.
     Choose `c ∈ C(F̄)` with `c σ̃(T) c⁻¹ = T` and `c σ̃(B_C) c⁻¹ = B_C⁻`, the Borel subgroup
     of `C` opposite to `B_C` with respect to `T`. Since `C` normalizes `R_u(σ(P))`, the
     semilinear automorphism `τ = Int(c) ∘ σ̃` maps `(T, B₀)` to `(T, B₀⁻)`, where
     `B₀⁻ = B_C⁻ · R_u(σ(P))` is the Borel subgroup opposite to `B₀` with respect to `T`.
     Since `S` is central in `C`, `Int(c)` fixes `S` pointwise, so `τ` acts on `S` as `σ`.
     Hence the action of `τ` on the characters of `T` maps positive roots to negative roots,
     and `-τ` is an automorphism of the based absolute root system, that is, of the `E_6`
     diagram, compatible with restriction: `(-τ α)|_S = -σ(α|_S)`.
  3. *The enlarged Levi subgroup.* Every automorphism of the `E_6` diagram fixes `α₂` and
     `α₄`, so `-σ` fixes their restrictions `ᾱ₂`, `ᾱ₄` to `S`. These restrictions are
     relative simple roots because `α₂` and `α₄` are distinguished over `E`, and no other
     simple root restricts to them, since `α₂` and `α₄` are fixed by the star action. As
     `-σ` permutes the relative simple roots, it permutes those other than `ᾱ₂`, `ᾱ₄`, so the
     identity component `S₁` of their common kernel in `S` is `σ`-stable and descends to a
     torus over `F`. Then `C₁ = Z_G(S₁)` is defined over `F` and contains `C = Z_G(S)`. Over
     `F̄` its roots are the absolute roots whose restriction to `S` is a combination of the
     relative simple roots other than `ᾱ₂`, `ᾱ₄`, that is, the roots in the span of
     `Π ∖ {α₂, α₄}`. So `C₁` is the standard Levi subgroup of type `Π ∖ {α₂, α₄}` relative to
     `(T, B₀)`, and `C₁ · R_u(P)` is a parabolic subgroup of type `Δ` containing `P`, with
     Levi subgroup `C₁`. This `C₁` is the source's `C`.
- *The subgroups `H`, `B` and `D`.* Let `H = [C₁, C₁]` be the derived group of the enlarged
  Levi subgroup `C₁`, the source's `H = [C, C]`. Over `F̄` it is generated by the root groups
  of `±α₁, ±α₃, ±α₅, ±α₆` and has type `A₂ × A₂`. Since `G` is simply connected, the simple
  coroots are a basis of the cocharacter lattice; the lattice orthogonal to
  `α₁, α₃, α₅, α₆` has rank two, contains the root lattice `ℤα₂ + ℤμ` of type `A₂`
  (determinant `3`), and is integral, so it equals it. Hence the identity component `B` of the
  centralizer of `H`, defined over `F` because `H` is, is simply connected of type `A₂`,
  with maximal torus the identity component of the centre of `C₁`, so `C ⊆ C₁ ⊆ D = HB`. The
  index of the coroot lattice of `H × B` in the cocharacter lattice is `3`
  (`9 · 3 = 3 · 3²`), so `N = H ∩ B` has order `3`. The full centralizer of `H` also contains
  the centre of `H`, of order `9`, which meets `B` only in `N`; the source's `B = Z_G(H)` is
  to be read as its identity component, which does not change `D`.
- *Hypotheses.* The source works over `L = K(√-1)` after using the vanishing of `H¹(L, G)`;
  here `E/F` is any quadratic Galois extension over which `α₂` and `α₄` are distinguished,
  which is what the argument uses, and the conclusion is about the image of `δ` in `G`. The
  cocycle `δ` is assumed trivial at the real places only: at a complex place `w` of `F` the
  cover `Spec (F_w ⊗_F E) → Spec F_w` has a section and every cocycle on it is trivial. At a
  real place inert in `E` the pullback is a cocycle of `Gal(ℂ/ℝ)`, so the hypothesis is the
  source's condition at the archimedean places (pushed from `C` to `D`).

## The reduction theorem

`numberFieldTypeE6QuadraticHasse_of_minimalParabolicLevi` assumes
`NumberFieldTotallyComplexTypeE6DistinguishedVerticesStatement`,
`NumberFieldQuadraticOppositeMinimalParabolicLeviStatement` and
`NumberFieldTypeE6QuadraticLeviHasseStatement` and proves
`NumberFieldTypeE6QuadraticHasseStatement.{u}`. Take `F`, `G`, `d`, `e`, a totally complex
quadratic Galois extension `E/F` and a locally trivial cocycle `ξ` on
`GaloisCocycle.cover F E`.

- `G` is semisimple (`IsSimplyConnected.isSemisimple`), so the minimal parabolic statement
  for `F`, `E` (an instance `IsTotallyComplex E` is made from the hypothesis) gives
  `t : C ⟶ G` with `IsQuadraticOppositeMinimalParabolicLevi E t`. Local triviality of `ξ` at
  the real places is, by definition of `Cocycle.baseChangePullback`, the hypothesis of that
  statement, which gives a cocycle `δ` of `C`, trivial at the real places, with
  `(δ.map t).Cohomologous ξ`.
- `G_E` is simply connected (`isSimplyConnectedFieldExtension`) and absolutely almost-simple
  (`IsAbsolutelyAlmostSimple.baseChange_of_algebraicExtension`), and `E` is a totally complex
  number field, so the first statement applied to `G_E` gives the index hypothesis of the
  second statement for every Tits index of `G_E`.
- The second statement makes `δ.map t` trivial, and `Cocycle.IsTrivial.of_cohomologous`
  makes `ξ` trivial.

No hypothesis is added to the target statement.

## Relation to the Library

- `NumberFieldTypeE6QuadraticHasseStatement` and `NumberFieldTotallyComplexTypeE6VanishingStatement`
  (module [`Rational.NumberFieldTypeE6HasseReduction`](NumberFieldTypeE6HasseReduction.md))
  give `NumberFieldTypeE6HasseStatement` by `numberFieldTypeE6Hasse_of_totallyComplex_quadratic`.
  The vanishing statement is the input of the source's proof of the first statement here.
- The Hasse principle for the factors of `H × B` (simply connected groups of type `A₂`, inner
  or outer, possibly Weil restrictions) is the subject of
  `numberFieldInnerTypeASimplyConnectedGaloisHasseKernel_of_reducedNormLocality`,
  `NumberFieldOuterTypeAHasseStatement` and
  `numberFieldAlmostSimpleSimplyConnectedGaloisHasseKernel_of_absolute`; the local vanishing
  at the finite places for simply connected groups is `localSimplyConnectedCocycleVanishing`.
  These are used in the source's proof of the second statement; this module uses none of them.
