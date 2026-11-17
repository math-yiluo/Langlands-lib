# Statement: first cohomology of simply connected groups over number fields lives at the real places

Worker 75.

`Langlands.GroupScheme.SimplyConnectedRealPlacesCohomologyStatement.{u} : Prop`
is a statement-only, `Prop`-valued definition with one universe parameter
`u`. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports:

- [`SimplyConnected.Basic`](../SimplyConnected/Basic.md), for
  `IsSimplyConnected`.
- [`CocycleRelativeTrivialization`](../CocycleRelativeTrivialization.md), for
  `Cocycle.baseChange`. Through its imports it also brings in
  [`TorsorCocycle`](../TorsorCocycle.md), for `Cocycle` and `Cocycle.twist`,
  and the base-change functor `GroupScheme.baseChange`
  ([`AbelianScheme.GroupScheme`](../../AbelianScheme/GroupScheme.md)).
- [`CocycleRefinement`](../CocycleRefinement.md), for `Cocycle.refine`.
- [`Torus.LatticeGalois`](../Torus/LatticeGalois.md), for `algebraBaseMap`.
- [`Global.AdelicGroupLocalPoints`](../../Global/AdelicGroupLocalPoints.md),
  for `placeCompletion`.

## Lean statement

```lean
def SimplyConnectedRealPlacesCohomologyStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F))),
    IsSimplyConnected G →
    (∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
      (ξ₁ ξ₂ : Cocycle G (Over.mk (algebraBaseMap F L))),
      (∀ w : NumberField.InfinitePlace F, w.IsReal →
        let b := algebraBaseMap F (Langlands.Global.placeCompletion F (.inl w))
        let r := (Over.mapPullbackAdj b).counit.app (Over.mk (algebraBaseMap F L))
        ∃ f : (Over.pullback b).obj (Over.mk (algebraBaseMap F L)) ⟶
            ((baseChange b).obj G).X,
          ∀ {Z : Over (Spec (CommRingCat.of (Langlands.Global.placeCompletion F (.inl w))))}
            (x y : Z ⟶ (Over.pullback b).obj (Over.mk (algebraBaseMap F L))),
            (ξ₂.baseChange b _ r).toFun x y = ((ξ₁.baseChange b _ r).twist f).toFun x y) →
      ∃ f : Over.mk (algebraBaseMap F L) ⟶ G.X,
        ∀ {Z : Over (Spec (CommRingCat.of F))} (x y : Z ⟶ Over.mk (algebraBaseMap F L)),
          ξ₂.toFun x y = (ξ₁.twist f).toFun x y) ∧
    (∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
      (c : ∀ w : {w : NumberField.InfinitePlace F // w.IsReal},
        Cocycle ((baseChange (algebraBaseMap F
            (Langlands.Global.placeCompletion F (.inl w.1)))).obj G)
          ((Over.pullback (algebraBaseMap F (Langlands.Global.placeCompletion F (.inl w.1)))).obj
            (Over.mk (algebraBaseMap F L)))),
      ∃ (L' : Type u) (_ : Field L') (_ : Algebra F L') (_ : FiniteDimensional F L')
        (_ : Algebra.IsSeparable F L') (e : L →ₐ[F] L')
        (ξ : Cocycle G (Over.mk (algebraBaseMap F L'))),
        ∀ w : {w : NumberField.InfinitePlace F // w.IsReal},
          let b := algebraBaseMap F (Langlands.Global.placeCompletion F (.inl w.1))
          let r' := (Over.mapPullbackAdj b).counit.app (Over.mk (algebraBaseMap F L'))
          let s : Over.mk (algebraBaseMap F L') ⟶ Over.mk (algebraBaseMap F L) :=
            Over.homMk (Spec.map (CommRingCat.ofHom (e : L →+* L'))) (by
              dsimp only [Over.mk_hom, algebraBaseMap]
              rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap])
          ∃ f : (Over.pullback b).obj (Over.mk (algebraBaseMap F L')) ⟶
              ((baseChange b).obj G).X,
            ∀ {Z : Over (Spec (CommRingCat.of (Langlands.Global.placeCompletion F (.inl w.1))))}
              (x y : Z ⟶ (Over.pullback b).obj (Over.mk (algebraBaseMap F L'))),
              ((c w).refine ((Over.pullback b).map s)).toFun x y =
                ((ξ.baseChange b _ r').twist f).toFun x y)
```

The declaration sits in namespace `Langlands.GroupScheme`. The `by` block
inside the statement only proves that `Spec e : Spec L' ⟶ Spec L` is a
morphism over `Spec F`; it asserts nothing else.

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)`.
- `IsSimplyConnected G`
  ([`SimplyConnected.Basic`](../SimplyConnected/Basic.md)): `G` is
  semisimple (`IsSemisimple`, which includes `IsConnectedReductive`: smooth,
  affine, connected, with trivial geometric unipotent radical, see
  [`Reductive.Basic`](../Reductive/Basic.md)), and every central isogeny
  `H ⟶ G` from a semisimple group `H` over the same field is an isomorphism.
  This is algebraic simple connectedness.
- **Cocycles** ([`TorsorCocycle`](../TorsorCocycle.md)). For `U : Over S`,
  `Cocycle G U` gives, for every test object `Z` over `S` and every pair
  `a b : Z ⟶ U`, a point `ξ.toFun a b : Z ⟶ G.X`, natural in `Z` and
  satisfying `ξ.toFun a c = ξ.toFun a b * ξ.toFun b c`. For
  `f : U ⟶ G.X`, `(ξ.twist f).toFun a b = (a ≫ f)⁻¹ * ξ.toFun a b * (b ≫ f)`.
  For a morphism of covers `t : V ⟶ U`, `ξ.refine t`
  ([`CocycleRefinement`](../CocycleRefinement.md)) is the cocycle on `V`
  with `(ξ.refine t).toFun a b = ξ.toFun (a ≫ t) (b ≫ t)`.
- `algebraBaseMap F L` ([`Torus.LatticeGalois`](../Torus/LatticeGalois.md))
  is `Spec.map` of `algebraMap F L`, so `Over.mk (algebraBaseMap F L)` is
  `Spec L` as a scheme over `Spec F`.
- **Real places.** `NumberField.InfinitePlace F` is Mathlib's type of
  archimedean places of `F` (complex embeddings up to conjugation), and
  `w.IsReal` says that `w` comes from a real embedding. The completion
  `placeCompletion F (.inl w)`
  ([`Global.AdelicGroupLocalPoints`](../../Global/AdelicGroupLocalPoints.md))
  is Mathlib's completion `w.Completion` of `F` at `w`, as an `F`-algebra;
  for a real place it is a copy of `ℝ`.
- **Base change to a completion.** Write `b = algebraBaseMap F F_w`.
  `(Over.pullback b).obj (Spec L)` is `Spec (F_w ⊗_F L)` over `Spec F_w`;
  `r` (and `r'` for `L'`) is the counit of `Over.map b ⊣ Over.pullback b`,
  the projection to `Spec L` over `Spec F`; and `ξ.baseChange b _ r` is the
  cocycle of `G_{F_w}` on `Spec (F_w ⊗_F L)` obtained from `ξ` by composing
  pairs of points with `r`.
- **Change of extension.** For an `F`-algebra map `e : L → L'`, `s` is
  `Spec e : Spec L' ⟶ Spec L` over `Spec F`, and
  `(Over.pullback b).map s : Spec (F_w ⊗_F L') ⟶ Spec (F_w ⊗_F L)` is its
  base change to `F_w`.

## Statement in words

Let `F` be a number field and `G` a semisimple simply connected group over
`F`.

1. **Injectivity.** Let `L` be a finite separable field extension of `F`
   and let `ξ₁`, `ξ₂` be cocycles of `G` on `Spec L → Spec F`. If, at every
   real place `w` of `F`, the base changes of `ξ₁` and `ξ₂` to the cover
   `Spec (F_w ⊗_F L) → Spec F_w` are cohomologous (one is a twist of the
   other), then `ξ₁` and `ξ₂` are cohomologous on `Spec L`. Archimedean
   complex places and finite places impose no condition.
2. **Surjectivity.** Let `L` be a finite separable field extension of `F`
   and, for every real place `w`, let `c_w` be a cocycle of `G_{F_w}` on
   `Spec (F_w ⊗_F L) → Spec F_w`. Then there are a finite separable field
   extension `L'` of `F`, an `F`-algebra map `e : L → L'` and a cocycle `ξ`
   of `G` on `Spec L'` such that, at every real place `w`, the base change
   of `ξ` to `Spec (F_w ⊗_F L')` is cohomologous to the refinement of `c_w`
   along `Spec (F_w ⊗_F L') → Spec (F_w ⊗_F L)`.

## Source

J. S. Milne, *Algebraic Groups: The theory of group schemes of finite type
over a field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page numbers
are printed page numbers; the PDF page is the printed page plus 16.

- Theorem 25.65, p. 563: "Let G be a simply connected semisimple group over
  a global field k. Then H^1(k, G) ≃ ∏_{v real} H^1(k_v, G)." Proof:
  "Theorems 25.61 and 25.64 show that the map is injective. For the
  surjectivity, see Platonov and Rapinchuk 1994, Theorem 6.6, p. 286." The
  next sentence reads: "Theorem 25.65 reduces the study of the cohomology of
  simply connected semisimple groups over global fields to that of the same
  groups over R."
- "Global fields", p. 562: "A global field is a finite extension of Q or
  F_p(T). We let V denote the set of primes (possibly infinite) of a global
  field k, and k_v the completion of k at a v ∈ V."
- Theorem 25.64 and the map (169), p. 562, and Theorem 25.61(a), p. 561
  ("If G is simply connected, then H^1(k, G) = 1", for a semisimple group
  over a local field, that is, "a finite extension of Q_p or F_p((T))").
- Section 25g, p. 559: "In this section, we write H^1(k, G) for the flat
  cohomology group (2.72)." Example 2.72, p. 61: "The torsors under G_{R_0}
  over R_0 having an R-point are classified by the cohomology set
  H^1(R/R_0, G) of the complex G(R) → G(R ⊗_{R_0} R) →
  G(R ⊗_{R_0} R ⊗_{R_0} R)", for a faithfully flat `R_0`-algebra `R`.
  Proposition 2.69, p. 60, transfers affineness from `G` to its torsors.
- Conventions, p. 4: "After p. 162, all algebraic groups are affine."
  Chapter 25 opening, p. 544: "Recall that all algebraic groups are affine
  over a base field k."

The 2022 corrected reprint (in the project literature folder, registered as
`milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`; the PDF page
is the printed page plus 11) has Theorem 25.65 on printed p. 566 with the
same wording, the same proof and the same following sentence.

Errata. The errata snapshot of 2026-11-02 for the 2017 book (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) has one
entry for p. 563; it concerns Theorems 25.66 to 25.69 (direct sums instead
of direct products, and local forms quasi-split for all but finitely
many places), not Theorem 25.65. It has no
entry for printed pp. 4, 61, 544, 559, 561 or 562, and its p. 60 entry asks
to define torsors over nonaffine bases (the bases here are affine). The
errata snapshot of 2026-11-04 for the 2022 reprint (source ID
`milne-2022-algebraic-groups-errata-2026-11-04`, SHA-256
`78e5f297fb2c80c6dacf413fc5abd7f82ba3dd5e5f83b5a5205dfd93bf160d49`) has no
entry for printed p. 566. Its entry headed "p.563. Section g" says: "I
sometimes write "cohomology group" for "cohomology set" (G is usually
noncommutative)"; so the isomorphism of Theorem 25.65 is a bijection of
pointed sets.

## Derivation from the source (provenance: derived)

- **Number fields only.** Milne states the theorem for global fields. A
  global function field has no real places, so there the theorem says that
  `H^1(k, G)` is trivial. That case is not stated here; the statement takes
  `F` to be a number field, matching the Library's number-field places and
  completions.
- **Group.** Milne's algebraic groups are affine of finite type (p. 4,
  p. 544). `IsSimplyConnected G` includes `IsConnectedReductive G`, hence
  smoothness and affineness, so no separate hypothesis is imposed. See
  [`SimplyConnected.Basic`](../SimplyConnected/Basic.md) for the comparison
  of `IsSimplyConnected` with Milne's notion.
- **The map.** Milne writes `≃` for the canonical map sending the class of a
  `G`-torsor `P` to the classes of its base changes `P_{k_v}` at the real
  places; his proof calls it "the map" and proves it injective using the
  map (169) of Theorem 25.64. Part 1 is its injectivity and part 2 its
  surjectivity. The archimedean complex places are omitted, as in Milne.
- **Real places.** `w : InfinitePlace F` with `w.IsReal`, completed at `w`,
  gives each real prime `v` of Milne's set `V` once, with `k_v = F_w`.
- **Cocycle formulation.** As in the companion statement
  `NumberFieldHassePrincipleStatement` (Milne 25.64, a separate candidate),
  `H^1` is the set of isomorphism classes of torsors (Section 25g, 2.72),
  and classes are represented by cocycles on finite separable covers. The
  facts used are: every `G`-torsor over `F` (or over `F_w`) has a
  point over a finite separable extension, since it is nonempty, affine and
  of finite type and the characteristic is zero; by 2.72, cocycles on a
  faithfully flat cover `Spec R → Spec R_0`, up to twisting, correspond to
  torsors with an `R`-point, up to isomorphism; the cocycle `ξ.baseChange`
  describes the base-changed torsor; and `F_w ⊗_F L` is a nonzero finite
  product of fields finite separable over `F_w`. In addition, refining a
  cocycle along a morphism of covers describes the same torsor, with the
  point pulled back. None of this is proved in this module.
  - Part 1 is equivalent to injectivity of the map. If the map is
    injective and the base changes of `ξ₁` and `ξ₂` are cohomologous at
    every real place, the torsors they describe have isomorphic base
    changes at every real place, so they are isomorphic, and `ξ₁` and `ξ₂`
    are cohomologous by 2.72. Conversely, two torsors with isomorphic base
    changes at every real place have points over a common finite separable
    extension `L` (a compositum). The base changes of their cocycles on
    `Spec L` are cohomologous at every real place, by 2.72 over `F_w`, so
    part 1 shows that the cocycles are cohomologous and the torsors
    isomorphic.
  - Part 2 is implied by surjectivity: given `L` and the `c_w`, choose a
    torsor `P` over `F` whose base change at each real `w` is isomorphic to
    the torsor described by `c_w`. Take a finite separable `L'` containing
    `L` over which `P` has a point (a compositum), and let `ξ` be the
    cocycle of `P` on `Spec L'`. At each real `w`, the base change of `ξ`
    and the refinement of `c_w` are cocycles on the same cover
    `Spec (F_w ⊗_F L') → Spec F_w` describing isomorphic torsors, so they
    are cohomologous by 2.72.
  - Part 2 implies surjectivity: given a torsor `P_w` over `F_w` for each
    real `w`, take `L = F(√-1)`. For real `w`, `-1` is not a square in
    `F_w`, so `F_w ⊗_F L` is a quadratic field extension of `F_w ≅ ℝ`,
    isomorphic to `ℂ`. Each `P_w` has a point over `ℂ` and is described by
    a cocycle `c_w` on `Spec (F_w ⊗_F L)`. The torsor described by the
    cocycle `ξ` of part 2 then has base change isomorphic to `P_w` at every
    real `w`.
- **Universe.** `F`, `L` and `L'` live in `Type u`; the completions are in
  `CommAlgCat.{u}`.

Sanity check. If `F` has no real place, part 2 holds trivially (take
`L' = L`, `e` the identity and any `ξ`), and part 1 says that any two
cocycles of `G` on `Spec L` are cohomologous, so `H^1(F, G)` is trivial.
For `G = SL_n` this is consistent with `H^1(F, SL_n) = 1` over every field,
a standard consequence of Hilbert's Theorem 90.

## Relation to the Library

- `Langlands.GroupScheme.NumberFieldHassePrincipleStatement` (module
  `Rational/NumberFieldHassePrincipleStatement`; Milne 25.64, submitted as a
  separate candidate and not yet in the Library) states injectivity of the map to all
  places, including case (a) for simply connected groups. Part 1 here is
  the stronger injectivity with only the real places.
- `LocalSimplyConnectedCocycleVanishingStatement`
  ([`SimplyConnected.LocalCocycleVanishingStatement`](../SimplyConnected/LocalCocycleVanishingStatement.md))
  states Milne 25.61(a) for nonarchimedean local fields in the same
  cocycle language.

## For the later proof (not part of this unit)

Milne proves injectivity from Theorems 25.61 and 25.64 (the finite places
and the complex places contribute trivial local cohomology) and refers to
Platonov and Rapinchuk 1994, Theorem 6.6, p. 286, for surjectivity.
