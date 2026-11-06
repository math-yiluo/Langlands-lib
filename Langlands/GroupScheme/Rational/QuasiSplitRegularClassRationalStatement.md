# Statement: rational points of Galois-stable strongly regular classes

Author: Worker 1601.

This module states one proposition and proves nothing:
`Langlands.GroupScheme.QuasiSplitRegularClassRationalStatement.{u}`, a
`Prop`-valued `def` with one universe parameter `u`. It is the core input of
the conditional reduction of
`Langlands.GroupScheme.QuasiSplitSimplyConnectedRegularConjugateStatement`
(module `Rational/QuasiSplitRegularConjugateStatement.lean`). It is the form
of Steinberg's Theorem 1.7, as extended by Borel–Springer 8.6, that this
reduction uses. The step it serves is "the conjugacy class of `y` in `G` is
over `k`, whence by 1.7 it contains an element `x` over `k`" in Steinberg
(1965), §10.

## Lean statement

```lean
def QuasiSplitRegularClassRationalStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (G : GroupScheme (Spec (CommRingCat.of K))),
    IsSimplyConnected G → IsQuasiSplit G →
    ∀ (z : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ G.X)
      (S : GroupScheme (Spec (CommRingCat.of L)))
      (j : S ⟶ (baseChange (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj G),
      IsTorus S → IsClosedSubgroup j →
      (∀ {Z : Over (Spec (CommRingCat.of L))}
          (c : Z ⟶ ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj G).X),
        c * (toUnit Z ≫ (baseChangeBasePointsEquiv _ G).symm z) =
            (toUnit Z ≫ (baseChangeBasePointsEquiv _ G).symm z) * c →
          ∃ s : Z ⟶ S.X, s ≫ j.hom.hom = c) →
      (∀ σ : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))),
        ∃ (E : Type u) (_ : Field E) (_ : Algebra K E)
          (q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))) ⟶
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))))
          (h : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))) ⟶ G.X),
          h * (q ≫ z) * h⁻¹ = q ≫ σ ≫ z) →
      ∃ (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G.X)
        (E : Type u) (_ : Field E) (_ : Algebra K E)
        (q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))) ⟶
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))))
        (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))) ⟶ G.X),
        g * (toUnit _ ≫ x) * g⁻¹ = q ≫ z
```

The module imports `CocharacterTransport` (for `baseChangeBasePointsEquiv`),
`SimplyConnected.Basic`, `Reductive.QuasiSplit`, `Torus.Lattice` and
`Mathlib.FieldTheory.Galois.Basic`.

## Meaning

Write `b : Spec L ⟶ Spec K` for the map induced by `algebraMap K L` and
`U = Over.mk b` for the finite Galois cover, viewed as an object over `Spec K`.

- `G` is simply connected (`IsSimplyConnected`: semisimple, and every central
  isogeny onto it from a semisimple group is an isomorphism) and quasi-split
  (`IsQuasiSplit`: connected reductive with a `K`-subgroup that is Borel over
  `K` and over `K̄`).
- `z : U ⟶ G.X` is a point of `G` with values in `L`. Its counterpart
  `(baseChangeBasePointsEquiv b G).symm z` is the corresponding `L`-rational
  point of the base change `G_L = (baseChange b).obj G`.
- `S` is an `L`-torus with a closed subgroup inclusion `j : S ⟶ G_L`. Every
  point `c` of `G_L`, on any test scheme `Z` over `Spec L`, that commutes with
  the restriction of that `L`-rational point factors through `S`. So the
  scheme-theoretic centralizer of `z` in `G_L` lies in, and in fact equals, the
  closed torus `S`: `z` is strongly regular. Since the point commutes with
  itself it lies in `S`, and `S` is commutative, so the centralizer equals `S`.
  In particular `z` is semisimple and its centralizer has dimension the rank,
  so `z` is regular semisimple.
- For every endomorphism `σ` of `U` over `Spec K`, that is, every element of
  `Gal(L/K)`, the Galois conjugate `σ ≫ z` is conjugate to `z` over some field
  extension. That is, there are a field `E` in universe `u`, a morphism of
  covers `q : Spec E ⟶ Spec L` over `K` (a `K`-embedding `L → E`), and a point
  `h ∈ G(E)` with `h (q ≫ z) h⁻¹ = q ≫ σ ≫ z`. So the geometric conjugacy
  class of `z` is stable under `Gal(L/K)`.

The conclusion provides a `K`-rational point `x` of `G`, together with a field
`E` in universe `u`, a morphism of covers `q : Spec E ⟶ Spec L` over `K` and a
point `g ∈ G(E)` with `g x g⁻¹ = q ≫ z`. That is, the geometric conjugacy class
of `z` contains the `K`-rational point `x`.

## Sources and provenance

Provenance: derived.

- R. Steinberg, *Regular elements of semi-simple algebraic groups* (1965),
  source `steinberg-1965-regular-elements-semisimple-groups`, SHA-256
  `bda20c4a4b3cf4a7e9e5b17a4eacd0147d0c9370063ab3a3778114a53c8349b9`.
  - Theorem 1.7 (printed p.51, PDF p.4): "Assume that `G` is simply connected
    and over `k` and that `G` contains a Borel subgroup over `k`. Then the
    natural map from the set of semisimple elements over `k` to the set of
    semisimple classes over `k` is surjective. In other words, each semisimple
    class over `k` contains an element over `k`." Here `k` is perfect (printed
    p.51) and `G` semisimple.
  - §10 (printed p.78, PDF p.31) applies this to the strongly regular element
    `y` of a twisted group: "Hence the conjugacy class of `y` in `G` is over
    `k`, whence by 1.7 it contains an element `x` over `k`."
- A. Borel and T. A. Springer, *Rationality properties of linear algebraic
  groups II* (1968), source `borel-springer-1968-rationality-properties-ii`,
  SHA-256
  `e465d0622ca9540ff21e0d53d7b2fdb00a14cf70a7caceee352c040a3cb1abef`,
  §8.6 (printed pp.483–484, PDF pp.41–42): "Let `G` be a connected,
  semi-simple simply connected `k`-group, which is quasi-split (i.e., contains
  a Borel subgroup which is defined over `k`). Then any regular semi-simple
  conjugacy class of `G` which is defined over `k` contains an element of
  `G(k)`." It adds: "Using 8.2, the proof given in loc. cit. carries over to
  arbitrary ground fields". This removes Steinberg's perfectness hypothesis
  for regular semisimple classes, the only ones used here.

Derived content. The sources state that a regular semisimple class defined
over `k` contains a `k`-rational element. In this statement:

- The class is the geometric conjugacy class of the `L`-point `z`. Strong
  regularity is the all-test containment of its centralizer in a closed
  `L`-torus; as noted under Meaning, this makes `z` regular semisimple.
- "Defined over `K`" is replaced by its concrete source: the class of `z` is
  stable under every element of `Gal(L/K)`, witnessed by conjugacy over some
  field extension. The class is the orbit of an `L`-point with smooth
  stabilizer, so it is defined over `L` ⊆ `K^s`. Stability under `Gal(L/K)`
  gives stability under `Gal(K^s/K)`, since the latter acts on `z` through
  its quotient `Gal(L/K)`. By Galois descent the class is then defined over
  `K`.
- "Contains an element of `G(k)`" is stated as conjugacy of the rational point
  `x` to `z` over some field extension `E`. An algebraic closure of `L` in
  universe `u` is one such field.

## What is not stated

- The general Theorem 1.7 for arbitrary semisimple classes, and any
  statement about classes that are not strongly regular, are not stated.
- No Steinberg cross-section or invariant-theoretic quotient map is stated.
  In particular no `K`-rational cross-section `N` is claimed. Steinberg's
  Theorem 1.6 (printed p.51, PDF p.4) constructs `N` over `k` only when `G`
  splits over `k`, or contains a Borel subgroup over `k` but no component of
  type `A_n` with `n` even. For type `A_n` with `n` even it offers "a
  substitute (see 9.7)".
- Nothing is proved here; the existence is the obligation of a separate
  exact-target proof.
