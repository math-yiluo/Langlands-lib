# Statement: rational representatives of strongly regular classes of inner forms

Author: Worker 1534.

This module states one proposition and proves nothing:
`Langlands.GroupScheme.QuasiSplitSimplyConnectedRegularConjugateStatement.{u}`,
a `Prop`-valued `def` with one universe parameter `u`. It is the core input of
the conditional infinite-field Steinberg reduction in
`Rational/QuasiSplitCocycleTorusReductionInfinite.lean`. It is the concrete form
of the step "the conjugacy class of `y` in `G` is over `k`, whence by 1.7 it
contains an element `x` over `k`" of Steinberg (1965, §10).

## Lean statement

```lean
def QuasiSplitSimplyConnectedRegularConjugateStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (G A : GroupScheme (Spec (CommRingCat.of K))),
    IsSimplyConnected G → IsQuasiSplit G →
    ∀ (π : G ⟶ A), IsCentralIsogeny π →
    ∀ (a : AutomorphicAction A G),
      (∀ {Z : Over (Spec (CommRingCat.of K))} (h g : Z ⟶ G.X),
        a.act (h ≫ π.hom.hom) g = h * g * h⁻¹) →
    ∀ (ξ : Cocycle A (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))))
      (H : GroupScheme (Spec (CommRingCat.of K)))
      (e : LocalGroupIso G H (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))))),
      e.HasDiscrepancy a ξ →
    ∀ (y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ H.X)
      (S : GroupScheme (Spec (CommRingCat.of K))) (j : S ⟶ H),
      IsTorus S → IsClosedSubgroup j →
      (∀ {Z : Over (Spec (CommRingCat.of K))} (c : Z ⟶ H.X),
        c * (toUnit Z ≫ y) = (toUnit Z ≫ y) * c → ∃ s : Z ⟶ S.X, s ≫ j.hom.hom = c) →
      ∃ (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G.X)
        (T : GroupScheme (Spec (CommRingCat.of K))) (i : T ⟶ G),
        IsTorus T ∧ IsClosedSubgroup i ∧
        (∀ {Z : Over (Spec (CommRingCat.of K))} (c : Z ⟶ G.X),
          c * (toUnit Z ≫ x) = (toUnit Z ≫ x) * c → ∃ t : Z ⟶ T.X, t ≫ i.hom.hom = c) ∧
        ∃ (L' : Type u) (_ : Field L') (_ : Algebra K L')
          (_ : FiniteDimensional K L') (_ : IsGalois K L')
          (r : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L'))) ⟶
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))))
          (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L'))) ⟶ G.X),
          e.toFun r (g * (toUnit _ ≫ x) * g⁻¹) = toUnit _ ≫ y
```

The module imports `LocalGroupIso`, `SimplyConnected.Basic`,
`Reductive.QuasiSplit`, `Torus.Lattice` and `Mathlib.FieldTheory.Galois.Basic`.

## Meaning

Write `U = Over.mk (Spec L → Spec K)` for the finite Galois cover.

- `G` is simply connected (`IsSimplyConnected`: semisimple, and every central
  isogeny onto it from a semisimple group is an isomorphism) and quasi-split
  (`IsQuasiSplit`: connected reductive with a `K`-subgroup that is Borel over
  `K` and over `K̄`).
- `π : G ⟶ A` is a central isogeny (`IsCentralIsogeny`: finite, flat,
  surjective, locally of finite presentation, with central scheme-theoretic
  kernel). The action `a` of `A` on `G` is inner along `π`: a point of `A` of
  the form `π h` acts on `G` by conjugation by `h`, on every test. In the
  assembly, `G` is the simply connected cover of a semisimple group `A` and `a`
  is the conjugation action descended along `π`.
- `ξ` is a natural cocycle of `A` on `U`, and `H` is the twist of `G` by `ξ`:
  `e` is a family of natural local group isomorphisms `G(Z) ≃* H(Z)` over the
  points of `U`, with `e_b (a.act (ξ(b,c)) g) = e_c g` (`HasDiscrepancy`).
  So `H` is an inner form of `G`.
- `y` is a `K`-rational point of `H` whose scheme-theoretic centralizer, on all
  test schemes, lies in a closed `K`-torus `S` of `H`: `y` is strongly regular,
  as produced by `Rational/InfiniteFieldStronglyRegularPointStatement.lean`.

The conclusion provides:

- a `K`-rational point `x` of `G` whose scheme-theoretic centralizer lies in a
  closed `K`-torus `T` of `G`, so `x` is again strongly regular; and
- a finite Galois extension `L'/K` in the same universe, a morphism of covers
  `r : Spec L' ⟶ Spec L` over `K` (equivalently a `K`-embedding `L → L'`), and
  a point `g ∈ G(L')` such that `e`, at the point `r` of `U`, carries
  `g x g⁻¹` to `y`. That is, `x` and the point of `G` corresponding to `y` are
  conjugate over `L'`.

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
  - §10 (printed p.78, PDF p.31). In the twisted group `x(G)` Galois acts by
    `x(γ) = i(x_γ) ∘ γ`, with `i(x_γ)` inner. For the strongly regular `y` over
    `k`, `i(x_γ) γ(y) = y`. "Hence the conjugacy class of `y` in `G` is over
    `k`, whence by 1.7 it contains an element `x` over `k`. Writing
    `y = i(a) x` with `a` in `G` ..." The centralizer of `x` is "a torus
    because `x` is strongly regular, and over `k` because `x` is".
  - §11 (printed p.79, PDF p.32). Kneser's remark: the twisted group can be
    formed when the cocycle is only a cocycle modulo the centre, which is why
    the cocycle takes values in the quotient `A` here.
- A. Borel and T. A. Springer, *Rationality properties of linear algebraic
  groups II* (1968), source `borel-springer-1968-rationality-properties-ii`,
  SHA-256 `e465d0622ca9540ff21e0d53d7b2fdb00a14cf70a7caceee352c040a3cb1abef`,
  §8.6 (printed pp.483–484, PDF pp.41–42): "Let `G` be a connected,
  semi-simple simply connected `k`-group, which is quasi-split ... Then any
  regular semi-simple conjugacy class of `G` which is defined over `k` contains
  an element of `G(k)`", and "the proof given in loc. cit. carries over to
  arbitrary ground fields". This removes the perfectness hypothesis for
  regular semisimple classes, the only ones used here.

Derived content. The sources state that a regular semisimple conjugacy class
defined over `k` has a rational element. The Lean statement packages the
§10 argument that applies this to the strongly regular `y` of an inner twist,
in finite-cover form. "The class is defined over `K`" is replaced by its
source: `H` is a twist of `G` through the inner action `a`. Hence the
`G`-conjugacy class of the point of `G_L` corresponding to `y` is stable under
`Gal(L/K)`, and it is defined over `L`. Galois descent along the separable
extension `L/K` makes it defined over `K`. Conjugacy over an algebraic closure
is replaced by conjugacy over a finite Galois extension `L'` containing `L`.
This is possible because the transporter from `x` to that point is a torsor
under the smooth centralizer torus, so it has a point over a finite separable
extension. Strong regularity of `x` is part of the conclusion. Its
centralizer is a `K`-form of the centralizer of `y`, hence a `K`-torus, as in
Steinberg's last sentence above.

## What is not stated

- The general Theorem 1.7 for arbitrary semisimple classes is not stated, nor
  any statement about non-inner forms.
- Nothing is proved here; the existence is the obligation of a separate
  exact-target proof.
