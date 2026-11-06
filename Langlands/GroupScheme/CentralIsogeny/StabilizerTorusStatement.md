# Statement: stabilizers of torus-centralized points under central isogenies

Author: Worker 1534.

This module states one proposition and proves nothing:
`Langlands.GroupScheme.CentralIsogenyStabilizerTorusStatement.{u}`, a
`Prop`-valued `def` with one universe parameter `u`. It is a prerequisite of the
conditional infinite-field Steinberg reduction in
`Rational/QuasiSplitCocycleTorusReductionInfinite.lean`. There the cocycle lives
in the non-simply-connected group `A`, and the torus is the image in `A` of the
centralizer torus in the simply connected cover.

## Lean statement

```lean
def CentralIsogenyStabilizerTorusStatement : Prop :=
  ∀ (K : Type u) [Field K] (G A : GroupScheme (Spec (CommRingCat.of K))) (π : G ⟶ A),
    IsCentralIsogeny π →
    ∀ (a : AutomorphicAction A G),
      (∀ {Z : Over (Spec (CommRingCat.of K))} (h g : Z ⟶ G.X),
        a.act (h ≫ π.hom.hom) g = h * g * h⁻¹) →
    ∀ (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G.X)
      (T : GroupScheme (Spec (CommRingCat.of K))) (i : T ⟶ G),
      IsTorus T → IsClosedSubgroup i →
      (∀ {Z : Over (Spec (CommRingCat.of K))} (c : Z ⟶ G.X),
        c * (toUnit Z ≫ x) = (toUnit Z ≫ x) * c → ∃ t : Z ⟶ T.X, t ≫ i.hom.hom = c) →
      ∃ (S : GroupScheme (Spec (CommRingCat.of K))) (j : S ⟶ A),
        IsTorus S ∧ IsClosedSubgroup j ∧
          ∀ {Z : Over (Spec (CommRingCat.of K))} (c : Z ⟶ A.X),
            a.act c (toUnit Z ≫ x) = toUnit Z ≫ x → ∃ s : Z ⟶ S.X, s ≫ j.hom.hom = c
```

The module imports `CentralIsogeny.Basic`, `AutomorphicAction`,
`Torus.Lattice` and `Reductive.Basic`.

## Meaning

- `K` is an arbitrary field. `G` and `A` are arbitrary group schemes over
  `Spec K`, and `π : G ⟶ A` is a central isogeny (`IsCentralIsogeny`: finite,
  flat, surjective, locally of finite presentation, with central
  scheme-theoretic kernel). No reductivity is assumed.
- `a` is an action of `A` on `G` by group automorphisms that is inner along
  `π`: `a(π h)` is conjugation by `h`, on every test.
- `x` is a `K`-rational point of `G` whose scheme-theoretic centralizer, on all
  test schemes, lies in a closed `K`-torus `T` of `G`.
- The conclusion gives a closed `K`-torus `j : S ⟶ A` such that every point
  `c` of `A`, over any test `Z`, that fixes the pulled-back `x` under `a`
  factors through `S`. That is, the scheme-theoretic stabilizer of `x` in `A`
  lies in a torus.

## Sources and provenance

Provenance: derived.

- R. Steinberg, *Regular elements of semi-simple algebraic groups* (1965),
  source `steinberg-1965-regular-elements-semisimple-groups`, SHA-256
  `bda20c4a4b3cf4a7e9e5b17a4eacd0147d0c9370063ab3a3778114a53c8349b9`, §11
  (printed p.79, PDF p.32). Kneser's remark that in 1.8 "the assumption that
  `G` is simply connected can be dropped". For infinite `k` the group `x(G)`
  "can be constructed even if `(x_γ)` is only a cocycle modulo the centre of
  `G`, so that if `G` is simply connected such a 'cocycle' is equivalent to one
  with values in a torus over `k`. By applying this to the simply connected
  covering group ...". The torus in the quotient is the image of the
  centralizer torus of §10. This proposition is the step that identifies the
  stabilizer of `x` in the quotient with that image.
- J. S. Milne, *Algebraic Groups* (2017), source
  `milne-2017-algebraic-groups`, SHA-256
  `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`,
  Definition 18.1 (printed p.387, PDF p.403): "An isogeny is central ... if
  its kernel is central". An isogeny is "a surjective homomorphism with finite
  kernel" (same page). The Library's `IsCentralIsogeny` and its comparison with
  this convention are in `CentralIsogeny/Basic.md`.

Derived content. No source states this proposition separately. Steinberg uses
it implicitly when passing from the simply connected cover to the quotient. The
derivation, valid for any central isogeny, is as follows. The kernel of `π` is
central, so its points commute with `x`. By the hypothesis they lie in `T`. The
quotient `S = T / ker π` is a torus, and the induced map `S → A` is a proper
monomorphism, hence a closed immersion. If `c ∈ A(Z)` fixes `x`, then after the
fppf cover `Z ×_A G → Z` it lifts to `h` with `π h = c`. Then `h x h⁻¹ = x`, so
`h` lies in `T` and `c` lies in `S` after that cover. Since `S` is closed in
`A`, `c` lies in `S` on `Z`. The Lean conclusion only asks for some closed torus
containing the stabilizer.

## What is not stated

- Equality of the stabilizer with `S`, and the identification `S = π(T)`, are
  not stated.
- Nothing is proved here; the existence is the obligation of a separate
  exact-target proof.
