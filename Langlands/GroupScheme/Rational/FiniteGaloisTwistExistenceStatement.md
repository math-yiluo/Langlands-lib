# Statement: twisting an affine field group by a finite-Galois cocycle

Author: Worker 1534.

This module states one proposition and proves nothing:
`Langlands.GroupScheme.FiniteGaloisTwistExistenceStatement.{u}`, a `Prop`-valued
`def` with one universe parameter `u`. It is a prerequisite of the conditional
infinite-field Steinberg reduction in
`Rational/QuasiSplitCocycleTorusReductionInfinite.lean`, where it produces the
group that Steinberg (1965, §10) calls "the group `G` twisted by the cocycle".

## Lean statement

```lean
def FiniteGaloisTwistExistenceStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (A G : GroupScheme (Spec (CommRingCat.of K))),
    IsAffineHom G.X.hom →
    ∀ (a : AutomorphicAction A G)
      (ξ : Cocycle A (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))))),
      ∃ (H : GroupScheme (Spec (CommRingCat.of K)))
        (e : LocalGroupIso G H (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))))),
        IsAffineHom H.X.hom ∧ e.HasDiscrepancy a ξ
```

The module imports `Langlands.GroupScheme.LocalGroupIso` and
`Mathlib.FieldTheory.Galois.Basic` and uses only published declarations.

## Meaning

Write `U = Over.mk (Spec L → Spec K)` for the cover of the finite Galois
extension `L/K`; both fields live in the same universe `u`.

- `A` and `G` are arbitrary group schemes over `Spec K` (group objects of
  `Over (Spec K)`); `G` is assumed affine over `K` (`IsAffineHom G.X.hom`).
  No finiteness, smoothness or reductivity is assumed of either.
- `a : AutomorphicAction A G` is an action of `A` on `G` by group
  automorphisms, given by one morphism `A × G → G` (module
  `AutomorphicAction`); `a.act h g` is its value on points over a common test.
- `ξ : Cocycle A U` (module `TorsorCocycle`) assigns to every test `Z` over
  `K` and every pair of points `b c : Z ⟶ U` a point `ξ(b,c) : Z ⟶ A`,
  naturally in `Z`, with `ξ(b,d) = ξ(b,c) · ξ(c,d)`.
- `LocalGroupIso G H U` (module `LocalGroupIso`) is a family of group
  isomorphisms `e_b : G(Z) ≃* H(Z)`, one for each test `Z` and each point
  `b : Z ⟶ U`, natural in `Z`. By Yoneda this is the same as an isomorphism
  of group schemes `G_L ≅ H_L` over `L`.
- `e.HasDiscrepancy a ξ` says `e_b (a.act (ξ(b,c)) g) = e_c g` for all tests
  `Z`, all `b c : Z ⟶ U` and all `g : Z ⟶ G`.

So the proposition says: every natural `A`-valued cocycle on the Galois cover,
acting on `G` through `a`, is the discrepancy of an actual affine `K`-form `H`
of `G` together with an identification `G_L ≅ H_L`. In classical language, `H`
is the twist of `G` by the image of `ξ` in the automorphisms of `G_L`.

## Sources and provenance

Provenance: derived.

- J. S. Milne, *Algebraic Groups* (2017), source
  `milne-2017-algebraic-groups`, SHA-256
  `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
  Section 3.k "Forms of algebraic groups" (printed pp.76–78, PDF pp.92–94):
  for a finite Galois extension `K/k` with group `Γ`, Theorem 3.43 (printed
  p.78, PDF p.94) says that for an affine algebraic group `G_0` over `k`,
  "The cohomology set `H^1(Γ, A(K))` classifies the isomorphism classes of
  `K/k`-forms of `G_0`", where `A(K)` is the automorphism group of `(G_0)_K`.
  Its proof refers to the proof of Theorem 3.37 (printed p.77, PDF p.93):
  a 1-cocycle `(a_σ)` is used to define a new semilinear action of `Γ`
  (`σ` acts as `a_σ` composed with the old action of `σ`), and its fixed
  points form the `k`-structure of the form, by the descent equivalence 3.36
  (printed p.77, PDF p.93). The "every class arises from a form" half of the
  theorem is what is used here.
- R. Steinberg, *Regular elements of semi-simple algebraic groups* (1965),
  source `steinberg-1965-regular-elements-semisimple-groups`, SHA-256
  `bda20c4a4b3cf4a7e9e5b17a4eacd0147d0c9370063ab3a3778114a53c8349b9`, §10
  (printed p.78, PDF p.31): "We form `x(G)`, the group `G` twisted by the
  cocycle `x` ... This is a group over `k`, isomorphic to `G` over `K`", where
  Galois elements act on `x(G)` by the inner automorphism by `x_γ` composed with
  the original action. This is the use made of the proposition.

Derived content. The sources state that a Galois 1-cocycle with values in the
automorphism group of `G_L` defines a form of `G`. The Lean formulation is
concrete and slightly more general in its bookkeeping. The cocycle is a natural
cocycle of the group scheme `A` on all points of the Čech pair of the cover,
not a function on `Gal(L/K)`. It acts through an automorphic action `a` rather
than taking values in `Aut(G_L)`. The form is recorded by natural local
isomorphisms on all tests over `Spec L`, with discrepancy `ξ`. Because
`L ⊗_K L ≅ ∏_{σ ∈ Gal(L/K)} L`, the scheme `Spec L ×_K Spec L` is a disjoint
union of copies of `Spec L` indexed by `Gal(L/K)`. Such a cocycle is therefore
the same as a Galois 1-cocycle with values in `A(L)`. Its image under `a` is a cocycle in `Aut(G_L)`, and
Milne's theorem applies to it. Milne's 3.k is stated for algebraic groups, that
is, affine groups of finite type. The descent argument of 3.36/3.37 uses only
that the coordinate ring is a Hopf algebra with a semilinear Galois action. The
Lean statement therefore assumes only that `G` is affine. The
conclusion records affineness of `H`, which is part of being such a form.

## What is not stated

- Uniqueness of `H` up to isomorphism, and the dependence only on the
  cohomology class of `ξ`, are not stated.
- Nothing is proved here; existence of `H` and `e` is the obligation of a
  separate exact-target proof.
