# Statement: central isogenies carry maximal tori onto maximal tori

Authors: Worker 1428, Worker 1531.

This module states one unproved proposition, the `Prop`-valued `def`
`Langlands.GroupScheme.CentralIsogenyMaximalTorusImageStatement` with one
universe parameter `u`. Nothing is proved here, and no other declaration is
introduced.

The module imports `Langlands.GroupScheme.Torus.Maximal` and
`Langlands.GroupScheme.CentralIsogeny.Basic`. It reuses by name the Library
declarations `GroupScheme`, `CommGroupScheme`, `CommGroupScheme.groupHom`,
`IsConnectedReductive`, `IsCentralIsogeny`, `IsMaximalTorus`, `IsTorus` and
`IsClosedSubgroup`.

## The statement

```lean
def CentralIsogenyMaximalTorusImageStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G H : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G → IsConnectedReductive H →
    ∀ (π : G ⟶ H), IsCentralIsogeny π →
    ∀ (T S : CommGroupScheme (Spec (CommRingCat.of k)))
      (i : T.toGrp ⟶ G) (j : S.toGrp ⟶ H) (f : T ⟶ S),
      IsMaximalTorus i → IsTorus S.toGrp → IsClosedSubgroup j →
      Surjective (CommGroupScheme.groupHom f).hom.hom.left →
      i ≫ π = CommGroupScheme.groupHom f ≫ j →
      IsMaximalTorus j
```

In words: let `k : Type u` be an arbitrary field (no perfectness,
separable-closedness or characteristic hypothesis), `G` and `H` connected
reductive groups over `Spec k` (`IsConnectedReductive`, `Reductive/Basic.lean`),
and `π : G ⟶ H` a central isogeny (`IsCentralIsogeny`,
`CentralIsogeny/Basic.lean`: finite, flat, surjective, locally of finite
presentation, with scheme-theoretic kernel in the centre on every test
scheme). Let `i : T ⟶ G` be a maximal torus (`IsMaximalTorus`,
`Torus/Maximal.lean`: `T` is a torus, `i` is a closed immersion, and every
factorization of `i` through a closed torus of `G` is by an isomorphism). Let
`S` be a torus and `j : S ⟶ H` a closed subgroup, and let `f : T ⟶ S` be a
homomorphism of commutative group schemes whose underlying morphism of
schemes is surjective, with `i ≫ π = f ≫ j`. Then `j` is a maximal torus of
`H`, maximal among all closed tori of `H`, split or not.

Neither torus is assumed split. The hypotheses say that `j(S)` is the image
`π(i(T))` of the maximal torus `i(T)`.

This is the image direction of the published
`FiniteHomMaximalTorusReflectionStatement`
(`Torus/FiniteHomMaximalityStatement.lean`), which transfers maximality from
the target to the source. The published, proved
`CentralSurjectionMaximalSplitTorusImageStatement`
(`Rational/CentralSurjectionMaximalSplitTorusImageStatement.lean`) gives
maximality only among split tori. Over a field that is not separably closed,
a maximal split torus need not be a maximal torus, so that result does not
imply this statement.

## Why it is true (derived statement)

The statement is derived, not quoted. Source: J. S. Milne, *Algebraic Groups*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`;
printed page = PDF page − 16.

- Proposition 17.20 (printed pp.357-358), over an algebraically closed field
  (the standing assumption of Section 17b, printed p.353): if `q : G → Q` is a
  quotient map of connected group varieties and `H` is a maximal torus of `G`,
  then `q(H)` is a maximal torus of `Q`.
- Theorem 17.82 (printed p.379): a torus `T` in a group variety `G` over `k`
  is maximal if and only if `T_{k'}` is maximal in `G_{k'}` for a field
  `k' ⊇ k`.
- Definition 5.5 (printed p.99): quotient maps are the faithfully flat
  homomorphisms. A central isogeny is one.

Derivation. Pass to an algebraic closure `k^a`. By 17.82, `i(T)_{k^a}` is a
maximal torus of `G_{k^a}`. The base change `π_{k^a}` is still finite, flat
and surjective, so it is a quotient map of connected group varieties. As `f`
is surjective and `S` is smooth, `π(i(T))_{k^a} = j(S)_{k^a}`. By 17.20 it is
a maximal torus of `H_{k^a}`, and by 17.82 again `j(S)` is a maximal torus of
`H`.

A proof inside the Library can avoid the base change. Let `m : M ⟶ H` be a
closed torus with `g : S ⟶ M` and `g ≫ m = j`. Let `N` be an exponent of the
central kernel of `π` (`IsCentralIsogeny.exists_pow_eq_one_kernel`,
`CentralIsogeny/KernelTorsion.lean`). The power lift
`CentralPowerLift.exists_comp_eq_multiplication_comp`
(`CentralIsogeny/PowerLift.lean`) gives `a : M ⟶ G` with
`a ≫ π = [2N] ≫ m`. Its image is a closed torus `Z` of `G`
(`torusImageClosedTorusStatement`, `Torus/ImageProof.lean`). The maps
`f ≫ g ≫ a` and `[2N] ≫ i` from `T` agree after `π`, so they differ by a
homomorphism into the central kernel, which `N` kills. So a power of `i`
factors through `Z`, hence `i` factors through `Z`, and maximality of `i`
gives `Z = i(T)`. Then `[2N] ≫ m` factors through `j`, so `M = j(S)`. This
sketch is a suggestion for a proof, not part of the statement.

The official Milne errata snapshots
`milne-2017-algebraic-groups-errata-2026-11-02` (2017 edition) and
`milne-2022-algebraic-groups-errata-2026-11-04` (2022 reprint) have no entry
for printed pp.99, 353, 357-358 or 379, nor for 5.5, 17.20 or 17.82.

## Use

This statement is meant to supply maximality of the torus `i'' : T' ⟶ Q` in a
proof of the planned `SplitCentralTorusQuotientStatement` (statement task
`2ea05a8b-453e-49c8-8d20-9b2ad61ac047`, not yet in the Library). There `π` is the
quotient `G → G / Ker(t)`, `f` is the isogeny `t` of split tori, and the
maximality is required among all tori.
