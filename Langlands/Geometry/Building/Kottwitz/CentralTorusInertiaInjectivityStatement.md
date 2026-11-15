# Injectivity of inertia coinvariants for a central induced torus quotient

This module states that, for a closed central induced torus `Z` of a connected
reductive group `H`, the map `π₁(Z)_I → π₁(H)_I` of inertia coinvariants is
injective. It also derives the z-extension case. The module contains no proof
of the statement.

## Sources

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), source ID
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

- Proof of Proposition 11.5.3, printed p. 431 / PDF p. 462, for a z-extension
  `1 → Z → G̃ → G → 1`: “The sequence X∗(Z)I → π1(G̃)I → π1(G)I → 0 is
  exact, since taking I-coinvariants is right-exact. The torsion-freeness of
  X∗(Z)I implies, as was argued in the proof of Lemma 2.5.20, that in fact the
  first map in this sequence is injective.”
- The cited argument does not appear in the proof of Lemma 2.5.20 (printed
  pp. 91–92 / PDF pp. 122–123), which is about the subgroups `T(K)_0`. It is
  written out in two other proofs:
  - Lemma 11.1.10, printed p. 425 / PDF p. 456, for an exact sequence
    `1 → T₁ → T₂ → T₃ → 1` of tori with `T₁` induced: “We claim that then the
    homomorphism X∗(T1)I → X∗(T2)I is injective. Indeed, its kernel is the
    image of the connecting homomorphism H1(I,X∗(T3)) → X∗(T1)I. We can
    replace I by a finite quotient through which it acts to see that
    H1(I,X∗(T3)) is finite. Since X∗(T1)I is torsion-free, the claim follows.”
  - Lemma 11.1.12(2), printed p. 426 / PDF p. 457: “If 1 → A → B → C → 1 is
    an exact sequence of k-tori and A has induced ramification, then the
    sequence 0 → X∗(A)I → X∗(B)I → X∗(C)I → 0 is exact.” Its proof gives the
    same argument.
- Definition 2.5.1, printed p. 86 / PDF p. 117: a torus is induced if `X_*(T)`,
  or equivalently `X^*(T)`, has a `ℤ`-basis invariant under the Galois group of
  a splitting extension. Definition 2.5.16 and Remark 2.5.17, printed p. 91 /
  PDF p. 122, define induced ramification: `T_K` is induced, or equivalently
  the lattice has a basis permuted by inertia.

The authors' *Corrections and additions* of 1 November 2024 (source ID
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`) change only
Section 11.7 in Chapter 11. In Section 2.5 they change only §2.5(b) and
Remarks 2.5.11 and 2.5.15. None of the passages above is affected.

## The statement

`InducedCentralTorusInertiaInjectivityStatement` quantifies over:

- a field tower `k → K → E` in universe `u` with `IsScalarTower k K E`, `E` a
  separable closure of `k` (`IsSepClosure k E`) and `K/k` normal
  (`Normal k K`). These are the hypotheses of the companion statement
  `CentralTorusInertiaExactnessStatement`. The inertia group is the Library's
  `relativeInertia k K E`, the kernel of restriction `Aut_k(E) → Aut_k(K)`. In
  KP, `K` is the maximal unramified extension of a local field `k`;
- a commutative group scheme `Z` over `Spec k` with `hZ : IsInducedTorus Z`
  (KP Definition 2.5.1, module `Langlands.GroupScheme.Torus.Induced`). There
  is a finite Galois splitting field over which the character lattice has a
  basis permuted by the Galois group;
- group schemes `H` and `G` over `Spec k` with `hH : IsConnectedReductive H`
  and an anonymous premise `IsConnectedReductive G`;
- homomorphisms `i : Z.toGrp ⟶ H` and `p : H ⟶ G` with `IsClosedSubgroup i`,
  `IsCentral i` and `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p`.
  The last premise says that `p` is the represented fppf quotient of `H` by the
  full subgroup functor of `Z`: flat, surjective and locally of finite
  presentation, with scheme kernel equal to the image of `i` on every test
  scheme. All these group data are the same as in
  `CentralTorusInertiaExactnessStatement`.

The conclusion is

```
Function.Injective
  (fundamentalInertiaMap k K E H hH Z.toGrp
    hZ.isTorus.isConnectedReductive_of_fieldSplitting i)
```

This is injectivity of the actual selected map `π₁(Z)_I → π₁(H)_I` of
`Langlands.Geometry.Building.Kottwitz.FundamentalGroup`. Here `π₁(-)_I` is
`FundamentalInertia`, the integral coinvariants of the actual Galois
representation on the chosen presentation of the algebraic fundamental group.
The map `fundamentalInertiaMap` is the selected descent of the actual
`fundamentalGroupMap` of `i`. The published proof `fundamentalInertiaMapStatement`
(module `Kottwitz.FundamentalInertiaMapProof`) shows that this descent exists
and is unique; its extra premise `Normal k E` follows from `IsSepClosure k E`. `π₁(Z)` is formed with the published proofs
`IsInducedTorus.isTorus` and `IsTorus.isConnectedReductive_of_fieldSplitting`,
as in the companion statement.

No injectivity, exactness, torsion-freeness of `X_*(Z)_I`, finiteness of
group homology, finite quotient of inertia or chosen splitting or basis is
assumed. The premises `IsConnectedReductive G` and the quotient map `p` do not
appear in the conclusion. They keep the setting of KP and of the companion
statement: `Z` is the kernel of a quotient map of connected reductive groups.
The premise on `G` is anonymous so that it is not an unused named binder.

## Provenance and scope

KP state this injectivity for z-extensions (proof of Proposition 11.5.3) and
for exact sequences of tori (Lemmas 11.1.10 and 11.1.12(2)). This statement is
a derived generalization: an arbitrary closed central induced torus of a
connected reductive group, with its fppf quotient, over any tower satisfying
the hypotheses above and in every characteristic. It is not a literal
quotation. KP's argument covers it:

1. `0 → π₁(Z) → π₁(H) → π₁(G) → 0` is an exact sequence of Galois modules.
   This is the companion group-scheme statement
   `Langlands.GroupScheme.AlgebraicFundamentalGroup.CentralTorusFundamentalExactnessStatement`.
   Its proof `centralTorusFundamentalExactness` (module
   `Langlands.GroupScheme.AlgebraicFundamentalGroupCentralTorusProof`, Task 6713)
   was published in Library commit `4abbe7aa`.
2. Inertia acts on these finitely generated groups through a finite quotient
   `Ī`. In the long exact homology sequence, the kernel of
   `π₁(Z)_I → π₁(H)_I` is the image of the finite group `H₁(Ī, π₁(G))`.
3. `π₁(Z)_I` is `X_*(Z)_I` by `TorusInertiaComparisonStatement`, proved as
   `torusInertiaComparison_proof` (module `Kottwitz.TorusInertiaComparisonProof`).
   `X_*(Z)` has a basis permuted by `Gal(L/k)` for a splitting field `L`, so
   inertia also permutes it, and `X_*(Z)_I` is free on the inertia orbits. A
   finite subgroup of a torsion-free group is zero.

The statement assumes that `Z` is induced. Induced ramification (KP
Definition 2.5.16) would be enough for this argument. The Library has no
predicate for it, and the objective of this task, like Proposition 11.5.3,
concerns induced tori.

Inducedness cannot simply be dropped. Take a quadratic extension `L/k` that is
not contained in `K`, so that inertia maps onto `Gal(L/k)`. Let
`H = R_{L/k} G_m`, let `Z` be its norm-one torus and let `p` be the norm onto
`G = G_m`. Then `X_*(Z) = ℤ` with the sign action, so `X_*(Z)_I = ℤ/2ℤ`. Its
generator `e₁ − e₂` maps to zero in `X_*(H)_I = ℤ`. This `Z` is a closed
central torus, but it is not induced.

## The z-extension case

`InducedCentralTorusInertiaInjectivityStatement.zExtension` derives from the
statement that, for every `z : ZExtension G` (module
`Langlands.GroupScheme.ZExtension`, KP §11.4),

```
Function.Injective
  (fundamentalInertiaMap k K E z.H z.isZExtension.source_reductive z.Z.toGrp
    z.isZExtension.induced.isTorus.isConnectedReductive_of_fieldSplitting z.i)
```

It applies the statement to `z.Z`, `z.H`, `G`, `z.i` and `z.p`, with the fields
`induced`, `source_reductive`, `target_reductive`, `closed`, `central` and
`quotient` of `z.isZExtension`. This is the injectivity in the proof of KP
Proposition 11.5.3. The derivation is an implication from the statement, not a
proof of it.

The proof term of `π₁(Z)` is written exactly as in the premise (Inj) of
`ZExtensionRationalKernelReductionStatement`
(module `Kottwitz.ZExtensionRationalKernelReduction`). A private compile check
confirmed that
`fun F _ _ _ _ _ z => h.zExtension F (UnramifiedClosure F) (SeparableClosure F) z`
proves that premise.

## Imports

`Kottwitz.FundamentalGroup` supplies `fundamentalInertiaMap`.
`GroupScheme.Torus.Induced` supplies `IsInducedTorus` and
`IsInducedTorus.isTorus`. `GroupScheme.ZExtension` supplies `ZExtension`, and
`Mathlib.FieldTheory.IsSepClosed` supplies `IsSepClosure`.
