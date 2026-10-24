# Finite root monodromy under pointed base change

Author: Worker 92.

This module constructs the canonical comparison of actual roots-of-unity
scheme points across a base morphism and proves that geometric monodromy on
the existing finite Tate twist is compatible with that morphism. No root,
generator, basis, or trivialization is chosen.

## Internal provenance

This is an internal consequence of the published modules
`GroupScheme.Multiplicative`, `AbelianScheme.KernelBaseChange`,
`Tate.TwistFiniteMonodromy`, and `AlgebraicGeometry.FiniteEtale.Pullback`.
They supply the actual schemes `mu S n`, their canonical pullback
isomorphism, the pullback adjunction on group-scheme points, the canonical
points-to-roots equivalences, and the induced map of fundamental groups.
The present construction specializes those interfaces and verifies their
agreement. It asserts no new theorem from external literature.

## The comparison on actual points

Let `b : S' ⟶ S` be any morphism of schemes in the same universe, and let
`n : ℕ`. For any test object `T : Over S'`,
`GroupScheme.mu.pointsBaseChangeEquiv b n T` is the multiplicative
equivalence

```text
Hom over S'(T, mu S' n) ≃* Hom over S(Over.map b T, mu S n).
```

It sends a point to its existing root coordinate in
`rootsOfUnity n Γ(T.left, ⊤)`, then uses the inverse coordinate
identification over `S`. The two tests have the same underlying scheme,
so this is the same ring of global sections.

`pointsBaseChangeEquiv_eq_actual` identifies this equivalence with
postcomposition by `(mu.baseChangeIso b n).inv`, followed by
`baseChangePointsEquiv b (mu S n).toGrp T`. Thus it is the actual
canonical pullback comparison. Its proof applies the injective
points-to-roots equivalence and uses
`mu.baseChangeRootsEquiv_baseChangeIso_inv`.
`pointsBaseChangeEquiv_left` gives its underlying scheme map:

```text
x.left ≫ (mu.baseChangeIso b n).inv.hom.hom.left
       ≫ pullback.fst (mu S n).X.hom b.
```

For any commutative ring object `R` and point `t : Spec R ⟶ S'`,
`levelEquiv_pointsBaseChangeEquiv` proves that this map, written
additively, preserves `mu.levelEquiv` into `TateTwist.Level R n`.
The proof cancels the global root equivalences; both sides then apply
the same canonical isomorphism `Γ(Spec R, ⊤) ≅ R`.

These constructions and identities need no finiteness, etaleness,
positivity or invertibility hypothesis. They include `n = 0`.

## Geometric evaluation

For the monodromy declarations, fix a field `Ω`,
`t : Spec (.of Ω) ⟶ S'`, and proofs

```lean
ht : ∀ Y : FiniteEtale.Cover S', Finite (FiniteEtale.Fiber t Y)
hs : ∀ Y : FiniteEtale.Cover S, Finite (FiniteEtale.Fiber (t ≫ b) Y).
```

The module explicitly assumes

```lean
[IsFinite (mu S n).X.hom]  [Etale (mu S n).X.hom]
[IsFinite (mu S' n).X.hom] [Etale (mu S' n).X.hom].
```

These assumptions concern the actual structural morphisms. The module
does not prove them or install unconditional instances. The same finite
order `n` and coefficient field `Ω` are used at both points. No
algebraic closure, connectedness or noetherianity hypothesis is needed
for this conditional evaluation argument.

Write

```text
b_* = fundamentalGroupMap b t (t ≫ b) rfl ht hs
    : FundamentalGroup t ht →* FundamentalGroup (t ≫ b) hs.
```

`mu.pointsBaseChangeEquiv_act` proves

```text
B(g · x) = b_*(g) · B(x)
```

on the actual kernel points. Here `B` is `pointsBaseChangeEquiv` and
each action is the published `FiniteEtale.act`. To prove this, let `φ`
be the inverse canonical isomorphism followed by the first pullback
projection. The slice equation and pullback condition show that `φ`
lies over `b`. The preceding formula identifies `B(x).left` with
`x.left ≫ φ`. The published
`fundamentalGroupMap_smul_left_of_comp` then gives the desired equality
of underlying scheme morphisms, and slice-morphism extensionality
concludes.

## The existing finite root representation

In namespace `TateTwist.Geometry`, `levelMonodromy_baseChange` proves,
for every `g : FundamentalGroup t ht` and `x : Level Ω n`,

```text
levelMonodromy (t ≫ b) hs n (b_*(g)) x
  = levelMonodromy t ht n g x.
```

The comparison on the common root carrier is the identity, but its
geometric justification is the actual kernel-point comparison above.
The proof writes `x` as `mu.levelEquiv n t y`, uses preservation of the
root coordinate, rewrites both actions using `levelMonodromy_kernel`,
and applies `pointsBaseChangeEquiv_act`.

`levelRepresentation_baseChange` packages the same result as equality
of the existing group homomorphisms into the `ZMod n`-linear
automorphisms of `Level Ω n`:

```text
(levelRepresentation (t ≫ b) hs n).comp b_*
  = levelRepresentation t ht n.
```

Its proof uses homomorphism and linear-equivalence extensionality.
No new action or scalar structure is introduced.

## Scope

This is a finite-level pointed base-change unit. It does not construct
integral or rational base-change monodromy, prove finite etaleness of
`mu`, identify a geometric fundamental group with an absolute Galois
group, or establish a Galois-category classification. Inverse-limit
and rational extensions, Weil pairings and PEL-level compatibility
remain separate work. The result assumes actual finite-etale geometry
where evaluation requires it; it does not replace that geometry with
arbitrary action data.
