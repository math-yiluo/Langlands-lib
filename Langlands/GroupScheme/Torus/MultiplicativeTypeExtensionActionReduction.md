# Central extensions of multiplicative type: rigidity inputs and the closing step

Worker 3502 (Task 6779).

This module supplies all steps of Milne's proof of Corollary 12.41 (the target
[`MultiplicativeTypeExtensionActionStatement`](MultiplicativeTypeExtensionActionStatement.md))
except the construction of the difference family `ψ : G × Q → N`. That construction is
`AutomorphicAction.centralDifference` (Worker 302,
[`AutomorphicAction.CentralDifference`](../AutomorphicAction/CentralDifference.md)). The
assembled proof is in
[`MultiplicativeTypeExtensionActionProof`](MultiplicativeTypeExtensionActionProof.md).

Every rigidity result here takes diagonalizable rigidity as an explicit hypothesis
`hRig : DiagonalizableRigidityStatement.{u}` (the Library's form of Milne, Theorem 12.36). The
module does not prove the target statement, and it adds no definitions and no axioms.

All declarations are in the namespace
`Langlands.GroupScheme.MultiplicativeTypeExtensionAction`. Throughout, `k` is a field and
`G H N Q : GroupScheme (Spec (CommRingCat.of k))`, with homomorphisms `j : N ⟶ H` and
`p : H ⟶ Q`. "Connected algebraic group" abbreviates the three hypotheses
`hGft : LocallyOfFiniteType G.X.hom`, `hGqc : QuasiCompact G.X.hom` and
`hGc : ConnectedSpace G.X.left`.

## Source

James S. Milne, *Algebraic Groups* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, printed pages 243–244.

- Theorem 12.36 (p.243) is rigidity for diagonalizable groups, parametrized by a connected
  algebraic scheme. In the Library it is the proposition `DiagonalizableRigidityStatement`.
- Corollary 12.37 (p.244): every action of a connected algebraic group on a group of
  multiplicative type is trivial. `act_eq_self` is this corollary. The implemented route goes through
  homomorphism families and a common splitting field; scalar extension is a
  step supplied by the cited Library inputs.
- The proof of Corollary 12.41 (p.244) begins: "Corollary 12.37 shows that the action of G
  on H factors through an action G × H/N → H". `act_comp_eq` and `act_comp_quotient` are the
  two applications of 12.37, to `N` and to `H/N`. The proof ends: "Theorem 12.36 now shows
  that this action is trivial". `act_eq_of_difference` is the formal last line, with the
  output of Theorem 12.36 as hypothesis.

The helper lemmas `isRepresentedBy_range` and `quasiCompact_quotient` are internal and have
no counterpart in the source.

## Declarations

### `homFamily_eq`

```lean
theorem homFamily_eq (hRig : DiagonalizableRigidityStatement.{u})
    (hGft : LocallyOfFiniteType G.X.hom) (hGqc : QuasiCompact G.X.hom)
    (hGc : ConnectedSpace G.X.left) (hQ : IsMultiplicativeType Q) (hN : IsMultiplicativeType N)
    {F : ∀ T : Over (Spec (CommRingCat.of k)), (T ⟶ G.X) → (T ⟶ Q.X) → (T ⟶ N.X)}
    (hF : HomFamily.IsHomFamily F) {T : Over (Spec (CommRingCat.of k))}
    (g : T ⟶ G.X) (q : T ⟶ Q.X) : F T g q = F T 1 q
```

Let `G` be a connected algebraic group and `Q`, `N` groups of multiplicative type. Let `F`
be a family of homomorphisms `Q → N` parametrized by `G`: multiplicative in the `Q`-point and
natural in the test object (`HomFamily.IsHomFamily`). Then `F` has the same value at every
point `g` of `G` as at the identity. Proof: this is the published
`HomFamily.eq_one_of_multiplicativeType` (Worker 798,
[`Torus.MultiplicativeTypeHomFamily`](MultiplicativeTypeHomFamily.md)), applied after the
three hypotheses on `G` are made available as instances. That lemma takes one field extension
`K` over which `Q` and `N` are both diagonalizable with finitely generated character groups
(`IsMultiplicativeType.exists_common_splitting`). It then applies
`HomFamily.eq_one_of_commonSplitting`, which descends diagonalizable rigidity (`hRig`) from
`K` to `k`. `homFamily_eq` only restates the lemma with the hypotheses on `G` as explicit
arguments, the form the other lemmas of this module use.

### `act_eq_self`

```lean
theorem act_eq_self (hRig : DiagonalizableRigidityStatement.{u})
    (hGft : LocallyOfFiniteType G.X.hom) (hGqc : QuasiCompact G.X.hom)
    (hGc : ConnectedSpace G.X.left) (hN : IsMultiplicativeType N)
    (a : AutomorphicAction G N) {T : Over (Spec (CommRingCat.of k))}
    (g : T ⟶ G.X) (x : T ⟶ N.X) : a.act g x = x
```

Every action of a connected algebraic group by group automorphisms on a group of
multiplicative type is trivial. Proof: `(T, g, x) ↦ a.act g x` is a homomorphism family `N → N`
parametrized by `G`. It is multiplicative by `AutomorphicAction.act_mul_right` and natural by
`AutomorphicAction.naturality`. By `homFamily_eq` (with `Q = N`) its value at `g` equals its
value at `1`, which is `x` by `AutomorphicAction.act_one_left`.

This is part 1 of the published statement `MultiplicativeTypeConnectedActionStatement`,
conditional on `hRig`. Part 2 of that statement is not used here.

### `isRepresentedBy_range`

```lean
theorem isRepresentedBy_range (hj : IsClosedSubgroup j) :
    (SubgroupFunctor.range j).IsRepresentedBy j
```

A closed subgroup `j` represents its range. A closed immersion is a monomorphism, so
`j.hom.hom` is a monomorphism of schemes over `Spec k`; `Over.mono_of_mono_left` transfers this
to the over category. The range of `j` is `SubgroupFunctor.range j` by definition.

### `quasiCompact_quotient`

```lean
theorem quasiCompact_quotient [QuasiCompact H.X.hom] [IsAffine Q.X.left] :
    QuasiCompact p.hom.hom.left
```

If `H` is quasi-compact over `Spec k` and `Q` is affine, then the underlying morphism of `p` is
quasi-compact. Proof: `p.hom.hom.left ≫ Q.X.hom = H.X.hom` (`Over.w`) is quasi-compact. Also
`Q.X.hom` is quasi-separated, being a morphism between affine schemes, so
`QuasiCompact.of_comp` applies. The only property of `p` used is that it is a morphism over
`Spec k`.

### `act_comp_eq`

```lean
theorem act_comp_eq (hRig : DiagonalizableRigidityStatement.{u})
    (hGft : LocallyOfFiniteType G.X.hom) (hGqc : QuasiCompact G.X.hom)
    (hGc : ConnectedSpace G.X.left) (hj : IsClosedSubgroup j) (hN : IsMultiplicativeType N)
    (a : AutomorphicAction G H)
    (ha : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (x : T ⟶ H.X),
      x ∈ (SubgroupFunctor.range j).carrier T →
        a.act g x ∈ (SubgroupFunctor.range j).carrier T)
    {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ G.X) (n : T ⟶ N.X) :
    a.act g (n ≫ j.hom.hom) = n ≫ j.hom.hom
```

The action fixes `N` pointwise: for every test object `T`, every point `g` of `G` and every
point `n` of `N` over `T`, `g · j(n) = j(n)`. The hypothesis `ha` is copied unchanged from the
target statement.

Proof: `AutomorphicAction.onRepresentedSubgroup a j _ ha` is the action of `G` on `N`
obtained by restricting `a` (it uses `isRepresentedBy_range hj`). The lemma
`onRepresentedSubgroup_act_comp` says `(restricted g · n) ≫ j = g · (n ≫ j)`. By `act_eq_self`
the restricted action is trivial.

### `act_comp_quotient`

```lean
theorem act_comp_quotient (hRig : DiagonalizableRigidityStatement.{u})
    (hGft : LocallyOfFiniteType G.X.hom) (hGqc : QuasiCompact G.X.hom)
    (hGc : ConnectedSpace G.X.left) (hHqc : QuasiCompact H.X.hom)
    (hp : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) p)
    (hQ : IsMultiplicativeType Q) (a : AutomorphicAction G H)
    (ha : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (x : T ⟶ H.X),
      x ∈ (SubgroupFunctor.range j).carrier T →
        a.act g x ∈ (SubgroupFunctor.range j).carrier T)
    {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ G.X) (x : T ⟶ H.X) :
    a.act g x ≫ p.hom.hom = x ≫ p.hom.hom
```

The induced action on `Q` is trivial: `p(g · x) = p(x)` for all points `g` of `G` and `x` of
`H` over every test object `T`.

Proof: `Q` is affine (`IsMultiplicativeType.isAffine`), so `p` is quasi-compact by
`quasiCompact_quotient`. Then `RelativeRoot.IsFppfQuotient.action a ha` is the action of `G`
on `Q` induced by `a`, and `IsFppfQuotient.action_act` says
`(induced g · (x ≫ p)) = (g · x) ≫ p`. By `act_eq_self` the induced action is trivial.

### `act_eq_of_difference`

```lean
theorem act_eq_of_difference (a : AutomorphicAction G H) (ψ : G.X ⊗ Q.X ⟶ N.X)
    (hψ : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (x : T ⟶ H.X),
      a.act g x = x * (lift g (x ≫ p.hom.hom) ≫ ψ ≫ j.hom.hom))
    (hrig : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (q : T ⟶ Q.X),
      lift g q ≫ ψ = lift 1 q ≫ ψ)
    {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ G.X) (x : T ⟶ H.X) :
    a.act g x = x
```

The closing step of Milne's argument. Suppose `ψ : G × Q → N` satisfies
`g · x = x · j(ψ(g, p(x)))` on all points (`hψ`). Suppose also `ψ(g, q) = ψ(1, q)` for all
points (`hrig`, the conclusion of rigidity with the identity of `G` as base point). Then the
action is trivial. Proof: rewrite `g · x` by `hψ`. Replace `ψ(g, p x)` by `ψ(1, p x)` using
`hrig`. Recognise `x · j(ψ(1, p x))` as `1 · x` by `hψ` again. Finish with
`AutomorphicAction.act_one_left`. This step needs no hypothesis on `j`, `p` or the groups.
