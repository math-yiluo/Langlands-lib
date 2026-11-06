# Statement: scaling the simple-root vectors of an actual pinning

Author: Worker 1416.

This module contains one `Prop`-valued statement,
`Langlands.GroupScheme.PinnedRootScalingStatement.{u}`. The Lean file only
defines the proposition. It contains no proof of it and adds no other
declarations or axioms. It imports only [`Reductive.Pinning`](Pinning.md).

## Binders

The universe `u` is arbitrary. The proposition quantifies over:

- every field `k : Type u`, with no restriction on the characteristic or
  on perfectness;
- a group scheme `G : GroupScheme (Spec (CommRingCat.of k))` with an
  `IsAffineHom G.X.hom` instance;
- a pinning `p : SplitPinning G` from [`Reductive.Pinning`](Pinning.md):
  actual connected reductivity, a split maximal torus
  `p.inclusion : p.torus ⟶ G`, a finite reduced root datum satisfying
  `IsRootDatumOf` on the actual lattices of `p.torus`, a base `p.base`, and
  trivializations of the actual simple-root Lie spaces with chosen vectors
  `p.pinning.rootVector a`;
- a family `c : p.base.support → kˣ` of units of `k`, one for each simple
  root.

## Conclusion

There is an automorphism `σ : G ≅ G` of group schemes over `Spec k` with

- `p.inclusion ≫ σ.hom = p.inclusion`: `σ` restricts to the identity of
  the pinned torus; and
- for every simple root `a`,
  `Lie.targetMapLinear σ.hom (CommRingCat.of k) (p.pinning.rootVector a)
  = (c a : k) • p.pinning.rootVector a`, where `Lie.targetMapLinear` is the
  published linear differential on the actual dual-number identity kernel
  ([`Lie.KernelTargetMaps`](../Lie/KernelTargetMaps.md)).

So the differential of `σ` multiplies each chosen simple-root vector by the
prescribed unit. The statement only asks for an automorphism. In general
`σ` cannot be conjugation by a `k`-point of the torus: for `SL₂` the simple
root is twice a generator of the character lattice, so conjugation by
`T(k)` scales the root vector only by squares.

## Source and provenance

The statement is derived from a published argument; the Lean form is not
verbatim. Source: B. Conrad, *Reductive group schemes* (2014), SGA3 summer
school notes; printed page = PDF page.

- Proof of Corollary 6.1.15, pp.195–196. The conjugation action of `G` on
  itself factors through `G/Z_G`, and Conrad writes `c_t` for the action
  of `t ∈ (T/Z_G)(S)`. This action is the identity on `T` (p.195–196:
  "the T/Z_G-action on G is the identity on T"). Restricted to a root
  group `U_a`, it is through the character `ā : T/Z_G → G_m` induced by
  `a`. The characters `ā` are the roots of `(G/Z_G, T/Z_G, M̄)` with
  `M̄ = ∑_{a∈Φ} ℤ a`, the character group of the split torus `T/Z_G`
  (Corollary 3.3.6(1)). Conrad shows that `∆̄` "is a ℤ-basis of M̄",
  because `M̄ = ∑_{a∈Φ} ℤa = ∑_{a∈∆} ℤa = ⊕_{a∈∆} ℤa`. With units `u_a`
  for `a ∈ ∆`, he concludes that the condition on `t` is `ā(t) = u_a` for
  all `a ∈ ∆`, and that this condition can be met.
- Theorem 4.1.4, p.110: `exp_a : W(g_a) → G` is `T`-equivariant for
  conjugation on `G` and `a`-scaling on `W(g_a)`, and induces the canonical
  inclusion `g_a ⊂ g` on Lie algebras.

**Translation.** Take `S = Spec k`, `T = p.torus` and `∆` the support of
`p.base`. Since `∆̄` is a basis of `M̄`, the split torus `T/Z_G` is
`D(M̄) ≅ G_m^∆` through the characters `ā`, so there is
`t ∈ (T/Z_G)(k)` with `ā(t) = c a` for all `a ∈ ∆`. Put `σ = c_t`. It is an
automorphism of `G` that is the identity on `T`, which is the first
conclusion. By Theorem 4.1.4, `σ (exp_a X) = exp_a (ā(t) X)` for `X ∈ g_a`,
and differentiating gives `dσ(X) = ā(t) X` on `g_a`. For `X` the chosen
vector this is the second conclusion. The field `k` and the based root
datum are those of the pinning; reducedness and the base are part of
`SplitPinning`.

This module proves none of these steps.

## Role in the Library

This statement is planned as the scaling hypothesis of
`PinnedIsomorphism.Prerequisites` in the module
`Reductive.PinnedIsomorphismReduction`, which is submitted separately and
is not yet in the Library. There it normalizes the simple-root vectors of
the isomorphism given by the common-torus Isomorphism Theorem, which gives
the existence part of the published
[`PinnedIsomorphismStatement`](PinnedIsomorphismStatement.md). This module
does not prove it.
