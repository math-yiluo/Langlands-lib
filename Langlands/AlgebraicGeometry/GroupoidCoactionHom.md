# Hom modules of coactions

This internal algebraic construction uses the published ring relation and
coaction definitions unchanged. The rings `B` and `C` have arbitrary universe
`u`; the two coefficient modules `G` and `M` have an independent arbitrary
universe `v`. The domain `G` is finitely presented over `B`. In particular,
the construction applies to a finite module over a Noetherian base.
It does not require finiteness of `M`.

For a flat `B`-algebra `S`, `homTensorEquiv` is the `S`-linear equivalence

```
S ⊗[B] Hom_B(G,M) ≃ Hom_S(S ⊗[B] G, S ⊗[B] M).
```

This is Mathlib's `Module.FinitePresentation.isBaseChange_map`, followed
by `IsBaseChange.equiv`. On pure tensors it evaluates by
`(c ⊗ f)(d ⊗ g) = (c*d) ⊗ f(g)`. Tensor induction proves its compatibility
with specialization along an algebra homomorphism `C →ₐ[B] S`.

Let `hE : RingEtaleEquivalenceRelation t`, and let `θG` and `θM` be actual
coactions. The published `reverseTensor` operator `R` on either source tensor
module is additive, involutive, and semilinear for reversal of the relation
ring. It sends `θ(g)` to `1 ⊗ g` and sends `1 ⊗ g` to `θ(g)`.
For `f : G →ₗ[B] M`, `homConjugate` is the map

```
R_M ∘ (f.baseChange C) ∘ R_G.
```

The two reversal actions cancel, so this map is `C`-linear.
Its inverse image under `homTensorEquiv` defines `homCoactionMap f`.
The map is additive. Scaling `f` by `b : B` scales the extended map by
the source image of `b`; reversal changes that scalar to `t(b)`.
This proves the required target semilinearity.
The defining evaluation identity is

```
homTensorEquiv (homCoactionMap f) (θG.coaction g) = θM.coaction (f g).
```

`linearMap_ext_coaction` proves that, after any algebra homomorphism
`φ : C →ₐ[B] S`, the specialized values `φ_*(θG(g))` determine every
`S`-linear map from `S ⊗[B] G`. No flatness or finite presentation is
needed for this generation assertion. Tensor induction first proves agreement
on `φ_*(R_G(x))` from agreement on the coaction values; involutivity then
gives agreement on `1 ⊗ g`, and linearity gives agreement everywhere.

The counit and coassociativity laws are first checked in flat test algebras.
For the counit, evaluate on the specialized coaction values and use the
two coefficient coactions' counits. For composition, tensor induction proves
that evaluation commutes with simultaneous `coactionCompose` on its two
inputs. Applying this identity to `homCoactionMap f` and `θG(g)`, followed
by the two coefficient coactions' coassociativity laws, proves the Hom
coassociativity law by the generation assertion and injectivity of
`homTensorEquiv`.

`hom` constructs the actual `GroupoidCoaction t (G →ₗ[B] M)`.
Source flatness follows from `hE.etale_algebraMap`. The identity test algebra
`B` is flat, and the published universal composable-point algebra is flat
by `hE.composable_flat`. Thus the preceding flat-test laws apply there.
The published `ofUniversal` constructor specializes these universal laws to
all test algebras, as required by the unchanged coaction definition.
The resulting construction has no additional flatness assumption.

`mem_hom_invariants_iff` identifies invariant linear maps with the
published equivariant-map predicate `θG.IsHom θM f`. The proof applies
the defining evaluation identity in one direction and the generation assertion
in the other. `hom_eval_isHom` proves that evaluation at any invariant
element of `G` is equivariant; on pure tensors, evaluating at `1 ⊗ g`
is scalar extension of ordinary evaluation.

The provenance is internal: these formulas and proofs are derived from
the existing reversal operators, universal-point constructor, and Mathlib
base change. No geometric pushforward, support dévissage, affine-descent
conclusion, or vanishing theorem is assumed or proved by this unit.
