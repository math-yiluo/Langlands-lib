# Complements of finite rational-point sets

This internal derived helper constructs the open complement of the
underlying points of a finite set of rational points. It connects
vanishing of an actual scheme module on that open to the published
`HasFiniteClosedSupport` predicate. It does not prove any
cohomology-and-base-change, rational-fibre, acyclicity or Leray theorem.

For a scheme `X`, an open `U` and an actual module `M : X.Modules`,
`stalkSupport_subset_compl_of_isZero_pullback` says that
`IsZero ((Scheme.Modules.pullback U.ι).obj M)` implies
`stalkSupport M ⊆ (U : Set X)ᶜ`. Mathlib's
`restrictFunctorIsoPullback` first identifies pullback with restriction.
The published module stalk criterion makes all restricted abelian
stalks zero. Mathlib's `restrictStalkNatIso` identifies a restricted
stalk at a point of `U` with the original stalk at its image in `X`.
Thus a point of `U` cannot lie in the actual nonzero-stalk support.
No finiteness or geometric premise is used in this lemma.

Now let `K : Type u` be an algebraically closed field,
`g : X ⟶ Spec (CommRingCat.of K)` locally of finite type, and

```text
F : Set (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk g).
```

Each element `x` is an actual rational point with structure equation
`x.w`. Write `c = IsLocalRing.closedPoint K`, the unique point of
`Spec K`. Mathlib's `pointEquivClosedPoint g` identifies `x` with the
closed point whose underlying point is `x.left c`.
`rationalPoint_apply_injective` proves that this evaluation function is
injective, using `ext_of_apply_closedPoint_eq` and extensionality of
over-morphisms.

Given `hF : F.Finite`, `rationalPointComplement g F hF : X.Opens`
has underlying set

```text
((fun x => x.left c) '' F)ᶜ.
```

It is open because the image is the finite union of the closed
singletons of the rational points. `mem_rationalPointComplement_iff`
states exactly that `x.left c` belongs to this open if and only if
`x ∉ F`. Injectivity of evaluation gives this equivalence.

Finally, `hasFiniteClosedSupport_of_isZero_rationalPointComplement`
says that if the actual pullback of any `M : X.Modules` to this open
is zero, then `HasFiniteClosedSupport M`. The first lemma puts its
support in the finite image of `F`; those image points are closed by
`pointEquivClosedPoint`. The proof applies the published
`HasFiniteClosedSupport.of_subset`.

This is an elementary internal composition of the published
[ModuleSupport](ModuleSupport.md) interface and Mathlib's actual
open-restriction stalk and rational-point interfaces, not a
transcription of a new external-source theorem. It includes empty `F`,
empty schemes, all characteristics and arbitrary common universe `u`.
There is no coherence, quasi-coherence, properness, smoothness,
line-bundle or nonempty-support hypothesis. In the second-projection
application, the separate rational-fibre theorem must first establish
that the higher direct images vanish on this open.
