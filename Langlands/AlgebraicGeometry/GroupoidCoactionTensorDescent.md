# Flat descent in tensor-presentation coordinates

This derived internal construction proves the cocycle comparison needed to
apply flat tensor zero detection to the unchanged published `GroupoidCoaction`.
It introduces no literature statement or geometric quotient theorem.

Let `A → B → C` be commutative algebras in an arbitrary common universe, and
let `M` be a `B`-module in an independent universe with compatible `A`-action.
Suppose `e : C ≃ₐ[B] B ⊗[A] B` sends the target map `t(b)` to `1 ⊗ b`.
The preceding coordinate adapter defines the `A`-linear map
`δ = presentationCoaction θ e ht : M → B ⊗[A] M`.

The ring `T = B ⊗[A] (B ⊗[A] B)` has its usual `B`-algebra structure
through the first factor, here called the third point's coordinate.
`presentationTripleEquiv` is the `A`-linear equivalence
`T ⊗[B] M ≃ B ⊗[A] (B ⊗[A] M)` with formula

`(b₃ ⊗ (b₂ ⊗ b₁)) ⊗ m ↦ b₁ ⊗ (b₂ ⊗ b₃m)`.

Its construction uses tensor symmetry, cancellation of base change, a swap
of the last two ring factors, and tensor associativity. In these coordinates,
three points of the relation are supplied by the following maps from `C`,
specified on `e⁻¹(c ⊗ d)`:

- `presentationFirst`: `1 ⊗ (c ⊗ d)`, with source in the middle factor.
- `presentationSecond`: `c ⊗ (d ⊗ 1)`, with source in the first factor.
- `presentationComposite`: `c ⊗ (1 ⊗ d)`, with source in the first factor.

The first point's source equals the second point's target, and the composite
point has the first point's target. These identities follow directly from
the tensor-presentation formula for `t`. Thus the published cocycle axiom
applies to these actual ring-valued points.

The inverse module coordinate equivalence sends `b ⊗ m` to `t(b) ⊗ m`.
Induction on these tensor coordinates proves that the triple equivalence
transforms the composite point's action into `(B ⊗ η)`, where
`η(m) = 1 ⊗ m`, and transforms `coactionCompose` into `(B ⊗ δ)`.
Applying the triple equivalence to the published cocycle equality therefore
gives

`(B ⊗ δ)(δ(m)) = (B ⊗ η)(δ(m))`.

Finally, assume `RingEtaleEquivalenceRelation t`, `Module.Flat A B`, and
`Nontrivial M`. The preceding coordinate adapter proves injectivity of `δ`
from the relation's identity point and the published counit. The generic
flat tensor zero-detection lemma then supplies a nonzero fixed element of
`δ`. Its fixed-element comparison makes this a nonzero element of the
original invariant subgroup, proving
`exists_nonzero_invariant_of_flat_presentation`.

No acyclicity or module finiteness is used in this conditional theorem.
Producing the flat tensor presentation for an actual finite-orbit relation,
and transporting a coaction to its restricted quotient rings, remain
separate obligations in the Serre criterion proof.
