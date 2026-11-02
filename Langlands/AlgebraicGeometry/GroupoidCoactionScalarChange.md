# Changing a groupoid coaction along a surjective scalar map

This is a derived internal construction for the Serre criterion proof. It uses
the unchanged published `GroupoidCoaction` and its pointwise counit and cocycle.
No new original-literature assertion or affine-descent theorem is assumed.

Let `B`, `S`, `C`, and `D` be commutative rings in an arbitrary universe `u`.
Assume compatible algebras `B → S → D` and `B → C`. Let `M`, in an independent
universe `v`, be an additive commutative group with compatible `B`- and
`S`-module structures. Given a `B`-algebra map `f : C → D`, the additive map
`scalarChangeTensor` sends `c ⊗[B] m` to `f(c) ⊗[S] m`. Tensor balancing follows
from `B`-linearity of `f` and the two scalar towers. The next lemmas prove that
this map respects multiplication by coefficients and tensoring ring-valued
points.

Let `t : B → C` and `τ : S → D` be ring maps satisfying
`τ ∘ (B → S) = f ∘ t`. If `B → S` is surjective, `scalarChange θ f hS hτ`
transports a coaction `θ : GroupoidCoaction t M` to a coaction
`GroupoidCoaction τ M`. Its additive map is `scalarChangeTensor f ∘ θ.coaction`.
Surjectivity is used to prove `S`-semilinearity: lift a scalar to `B`, apply the
original semilinearity law, and use compatibility of the target maps.

For the counit, view an `S`-algebra `T` as a `B`-algebra by composition. A
`D`-valued diagonal point pulls back along `f` to a `C`-valued diagonal point.
Apply the original counit, followed by `T ⊗[B] M → T ⊗[S] M`. Naturality of the
tensor map identifies the result with the required new counit.

For the cocycle, pull back the three given `D`-points along `f`. Compatibility
of the target maps gives the original composability and target equations. The
lemma `scalarChangeTensor_coactionCompose`, proved on pure tensors and then
by additivity, shows that tensor scalar change commutes with the published
`coactionCompose`. Applying it to the original pointwise cocycle proves the new
one. No equivalence-relation hypothesis is needed for this transport itself.

Finally, `scalarChange_mem_invariants_iff` assumes that `scalarChangeTensor f`
is injective and proves that the transported and original invariant equations
are equivalent for each element of `M`. The unit tensor maps to the unit tensor,
so injectivity reflects the invariant equation. Proving this injectivity for
the actual quotient rings `B/I` and `C/(I C)`, and using the restricted coaction
in the Serre criterion, are separate obligations.
