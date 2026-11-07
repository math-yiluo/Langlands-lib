# The continuous multiplication pairing of a topological ring

This internal construction supports the proof of adelic additive self-duality.
It applies to any topological ring `R`; commutativity, arithmetic, and
nontriviality of the character are not required here. It does not prove
bijectivity of the pairing.

Given a continuous additive character `ψ : AddChar R Circle`, `character ψ hψ a`
is the continuous character `x ↦ ψ (a*x)`. The source is
`Multiplicative R`, which retains the topology of `R` and retags its additive
group as a multiplicative group. Multiplication inside `ψ` is ring
multiplication. The target is the full `PontryaginDual (Multiplicative R)`,
including the trivial character, with its existing compact-open topology.

`hom ψ hψ` bundles this assignment as a continuous group homomorphism.
Distributivity and the additive-character law prove the homomorphism property.
The function `(a,x) ↦ ψ (a*x)` is jointly continuous because ring multiplication
and `ψ` are continuous. Mathlib's compact-open currying theorem
`ContinuousMonoidHom.continuous_of_continuous_uncurry` therefore proves
continuity into the dual.

`equivOfBijective` assumes that this particular homomorphism is bijective and
that `R` is locally compact and sigma compact. The Pontryagin dual of a locally
compact group is locally compact and Hausdorff, hence a Baire space. Mathlib's
`MonoidHom.isOpenMap_of_sigmaCompact` makes the surjective pairing an open map.
Its algebraic inverse is consequently continuous. The resulting group
homeomorphism has the same forward function, so
`equivOfBijective_apply` proves the exact evaluation law by reflexivity.

The provenance is a direct application of Mathlib's multiplication-shift,
compact-open, and open-mapping infrastructure. For actual number-field adeles,
the separate published local-compactness and second-countability results supply
the two topological assumptions. Injectivity, surjectivity, and the diagonal
annihilator must still be proved by the arithmetic duality argument.
