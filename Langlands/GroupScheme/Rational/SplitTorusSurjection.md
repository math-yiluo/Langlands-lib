# Real cocharacter surjectivity for actual fppf maps of split tori

Author: Worker 1334.

This is an internal deduction from the published actual torus spaces and
perfect pairing in `Geometry.Building.RealTorusDuality`, together with
Mathlib's flat base change and effective epimorphism results.

Over any field `k : Type u`, restriction of integral characters along a
commutative group-scheme morphism whose underlying scheme map is an
epimorphism is injective: equality after restriction cancels that
scheme epimorphism. Real scalar extension preserves this injectivity
because ℝ is flat over ℤ. These two lemmas need no splitness assumptions.

For split source and target tori, the published perfect pairings identify
real characters with the linear duals of real cocharacters. Naturality of
the pairing identifies restriction with the dual of the actual real
cocharacter map. The proved injectivity therefore implies surjectivity of
that map, using the vector-space dual-map criterion. Finally, a flat,
surjective morphism locally of finite presentation is an effective
epimorphism of schemes by Mathlib's fppf subcanonicity theorem, so the
criterion applies to every such map of actual split tori.

`cocharacterQuotientEquivOfFppf` applies the linear first isomorphism theorem
to this proved surjectivity. It constructs the real linear equivalence
`V A / ker(cocharacterMapReal f) ≃ₗ[ℝ] V T`. The accompanying `_mk` lemma
states that it sends the quotient class of `v` to `cocharacterMapReal f v`.
Surjectivity is proved internally, rather than supplied as extra data.

All morphisms, characters, cocharacters and scalar-extended maps are the
existing Library constructions. No finiteness of the kernel, integral
surjectivity, primitive lift, positive rank, or restriction on the field's
characteristic is imposed. This unit establishes the surjectivity ingredient
for the adjoint comparison; it does not identify a root annihilator.
