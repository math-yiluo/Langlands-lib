# Actual products of nondegenerate original modules

Worker 6 constructs the product described in the proof of Renard I.6,
printed p.27 / PDF p.33 of the French edition dated 9 July 2026.
The governing registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original I.6 passage on PDF33–34 was read. Its proof says to take the
nondegenerate part of the ambient product because that ambient product
need not be nondegenerate. This module constructs precisely that object,
its maps and its categorical universal property.

The source works with complex idempotented algebras. This construction uses
only a nonunital ring with finite local units, the specified additive module
actions, and nondegeneracy. It therefore retains those more general original
actions. It assumes neither a unital action nor a field, finite dimension,
finite generation, nontriviality, or finiteness or nonemptiness of the family.

For `A : Type uA`, `I : Type uI` and
`P : I → NondegenerateModuleCat.{uA, max uI uM} A`, `ambient P` is
the actual function module `∀ i, (P i).obj`. Its action is the published
`NonUnitalModule.pi`, so multiplication is coordinatewise with each original
action. The published bundled ambient product interface was restricted to
`I : Type`; the unbundled coordinate action already allows an independent
index universe. This construction uses that action directly without changing
the existing interface.

`object P hA` applies the published `nondegeneratePartFunctor hA` to
`ambient P`. Its carrier consists of actual tuples fixed by a single
idempotent of `A`. The original subtype action and additive group are
inherited from the ambient function module. `mem_part_iff` states the exact
condition: some `e : Idempotent A` fixes every coordinate of the tuple
simultaneously. The object is nondegenerate by the published intrinsic proof
for the actual part. The construction never assumes that the entire
function module is nondegenerate.

`projection P hA i` is the original additive intertwiner that evaluates
the tuple at `i`. For original maps `f i : N ⟶ P i`, `lift P hA f`
first assembles the original map `n ↦ (fun i => f i n)` into `ambient P`,
then applies the published `NonUnitalModuleHom.factorNondegeneratePart`.
An idempotent fixing `n` fixes every `f i n` by equivariance, which proves
membership in the actual part. There is no extra common-idempotent
hypothesis on `f`. The evaluation laws `projection_apply` and `lift_apply`
state these formulas on the original carriers.

`lift_projection` proves the factorization equations. `hom_ext` proves
uniqueness by the existing original-map extensionality, subtype
extensionality and function extensionality. `lift_eta` recovers an original
map from its coordinates. `fan P hA` is the actual Mathlib `Fan P` with the
constructed vertex and projections; `fanIsLimit` builds its `IsLimit` using
the displayed lift and uniqueness. `hasProduct` packages this cone as
`HasProduct P`. These laws are the intrinsic verification of the displayed
construction.

The ring, index and residual module universes `uA,uI,uM` are independent.
The carrier universe of the category is explicitly `max uI uM`; this
ensures that the actual function carrier and its subtype live in that same
category. No comparison between `uA` and the carrier universe is required.
Taking `uI = uM` covers all families indexed in the carrier universe.
Complete unapplied interfaces check the universal property and existence
with these independent bounds, including a larger index universe than the
ring universe and a larger ring universe than the carrier universe.

This is a focused construction unit. It supplies no global limit instance,
general small-limit or colimit construction, AB5 proof, local finite-type
proof (the source's AB6), or filtered-colimit exactness proof. Those remaining
assertions of I.6 require separate statements and proofs.

The previously read supplementary 2010-edition corrections, registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
do not replace the governing 2026 passage. The construction uses the actual
published original modules and part functor and does not rely on the
unrestricted abelian-subcategory criterion discussed in
`notes/renard/appendix-a-corrections.md`.
