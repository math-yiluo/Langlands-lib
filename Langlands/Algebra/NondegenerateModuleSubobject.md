# Actual subobjects of nondegenerate original modules

Worker 6's implementation comparison, extended by Worker 1212 with direct
range-inclusion and factorization laws, for Renard I.6, printed
pp.27–28 / PDF pp.33–34 of the French edition dated 9 July 2026.
The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original passage has been read. This is derived implementation
content, not a separately numbered assertion of the book.

The construction `subobjectOrderIso hA M` identifies categorical subobjects
of the actual nondegenerate module `M` with the stable additive subgroups
for its original stored action. Its intermediate comparison sends the
class of a monomorphism to the class of the same original intertwiner
in the ambient category. The inclusion is full, so factorization order
is unchanged. Conversely, the domain of each ambient subobject arrow is
nondegenerate by the published closure theorem. This gives surjectivity
of the comparison. In Lean, `subobjectToAmbient` is defined on actual
monomorphism classes using `Subobject.lift`. Isomorphic representatives
give the same ambient class by mapping the commuting isomorphism through
the original inclusion. `subobjectToAmbient_le_iff` uses
`Subobject.ofMkLEMk` to witness factorization in either category and
`ObjectProperty.homMk` to lift the same original map back into the full
subcategory. `subobjectToAmbient_surjective` applies the published
subobject closure to the original arrow of an ambient subobject.
The order isomorphism chooses preimages under this surjection; order
reflection proves the inverse law.

The intermediate ambient comparison assumes that the inclusion preserves
monomorphisms. The final `subobjectOrderIso` discharges this using the
published named abelian structure and
`nondegenerateInclusion_preservesHomology hA`; this is not an assumption
on its public interface. It then composes with the published ambient
`NonUnitalModuleCat.subobjectOrderIso`, which uses integer unitization
without changing the original action or carrier.

`mem_subobjectOrderIso_mk` and `coe_subobjectOrderIso_mk` identify the
image of a mono class with the range of its original additive intertwiner.
`mem_subobjectOrderIso` gives the same range formula for the original
arrow of an arbitrary subobject. `submoduleObject M S` bundles the same
stable subgroup `S` and proves its nondegeneracy by subobject closure;
this construction needs no local-unit hypothesis. `subtypeHom M S`
uses exactly `S.subtype` in the full subcategory and is monic by
reflection along its faithful inclusion.
`subtypeHom_hom` records by reflexivity that its ambient intertwiner is
the existing `S.subtype`.
`subobjectOrderIso_mk_subtypeHom` proves that the comparison returns `S`
itself. Consequently `subobjectOrderIso_symm_apply` identifies the inverse
with that actual subtype inclusion. The remaining laws give the recovery
of every subobject and the equivalence of factorization order with
stable-subgroup inclusion. In particular, `subobjectOrderIso_le_iff`
states order preservation and reflection for arbitrary subobjects.
`subobject_mk_le_mk_iff` identifies comparison of two monomorphism classes
with inclusion of the ranges of their original additive maps.
`exists_factor_iff_range_subset` states this as existence of an actual
intertwiner `i` with `i ≫ f₂ = f₁`. Its proof uses
`Subobject.ofMkLEMk` for the factor and the unchanged commuting-map
criterion for the converse.

The coefficient and carrier universes `uA,uM` are independent. The main
comparison assumes an arbitrary nonunital ring with finite local units
(`IsIdempotented A`). Its codomain explicitly uses `M.obj.isAddCommGroup`
and `M.obj.isModule`, the stored original additive group and action. No
unitality law, dimension, finiteness or additional scalar-linearity
condition is imposed. The source's complex-algebra case is a
specialization. Complete unapplied interface examples and the
specializations `(uA,uM)=(0,1)` and `(1,0)` check the universe scope.
Further complete unapplied examples check the range, inverse, recovery,
order and actual-factorization law interfaces at independent `uA,uM`.
This is infrastructure for the source's setwise AB5 and local finite-type
arguments; it does not itself assert either property or filtered-colimit
exactness. The source calls the local finite-type property AB6; its footnote
on printed p.28 distinguishes this from Grothendieck's AB6.
The book does not name this order comparison separately: it
states that all objects are modules and invites setwise proofs. The
comparison supplies the implementation link needed to interpret those
arguments with Mathlib's categorical subobjects. The construction has
compiled privately, including its intrinsic laws and independent
universes; private compilation is not semantic acceptance or publication.
