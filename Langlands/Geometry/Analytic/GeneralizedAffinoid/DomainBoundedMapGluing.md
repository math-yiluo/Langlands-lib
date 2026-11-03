# Bounded algebra-map descent on finite full-domain covers

Let `K` be any complete ultrametric normed field, `A` an actual presented
affinoid algebra, `U : Domain K A` a full represented affinoid domain, and
`c : FiniteCover U` an actual finite cover by full represented domains. The
stored target algebra is `U.algebra`; every cover member has its actual stored
algebra and its original bounded restriction map from this target algebra.
This internal construction proves a norm estimate for these original
restrictions and uses it to descend compatible bounded algebra homomorphisms.
It imposes no nontriviality of the valuation, strictness, reducedness,
nonzero-quotient, nonempty-spectrum, or nonempty-cover hypothesis.

## Norm detection and local boundedness

`exists_algebraRestrictionBound` constructs a positive real constant `C` such
that

`‖a‖ ≤ C * ‖c.algebraRestrict a‖`

for every `a : U.algebra`. Take the existing actual relative rational refinement
of `c`, whose charts cover the whole spectrum of the unchanged algebra
`U.algebra`. The unrestricted finite rational inverse estimate applies to these
charts. The refinement gives actual bounded maps from the original covering
algebras to the refined chart algebras. For each such map, choose a positive
bound. Their finite sum plus one bounds every component map, even if the
refinement is empty. The proved `restriction_comp` identity identifies the
composite through the original cover with the rational structural map. The
finite product norm inequality thus bounds the refined restriction family in
terms of the original family. Composing the two inequalities gives `C`.

`algebraRestrictionBound` chooses a constant from this proof;
`algebraRestrictionBound_pos` and `norm_le_algebraRestrictionBound` give its
positivity and bound for the stored algebra and the original restrictions.

For any normed commutative `K`-algebra `S`, `bounded_of_restrictions` proves that
an actual algebra homomorphism `f : S →ₐ[K] U.algebra` is bounded if all its
composites with the original cover restrictions are bounded. Choose positive
bounds for those finitely many composites. Again their sum plus one is a common
positive bound, so it bounds the norm of the restriction family of `f s` by a
constant times `‖s‖`. Apply the inverse restriction estimate to `f s` to get a
positive bound for `f` itself. No completeness, ultrametric, finite-presentation,
or nontriviality hypothesis on `S` is needed beyond the displayed normed
commutative algebra structure.

## Descent of actual bounded maps

Let `f i : BoundedAlgHom K S (c.obj i).algebra` be supplied local maps.
`BoundedMapCompatible` requires agreement after every actual full-domain test:
for all cover indices `i,j`, every full represented domain `W` of the original
ambient `A`, and arrows `p : W → c.obj i` and `q : W → c.obj j`, the actual
bounded maps `p.restriction.comp (f i)` and `q.restriction.comp (f j)` agree.
The arrows retain the existing direction from spaces, so the algebra
restrictions go in the opposite direction. This definition does not presume a
constructed full-domain intersection object.

`algebraCompatible_mapFamily` evaluates these equalities at an arbitrary input
`s : S` to obtain exactly the published scalar full-test compatibility condition.
`mapGlueValue` applies the existing scalar descent to that family.
`restriction_mapGlueValue` proves that its original restriction to member `i`
is exactly `f i s`.

`glueAlgHom` bundles these values into an actual `K`-algebra homomorphism. To
prove preservation of zero, one, addition, multiplication, and original scalar
constants, use separation by the actual cover restrictions. The preceding
restriction identity reduces each equality to the corresponding law of the
supplied local algebra maps. `restriction_comp_glueAlgHom` identifies each
original composite algebra homomorphism with the supplied one.

`glueBoundedAlgHom` equips this homomorphism with the proved boundedness. Apply
`bounded_of_restrictions` and use `restriction_comp_glueAlgHom` to replace each
composite by the supplied bounded local map. No bound on the glued map is assumed
or included as extra input. `restriction_comp_glueBoundedAlgHom` is equality of
the original composite bounded homomorphisms with the supplied local maps.
Finally, `glueBoundedAlgHom_unique` proves that any actual bounded algebra map
having those composites is the constructed map: evaluate at each input and use
scalar separation on the cover.

## Provenance and scope

This is an internal derived construction. It uses the existing full-domain
relative rational refinement, its actual commuting bounded restrictions, and
scalar full-cover algebra gluing, together with the constructed unrestricted
finite rational norm estimate. All estimates use actual quotient norms; all
algebra maps act on quotient elements and therefore retain nilpotents. No new
original-literature assertion or assumed analytic output is introduced.

The delivered descent requires the explicitly stated full-test compatibility of
the local bounded maps. It does not replace that condition by an unconstructed
pairwise full-domain intersection. General full intersections, unrestricted
analytic atlas restrictions, analytic etale and quasi-etale sites, equivariant
sites, distinguished domains, and Harris tower constructions remain outside this
focused unit.
