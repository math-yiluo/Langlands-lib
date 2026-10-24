# Affine evaluation of transported cocharacters

This module is an internal derivation from `CocharacterTransport`, the
multiplicative group's affine-unit equivalence, and `AffinePointAutomorphisms`.
It introduces no source convention or additional descent assumption.

## Evaluation and the comparison formula

Let R and S be commutative rings, with S an R-algebra, and let G be a
group scheme over Spec R. Write b:Spec S→Spec R for the scalar map.
For an actual cocharacter χ:Gm_S→b*G and u∈S×,
`G.affineCocharacterValue χ u` is the actual S-valued point of G over
Spec R obtained by evaluating χ on the point corresponding to u, then
using `baseChangeBasePointsEquiv b G`. The theorem
`affineCocharacterValue_left` identifies its underlying scheme map with
evaluation followed by projection from the pullback.

For an R-algebra automorphism s of S, `affineCocharacterValue_transport`
proves

\[
 \operatorname{value}(T_{\operatorname{Spec}(s)}\chi,u)
   = s_*\operatorname{value}(\chi,s^{-1}(u)).
\]

Here s acts on units by `Units.map s.symm.toMonoidHom` on the argument,
and s_* on the output is exactly the previously defined
`G.affinePointAut s`: precomposition by Spec(s) on actual affine points.
The theorem takes the equality Spec(s)≫b=b as an explicit proof argument,
matching the generic transport interface. For an R-algebra automorphism
this equality follows from scalar compatibility; the module does not
assume a separate descent isomorphism.

## Implemented proof

The proof separates affine units from the group-scheme projection.
`Gm.affinePointsEquiv_naturality_of_left` establishes unit naturality for
any morphism between affine test schemes whose underlying map is the
specified spectrum map. It uses naturality of global units and of
`Scheme.ΓSpecIso`. `affinePointsEquiv_change_structure` shows that the
same global unit has the same affine coordinate when the structural map
changes. `affinePointsEquiv_symm_aut` combines these results with a ring
endomorphism s and a multiplicative map t satisfying s(t(x))=x. It proves
that precomposition along Spec(s) sends the point of t(u) to the point
of u on the changed test scheme.

`Gm.baseEndMap` constructs that morphism from the changed base test
scheme to the original base test scheme. `baseEndMap_points` identifies
its composite with the point of t(u) as the point of the unchanged global
unit used by generic transport.

`transportCocharacter_points_left` projects the established
all-test-scheme transport formula to underlying scheme maps. Its
`transportCocharacter_base_points_left` specialization records the formula
for two base points related by precomposition. The theorem
`affineCocharacterValue_transport_left` instead combines the explicit
projection formula for affine evaluation with `baseEndMap_points`, then
uses associativity of scheme morphisms. This version permits a ring
endomorphism with a specified multiplicative right inverse and the proof
that its spectrum map lies over Spec R.

Finally, specialize t to the inverse of the R-algebra automorphism s.
`affinePointAut_left` identifies the existing affine-point action with
precomposition by Spec(s). Extensionality of morphisms over Spec R gives
the displayed equality of actual points.

The result applies to arbitrary commutative coefficient algebras, not
only fields. It compares evaluation of the already constructed scheme
transport with the affine-point action; it does not derive equality of
scheme morphisms from field-valued points, compute matrix factors, or
identify a reflex stabilizer.
