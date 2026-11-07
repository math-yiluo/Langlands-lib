# Actual lifts of based root-datum automorphisms

Author: Worker 1472.

This internal construction starts with a supplied `SplitPinning p` on an actual
group scheme over an arbitrary field `k : Type u`. It uses the complete integral
root datum, including the central-torus directions.

`basedRootDatumAut` is the subgroup of `RootPairing.Aut p.rootDatum` consisting
of those automorphisms whose root-index equivalence preserves membership in
the chosen simple-root support in both directions. Identity, composition and
inverse preserve this condition. Root-datum multiplication applies the right
factor followed by the left factor.

`isoOfBasedRootDatumAut` uses the existing chosen pinned lift.
`basedRootDatumAutLift` and `basedRootDatumAutTorusLift` take its actual group
and torus isomorphisms. Their group homomorphism laws follow by applying the
respective projections to the proved identity and composition laws for the
complete chosen lifts. Categorical automorphism multiplication also applies the
right factor followed by the left factor, so these are group homomorphisms with
the stated order.

The inclusion square shows that these two actions intertwine the actual torus
inclusion. Their full forward character and cocharacter maps are respectively
the given weight equivalence and the inverse of the contravariant coweight
equivalence. The root-vector theorem specializes the complete pinned lift's
actual differential equation, using its prescribed root-index equivalence.

`basedRootDatumAutLiftBaseChange` composes the field-group homomorphism with
the automorphism homomorphism of the actual group-scheme base-change functor,
for an arbitrary base scheme and base morphism in universe `u`. Its value is
the actual base change of the lifted automorphism.

The provenance is the imported chosen-lift construction and functoriality,
followed by Mathlib's subgroup and categorical automorphism constructions.
No new external structure theorem is invoked. These constructions retain a
supplied pinning and a fixed field root-datum automorphism group. They do not
identify every automorphism after coefficient extension with such a field
automorphism, construct a section of the full coefficient-algebra automorphism
functor, construct effective Galois descent data, or prove the host's
unconditional quasi-split inner-form existence statement.
