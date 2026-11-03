# Central shifts preserve dynamic subgroup functors

This internal construction works over any base scheme `S`. Let `T` be a
commutative group scheme, let `i : T.toGrp → G` be any group-scheme
homomorphism, and let `ν` and `ζ` be actual cocharacters of `T`. Assume that
the composite of `ζ` with `i` is central on every scheme test.

`Dynamic.orbit_add_of_isCentral` proves equality of the actual conjugation
orbit morphisms for `ν + ζ` and `ν`. Evaluating their sum multiplies the
two cocharacter values. The value of `ζ` commutes with the tested point,
so its contribution to conjugation cancels. The proof applies centrality
on the full product test scheme and therefore includes nonreduced tests.

The same orbit extensions, with the same evaluations at zero, consequently
define the parabolic, centralizer and contracting subgroup functors for
both cocharacters. The three `*_add_of_isCentral` lemmas express these
equalities of subgroup functors.

`Dynamic.centralShiftParabolicIso` constructs the canonical group-scheme
isomorphism between any two representatives of these parabolic functors.
Its forward map followed by the second ambient inclusion is the first
ambient inclusion, as proved by `centralShiftParabolicIso_hom_comp`.
This uses the published uniqueness isomorphism for representatives.

These are direct deductions from the published pointwise additive law
for homomorphisms of commutative group schemes, all-test centrality and
dynamic orbit-extension definitions. No smoothness, field, reductivity,
torus splitness, root-system assertion or root-reflection existence
assertion is assumed or proved.
