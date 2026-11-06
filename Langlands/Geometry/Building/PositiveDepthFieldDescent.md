# Descent of generated actual positive-depth root subgroups

This internal construction retains the actual field extension, split torus
inclusion, rational point map, and literal restricted root-function family.
It assumes the original smooth affine group, a monomorphic torus inclusion,
and local opposite factor pairs for the original split torus.

`rootDepthGeneratedSubgroup` is the algebraic subgroup closure of the union
of the original selected filtrations at their original real depths. It is
defined for an arbitrary root-function family without valuation axioms.

The field-descent theorem assumes a valuation only upstairs. Its selected
root set and depth function obey the displayed closed-positive condition,
the doubled-root absorption bound, and explicit coverage by the pullbacks
of a complete injective list of indivisible positive roots or their doubles.
The downstairs selected set is the exact preimage under character pullback,
and its depths are composition with that same map.

The proof first reflects membership in each retained ray factor. In the
doubled-root-only branch it reflects membership in the actual doubled-root
group, retaining its original bound. In the unused branch injectivity of
the actual rational extension reflects equality to the identity. Collection
upstairs yields an ordered ray factorization. Effective-epimorphism ordered
factor descent returns the original primitive-root factors, and the retained
ray conditions then descend literally. Each such factor belongs to the
downstairs generated subgroup. Preservation follows on its original
generators by the subgroup closure universal property.

The internal provenance is composition of the preceding actual positive-depth
ray compression, ordered root-factor descent, and single-root field-membership
reflection, together with the algebraic subgroup closure universal property.
No downstairs valuation or commutator axiom is assumed to reflect membership
in the generated subgroup.

The positive-cone depth and coverage hypotheses remain explicit. This unit
does not yet establish V3 of the restricted family, construct a valuation or
an apartment, or prove the supplied-model building comparison.
