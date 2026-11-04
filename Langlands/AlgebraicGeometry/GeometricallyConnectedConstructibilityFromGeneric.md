# Noetherian generic constancy and actual-fibre constructibility

Worker 105. This internal reduction connects generic fibre geometry to the
existing general geometric-connectedness constructibility target. It
explicitly retains generic constancy as a premise, then derives that
premise conditionally from the full generic-component splitting and
geometric-irreducibility spreading propositions and the field closed-cover
criterion. It does not prove those three inputs.

The source is registered collection
`stacks-fibre-constructibility-local-dimension-2026-11-04`, SHA256
`1f3421cf5c5733cafdf296e8a9d38af7e4730550989a3d727d4b9a61cf1f3db3`,
retained `055C.html`, Lemmas 37.28.5 (055H) and 37.28.6 (055I). The former
reduces to the reduced induced scheme on an irreducible closed subset;
the latter uses generic constancy over a Noetherian base and Noetherian
approximation. This development treats only the truth value of geometric
connectedness, the geometric-component-count-one case, and does not
construct the general component-count function.

`NoetherianGeometricallyConnectedFiberGenericConstancy` quantifies actual
locally finite-type, quasi-compact morphisms to arbitrary Noetherian
schemes. At every whole-space generic point it requires the existing
`GeometricallyConnectedFiberConstancyAt` property: the actual residue-field
fibre is geometrically connected throughout an open neighbourhood exactly
when it is so at the specified point. The definition is a premise to
discharge, not a new axiom or an unconditional theorem.

For each irreducible closed subset `Z` of a Noetherian target, the proof uses
the actual scheme of its vanishing-ideal sheaf and its actual closed
immersion. Its underlying space is the subtype `Z`, its range is exactly
`Z`, and it is Noetherian and irreducible. Its generic point exists because
scheme spaces are sober. Apply the stated generic-constancy premise to the
actual pullback of the original morphism along this immersion. Actual
cartesian fibre invariance descends the constant truth value to the image
of the resulting open subset. Since the immersion induces the subspace
topology, this image is `Z ∩ V` for an ambient open `V`. It is nonempty.
The common truth value makes this intersection either lie in the original
geometric-connectedness fibre locus or be disjoint from it.

The already proved induction on Noetherian closed subsets now yields
constructibility for every finite-type morphism to a Noetherian scheme.
The existing proved Noetherian affine approximation comparison then gives
`GeometricallyConnectedFiberLocalConstructibility` for arbitrary
locally finite-presentation, quasi-compact, quasi-separated morphisms.
In particular the final families need not have Noetherian targets.

The final reduction obtains the Noetherian generic-constancy premise from
the previous open-image descent theorem, which explicitly assumes the full
finite étale splitting proposition, the full geometric-irreducibility
spreading proposition and the field closed-cover criterion. Thus the
conclusion is the exact general local-constructibility target, conditional
on those three inputs. Neither unrestricted finite-type generic constancy
nor unconditional constructibility is claimed.

All schemes use an arbitrary common universe `u`. The Noetherian stage has
no reducedness, flatness, properness, smoothness, separatedness or
quasi-separatedness premise on the original morphism. Quasi-separatedness
is retained at the final finite-presentation approximation stage, together
with local finite presentation and quasi-compactness.
