# Actual open-image descent of generic fibre connectedness constancy

Worker 105. This derived reduction implements the first descent step in the
proof of Stacks Lemma 37.28.4 (055G), registered collection
`stacks-fibre-constructibility-local-dimension-2026-11-04`, SHA256
`1f3421cf5c5733cafdf296e8a9d38af7e4730550989a3d727d4b9a61cf1f3db3`,
retained `055C.html`. Its final theorem explicitly assumes the full finite
étale generic-component splitting and geometric-irreducibility spreading
propositions, together with the field closed-cover criterion. None of these
inputs is proved here.

`GeometricallyConnectedFiberConstantOn f S` says that all actual residue-field
fibres over points in the actual set `S` have the same geometric-connectedness
truth value. It is vacuous for an empty set and requires no generic point,
finiteness, separation or topological hypothesis.

For any actual cartesian scheme square, uniform truth value on a set upstairs
descends to its actual image downstairs. This follows point by point from
the existing preservation and reflection of geometric connectedness under
residue-field extension. Surjectivity and openness are unnecessary for this
set-theoretic comparison.

If the base-change map is open and constancy holds on an open neighbourhood
of any point upstairs, its image is a nonempty open downstairs with constant
truth value. Every whole-space generic point downstairs belongs to this
image. Comparing with that point gives
`GeometricallyConnectedFiberConstancyAt` downstairs. There is no need to
identify the image of the chosen point upstairs with the generic point
downstairs.

The final theorem starts with a locally finite-type quasi-compact morphism
to a Noetherian scheme having a whole-space generic point. The assumed
finite étale splitting proposition supplies an actual irreducible affine
finite étale cover of an actual open restriction with geometrically
irreducible generic components. Its source is Noetherian. The earlier
conditional split-component assembly gives constancy near its generic
point. The actual cartesian square is obtained by pasting the splitting
pullback with the open-restriction square. Étaleness makes the cover map
open, and the open immersion of the restriction is open, so open-image
descent proves Boolean generic constancy for the original morphism.

Schemes have arbitrary common universe `u`. No reducedness, flatness,
properness, smoothness, separatedness or quasi-separatedness hypothesis
is imposed on the original morphism. The Noetherian hypothesis comes from
the earlier closure-incidence assembly and is retained explicitly.
The unrestricted generic-constancy theorem, constructibility and the
assumed splitting, spreading and closed-cover results remain separate
proof obligations.
