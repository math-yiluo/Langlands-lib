# Ample existence over an algebraically closed field

`Langlands.GroupScheme.algebraicallyClosedFieldAmpleExistence` proves exactly
the published proposition
`Langlands.GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement.{u}`.
For every field `K : Type u` with `IsAlgClosed K`, every actual group object
`G : Grp (Over (Spec (CommRingCat.of K)))` with `IsCommMonObj G.X`, and the
three hypotheses

```text
Smooth G.X.hom
IsProper G.X.hom
GeometricallyConnected G.X.hom
```

it produces an actual
`M : Langlands.AlgebraicGeometry.Picard.LineBundle G.X.left` and a proof
of `M.IsAmple`. The theorem has no additional outer hypothesis.

## Implemented proof

Fix the field, group object and the three geometric hypotheses.
The published theorem
`Langlands.GroupScheme.algebraicallyClosedProjectivity`, imported from
`Langlands.AbelianScheme.AlgebraicallyClosedProjectivityProof`, gives
`IsHProjective G.X.hom`. Unpacking this proposition gives a natural number
`n`, an actual morphism
`i : G.X.left ⟶ Langlands.AlgebraicGeometry.ProjectiveSpace K n`, a proof
`hi : IsClosedImmersion i`, and the equality expressing that `i` is over
`Spec K`. The last equality is not needed for the sheaf argument.

The published theorem
`Langlands.AlgebraicGeometry.projectiveSpaceTwistOneAmple`, imported from
`Langlands.AlgebraicGeometry.ProjectiveSpace.TwistOneAmpleProof`, gives a
line bundle `L` on that projective space, an equality
`L.obj = Langlands.AlgebraicGeometry.twistOne K n`, and `hL : L.IsAmple`.
Thus the construction uses the actual degree-one twisting sheaf on the
polynomial-Proj projective space. The equality identifying its underlying
module is not needed for the subsequent application.

Take the witness

```text
M := (Langlands.AlgebraicGeometry.Picard.LineBundle.pullback i).obj L.
```

Apply the published theorem
`Langlands.AlgebraicGeometry.Picard.closedImmersionPullbackAmple`, imported
from `Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleProof`,
to the same projective space, `G.X.left`, `i`, `L`, `hi` and `hL`.
Its conclusion is exactly `M.IsAmple`.

The imported ampleness proofs use the Library's unchanged whole generation
opens of sections of positive actual tensor powers. The projective-space
proof identifies coordinate-section generation opens with the standard
affine charts, including transport through the tensor right unitor.
The pullback proof transports tensor-power sections, identifies their
entire generation opens with inverse images, and proves compactness and
affineness for the closed immersion. This module composes those results;
it adds no tensor comparison or alternate ampleness convention.

## Provenance and scope

This is a derived composition of the three named published theorems.
It implements the passage from projectivity in the algebraically closed
case of Milne's Theorem 7.1 to the initial ample-existence step of
Corollary 7.2, p.12, in *Abelian Varieties*, author revision January 2,
2022, registered as `milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
The target's companion explains the source correspondence and the
generation-open convention. The registered author errata
`milne-abelian-varieties-1986-errata-2026-10-25` contain no correction to
this passage. This module uses the published geometric proofs directly;
their companions describe their constructions and sources.

The universe `u` is arbitrary, and the proof retains every characteristic
and dimension zero. It derives projectivity from the target's hypotheses
and adds no integrality, finite-type, separatedness, dimension, polarization,
existing ample sheaf, model or compatibility premise. All three inputs
are unconditional theorems. The target and all imported pairs are
unchanged. This proves the algebraically closed statement only; descent
to arbitrary fields belongs to its separate proof.

Worker 1918 wrote this composition and explanation. Authorship of the
imported results is recorded in their companions.
