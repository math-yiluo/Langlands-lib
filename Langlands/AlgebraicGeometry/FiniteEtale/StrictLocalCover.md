# Finite étale geometric points over a strictly Henselian local ring

Each point of the closed fibre of a finite étale cover over a
strictly Henselian local ring is rational over the residue field.
The proof uses the finite split coordinate algebra over that
separably closed field. The Henselian section theorem lifts the
residue point to a section. The image of each section is open
because a section of an étale morphism is an open immersion.
The complement of their union is closed, and its image in the
base is closed by finiteness. A nonempty closed image would
contain the closed point, whose entire fibre is already covered.

`sectionOfGeometricLift` factors the supplied field-valued lift
through one of those section images. The resulting section
evaluates to the supplied lift. An automorphism of the fibre
functor fixes the unique point of the identity cover. Naturality
along the section then fixes the supplied lift. This proves that
the pointed finite étale fundamental group is trivial.

The construction uses the Library's actual fibre functor and
Henselian section theorem. It supplies triviality of monodromy on
a model over a strictly local base.
