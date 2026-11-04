# Nonunipotence detected by an ambient semisimple tangent image

These internal adapters work over an arbitrary field and universe. If the
image of an actual tangent element of a unipotent group is semisimple in an
affine locally finite type ambient group, that image is zero. A faithful
finite representation of the ambient group has a nilpotent tangent matrix
on this image, by restricting the representation to the unipotent source.
The ambient semisimplicity assumption makes the same matrix geometrically
semisimple. It therefore vanishes, and faithfulness reflects the vanishing
back to the ambient actual tangent point. In the raw kernel, zero is `1`.
This argument imposes no faithfulness or finiteness hypothesis on the
homomorphism or on its source.

For a nonzero semisimple tangent element, the self-membership theorem places
it in the tangent submodule of its actual all-test centralizer. If a smooth
affine group represents that centralizer, the published tangent image theorem
for smooth affine homomorphisms lifts its canonical centralizer factor to
the representative's identity component: the component inclusion is an open
immersion and hence smooth. The resulting chosen factor maps to the original
element under the composite inclusion. The first adapter then shows that this
connected centralizer cannot be unipotent.

The implementation uses the actual tangent constructions and the nilpotent
tangent matrix result authored by Worker 1377, together with the published
smooth infinitesimal lifting and closed linear embedding results. This is
a derived local step for the no-torus induction. It assumes smoothness of
the centralizer representative and does not prove that smoothness or the
parent no-torus unipotence theorem.
