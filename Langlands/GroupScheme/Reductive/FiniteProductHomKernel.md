# Finite product homomorphisms with monic factor restrictions

Worker 632.

Internal lemmas for actual component product assembly in the proof of Conrad's
Proposition 6.4.4 and Remark 6.4.5. Let `f : pi H ⟶ G` be a homomorphism from a
finite categorical product. If each restriction to a factor is monic on all
relative test points, then the full scheme kernel of `f` is central. Conjugation
of a one-coordinate point by a kernel point remains in that coordinate; after
applying `f` it fixes the point, and factorwise monicity gives commutation.

A flat surjective group-scheme homomorphism sends the full centre into the full
centre: lift an arbitrary target point over the pullback of the map and cancel
the resulting flat surjective map of test schemes. Applying this to central
points in a single factor shows that a factorwise monic flat surjection onto a
group with trivial full centre has source product with trivial full centre.
These assertions hold over arbitrary bases, including nonreduced bases.

Over a field, if the factors are semisimple, the target is connected reductive
and `f` is surjective on the underlying scheme, its central kernel is finite,
because the actual source has finite full centre. The map is flat by the
field-group flatness theorem, and finite by fpqc descent from its finite kernel;
it is therefore a central isogeny. The file constructs `piHomIso_of_isSimplyConnected` and
`piHomIso_of_isAdjoint` when the target is simply connected or adjoint. Their
forward homomorphism is exactly the original supplied `f`. The product can be empty.
All centres and kernels are full scheme-theoretic objects; no rational-point
or reduced-subgroup replacement is used.
