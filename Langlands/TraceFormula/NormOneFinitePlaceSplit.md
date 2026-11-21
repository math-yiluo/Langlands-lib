# Splitting off a finite place in the norm-one group

`normOneFinitePlaceSplit` proves `NormOneFinitePlaceSplitStatement`.
For an affine group over a number field with a central split torus
satisfying the Library's character restriction hypotheses, its
norm-one adelic group is the topological direct product of the
local point group at a finite place and the kernel of projection
to that place. The first coordinate is exactly the finite-place
projection. An algebraic automorphism fixing the positive torus
acts on this product by its local action and its action on the
kernel.

The proof first glues an adelic point with the given component at
the chosen place and identity components elsewhere. For each
regular function, the evaluations at all other places are constant.
Outside a finite set they are integral, since they agree with
evaluation at the adelic identity. This supplies continuity into
the finite restricted product and hence into the adelic point
group.

Removing the positive torus factor gives a continuous group
section of the same finite projection on the norm-one group.
The section commutes with the kernel, since the inserted adelic
point commutes with it at every place and the removed factor is
central. Multiplying the section by a kernel point gives the
product homeomorphism. Naturality of insertion and preservation of
the positive factor prove twist compatibility.

This internal construction uses the split-centre and norm-one
convention of Getz–Hahn, §2.6. It supplies the group
decomposition used to separate a distinguished finite orbital
integral in the global comparison.
