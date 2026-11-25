# Nilpotent rigidity of diagonalizable actions on arbitrary schemes

This is an internal consequence of the affine scheme-action
rigidity theorem and the invariant-open restriction construction. It asserts
no new external literature input.

Let R be a commutative ring, I a nilpotent ideal, and M any abelian group.
Suppose the diagonalizable group D(M) acts on any scheme X over Spec R.
Assume the action is trivial on all affine test schemes whose R-algebras
annihilate I. Then the action morphism equals the second projection. In
particular, the action on points of every test scheme is trivial.

The preceding local module proves that every open of X is invariant, by
testing the action at residue fields of the product scheme. Restrict the
action to each affine open V. Composing with its open immersion shows that
the restricted action satisfies the same quotient hypothesis, so affine
rigidity makes it trivial. Any test point with image in V is consequently
fixed, by factoring it through V.

For the global morphism equality, pull back an affine open cover of X along
the second projection from D(M) times X. On each member, the second-projection
point lies in the corresponding affine open. The local fixedness equality
therefore equates the action and second projection on that member.
The open-cover morphism extensionality theorem gives equality globally.

The proof works in an arbitrary universe and assumes no affineness,
separatedness, smoothness or finite-presentation condition on X, and no
finite-generation condition on M.
