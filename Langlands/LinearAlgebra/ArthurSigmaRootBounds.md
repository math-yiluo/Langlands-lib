# Simple-root bounds on the truncated support of Arthur's sigma function

`ArthurSigmaRootBoundsStatement` gives root-coordinate bounds on the
intersection of Arthur's sigma support and the truncated chamber of the
lower parabolic. It uses a lower bound for the simple roots of the lower
index, nonpositive weight coordinates for that index, and an upper bound
for the active roots in the difference of the indices. Under these
conditions the active roots are positive and the absolute values of all
simple roots are bounded linearly in the two given bounds.

Write the height vector as its projection annihilating the lower simple
roots plus the lower coroot component. The weights of the lower index
are computed using an entrywise nonnegative inverse Cartan block. The
root lower bounds and the weight upper bounds control the absolute value
of each coefficient of the coroot component. Off-diagonal Cartan entries
are nonpositive, so each active root takes a nonnegative value on this
component. Hence positivity of the active roots on the projection gives
positivity on the original vector.

On the projection, the simple roots in the upper index are bounded above
by the supplied active-root bound. The remaining roots are nonpositive
and their full weight coordinates are positive by the characterization
of sigma support. The diagonal entry of the inverse Cartan block then
bounds the negative part of each such root in terms of the positive
upper bound. Adding the coroot component yields the full bound.

This formulation follows from Arthur 1978, Lemma 6.1, and uses the same
inverse Cartan estimates as the proof of the support bound of Arthur
2005, Lemma 8.3(b). The lower coroot component accounts for the truncation
inequalities in Arthur 2005, §13, in the use of that support bound for
(13.7).
