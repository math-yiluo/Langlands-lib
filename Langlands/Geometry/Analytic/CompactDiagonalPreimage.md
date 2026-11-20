# Compact relative pullbacks from analytic-domain diagonals

Let `f : U ⟶ B`, `g : V ⟶ B`, and `b : B ⟶ X` be maps with
`U`, `V`, and `B` compact Hausdorff. Both `b` and `f ≫ b` are
quasi-étale. The construction uses supplied pullbacks of `U` and `V`
over `X` and of `B` with itself over `X`. The diagonal of `B` is
represented by an analytic domain in the self-pullback.

`compactRelativePullbackOfDiagonal` pulls that analytic domain back
along the comparison map from the first square to the second. The
domain base-change theorem gives the square with the diagonal.
For a pair of analytic test arrows agreeing over `B`, the first
pullback gives their unique map over the ambient space. The second
pullback identifies its composite to the self-pullback with the
diagonal of the common arrow to `B`. The domain square then gives
the required relative lift. The same universal properties prove
uniqueness.

The quasi-étale map `b` gives Hausdorffness of the self-pullback.
The diagonal domain is compact through its isomorphism with `B`, so
it is closed and its inverse image is closed. The set of factor
pairs with equal images in `B` is compact and consists of compatible
pairs over `X`. The quasi-étale map `f ≫ b` gives Hausdorffness of
the first pullback and compactness of the inverse image of those
pairs under its projection-pair map. The cut is a closed subspace of
this compact Hausdorff inverse image. The construction retains the
literal analytic domain and both projections.

The categorical diagonal argument is adapted from Worker 611's
compact quasi-étale diagonal construction. The compact-preimage
argument uses Hausdorffness of the three compact spaces and local
Hausdorff patches in the ambient space.
