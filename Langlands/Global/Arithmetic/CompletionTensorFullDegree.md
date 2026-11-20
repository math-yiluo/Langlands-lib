# Tensor evaluation at a completion of full local degree

Let `B/F` be an extension of number fields and let `w` lie over `v`.
When the local degree `[B_w : F_v]` equals `[B : F]`, the canonical
evaluation `F_v ⊗[F] B → B_w` is an algebra isomorphism over `F_v`.
The module implements it for both finite and infinite places. On a
pure tensor it multiplies the images of the two factors in `B_w`.

The evaluation is the projection of the surjective tensor comparison
to the product of the completions above `v`. The projection is itself
surjective, by using a family supported at `w`. The rank of the
domain over `F_v` is `[B : F]`, so the assumed equality of ranks
makes the surjective linear map bijective.
