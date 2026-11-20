# Equivalences of finite adelic tensor representations

`tensorEquivOver` compares restricted tensors of local representations when the local equivalences carry one reference family to the other outside a finite set. It uses the restricted tensor equivalence on the underlying direct limits and the intertwining property of the component maps for the pullback to the actual finite adelic group.

`tensorEquiv_of_eventually_unit_smul` applies this construction to two choices of reference vectors in the same local representations. At each place where one reference is a nonzero scalar multiple of the other, it chooses that scalar and uses the corresponding scalar multiplication equivalence. The other places may be included in the finite exceptional set for the induced map. This derived construction allows two realizations of a restricted tensor to use different normalizations of the same spherical lines.
