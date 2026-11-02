# Restricting stacks along an inclusion of Grothendieck topologies

For two Grothendieck topologies `J ≤ K` on the same category and any
Cat-valued contravariant pseudofunctor `F`, `prestack` restricts morphism
descent from `K` to `J`, and `stack` restricts full effective descent from
`K` to `J`. The coefficient categories need not be groupoids.

This is an internal derived API. A `J`-covering sieve is also `K`-covering
by the stated inequality. The two constructions therefore apply Mathlib's
`isPrestackFor'` and `isStackFor'` to each such sieve and use the constructors
`IsPrestack.of_isPrestackFor` and `IsStack.of_isStackFor`. Thus both the
full-faithfulness and the essential-surjectivity requirements remain those of
the existing descent functors; neither is replaced by descent of object
classes.

No geometric stack instance is proved here. For example, using the second
construction with the inclusion of the fppf topology in the fpqc topology
still requires an actual fpqc stack instance.
