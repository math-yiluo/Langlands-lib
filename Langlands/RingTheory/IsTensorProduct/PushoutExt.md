# Extensionality for algebra maps out of a pushout

Suppose `S'` is the pushout of `S` and `R'` over `R`, in the sense of Mathlib's `Algebra.IsPushout R S R' S'`. Then two `R'`-algebra maps out of `S'` are equal as soon as they agree on the image of `S` (`Algebra.IsPushout.algHom_ext'`, an extensionality lemma). They agree on the image of `R'` because both are `R'`-linear, and Mathlib's `Algebra.IsPushout.algHom_ext` says that maps of `R`-algebras out of the pushout which agree on both images are equal.

The module also imports the base-change lemmas of [Base-change maps on pure tensors](../TensorProduct/BaseChangeMaps.md).
