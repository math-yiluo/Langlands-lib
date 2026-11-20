# The center of a tensor product of algebras

This internal comparison identifies the associative center of the tensor
product of two algebras over a field with the tensor product of their
centers. It supplies a binary product step for the enveloping center
comparison in Harish-Chandra, *Automorphic forms on semisimple Lie groups*
(1968), Chapter I, §6, printed pp. 19–20 (PDF pp. 29–30).

The tensor of the center inclusions is injective because modules over
the field are flat. Its image is central by multiplying pure tensors
and extending by additivity. For surjectivity, first centralize the
left tensor factor. Mathlib's centralizer description places the
element in the tensor of the left center and the full right factor.
Injectivity transports commutation with the right factor into that
tensor product. The right centralizer description then identifies
the preimage as a tensor of the two centers.

Applying this equivalence to the enveloping algebra of a product Lie
algebra identifies its center with the tensor product of the two
enveloping centers.

[The tensor of the center inclusions](TensorProductCenterMap.md) constructs the equivalence directly from the two inclusions.
