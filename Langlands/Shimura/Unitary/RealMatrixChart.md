# Actual complex matrix coordinates at a real embedding

`embeddingOverReal` extends the real embedding to a complex embedding
of the CM field. `realCenterEquiv` identifies the real scalar extension
of that field with the complex numbers and carries center conjugation
to complex conjugation. An element with nonreal image together with the
real scalars spans the complex field, so the center map is surjective.
Both sides have real dimension two.

`realMatrixChart` compares the real scalar extension of the full algebra
with its scalar extension to the complex field along the chosen embedding.
The center comparison and the original algebra elements together give
surjectivity on pure tensors. A dimension count gives bijectivity.
The central simple algebra over the complex field has its matrix
splitting of the original degree. The construction retains the actual
map from the completed center, and `realInvolution_center` computes the
action of the involution on that map.
