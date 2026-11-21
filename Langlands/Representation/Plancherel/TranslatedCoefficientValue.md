# Evaluation of the actual translated coefficient section

Waldspurger’s V.3 formula (1) uses simultaneous left translation on the
induced vector and the induced smooth dual before applying the standard
operators. The original is `waldspurger-2003-plancherel`, printed p. 295,
PDF p. 61. The fixed coefficient values also use the compact pictures
of IV.1, printed pp. 276–277, PDF pp. 42–43.

`conjugateValue` sends a product coefficient value to the product on the
conjugate inducing object. It keeps its vector and takes the canonical
conjugate smooth dual with the same underlying functional. It works on
the actual tensor of the inducing carrier and its actual smooth dual.

`translatedProduct_eval` evaluates the composite of the published
Levi-normalized coefficient left translation and a displayed inducing
equivalence. The original section is evaluated at `(g, g)⁻¹ * x`. Its
value is then carried by `conjugateValue` and the published product-Levi
equivalence. The proof compares two linear maps after the surjective
product induction tensor equivalence and checks them on pure tensors.

`untwist_conjugateValue` compares the two routes from twisted source
tensor values to untwisted target values. It assumes the displayed
inducing equivalence of the conjugate twists acts as the identity on
the vector carrier. Under that premise both routes retain the vector
and have the same evaluations as linear functionals on the smooth
dual. This is the value computation for reindexing a compact product
section under conjugation.
