# Stabilizer-field embeddings and actual factor indices

This internal construction by Worker 166 identifies embeddings of the exact
selected-factor stabilizer field with the actual product-factor indices.
Its input is an actual smooth affine almost-simple product presentation after
a Galois field extension `L/k`. The original group's structure map is
quasi-compact, quasi-separated and locally of finite presentation. The full
bijection additionally assumes that the original group is affine and
almost-simple.

Restricting an upper-field automorphism gives an embedding of the stabilizer
field. Two automorphisms give the same factor index exactly when their quotient
fixes that field pointwise: the actual factor action laws and the previously
proved exact fixer equality establish this criterion.

Every stabilizer-field embedding extends to an automorphism of the normal
upper field, by the field embedding extension theorem. The index selected by
an extension is independent of the choice, by the preceding criterion. This
constructs `factorIndexOfEmbedding` and proves it injective. Transitivity of
the canonical actual factor action for an almost-simple original group gives
surjectivity and the equivalence `factorEmbeddingEquiv`. Its restriction
formula retains the original canonical Galois action on actual factors. The
original field inclusion selects the original factor, and composing an
embedding with any upper-field automorphism agrees with that actual factor
action, so the full equivalence is Galois equivariant.

This correspondence constructs no Weil restriction or product comparison. It
introduces no finite-degree hypothesis on `L/k`, no perfectness assumption and
no additional structural classification premise.
