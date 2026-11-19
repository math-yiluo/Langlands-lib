# The cyclic Hasse norm theorem for principal ideles

For a cyclic Galois extension of number fields \(E/F\), suppose that the
principal idele attached to \(a\in F^\times\) equals the idele norm of
\(b\in J_E\). Then \(a\) is the field norm of some \(x\in E^\times\).

`Langlands.ClassField.Global.CyclicHasseNormStatement` uses the Library's
idele norm `ideleNorm`, the principal embedding `IdeleGroup.unitEmbedding`,
and the field-unit norm `Units.map (Algebra.norm F)`. The fields share an
arbitrary universe. The extension is finite because both fields are number
fields.

This is the principal-idele formulation of the norm implication in J. S.
Milne, *Class Field Theory*, version 4.03 (2020), Chapter VIII, Theorem 3.1
and its proof, printed p. 234 (PDF p. 243). The proof there gives injectivity
from the field-unit norm quotient into the idele norm quotient by cyclic
periodicity and the sequence of principal ideles. The Lean statement
expresses this injectivity on a field unit whose principal idele has a given
idele norm preimage.

Registered source `milne-2020-class-field-theory`, SHA-256
`50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5`.
