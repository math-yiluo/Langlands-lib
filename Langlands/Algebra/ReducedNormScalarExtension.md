# Scalar extension of reduced norm and reduced characteristic polynomials

`Langlands.CentralSimple.ReducedNormScalarExtensionStatement` identifies the original reduced norm law at an extension field with the reduced norm of the scalar-extended central simple algebra at that field. The module also proves that the reduced characteristic polynomial extends by mapping its coefficients. These are consequences of the determinant definitions in the existing reduced norm and reduced characteristic polynomial modules.

The proof computes both values in a common matrix chart over the algebraic closure of the extension field. The tensor tower equivalence identifies the chart inputs. The field inclusion reflects the determinant equality and the coefficientwise polynomial equality.

A field-valued element is a unit precisely when its reduced norm is nonzero, since the determinant of regular left multiplication is a positive power of the reduced norm. In a splitting chart, a diagonal matrix with one prescribed nonzero entry gives surjectivity of the reduced norm on units.
