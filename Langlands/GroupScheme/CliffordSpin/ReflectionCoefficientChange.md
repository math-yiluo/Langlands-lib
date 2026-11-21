# Reflection matrices under change of coefficients

`reflectionOfUnit` reflects along a vector whose quadratic value is a unit of the coefficient ring. It uses the value-one reflection for the form scaled by the inverse of that unit. The resulting involution preserves the original form, has determinant minus one on a finite free module, and agrees with the usual field reflection.

`reflectionMatrix` writes this involution in the scalar-extended basis. Both the quadratic value and the polar pairing of extended vectors commute with maps of coefficient algebras. The matrix entry formula then gives `map_reflectionMatrix`, which specializes a reflection to the reflection of the specialized vector and value unit.

These are derived coefficient formulas for reflection products of the kind used in Kneser, *Lectures on Galois Cohomology of Classical Groups*, §5.11, p. 99. The ring-valued formulation lets the reflection vector and its value vary along an affine family.
