# Finitely supported tensor coordinates

Linear maps from a vector space to a family of coefficient spaces
assemble into a linear map to the dependent direct sum when their
values on each vector have finite support. Mathlib's distributivity
equivalence for tensor products and dependent direct sums then puts the
tensor of these maps in the direct sum indexed by tuples of coordinates.
At each tuple its value is the tensor of the corresponding factor
coordinate maps, as checked on pure tensors. Consequently each tensor
has finite projected support.

If the coordinate maps separate each factor, their direct-sum map
is injective and has a linear left inverse over the field. Tensoring the
left inverses gives a left inverse before the distributivity equivalence.
Thus the tensor coordinate maps also separate. This is an internal
algebraic consequence of Mathlib's dependent direct sums and tensor
products for projecting the cuspidal Levi coefficients.
