# A common finite level and matrix Casimir polynomial for Levi slices

At a fixed translated-period vector, one open subgroup of the ambient finite group fixes the vector. Its inverse image under the block inclusion fixes every slice in that block, since finite block operators intertwine the slice maps. The predicate `IsCommonBlockSliceLevel` records the resulting single level for all the other Levi arguments.

A single original realized form supplies all the slices of the vector. Their common enveloping-centre annihilator has finite codimension. An element of this centre therefore satisfies a monic polynomial in the quotient by the annihilator. The same polynomial, evaluated in that central operator, kills all the slices. For a Hecke determinant twist apply this argument to the shifted matrix Casimir and transport the polynomial identity across the actual determinant multiplier.

This supplies uniform bounds for the coefficient construction in the proof of `CuspidalSupportExistenceStatement`, using the block periods of Langlands, *On the notion of an automorphic representation* (1979), Lemma 4 and the subsequent cuspidal support argument, printed pp. 204–205.
