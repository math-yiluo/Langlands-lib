# Joint admissibility of the cuspidal induction tensor

`sourceTensor_isJointlyAdmissible` proves joint admissibility for the
finite translations and the full archimedean compact action on the tensor
of the normalized local inductions in the original cuspidal block order.
It uses the finite reference vectors of the chosen tensor subquotient.
The statement keeps both the number-field and the spectral-presentation
universes.

`sourceTensor_isAdmissible` gives finite adelic admissibility. Each real
standard module is a subspace of its scalar principal series. Each
complex standard module is its scalar principal series. At either place,
the translate of evaluation at the identity by a compact element is
point evaluation at that element. A principal-series function is
determined by these values by the diagonal, upper-unipotent and compact
factorization. Thus the hypotheses of `tensor_isJointlyAdmissible` hold
for the same source and prescribed quotient as in
`CuspidalIsobaricInducedTensor.lean`.

This specializes the internal compact evaluation argument to the
inducing representations in Langlands, *On the notion of an automorphic
representation* (1979), Lemma 7, printed pp. 205–206 (Corvallis Part I
PDF pp. 200–201). The algebraic restricted tensor model is that of Flath,
*Decomposition of representations into tensor products* (1979), §2,
Example 2 and §3, printed pp. 181–182 (Corvallis Part I PDF pp. 177–178).
