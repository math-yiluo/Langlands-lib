# Descent for the prescribed cuspidally induced finite and infinite constituents

`Langlands.Global.CuspidalInducedFiniteTensor.HasTensorRealization` fixes the
finite target of the given restricted tensor diagram and the actual real and
complex quotients of the supplied standard modules. It asks for a free
operator action on their tensor with the specified place actions and an
equivariant surjection from a stable subspace of genuine automorphic functions.

`exists_placeEmbeddings_of_tensorRealization` proves irreducibility using the
finite translation density theorem and density for the specified standard
quotients. It descends the tensor to a single automorphic quotient. The
conclusion embeds the grouped finite factor for the finite adelic action and
each real and complex factor for its prescribed compact and Lie actions.
`CuspidalInducedFiniteTensor.localEmbeddings` restricts the finite tensor
embedding to the individual finite places.

The proof formalizes the tensor and quotient steps of Langlands (1979), Lemma
1 and Proposition 2, printed pp. 203–206 (Corvallis I PDF pp. 198–201). The
prescribed local models are the data appearing in Getz–Hahn (2024), Theorem
10.7.5, printed p. 288 (PDF p. 300). The equivariant surjection in
`HasTensorRealization` is the input to this descent.
