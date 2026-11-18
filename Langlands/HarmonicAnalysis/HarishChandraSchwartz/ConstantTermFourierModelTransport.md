# Transport of the coefficient Fourier transform between Levi models

In the constant-term diagram in VIII.2.1, the last two normalized
constant terms are functions on identified Levi groups. The
coefficient Fourier transform also respects this identification
when the measures and formal degree agree. The two inverse
half-moduli from III.6 multiply the resulting tensor. [Waldspurger,
*La formule de Plancherel pour les groupes p-adiques* (2003),
pp. 272, 314–315, 322](https://doi.org/10.1017/S1474748003000082)

`ConstantTermFourierModelTransportStatement` is the derived
transport identity for the actual coefficient Fourier transform.
It uses a topological group isomorphism preserving the
supplied measures and an equivalence from the pullback
representation to the second inducing representation. The tensor
map is the published `coefficientTensorPullbackEquiv` followed by
`coefficientTensorCongr`.
`coefficientFourierTransform_eq_smul_of_modelTransport` proves the
identity by comparing the actual endomorphisms using the
smooth-dual characterization of the Schwartz action and changing
variables in the scalar integral.
The theorem uses a common degree parameter. Its application to
actual discrete series requires the formal-degree comparison for
the corresponding quotient Haar measures.
