# Compact probability and actual formal degree on induced tensors

This is a derived construction implementing the Hermitian tensor formula in
Waldspurger, *La formule de Plancherel pour les groupes p-adiques* (2003),
V.2, printed p.293 (PDF p.59). That passage equips the two actual normalized
inductions of a discrete-series representation and its smooth dual with
invariant Hermitian forms, then multiplies their tensor product by the inverse
formal degree of III.1(3). Its independence assertion concerns the tensor
product; the individual forms scale reciprocally.

The construction uses the existing `NormalizedInductionDualTensor` and its
external `G × G` action. Both factors use exactly
`CompactInduction.invariantPositiveForm`, with its existing intrinsic compact
Haar probability on the supplied compact open subgroup `K`. The earlier
`invariantPositiveForm_inner_normalizedHaar` identifies this probability with
spherical Haar. No equality of this measure with an arbitrarily chosen
Bruhat-density measure is asserted.

## Hypotheses and objects

The group is locally compact, second countable and nonarchimedean, with its
Borel measurable structure. The actual closed subgroups `P`, `M`, `U` have a
semidirect decomposition, `P` is locally compact, and `G = P K` is supplied
for the compact open subgroup `K`. Ambient unimodularity and equality of the
full parabolic modular character with the intrinsic modulus on `U` are
explicit hypotheses.

The inducing object `A` is a canonical `SmoothRep` of `M`. The tensor form
uses admissibility and compact-open cofinality on `M` to construct the actual
smooth-dual form. Its independence from every positive inducing form
additionally uses irreducibility of `A`. There is no irreducibility assumption
on either induced representation.

For formal-degree normalization, `C` is a normal central subgroup of `M`;
the fixed Borel quotient measure `μ` is Haar and invariant under inversion.
The representation of `A` is square integrable modulo `C` and irreducible.
The normalizing degree is the existing proved positive
`representationFormalDegree C hC μ hcof hsq hi`, not an additional scalar
parameter.

## Declarations and implemented proofs

`tensorForm` tensors the two actual compact-induced positive forms, using
the actual smooth-dual form in the second factor. `tensorForm_inner_tmul`
computes their product on pure tensors.

`tensorForm_rescale` uses the proved inverse scaling of the smooth-dual
form and the exact compact integral scaling in both factors. The tensor
rescaling theorem cancels the two reciprocal scalars on the entire tensor.
`tensorForm_independent` applies the proved uniqueness, up to positive scalar,
of arbitrary invariant positive forms on the irreducible admissible inducing
representation.

`formalDegreeTensorForm` chooses an inducing form from the proved
unitarizability consequence of square integrability and rescales the tensor
by the actual inverse formal degree. `formalDegreeTensorForm_eq` removes
dependence on this choice by computing the result with every positive
inducing form. `formalDegreeTensorForm_inner_tmul` proves the source's
inverse-degree product formula with the same fixed compact probability in
both induced factors.

The comparison with the smooth dual of the first induced representation,
representative independence, spectral families, wave packets and the
Plancherel theorem remain separate obligations.
