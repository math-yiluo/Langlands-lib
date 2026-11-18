# Actual standard constant terms of coefficient tensors via the same Jacquet module

This derived module identifies the published chosen `standardConstantTerm` of
every coefficient tensor of an admissible actual rational-point representation
with the explicit tensor coefficient built from any stable Casselman pairing for
the specified standard parabolic. All summands use the same actual normalized
coinvariant action, rather than an unspecified admissible representation.
The field and representation carrier universes remain independent.

`StablePairingData.coefficientTensorConstantTerm` extends the published
`coefficientConstantTerm` linearly from pure tensors. The normalization is the
specified positive radical modulus, with inverse square root in the Jacquet
action. Its value on `v ⊗ ℓ` is precisely the published constant-term coefficient
`m ↦ b([ℓ], J(m)[v])`.

For the actual standard Casselman data and an admissible smooth representation,
the published asymptotic theorem supplies the constant-term property on every
pure tensor. Admissibility of the normalized Jacquet action and the published
coefficient-space theorem make this coefficient right finite under the specified
component. Tensor induction extends both properties to every coefficient tensor,
using their addition laws. Actual right-finite constant-term uniqueness then
identifies this explicit tensor map with `standardConstantTerm`.

The source context is Waldspurger, *La formule de Plancherel pour les groupes
p-adiques, d'après Harish-Chandra* (2003), source `waldspurger-2003-plancherel`,
Proposition I.6.2, printed p.249, and its use for induced coefficient families in
VI.2.1–VI.2.3, printed pp.297–300. The proof composes the published actual
standard asymptotics, normalized Jacquet admissibility, coefficient-space right
finiteness, and constant-term uniqueness. No extra coefficient bound or
constant-term realization is assumed. Uniform choice of a fixed level and
uniform spectral estimates for the actual orbit remain separate obligations.
