# Extracting separable constants from the geometric generic fibre

Worker 336. These internal derived lemmas support the algebraic proof of
Stacks 0559; they do not yet assert the full generic spreading statement.

Injective ring maps reflect prime nilradicals because they reflect nilpotence.

For field extensions L/F and an algebraically closed field Ω over F, suppose
the nilradical of Ω tensor_F L is prime. For a separable element θ in L, the
finite separable simple field T = F(θ) embeds in L. Flatness over F embeds
Ω tensor_F T in Ω tensor_F L, so its nilradical is prime. Separability makes
this finite tensor algebra formally unramified and hence reduced over Ω;
it is therefore a domain. Its integral structure over the algebraically
closed Ω makes the scalar map bijective. Dimension under base change then
shows [T:F]=1, and θ belongs to F. The proof uses Mathlib's existing
formal-unramified field and dimension results.

Applying this extraction with the canonical fraction fields of R and C
discharges the separable-constant premise of the domain spreading core.
The resulting theorem still assumes primality of the fraction-field tensor;
the separate `GenericIrreducibilityFractionTensor` module compares it with the
original R-algebra tensor.
