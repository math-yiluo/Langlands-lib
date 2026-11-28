# Regular families of induced twisted traces in unramified parameters

Fix a nonarchimedean local field `E`, an automorphism `σ` of `E` over `F`,
and a block shape `C` of `N`. The blocks of `C` are grouped into `r`
parameter slots by a map `g : Fin C.length → Fin r`. The module builds the
family of induced twisted traces obtained by twisting a fixed σ-stable
block datum by unramified characters. It then proves that the family is
regular in the parameters and rigid on the unitary torus.

`twistedDistribution_inducedSigma_congr`: equal inducing representations
with σ-intertwiners of the same underlying map give the same induced
twisted trace.

## Characters

- `piProductCharacter χ` is the character `m ↦ ∏ i, χ i (m i)` of a
  finite product of groups. `twist_external_piProductCharacter` says that
  twisting `FiniteTensor.external ρ` by it twists each factor.
- `determinantUnramified E m z` is the unramified character
  `g ↦ z ^ ord(det g)` of `GL_m(E)`. The module proves that it is
  unramified, has open kernel, has unit norm for `‖z‖ = 1`, and is
  multiplicative in `z`. It is invariant under `entrywiseAut σ m`, because
  `determinantOrderHom` is (`determinantOrderHom_entrywiseAut`, from the
  invariance of the normalized absolute value of the determinant).
- `leviUnramified E C g z` is the Levi character
  `m ↦ ∏ j, z (g j) ^ ord(det m_j)`. Its value is the Laurent monomial
  `∏ k, z k ^ leviUnramifiedExponent E C g m k`
  (`leviUnramified_eq_prod_exponent`), and it is invariant under
  `leviAut σ C`.
- `leviHalfModulus_leviAut`: the half modulus of the standard block Levi
  is σ-invariant.

## The family

For block representations `R j` with σ-intertwiners `A j` and a σ-invariant
Levi character `κ` with open kernel (the half modulus in the normalized
case), `familyInducing C R κ` is `twist κ (C.blockTensor R)`. The operator
`familyInducingIntertwiner` is the tensor product of the block
intertwiners. `unramifiedFamilyTrace σ C g R A κ _ _ μ hR z` is the twisted
trace, for a left-invariant measure `μ` finite on compact sets, of the
unnormalized smooth induction from the standard parabolic of
`twist (leviUnramified E C g z) (familyInducing C R κ)`. The operator is the
induced σ-intertwiner `TwistedPaleyWiener.inducedSigmaIntertwiner`.
`twist_familyInducing` and `nonempty_familyInduced_equiv` identify the
induced representation with the induction of `κ` times the tensor of the
twisted blocks `twist (determinantUnramified E (C.size j) (z (g j))) (R j)`.
The inducing representation of admissible blocks is admissible
(`isAdmissible_familyInducing`), and irreducible when the blocks are also
irreducible (`isIrreducible_familyInducing`). Admissibility of the
induced representation (`isAdmissible_familyInduced`) uses compactness
of the parabolic quotient and admissibility of inflation.

## Regularity and comparison

- `unramifiedFamilyTrace_regular`: if `0 < d`, `σ ^ d = 1` and the blocks
  are irreducible and admissible, every test function evaluates the family
  to a Laurent polynomial in `z`. The block intertwiners are arbitrary
  here. The proof applies `sigmaInducedTraceRegularity` to the fixed
  inducing representation. That lemma gives a finitely supported
  coefficient function on the Levi. Each Levi element contributes the
  monomial with exponent `leviUnramifiedExponent`.
- `leviTensorIntertwiner_pow`: block intertwiners with `A j ^ d = 1` give
  a tensor intertwiner with `d`-th power one.
- `familyIntertwiner_pow`: if `σ ^ d = 1` and `A j ^ d = 1` for all `j`,
  then the induced σ-intertwiner of the family has `d`-th power one at
  every parameter `z`. Both hypotheses are needed. The `d`-th power of the
  induced operator sends `f` to `g ↦ B ^ d (f (θ ^ (-d) g))`, where `B` is
  the inducing operator and `θ = entrywiseAut σ N`
  (`inducedTwistedIntertwiner_pow_eq_one`). `σ ^ d = 1` gives `θ ^ d = 1`,
  and `B ^ d = 1` comes from `leviTensorIntertwiner_pow`, since twisting
  by the σ-invariant characters does not change the underlying map.
- `leviTensorIntertwiner_scale` and `unramifiedFamilyTrace_scale`: scaling
  the block intertwiners by `c j` scales the family by `∏ j, c j`.
- `unramifiedFamilyTrace_comparison` takes `0 < d`, `σ ^ d = 1`, and two
  such families with irreducible admissible blocks and block intertwiners
  of order dividing `d`. Suppose that at every unitary parameter the first
  induced representation is irreducible and equivalent to the second. Then
  one `c` with `c ^ d = 1` satisfies `second z = c • first z` at every
  parameter `z`. The proof restricts to the circle torus and applies
  `regularTwistedDistributionComparison`, with the regularity above and
  `familyIntertwiner_pow` for both families.

Regularity of `ψ ↦ Φ(ι_α[Π_ψ, A_ψ])` in the unramified character `ψ`
is condition (ii) of the twisted Paley–Wiener theorem in Henniart–Lemaire
(2011), II.5.7, p. 105. There `Φ` is an element of `𝒢^{*}_0(G(E),σ)`:
a ℤ-linear form on `𝒢_0(G(E),σ)` with `Φ(Π, λA) = λ Φ(Π, A)`. Such a
form factors through the quotient `Ḡ(G(E),σ)` of II.5.4. By Remarque (2) there, proved in II.5.12, Lemme 2, it suffices
to check it for tempered inducing pairs. `unramifiedFamilyTrace_regular`
is the special case in which `Φ` is the twisted trace of one fixed test
function. That special case is Rogawski (1988), Lemma 11.1(a), p. 228.
Its proof there uses the polynomial dependence of the matrices of the
induced operators on a fixed space of `K`-fixed vectors. Here it is
deduced from `sigmaInducedTraceRegularity`. The comparison of two
families through their unitary specializations is the mechanism of
`regularTwistedDistributionComparison`. The sources do not argue this
way.
