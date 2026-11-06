# Positive unramified twists with unitary central character

Lean module: `Langlands.Representation.Exponents.PositiveUnramifiedCentralTwist`.

The proof of Renard 2026, VII.1.3 (printed p.224/PDF p.230) begins with a reduction. By
"an argument from the proof of Theorem VI.8.5", some unramified character `χ` of `G`
makes the central character of `π ⊗ χ` unitary. This module proves that step for an
irreducible smooth representation of `H(F)`, where `H` is an arbitrary connected reductive
group over a nonarchimedean local field `F`. The character it produces also takes
positive real values, which is more than Renard's sentence asks for.

The construction does not need the image of the center under the valuation map to have
finite index. This differs from the Library's
`Langlands.Representation.Unitary.RationalCentralUnitarizer`, which needs it. The central
character's modulus is extended in one step, using that the positive real units form a
divisible group.

## Extension of positive characters

Namespace `Langlands.PositiveCharacter`.

- `expAddHom : ℝ →+ Additive ℝ≥0ˣ` is `t ↦ exp t`. `expAddHom_surjective` states that it
  is surjective; the preimage of `a` is `log a`.
- `exists_extension`: for an injective homomorphism `f : A →* B` of commutative groups,
  every `χ : A →* ℝ≥0ˣ` equals `ψ ∘ f` for some `ψ : B →* ℝ≥0ˣ`.

  Proof: `ℝ≥0ˣ` is divisible as a `ℤ`-module, since it is the image of the divisible
  group `ℝ` under the surjection `expAddHom` (`Function.Surjective.divisibleBy`). Baer's
  criterion `Module.Baer.of_divisible` makes it an injective `ℤ`-module, and
  `extension_property_addMonoidHom` extends `χ` along `f`, after passing to additive
  notation.

## Abstract correction

Namespace `Langlands.Plancherel`. Here `G` is a group, `ν : I → (G →* ℝ≥0ˣ)` is a family
of positive characters, and `G¹ = commonNormKernel ν` is their common kernel.

- `exists_positiveCharacter_restrict_eq`: let `A` be a subgroup of `G` and `χ` a positive
  character of `A` that is trivial on `A ∩ G¹`. Then `χ` is the restriction of a positive
  character `θ` of `G` that is trivial on `G¹`.

  Proof: let `N = MonoidHom.pi ν : G → (I → ℝ≥0ˣ)`, whose kernel is `G¹`, and let
  `φ = N|_A`. The kernel of `φ` lies in the kernel of `χ`, so `χ` factors through
  `A / ker φ ≅ range φ` (`QuotientGroup.lift`, `QuotientGroup.quotientKerEquivRange`).
  Extend this factor from `range φ` to the commutative group `I → ℝ≥0ˣ` by
  `exists_extension`, and compose with `N`.

The remaining results assume that `G` is a topological group.

- `exists_positive_unramifiedCharacter_norm_mul_eq_one_of_norm`: suppose `G¹` is open, `A`
  is a subgroup, and `ω : A →* ℂˣ` satisfies `‖ω a‖ = 1` on `A ∩ G¹`. Then some
  `ψ ∈ unramifiedCharacters ν` takes positive real values and satisfies `‖ψ(a) ω(a)‖ = 1`
  for all `a ∈ A`.

  Proof: apply the previous result to the modulus `PositiveCharacter.normCharacter ω`,
  which gives `θ`. Set `ψ = θ⁻¹`, viewed in `ℂˣ` through `positiveUnitsToComplex`. It is
  trivial on `G¹`. Since `G¹` is open, its kernel is open, so it is continuous
  (`Langlands.Weil.continuous_of_open_kernel`). On `A`, `‖ψ(a) ω(a)‖ = ‖ω(a)‖⁻¹ ‖ω(a)‖ = 1`.
- `exists_positive_unramifiedCharacter_norm_mul_eq_one_of_isCompact`: the same conclusion
  when `A ∩ G¹` is compact and `ω` has open kernel. The modulus of `ω` has open kernel
  (`PositiveCharacter.isOpen_ker_normCharacter`). A positive character with open kernel
  is trivial on a compact subgroup (`PositiveCharacter.eq_one_on_compact`), so
  `‖ω‖ = 1` on `A ∩ G¹`, and the previous result applies.

## Rational points of a reductive group

Namespace `Langlands.Aubert.General.RepresentedParabolic`. Here `H` is a group scheme over
a nonarchimedean local field `k` with affine structure morphism, and `H(k)` carries the
point topology `RationalPointFamily.pointTopology`. The unramified characters are those
for the norms `|c(·)|` of the rational characters `c` of `H`.

- `exists_positive_unramifiedCharacter_norm_mul_eq_one`: if `H` is connected reductive and
  `ω` is a character of the center `Z` of `H(k)` with open kernel, then some unramified
  `ψ` with positive real values satisfies `‖ψ(z) ω(z)‖ = 1` on `Z`. This is the compact
  case with `A = Z`. The Library supplies the inputs: `G¹` is open
  (`Plancherel.isOpen_rationalCommonNormKernel`), and `G¹ ∩ Z` is compact
  (`Plancherel.isCompact_rationalCommonNormKernel_inf_center`).
- `twistUnitaryCentralCharacter`: suppose `ρ` has central character `ω`, with open kernel,
  and `ψ` is a character with open kernel satisfying `‖ψ(z) ω(z)‖ = 1` on `Z`. Then this
  definition builds a unitary central character of `Langlands.twist ψ ρ`. The character
  is `ψ|_Z · ω`. Its kernel contains the open subgroup `ker ψ|_Z ∩ ker ω`, so it is open.
  The definition assumes that `H(k)` is a topological group, which this openness argument
  uses.
- `exists_positive_unramifiedTwist_unitaryCentralCharacter`: assume moreover that `H(k)` is
  a nonarchimedean group (this is the instance that gives unramified characters open
  kernels, `Plancherel.unramifiedCharacter_isOpen_ker`). If `H` is connected reductive and
  `π` is an irreducible smooth representation of `H(k)`, then some unramified character
  `ψ` with positive real values makes `π.twist ψ` have a unitary central character. The
  twist uses the open-kernel proof `Plancherel.unramifiedCharacter_isOpen_ker _ ψ`.

  Proof: `CuspidalSupport.rationalPointCentralCharacter` gives the central character `ω`
  of `π` (Schur's lemma). An irreducible representation is nonzero
  (`Whittaker.MirabolicRigidity.exists_ne_zero_of_isIrreducible`), so `ω` has open kernel
  (`SmoothRep.HasCentralCharacter.isOpen_ker`). The previous two results then give `ψ`
  and the unitary central character of the twist.
