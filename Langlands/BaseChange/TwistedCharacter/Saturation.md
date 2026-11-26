# Twisted character values on twisted conjugacy saturations

Module `Langlands.BaseChange.TwistedCharacter.Saturation`.

Let `G` be a topological group and `θ : G →* G` a monoid endomorphism. Twisted conjugation by
`x` is the map `y ↦ x * y * (θ x)⁻¹`; it is the composite of left multiplication by `x` and
right multiplication by `(θ x)⁻¹`, so it is a homeomorphism without any continuity assumption
on `θ`.

## Declarations

- `twistedConjugationHomeomorph θ x : G ≃ₜ G`, with `twistedConjugationHomeomorph_apply`:
  `y ↦ x * y * (θ x)⁻¹`.
- `twistedConjugacySaturation θ U`: the union over all `x : G` of the images
  `x U (θ x)⁻¹`. It is open when `U` is (`isOpen_twistedConjugacySaturation`), contains `U`
  (`subset_twistedConjugacySaturation`) and contains every twisted conjugate of a point of `U`
  (`twistedConj_mem_twistedConjugacySaturation`).

From here on `G` is Hausdorff, locally compact and totally disconnected with its Borel
σ-algebra, `μ` is a left Haar measure, `ρ` is an admissible complex representation on `V` and
`A : V →ₗ V` satisfies `A ∘ ρ(g) = ρ(θ g) ∘ A` for all `g`. The twisted distribution is the
Library's `twistedDistribution μ ρ hρ A`, `f ↦ tr(ρ(f) ∘ A)`.

- `integratedAction_twistedConjugation`: for the pulled-back test function
  `f' (y) = f (x y θ(x)⁻¹)`,
  `ρ(f') v = Δ(θ x) • ρ(x)⁻¹ (ρ(f) (ρ(θ x) v))`, where `Δ = Distribution.renardModular`. The
  proof evaluates both sides on an arbitrary algebraic linear functional, which turns the
  integrated action into a scalar Bochner integral (`Hecke.integratedAction_dual`), and applies
  the translation law `∫ F(h' y h⁻¹) dμ(y) = Δ(h) ∫ F dμ`
  (`Distribution.RenardModular.translation`) with `h' = x`, `h = θ x`.
- `twistedDistribution_twistedConjugation`: `Θ_A(f') = Δ(θ x) Θ_A(f)`. Composing the previous
  identity with `A` and using `A ∘ ρ(x) = ρ(θ x) ∘ A` gives
  `ρ(f') ∘ A = Δ(θ x) • ρ(x)⁻¹ ∘ (ρ(f) ∘ A) ∘ ρ(x)`; the finite-rank trace is invariant under
  conjugation by a linear equivalence (`FiniteRankEnd.trace_conjugate`).
- `twistedDistribution_eq_of_support_twistedConjugacySaturation`: if `U` is open and
  `Θ_A(f) = a ∫ f dμ` for every test function supported in `U`, the same identity holds for
  every test function supported in `twistedConjugacySaturation θ U`. On a single twisted
  conjugate `x U (θ x)⁻¹` this follows from the two transformation laws, since the Haar
  integral of `f'` is also `Δ(θ x) ∫ f dμ` and `Δ(θ x) ≠ 0`. The distribution
  `Θ_A - a · μ` thus vanishes near every point of the saturation, and the sheaf property of
  distributions on open sets (`Distribution.openRestrictionLocality`) shows that it vanishes on
  every test function supported in the saturation. This is the twisted form of
  `SigmaLiftCharacterIdentity.evaluate_saturation`, with the same proof.
- `HasTwistedCharacterValue.exists_saturation`: a twisted character value `c` at `g` gives,
  for every Haar measure, an open window `U ∋ g` such that `Θ_A(f) = c ∫ f` for every test
  function supported in the twisted conjugacy saturation of `U`.
- `HasTwistedCharacterValue.twistedConj`: a twisted character value at `g` is also a twisted
  character value at `x * g * (θ x)⁻¹`, for every `x`.

No unimodularity of `G` is assumed; the modular factors of the distribution and of the Haar
integral cancel.

## Use

For a standard block Levi `M = B.Levi E` of `GL_n(E)` and `θ = leviAut σ B`, the tensor product
`leviTensorIntertwiner σ B A` of block σ-intertwiners satisfies the intertwining hypothesis.
These results then say that the twisted character of the Levi tensor representation is
invariant under σ-conjugation in `M(E)`, as used in Henniart–Lemaire, *Changement de base et
induction automorphe pour GL_n en caractéristique non nulle* (2011), II.4.5, printed p. 87
(the invariance of `Θ^B_Ξ` under σ-conjugation in `M(E)`).
