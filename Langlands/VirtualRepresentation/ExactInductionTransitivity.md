# Transitivity of finite-index induction

Helper module for the proof of
`Langlands.ClassField.Global.RelativeWeilGroup.InducedCharacterGenerationStatement`
(Brauer induction for relative Weil groups). It proves that induction in two
steps, from `T` to `S` and then from `S` to `G`, is induction from `T` to `G`.
This holds both for the published function model of induction and for the
continuous exact virtual groups. The results are general: `G` is any group, or
any topological group in the virtual statements.

## Function model (`Langlands.FiniteRep`)

Let `T ≤ S` be subgroups of a group `G` (hypothesis `hTS`), and let `σ` be a
representation of `T` on `W` over a commutative ring. Inside `S`, the subgroup
`T` is `T.subgroupOf S`. It acts on `W` through Mathlib's
`Subgroup.subgroupOfEquivOfLe hTS : T.subgroupOf S ≃* T`.

- `coindTransLinearEquiv hTS σ` is a linear equivalence. Its source is
  Mathlib's coinduced space from `S` to `G` of the coinduced representation
  from `T.subgroupOf S` to `S`. Its target is the coinduced space from `T` to
  `G`. A function `F : G → (S → W)` goes to `g ↦ F g 1`, its value at the
  identity of `S`. The inverse sends `f : G → W` to `g ↦ (s ↦ f (s g))`. The
  equivariance conditions are checked directly from the defining identities
  `F (s g) = s · F g` and `f (t g) = σ t (f g)`.
- `coindTransEquiv hTS σ` is the same map as an equivalence of
  representations of `G`. Both actions are right translation, so the map is
  equivariant by definition.

## Exact virtual groups (`Langlands.VirtualRepresentation.ExactGrothendieckGroup`)

Here `G` is a topological group, `S` and `T` have finite index, and both are
open.

- `subgroupOfContinuousHom hTS : T.subgroupOf S →ₜ* T` is the identification of
  `T`, viewed inside `S`, with `T`, as a continuous homomorphism.
- `isOpen_subgroupOf` states that `T.subgroupOf S` is open in `S` when `T` is
  open in `G`. It is a preimage under the inclusion of `S`.
- `continuousInduce_continuousInduce_ofRepresentation S T hS hT hTS B hB`: for
  a continuous representation `B` of `T`,
  `continuousInduce S hS (continuousInduce (T.subgroupOf S) _ [restrict B]) =
  continuousInduce T hT [B]`. Here `restrict B` is the restriction of `B` along
  `subgroupOfContinuousHom hTS`. The proof unfolds both sides with the
  published `induce_ofRepresentation`, then applies
  `ofRepresentation_eq_of_equiv` to `coindTransEquiv`. The two carrier
  universes, `max uG (max uG uV)` and `max uG uV`, are the same level.
- `continuousInduce_continuousInduce_characterClass` is the case of a
  continuous character line:
  `Ind_S^G Ind_{T.subgroupOf S}^S [θ ∘ subgroupOfContinuousHom hTS] =
  Ind_T^G [θ]` for `θ : T →ₜ* ℂˣ`. The restricted character line is
  definitionally the character line of the composed character.

## Dependencies

The module imports the published `Langlands.VirtualRepresentation.ExactInductionTwist`
(`continuousInduce`, `induce_ofRepresentation`, `ofRepresentation_eq_of_equiv`)
and `Langlands.Weil.Representation.CharacterLine` (`characterClass`,
`characterLine_isContinuous`). It also uses the published
`FiniteRepresentation.isContinuous_restrict`.
