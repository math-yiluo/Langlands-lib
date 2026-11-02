# Actual highest-derivative constituents and smooth-dual quotients

Author: Worker 357.

This derived supporting construction selects an actual irreducible
subrepresentation of a finite-length highest left derivative and an actual
surjective intertwiner from the same-order right derivative onto that
subrepresentation's smooth contragredient. The derivative's finite length is
an explicit hypothesis. The construction retains the chosen invariant
pairing and the quotient's evaluation formula.

## Actual data

`Langlands.InvariantBilinear.ConstituentDualQuotientData A B` is a structure
for two smooth complex representations of a topological group `G`, with
`[IsTopologicalGroup G]`. The group universe and both carrier universes are
independent. Its fields are:

- `constituent`: a literal `Subrepresentation A.representation`;
- `irreducible` and `admissible`: these properties of the actual smooth
  representation `SmoothRep.subrepresentation A constituent`;
- `form`: an actual form on the ambient representations `A` and `B`, with
  simultaneous covariance one;
- `separatingLeft`: left separation of that ambient form;
- `quotient`: an actual intertwiner from `B.representation` to the full
  `smoothContragredient` of the smooth constituent's representation;
- `surjective`: surjectivity of that map on the actual carriers;
- `quotient_apply`: for `w : B` and `x` in the smooth constituent,
  `(quotient w).val x = form.val x.val w`.

The smooth contragredient here consists of all smooth functionals, with the
usual inverse-action dual representation. The constituent is a subrepresentation,
not merely an isomorphism class. The form remains a form on the ambient
left representation; the evaluation formula restricts it to the chosen
subrepresentation. No uniqueness or canonicity is asserted.

## Highest-derivative constructor

`Langlands.Derivative.Mirabolic.chooseHighestDerivativeConstituentQuotient`
has independent universe parameters `uF`, `uV`, and `uW`. It takes arbitrary
`{p : ℕ} [Fact p.Prime]`, `{F : PadicField.{uF} p}`, the supplied
`T : F.TopologicalData`, and a supplied unitary additive character `ψ` for
`T.topology`. There is no additional nontriviality hypothesis on `ψ` in
this interface. Its remaining inputs are:

- natural numbers `N` and `k` with `hk : 0 < k ∧ k ≤ N + 1`;
- `A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear.mirabolic N F.Carrier)` and
  `B : SmoothRep.{0,uF,uW} ℂ (GeneralLinear.mirabolic N F.Carrier)`;
- nontriviality and finite length of the actual order-`k` derivative of `A`;
- subsingleton carriers for every valid order-`j` derivative of `A` with
  `k < j`;
- an actual form `β` on `A × B` with simultaneous determinant covariance
  `g ↦ ((((T.determinantNorm (N + 1)) g.val : ℝ≥0) : ℝ) : ℂ)`;
- left separation of `β`, expressed as
  `∀ v : A, (∀ w : B, β.val v w = 0) → v = 0`.

Write `DA` and `DB` for the order-`k` derivatives of `A` and `B`, using the
actual `mirabolicDerivativeOfOrder T ψ N k hk` functor. The result is actual
`ConstituentDualQuotientData DA DB` on `GL_(N+1-k)(F)`, with the topology and
topological-group instance supplied by `T`. This includes `N = 0` and
`k = N + 1`, where the target group has rank zero. No resizing of either
representation carrier is performed.

Only `A` is assumed highest. The right representation is assumed smooth
through its `SmoothRep` type; neither it nor `DB` is assumed admissible,
irreducible, or of finite length. The result supplies a surjective map
`DB → smoothContragredient S`, not an equivalence. Finite length of `DA`
is supplied directly; the constructor does not infer it from finite length
of `A`.

## Implemented construction

First, `chooseHighestDerivativePairing` from
`MirabolicPairingLevelComparison` selects a covariance-one form `γ` on
`DA × DB` which separates the left input. It is a choice from the proved
`mirabolicHighestDerivativePairing` theorem. No formula relating this
chosen `γ` to the original `β`, and no naturality assertion, is added here.

The private `existsIrreducibleSubrepresentation` lemma applies finite length
to the actual complex group-algebra module of `DA`. Its Artinian property
and nontriviality supply an atom `M` below the top submodule. The definition
`Subrepresentation.ofSubmodule' M` gives the actual subrepresentation `S`.
An explicit bijective group-algebra linear map from the module of the actual
smooth restricted representation to `M` transports simplicity. Mathlib's
irreducible-representation equivalence therefore proves irreducibility of
that smooth representation. This argument selects an actual subrepresentation;
it does not require a separate constituent-existence premise.

The proved `CuspidalSupport.cuspidalEmbedding` theorem gives admissibility
of this irreducible representation of `GL_(N+1-k)(F)`. Its rank-zero branch
handles the top derivative. The compact-open basis supplied by
`T.generalLinearCompactOpen` gives a compact open subgroup inside every
open subgroup of this actual general linear group.

Finally, `InvariantBilinear.smoothDualQuotientOfLeftEmbedding` from
`InvariantBilinearSmoothDual` is applied to the actual injective inclusion
`S → DA`, its irreducibility and admissibility, smoothness of `DB`, and the
chosen left-separating form `γ`. This yields the actual surjective map
`q : DB → smoothContragredient S`. The data store `S`, `γ`, `q`, and all
these proofs. For `w : DB` and `x : S`, the evaluation formula is exactly
`(q w).val x = γ.val x.val w`; in this implementation it is definitional.

The provenance is internal composition of the imported proved pairing,
Mathlib's Artinian-atom and simplicity results, the proved cuspidal embedding
and compact-open constructions, and the actual smooth-dual quotient
constructor. This module introduces no new assertion from the literature
and no unproved proposition target as an input theorem.

## Independence and scope

The import audit at Library commit
`dad4d948ab2f6838277ce9094bcc92df1507b0cb` contains 190 project modules,
including this module and the separately submitted `InvariantBilinearSmoothDual`
helper, and 118 external import roots. All 188 other inherited Lean/Markdown
pairs match that Library byte for byte. The smooth-dual helper's pair matches
its separately reviewed submission exactly; it requires separate publication
and is not part of this module's integration payload.

The four `Classification` modules in the closure are `Supercuspidal`,
`SupercuspidalTwist`, `SupercuspidalContragredientStatement`, and
`SupercuspidalContragredientAux`. They provide lower predicates, twist
infrastructure, and the proved general duality-transfer helper used by the
smooth-dual construction. A proposition target is not used as a proved
conclusion. The derivative branch uses the proved general mirabolic
highest-pairing theorem and its actual functors. The closure contains no
excluded segment derivative or Jacquet formula, segment-socle conclusion,
two-factor irreducibility, special-head irreducibility, multisegment
uniqueness or exhaustion, ordered-head existence, quotient coverage,
ordered conversion, tempered uniqueness, square-integrable classification
or exhaustion, or regular exhaustion conclusion. No proof holes, new axioms,
or kernel-bypassing commands occur in its Lean code. Declaration inspection
reports independent `uF`, `uV`, and `uW` and only `propext`, `Classical.choice`,
and `Quot.sound`.

This supporting construction supplies the constituent and smooth-dual quotient
step under explicit finite-length and highest-derivative hypotheses. It
proves neither direction of `SegmentHeadProductIrreducibility`. Individual
special-head derivative information, the required finite-length inputs,
the linked-pair argument, and the remaining product and support arguments
are separate obligations. The full repeated-segment special-head criterion
and its original carrier universes remain the host target.
