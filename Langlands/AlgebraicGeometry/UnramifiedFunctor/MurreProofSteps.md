# The steps of Murre's proof of the criterion for unramified functors

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreProofSteps` states
the three steps into which Murre's outline (Bourbaki exp. 294, Section 2)
splits the proof of
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCriterionStatement`.
It defines three helpers and five `Prop`-valued statements and proves nothing.
The companion module
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreReduction` proves that the
three steps together imply `MurreCriterionStatement`.

Throughout, `S : Scheme.{u}` and `F : (Over S)ᵒᵖ ⥤ Type v`. The conditions
`SmallValues`, `ZariskiSheaf`, … and the helpers `algebraOver`, … are those of
the published module
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCriterionStatement`, whose
Markdown records their correspondence with Murre's (F1)–(F8).

## Helpers

- `MurreConditions F` is the conjunction, in this order, of the ten hypotheses
  of `MurreCriterionStatement`: `SmallValues F`, `ZariskiSheaf F` (F1a),
  `FaithfullyFlatSheaf F` (F1b), `FilteredColimits F` (F2), `AdicLimits F`
  (F3), `ArtinianLifting F` (F4′), `NilpotentInjective F` (strong F5),
  `ValuativeSeparation F` (F6), `OneDimensionalLifting F` (F7) and
  `GenericNonLifting F` (F8).
- `UnramifiedRepresentable F` is the conclusion of `MurreCriterionStatement`:
  there are `Y : Scheme.{u}` and `q : Y ⟶ S` with
  `Nonempty (F.RepresentableBy (Over.mk q))`, `IsSeparated q`,
  `LocallyOfFiniteType q` and `FormallyUnramified q`.
- `baseChange g F`, for `g : S' ⟶ S`, is the presheaf `(Over.map g).op ⋙ F`
  on `Over S'`. It sends `T' ⟶ S'` to `F(T' ⟶ S' ⟶ S)`. This is Murre's
  `F ×_S S'` (`F_{S'}`): a morphism `T' ⟶ F ×_S S'` over `S'` is a morphism
  `T' ⟶ F` over `S`.

## Statements

- `MurreBaseChangeStatement.{u, v}` (Murre's "the above conditions on `F` are
  stable under base change"): for all schemes `S S' : Scheme.{u}`, every
  morphism `g : S' ⟶ S` and every `F : (Over S)ᵒᵖ ⥤ Type v`,
  `MurreConditions F` implies `MurreConditions (baseChange g F)`. No
  noetherian hypothesis is made on `S` or `S'`.
- `MurreLocalToGlobalStatement.{u, v}` (Murre's Proposition 2): let `S` be
  locally noetherian and let `F` satisfy `MurreConditions F`. If, for every
  point `s : S`, the base change `baseChange (S.fromSpecStalk s) F` along
  Mathlib's canonical morphism `S.fromSpecStalk s : Spec 𝒪_{S,s} ⟶ S` satisfies
  `UnramifiedRepresentable`, then `F` satisfies `UnramifiedRepresentable`.
- `MurreDimensionBound.{u, v} n`, for `n : ℕ`: for every locally noetherian
  `S : Scheme.{u}` all of whose local rings have Krull dimension `< n`
  (`ringKrullDim (S.presheaf.stalk s) < n` for every `s : S`) and every
  `F : (Over S)ᵒᵖ ⥤ Type v` with `MurreConditions F`, `UnramifiedRepresentable F`
  holds. This is the criterion restricted to such bases; it is the induction
  hypothesis of the local step.
- `MurreLocalStepStatement.{u, v}` (Steps 1, 2a and 2b of Murre's Case I): for
  every `n : ℕ`, if `MurreDimensionBound.{u, v} n` holds, then for every
  `R : CommRingCat.{u}` that is a local noetherian ring with
  `ringKrullDim R = n`, and every `F : (Over (Spec R))ᵒᵖ ⥤ Type v` with
  `MurreConditions F`, `UnramifiedRepresentable F` holds.
- `MurreProofStepsStatement.{u, v}` is the conjunction
  `MurreBaseChangeStatement ∧ MurreLocalToGlobalStatement ∧
  MurreLocalStepStatement`.

Each statement is a consequence of Murre's Theorem 1 in the form of its
Corollary 1 (the local-to-global and local steps are special cases of its
conclusion), except the base-change statement, which is Murre's separate
remark. None of them is proved here.

## Source and provenance

J. P. Murre, *Representation of unramified functors. Applications (according to
unpublished results of A. Grothendieck)*, Séminaire Bourbaki exp. 294
(1964–65), registered as `murre-1965-bourbaki-294-unramified-functors`
(SHA-256 `e36edaf9f965bbc92b0bdc36d8026fd7c87d890b859841d1dd965193385227dd`).
Printed page `p` is PDF page `p − 241`.

- Base change, printed p.247 (PDF p.6), first sentence of Section 2: "First of
  all, we note that the above conditions on `F` are stable under base change."
- Case I, induction on `dim S`, printed pp.247–249 (PDF pp.6–8): Step 1
  (`dim S = 0`) with Lemma 1, Step 2a (`S = Spec A`, `A` complete local
  noetherian of dimension `n`, using the induction hypothesis on the punctured
  spectrum `S − {s}`), Step 2b (`A` local noetherian of dimension `n`, by
  descent along `Spec Â ⟶ Spec A`, Proposition 1).
- Step 2c and Case II, printed pp.249–250 (PDF pp.8–9): both follow from
  Proposition 2: "Let `F` satisfy the conditions of theorem 1. Suppose
  `F ×_S Spec(𝒪_{S,s})` is representable for all `s ∈ S`. Then `F` itself is
  representable." Murre's remark after it notes that the conditions make the
  representing schemes locally of finite type, unramified and separated.

Provenance is derived: the decomposition follows Murre's outline, with these
choices.

- **Induction measure.** Murre inducts on `dim S` and treats `dim S = ∞`
  (Case II) separately. Here the measure is a strict bound `n` on the
  dimensions of all local rings of `S`. For a scheme, `dim S` is the supremum of
  the dimensions of its local rings, so `dim S < n` is the same condition. A
  locally noetherian scheme can have local rings of unbounded dimension, and
  then no bound applies; Proposition 2 handles this, as in Murre's Case II.
- **Local step.** Steps 1, 2a and 2b together prove the criterion over the
  spectrum of a local noetherian ring of dimension `n`, assuming it in lower
  dimension. The induction hypothesis is stated for arbitrary locally
  noetherian bases with all local rings of dimension `< n` (Murre applies it to
  the punctured spectrum `S − {s}` in Step 2a). Step 1 is the case `n = 0`, in
  which the hypothesis `MurreDimensionBound 0` only concerns empty bases.
- **Representability with properties.** Murre's Proposition 2 assumes and
  concludes plain representability; by his remark, the representing schemes
  are then locally of finite type, unramified and separated. The statement
  here assumes and concludes representability by such schemes, recorded as in
  `MurreCriterionStatement` by `IsSeparated`, `LocallyOfFiniteType` and
  `FormallyUnramified`.
- **Local schemes.** Murre's `Spec(𝒪_{S,s})` with its canonical morphism to `S`
  is Mathlib's `S.fromSpecStalk s`.
