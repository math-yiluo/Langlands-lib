# The parts of the local step of Murre's induction

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalStepParts`
states Murre's Lemma 1 and Steps 1, 2a and 2b of Case I of Murre's outline
(Bourbaki exp. 294, Section 2). Steps 1, 2a and 2b together give
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalStepStatement`. The
module defines three helpers and five `Prop`-valued statements and proves
nothing. The companion module
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalStepReduction` proves
that `MurreLocalStepPartsStatement` implies `MurreLocalStepStatement`.

`MurreConditions`, `UnramifiedRepresentable` and `baseChange` are the helpers
of the published module
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreProofSteps`. The conditions
`ZariskiSheaf` (F1a), `FaithfullyFlatSheaf` (F1b), `FilteredColimits` (F2),
`AdicLimits` (F3) and the helper `algebraOver` are those of the published
module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCriterionStatement`.
In this module `R`, `A` are rings of universe `u`, and `F` is a presheaf
`(Over (Spec R))ᵒᵖ ⥤ Type v` (or on `Over (Spec A)`).

## Helpers

- `puncturedSpectrum R`, for a local ring `R : CommRingCat.{u}`, is the open
  subset `{closedPoint R}ᶜ` of `Spec R`. It is open because the closed point
  is closed (`isClosed_singleton_closedPoint`). This is Murre's `S' = S − {s}`
  in Step 2a. Its inclusion is the open immersion
  `(puncturedSpectrum R).ι : (puncturedSpectrum R).toScheme ⟶ Spec R`.
- `maximalIdealPowQuotientMap R k : Spec (R ⧸ m^(k+1)) ⟶ Spec R`, for a local
  ring `R` with maximal ideal `m` and `k : ℕ`, is `Spec` of the quotient map
  `R → R ⧸ m^(k+1)`. Murre's `S_n = Spec A_n` with `A_n = A/m^(n+1)` in
  Step 2a is its source for `k = n`.
- `completionMap R : Spec R̂ ⟶ Spec R`, for a local ring `R`, is `Spec` of the
  canonical map `R → R̂` into the completion
  `R̂ = AdicCompletion (maximalIdeal R) R`. This is Murre's `S' = Spec(Â) ⟶ S`
  in Step 2b.

## Statements

- `MurreArtinianDetectionStatement.{u, v}` (Murre's Lemma 1, bijective
  version, for a represented source): let `A` be a noetherian ring and let
  `F : (Over (Spec A))ᵒᵖ ⥤ Type v` satisfy `ZariskiSheaf F`,
  `FaithfullyFlatSheaf F`, `FilteredColimits F` and `AdicLimits F`. Let
  `Y : Scheme.{u}` with `q : Y ⟶ Spec A` locally of finite type, and
  `ξ ∈ F(Y)` (an element of `F.obj (op (Over.mk q))`). Suppose that for every
  `A`-algebra `B : Type u` which is a local artinian ring and quasi-finite over
  `A` (`Algebra.QuasiFinite A B`), the map
  `(Spec B ⟶ Y over Spec A) → F(Spec B)`, `g ↦ F(g)(ξ)`, is bijective; here
  `Spec B` is the object `algebraOver (𝟙 (Spec A)) B`. Then for every
  `T : Over (Spec A)` the map `(T ⟶ Y over Spec A) → F(T)`, `g ↦ F(g)(ξ)`, is
  bijective. That is, `ξ` exhibits `Y` as representing `F`.
- `MurreArtinianBaseStatement.{u, v}` (Step 1): for every local artinian ring
  `R : CommRingCat.{u}` and every `F` on `Over (Spec R)` with
  `MurreConditions F`, `UnramifiedRepresentable F` holds.
- `MurreCompleteLocalStepStatement.{u, v}` (Step 2a): let `R : CommRingCat.{u}`
  be a local noetherian ring that is complete for its maximal ideal `m`
  (`IsAdicComplete (maximalIdeal R) R`), and let `F` on `Over (Spec R)` satisfy
  `MurreConditions F`. If
  `UnramifiedRepresentable (baseChange (puncturedSpectrum R).ι F)` and, for
  every `k : ℕ`,
  `UnramifiedRepresentable (baseChange (maximalIdealPowQuotientMap R k) F)`,
  then `UnramifiedRepresentable F`.
- `MurreCompletionDescentStatement.{u, v}` (Step 2b): let `R : CommRingCat.{u}`
  be a local noetherian ring and let `F` on `Over (Spec R)` satisfy
  `MurreConditions F`. If
  `UnramifiedRepresentable (baseChange (puncturedSpectrum R).ι F)` and
  `UnramifiedRepresentable (baseChange (completionMap R) F)`, then
  `UnramifiedRepresentable F`.
- `MurreLocalStepPartsStatement.{u, v}` is the conjunction
  `MurreArtinianBaseStatement ∧ MurreCompleteLocalStepStatement ∧
  MurreCompletionDescentStatement`. Lemma 1 is not part of it: the reduction
  to `MurreLocalStepStatement` does not use it. It is stated here as a tool
  for proving Steps 1 and 2a, where Murre uses it.

Steps 1, 2a and 2b are special cases of Murre's Theorem 1 in the form of its
Corollary 1 (`MurreCriterionStatement` over `S = Spec R`), with extra
hypotheses in Steps 2a and 2b. None of the statements is proved here.

## Source and provenance

J. P. Murre, *Representation of unramified functors. Applications (according to
unpublished results of A. Grothendieck)*, Séminaire Bourbaki exp. 294
(1964–65), registered as `murre-1965-bourbaki-294-unramified-functors`
(SHA-256 `e36edaf9f965bbc92b0bdc36d8026fd7c87d890b859841d1dd965193385227dd`).
Printed page `p` is PDF page `p − 241`.

- Step 1 and Lemma 1, printed p.247 (PDF p.6). Step 1: "dim S = 0. We can
  assume S = Spec(A), A local artinian ring." Lemma 1 ("A noetherian ring"):
  "Let X and F be two contravariant functors from (Sch/A) to (Sets)
  satisfying both (F1), (F2), and (F3). Let p : X → F be a functor morphism.
  Assume that the map X(T) → F(T), defined by p, is injective (resp.
  bijective) for preschemes T of type T = Spec(B) with B a local A-algebra
  which is artinian and the residue field of which is a finite algebraic
  extension of k(s) (s is the point of S = Spec(A) below the closed point of
  Spec(B)). Then p is a monomorphism (resp. isomorphism)." Murre's sketch of
  its proof is on printed p.248 (PDF p.7).
- Step 2a, printed pp.248–249 (PDF pp.7–8): "Let S = Spec(A) with A
  noetherian local ring which is complete and dim A = n. Let s be the closed
  point, S' = S − (s). By the induction assumption, F_{S'} = F ×_S S' is
  representable by a S'-scheme X' which is locally of finite type and
  unramified over S'. Put A_n = A/m^{n+1} … According to step 1, F_{S_n} is
  representable by a scheme Y_n …" Murre glues `X'` with a scheme `Y` built
  from the `Y_n`, and concludes with Lemma 1.
- Step 2b, printed p.249 (PDF p.8): "S = Spec(A) with A noetherian local ring,
  dim S = n. Consider S' = Spec(Â) where Â is the completion of A, and
  F' = F ×_S S'. By step 2a, this F' = X' is representable and X' has by
  construction a descent datum with respect to S' → S." Murre concludes with
  Proposition 1 (descent of locally quasi-finite separated schemes along
  faithfully flat quasi-compact morphisms of locally noetherian schemes).

Provenance is derived: the statements follow Murre's text, with these choices.

- **Lemma 1, represented source.** Murre's `X` is an arbitrary functor with
  (F1), (F2), (F3). In his applications `X` is represented by a scheme (`X =
  ∐ Spec(A_i)` in Step 1, the glued scheme in Step 2a), locally of finite type
  over `A`. The statement takes `X` represented by `Y` with `Y ⟶ Spec A`
  locally of finite type and the morphism `p : X → F` given by `ξ ∈ F(Y)`
  (Yoneda). Such an `X` satisfies (F1), (F2) and (F3): representable functors
  are fpqc sheaves, a morphism locally of finite type over a noetherian base is
  locally of finite presentation (F2), and morphisms from the spectrum of a
  complete local ring into a scheme are determined by compatible systems on
  the artinian quotients (F3). Only the bijective version is stated; the
  injective version is an intermediate step of its proof.
- **Lemma 1, test algebras.** Murre's test schemes are `Spec B` with `B` a
  local artinian `A`-algebra whose residue field is finite over `k(s)`, `s` the
  image in `Spec A` of the closed point. For a local artinian `A`-algebra `B`
  this is equivalent to Mathlib's `Algebra.QuasiFinite A B` (for every prime
  `p` of `A`, the fibre `κ(p) ⊗_A B` is finite over `κ(p)`): the only nonzero
  fibre is the one over `s = m_B ∩ A`, which is `B/sB`, a local artinian ring
  with residue field `B/m_B`; it is finite over `κ(s)` exactly when `B/m_B` is.
  Murre's condition (F1) is the pair `ZariskiSheaf`, `FaithfullyFlatSheaf`.
- **Step 1.** Murre reduces `dim S = 0` to `S = Spec(A)` with `A` local
  artinian; the statement is that case.
- **Steps 2a and 2b, hypotheses.** Murre obtains the representability of
  `F ×_S S'` over the punctured spectrum from the induction assumption, that of
  `F ×_S S_n` from Step 1 (Step 2a), and that of `F ×_S Spec(Â)` from Step 2a
  (Step 2b). The statements take these representability results as
  hypotheses, so that they do not depend on the induction hypothesis or on
  `dim A = n`. The dimension bookkeeping is in
  `MurreLocalStepReduction`. Murre uses the punctured spectrum of `A` only in
  Step 2a; Step 2b here also assumes representability over the punctured
  spectrum `S − {s}` of the non-complete `A`, which the induction hypothesis
  supplies in the same way. This extra hypothesis is not in Murre's text.
- **Representability with properties.** As in `MurreProofSteps`, the
  representability assumed and concluded is `UnramifiedRepresentable`:
  represented by a scheme separated, locally of finite type and formally
  unramified over the base. Murre's induction assumption likewise gives schemes
  locally of finite type and unramified over `S'`.
- **Completeness and powers.** Murre's "complete" is
  `IsAdicComplete (maximalIdeal R) R` (Hausdorff and complete for the
  `m`-adic topology). His `A_n = A/m^{n+1}` is `R ⧸ maximalIdeal R ^ (k + 1)`.
