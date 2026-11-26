# Harish-Chandra homomorphisms from second adjointness, the joint special-compact basis and finiteness

Module `Langlands.Representation.CuspidalSupport.HarishChandraHomomorphismReduction`, namespace
`Langlands.Aubert.General.RepresentedParabolic`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`
(SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`), VI.10.5, printed
p.213 / PDF p.219.

**Scope.** This module does not prove the published `HarishChandraHomomorphismStatement`
unconditionally. It states the finiteness part of Renard's VI.10.5 as a separate proposition,
`HarishChandraFinitenessStatement`, and proves that `HarishChandraHomomorphismStatement` follows
from the published `LeviSecondAdjointnessStatement` (Renard VI.9.6), the published
`JointSpecialCompactBasisExistenceStatement` (Renard V.5.1–V.5.2) and
`HarishChandraFinitenessStatement`. All four propositions are used unchanged.

## `HarishChandraFinitenessStatement`

The data are those of `HarishChandraHomomorphismStatement`: a nonarchimedean local field
`k : Type u` with `[T2Space k]`, a connected reductive `G` over `Spec k` with `G(F)` locally
compact and nonarchimedean in the canonical topology, an actual rational parabolic `P = MN`
(`p`, `l`, `r`, `hp`, `hl`, `hr`, `hmul`), `M(F)` with `leviPointTopology l hl` and the published
local compactness and nonarchimedean instances, and `I = leviInductionFunctor.{u, max u v} p l r
hp hr hl hmul`. The proposition says: for every ring homomorphism
`φ : CatCenter (SmoothRep.{0, u, max u v} ℂ G(F)) →+* CatCenter (SmoothRep.{0, u, max u v} ℂ M(F))`
with `I.map ((φ z).app σ) = z.app (I.obj σ)` for all `z` and `σ`, the centre of the category of
smooth representations of `M(F)` is a finitely generated module over that of `G(F)` for the
structure `Module.compHom _ φ`.

Provenance: this is the sentence of Renard VI.10.5 "Puisque le morphisme `i_{MG}` est fini, `ℨ(M)`
est un `ℨ(G)`-module de type fini", with the Harish-Chandra homomorphism `i*_{MG}` characterized by
its compatibility with `i_P^G` (the first compatibility of Renard's Proposition) instead of by the
variety structures on `Ω(M)` and `Ω(G)`. Since `I` is faithful (`leviInductionFunctor_faithful`),
at most one `φ` satisfies the compatibility (the published `leviCenterDescent_unique` proves this
whenever central components lift), so the universal quantifier over `φ` describes Renard's
homomorphism. The module structure is `Module.compHom`, as in `HarishChandraHomomorphismStatement`.

## Declarations and proofs as implemented

- `harishChandraHomomorphism_of_lift_of_finite`:
  `LeviCenterComponentsLiftStatement.{u, v} → HarishChandraFinitenessStatement.{u, v} →
  HarishChandraHomomorphismStatement.{u, v}`. After introducing the data, the lift statement gives
  `h : Renard.CenterComponentsLift I` (it is that proposition after unfolding). The published ring
  homomorphism `leviCenterDescent p l r hp hr hl hmul h` is the witness `φ`. The induction
  compatibility is `leviCenterDescent_induction`. The Jacquet compatibility
  `r_P^G(z) = (φ z)_{r_P^G π}` is `leviCenterDescent_jacquet`, which derives it from the induction
  compatibility through the first adjunction `r_P^G ⊣ i_P^G`. Finiteness is the finiteness
  statement applied to this `φ` and its induction compatibility.
- `HarishChandraHomomorphismReductionStatement` is the implication
  `LeviSecondAdjointnessStatement.{u, v} → JointSpecialCompactBasisExistenceStatement.{u} →
  HarishChandraFinitenessStatement.{u, v} → HarishChandraHomomorphismStatement.{u, v}`.
- `harishChandraHomomorphismReductionStatement_holds` proves it by composing
  `leviCenterComponentsLiftReductionStatement_holds` (module
  `Langlands.Representation.CuspidalSupport.LeviCenterComponentsLift`), which derives
  `LeviCenterComponentsLiftStatement` from the first two premises, with
  `harishChandraHomomorphism_of_lift_of_finite`. The axioms used are `propext`, `Classical.choice`
  and `Quot.sound`.

## Remarks

- The universes are those of `HarishChandraHomomorphismStatement`: `u` for the field and the
  group, and carriers in `max u v`. The second adjointness premise is used at the universes
  `.{u, v}`, which give adjunctions between categories of smooth representations on carriers in
  `max u v`, both for `P` in `G` and for parabolics of `M`.
- The finiteness statement is not proved here. Renard deduces it from the finiteness of
  `i_{MG} : Ω(M) → Ω(G)` (VI.7.3), which rests on the description of the centres in VI.10.4.
