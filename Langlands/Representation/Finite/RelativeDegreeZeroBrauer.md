# Degree-zero Brauer induction relative to a normal subgroup

Lean module: `Langlands.Representation.Finite.RelativeDegreeZeroBrauer`.

## Source

- P. Deligne and G. Henniart, *Sur la variation, par torsion, des constantes locales
  d'équations fonctionnelles de fonctions L*, Invent. Math. 64 (1981), proof of Lemma
  4.3, printed p. 109 (PDF p. 21). The proof applies "la variante ([1], 1.5) du théorème
  de Brauer en dimension 0" to a degree-zero virtual representation `W` whose
  constituents are trivial on a ramification subgroup. It writes `W` as an integral
  combination of `Ind_H (χ - 1)`, where `H` contains that subgroup and `χ` is a
  character of `H` trivial on it. The proof of Lemma 4.7 (printed pp. 110-111) uses the
  same step.
- P. Deligne, *Les constantes des équations fonctionnelles des fonctions L* (1973),
  Proposition 1.5 (PDF p. 10): degree-zero Brauer induction.

This module is the finite-group form of that step, for complex representations of a
finite group `G` and a normal subgroup `N`. It is the inflation of degree-zero Brauer
induction from `G ⧸ N`.

## Definitions

- `relativeDegreeZeroGenerators G N` is the set of classes
  `virtualInduce S ([oneDimensional χ] - [oneDimensional 1])` in `VirtualRep ℂ G`.
  Here `S` is a subgroup with `N ≤ S`, and `χ : S →* ℂˣ` satisfies
  `χ (Subgroup.inclusion hNS n) = 1` for all `n ∈ N`. These are actual inductions of
  `χ - 1`.
- `relativeDegreeZeroSpan G N` is their integral span.
- `trivialOnSpan G N` is the integral span of the classes `ofClass (classOf V)` of actual
  finite-dimensional representations `V` with `V.ρ n = 1` for all `n ∈ N`.
- `RelativeDegreeZeroBrauerStatement G : Prop` says the following. For every normal
  subgroup `N`, every `x ∈ trivialOnSpan G N` with `x ∈ degreeZeroVirtualReps G`
  (virtual degree zero) lies in `relativeDegreeZeroSpan G N`.

## Main theorem

`Langlands.FiniteRep.relativeDegreeZeroBrauer (G) [Group G] [Fintype G] :
RelativeDegreeZeroBrauerStatement G`.

## Proof (as implemented)

Let `π = QuotientGroup.mk' N`.

1. A representation `V` trivial on `N` descends to `G ⧸ N` through
   `QuotientGroup.lift`, with the same character along `π` (`exists_descent`). By span
   induction, every `x ∈ trivialOnSpan G N` has the character of the pullback along `π`
   of some `y ∈ VirtualRep ℂ (G ⧸ N)` (`exists_pullback`).
2. Evaluating at `1` shows that `y` has degree zero. So `y` lies in the Library's
   degree-zero Brauer span of `G ⧸ N`, by `DegreeZeroBrauer.finiteDegreeZeroBrauer`.
3. Pullback carries the character of each generator `Ind_S (χ - χ')` of `G ⧸ N` to
   `Ind_{π⁻¹ S} (χ∘π - χ'∘π)`, by the Library lemma `DegreeZeroBrauer.ind_comap`. The
   subgroup `π⁻¹ S` contains `N = ker π`, and `χ∘π` and `χ'∘π` are trivial on `N`. Hence
   this is the difference of the characters of two relative generators
   (`ind_sub_one_mem`, `ind_sub_mem`, `pullback_mem_rel`).
4. The character of `x` therefore lies in the image of `relativeDegreeZeroSpan G N`
   under `virtualCharacter`. Faithfulness of `virtualCharacter`
   (`VirtualCharacter.faithfulness`) gives `x ∈ relativeDegreeZeroSpan G N`.

## Provenance

The statement is the finite-group content of the Brauer step in DH81 4.3/4.7 (cited
above). That step is Deligne's Proposition 1.5 applied to the quotient by the normal
subgroup. The formal statement fixes how "constituents trivial on `N`" is expressed: as
membership in the span of actual representations on which `N` acts trivially. The helper
`relCharSpan` (the character image of the relative span) is internal to the proof.
