# Normalized induction from the full parabolic

Author: Worker 892.

This module treats the full-index case of
`Langlands.Aubert.General.RationalPointFamily.RationalSupercuspidalInductionFiniteLengthStatement`
(the finite-length part of Renard, Théorème VI.5.4). It does not prove that statement:
the proper indices `I ≠ Finset.univ` are not treated. The Library statement file is
imported and left unchanged.

## Generic part

Let `G` be a group with a semidirect decomposition `P = M ⋉ U`
(`IsSemidirectDecomposition P M U`, with `U` closed), and suppose every element of `G`
lies in `P` (`hP : ∀ g : G, g ∈ P`).

- `fullParabolicInclusion hP : G →* P` is the identity of `G` with codomain restricted
  to `P`. It is surjective (`fullParabolicInclusion_surjective`) and its value is `g`
  as an element of `G` (`fullParabolicInclusion_apply`).
- `fullParabolicEvaluation h hU hP A` is evaluation at the identity, `f ↦ f(1)`. It maps
  the normalized induced representation `(normalizedInductionFunctor h hU).obj A` to the
  inducing action `inducingRepresentation h hU A`, read on `G` through
  `fullParabolicInclusion hP`. The inducing action is `p ↦ δ(p)^{1/2} σ(m(p))`; in Lean
  it is `Langlands.twist` of the inflation `A.representation.comp h.projection` by
  `HaarModulus.closedHalfCharacter`. The map is an intertwiner because
  `f(1 · g) = f(g · 1)`, and covariance
  (`normalizedInductionFunctor_covariant`) applied to the parabolic element `g` gives
  `f(g) = (inducing action)(g)(f(1))`.
- `fullParabolicEvaluation_injective`: by the same covariance at `p = ⟨x, hP x⟩`,
  `f(x) = (inducing action)(x)(f(1))` for every `x : G`. So a covariant function is
  determined by its value at `1`. The two subtype layers of the smooth induced space are
  peeled off with `Subtype.ext`.
- `inducingRepresentation_comp_fullParabolicInclusion_finiteLength`: if `A` has finite
  length, the inducing action read on `G` has finite length over `ℂ[G]`. The Levi
  projection `h.projection : P →* M` is surjective, since it is the identity on `M`
  (`h.projection_levi`). Then `FiniteLengthAssembly.finiteLength_comp_surjective_iff`
  (for the Levi projection), `Langlands.finiteLength_twist_iff` (for the scalar twist)
  and `FiniteLengthAssembly.finiteLength_comp_surjective_iff` again (for
  `fullParabolicInclusion hP`) transport finite length.
- `normalizedInduction_hasFiniteLength_of_forall_mem`: normalized induction along such
  a parabolic preserves finite length. The proof is
  `FiniteLengthAssembly.finiteLength_of_injective` applied to the injective intertwiner
  `fullParabolicEvaluation`.

Evaluation at `1` is only claimed to be injective. It need not be surjective: the
decomposition `P = M ⋉ U` is algebraic and `M` need not be closed, so the inflated action
of a smooth `M`-representation need not be smooth on `G`, and smooth induction keeps only
covariant functions with open stabilizers. (Reviewer 11870 gave an example with
`G = P = (F_2)^ℕ × F_2` where smooth induction is zero and the inducing action is
one-dimensional.) Injectivity suffices for finite length, and no smoothness premise is
added.

## Rational-point specialization

All declarations below are in `Langlands.Aubert.General.RationalPointFamily` and use the
published families `parabolic i ν I`, `levi i ν I`, `unipotent i ν I`.

- `mem_parabolic_univ`: under `StandardCocharacterStatement`, every rational point lies
  in the full-index standard parabolic `parabolic i ν Finset.univ`. This is the
  membership form of the Library's `parabolic_univ_eq_top`
  (`Langlands.Representation.Aubert.General.RationalEndpoint`), which shows
  `parabolic i ν Finset.univ = ⊤`: the standard cocharacter of the full simple-root set
  is `0`, and its dynamic parabolic is the whole group.
- `rationalSupercuspidalInductionFiniteLength_univ` repeats the complete binder telescope
  of the target statement, including the universe `uV` of the input carrier, which is
  independent of `u`. For `I = Finset.univ`, normalized induction
  `(normalizedInductionFunctor (h Finset.univ) (hU Finset.univ)).obj σ` has finite length
  for every finite-length smooth representation `σ` of `levi i ν Finset.univ`. Here `h`
  is the published `isSemidirectDecomposition_of_standardCocharacterStatement`. Only
  `hStandard`, `hRoots` (for the `Fintype` instance on simple roots) and `hU` are used;
  the binders `hInter` and `hM` are kept only to match the telescope.
- `rationalSupercuspidalInductionFiniteLength_univ_of_isIrreducible` is the literal
  `I = Finset.univ` instance of the target. It has the same telescope, with the
  published `hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν`, and keeps both
  hypotheses `σ.IsIrreducible` and
  `IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU Finset.univ (hM Finset.univ) (hL Finset.univ) σ`.
  Irreducibility gives finite length (`SmoothRep.hasFiniteLength_of_isIrreducible`).
  The cuspidality hypothesis is not used.

## Provenance and scope

The provenance is internal. The argument is the elementary observation that, when
`P = G`, covariance determines a function by its value at the identity, so evaluation at
`1` is an injective intertwiner into the inducing action. It is combined with the
published Library definitions and lemmas named above. It is not a step of Renard's proof of
VI.5.4, which concerns proper parabolics and uses the embedding VI.2.1, Lemma VI.5.2
and the geometric lemma (Renard, pp. 178–180 of the PDF).

This module proves nothing about proper indices. Those are the substantive content of
VI.5.4. In this project they depend on the rational Bruhat decomposition, the
Iwasawa/Cartan decompositions and the finiteness of `G/(⁰G Z(G))` (Renard V.2.6), none
of which is a premise of the target statement.
