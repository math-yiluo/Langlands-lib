# `ℨ_D^{W(D)} ⊂ ℨ_Ω` for an actual Bernstein cuspidal datum: proof

Module `Langlands.Representation.CuspidalSupport.BernsteinBlockCenterFunctionsInvariantCenterProof`,
namespace `Langlands.CuspidalSupport`.

The theorem `bernsteinInvariantCenterInclusion` proves the published statement
`BernsteinInvariantCenterInclusionStatement` at the universe levels `uF, uV`. That is Renard
2026, VI.10.4, proof of the Theorem, the inclusion `ℨ_D^{W(D)} ⊂ ℨ_Ω` (printed pp. 211–212,
PDF pp. 217–218; source `renard-2026-representations-groupes-reductifs-padiques`). The
statement is used exactly as published. The proof adds no hypothesis and uses no conditional
input: neither second adjointness, nor the projectivity of `Π_D`
(`JointSpecialCompactBasisExistenceStatement`), nor the geometric lemma as a premise. Its
axioms are `propext`, `Classical.choice` and `Quot.sound`.

## The claim

Let `a = (M, ρ)` be an actual standard cuspidal datum of a `BernsteinStandardFamily`, `ρ₀` an
irreducible representation of `⁰M` with an injective `j : ρ₀ → ρ|_{⁰M}`,
`Π_D = ind_{⁰M}^{M} ρ₀` (`piD`) and `I = i_P^G`
(`bernsteinStandardRepresentedInductionFunctor`). Let `ζ` be central in `End(Π_D)` and assume
the invariance hypothesis `hinv`: whenever `ω ~ ω'` (`Assoc`: `ρ ⊗ ω ≅ c^*(ρ ⊗ ω')` for a
`RationalLeviConjugacy` `c` of the standard Levi to itself) and `ζ ≫ φ = c' • φ` for all
`φ : Π_D → ρ ⊗ ω`, then `ζ ≫ φ' = c' • φ'` for all `φ' : Π_D → ρ ⊗ ω'`. Then `I(ζ)` is central
in `End(I Π_D)`.

## Route

Renard identifies `R_Ω` with `Hom_M(Π_D, r_D i_P Π_D)` by second adjointness, filters it by the
geometric lemma with quotients `Hom_M(Π_D, w·Π_D)`, `w ∈ W(D)`, uses the projectivity of
`Π_D` and the filtered-bimodule Lemma. The Lean proof uses ordinary Frobenius reciprocity
instead, `R_Ω ≅ Hom_M(r_P i_P Π_D, Π_D)`, and the support filtration of `r_P i_P Π_D`:

1. `RepresentedParabolic.leviInduction_map_mem_center_of_twistedCommutation`
   (`CuspidalSupport/InducedCenterCriterion`): for `σ` supercuspidal, with no nonzero vector
   fixed by an element `t` with `tⁿ ∉ ⁰M` for all `n > 0`, and `ζ` central, `i_P(ζ)` is central
   as soon as `ζ` commutes with every linear `T : σ → σ` that is twisted-equivariant along an
   automorphism `φ` of `M` induced by some `w ∈ G(F)`. Pieces of the support filtration whose
   intersection parabolic of `M` is proper vanish (supercuspidality). The other pieces are
   `σ` twisted by such `φ`; on them every map to `σ` intertwines `ζ` (this is where `T` appears),
   and distinct pieces are separated by central elements of `M(F)`, using Renard V.3.5
   (`leviNormalizerNormFixing`, the faithfulness of `W(M)` on norms) and the fixed-vector
   property. This replaces Renard's step `Hom(Q_w, Q_{w'}) = 0` and the torsion-freeness
   over `ℨ_D`.
2. The twisted-commutation input for `Π_D`, proved here from `hinv` (the `W(D)`-invariance).

## Declarations of this module

- `bernsteinSummand_exists_twist_iso_of_surjective`: an irreducible quotient `τ` of `Π_D` is
  isomorphic to some `ρ ⊗ χ`. `Π_D` lies in the inertia block of the lifted `ρ`
  (`rationalSummandInduction_mem_block`, the Levi being connected reductive by
  `bernsteinStandardRepresentativesGeometric`); `τ` is a subquotient
  (`SmoothRep.IsQuotient.isSubquotient`); the block property gives `τ ≅ (lifted ρ) ⊗ χ`, and the
  carrier lift is removed by twisting `SmoothRep.mkIso (SmoothRep.universeLiftEquiv ρ)`.
- `bernsteinSummandCenter_exists_scalar`: a central `ζ` acts on all maps `Π_D → ρ ⊗ ω` by one
  scalar `s(ω)`. This is the last clause of Renard VI.4.4 at the Levi
  (`bernsteinLeviCenterVarietyStatement_holds`), applied to `ζ` viewed in
  `Subalgebra.center ℂ (End Π_D)`.
- `bernsteinSummandTwistedHom`: for `c` a `RationalLeviConjugacy`, `T` linear with
  `T ∘ Π_D(m) = Π_D(c.iso m) ∘ T` and `U : Π_D → ρ ⊗ ω`, the composite `U ∘ T` as a morphism
  `Π_D → c^*(ρ ⊗ ω)` (`rationalIsoPullback c.iso`).
- `bernsteinSummandCenter_hom_comm_twisted`: for such `c, T` and every `U : Π_D → ρ ⊗ ω`,
  `U(T(ζ v)) = U(ζ(T v))`, given scalars `s` as above and the transferred invariance: for every
  `χ` with `ρ ⊗ χ ≅ c^*(ρ ⊗ ω)`, `ζ` acts on the maps `Π_D → ρ ⊗ ω` by `s(χ)`. Let `V = U ∘ T`.
  If `V = 0`, both sides are `0` (the right side is `s(ω) U(T v)`). Otherwise `c^*(ρ ⊗ ω)` is
  irreducible (`isIrreducible_rationalUnramifiedTwist_iff`,
  `SmoothRep.isIrreducible_pullbackFunctor_obj_iff`), so `V` is surjective, and
  `bernsteinSummand_exists_twist_iso_of_surjective` gives `e : c^*(ρ ⊗ ω) ≅ ρ ⊗ χ`. Applying
  `s` to `V ≫ e` and cancelling `e` gives `ζ ≫ V = s(χ) V`, so `U(T(ζ v)) = s(χ) U(T v)`; the
  transferred invariance gives `U(ζ(T v)) = s(χ) U(T v)`.
- `bernsteinSummandCenter_comm_twisted`: under `hinv`, `T ∘ ζ = ζ ∘ T`. The invariance is
  transferred with `Assoc χ ω` witnessed by `c` and `e.symm`, and the scalar `s(χ)`. The vector
  `T(ζ v) - ζ(T v)` is killed by every `U : Π_D → ρ ⊗ ω`, hence is zero by
  `rationalNormKernelSummandInduction_eq_zero_of_forall_twist`
  (`CuspidalSupport/RationalSummandTwistSeparation`, with the injective `j`).
- `bernsteinInvariantCenterInclusion`: the target. It applies
  `leviInduction_map_mem_center_of_twistedCommutation` with the standard parabolic data of `a`
  (`bernsteinStandardRepresentativesGeometric`; `bernsteinStandardRepresentedInductionFunctor`
  is by definition `leviInductionFunctor` for these data), `hG = family.connectedReductive`
  and `σ = Π_D`. The supercuspidality of `Π_D` is
  `isSupercuspidal_rationalNormKernelSummandInduction` from `a.isSupercuspidal`; the
  fixed-vector property is `Induction.compactInduced_eq_zero_of_fixed` for the open normal
  subgroup `⁰M`. Both goals are stated with the Levi point topology, so the proof installs
  `leviPointTopology`, `leviPoints_locallyCompactSpace` and `leviPoints_nonarchimedeanGroup`
  first. For the twisted input, given `w, φ` with `φ ≫ (l ≫ p) = (l ≫ p) ≫ Int(w)`, the
  equation `l ≫ p = leviHom` (`Standard.leviToParabolic_comp`) gives the
  `RationalLeviConjugacy` `⟨w, φ, _⟩`, and `bernsteinSummandCenter_comm_twisted` applies.

## Technical notes

The module sets `maxHeartbeats 1200000` and `backward.isDefEq.respectTransparency.types false`,
as `BernsteinBlockCenterFunctionsReduction` does, and repeats its local instances on `G(F)` and
the standard Levis. Calls of the helper lemmas give the universes explicitly (`.{uF, uV}`).

## Helper modules

The proof depends on these helper modules, written for it, each with its paired Markdown:

- `Langlands/Representation/Filtration/CommutingHomDevissage`
- `Langlands/Representation/CuspidalSupport/InducedCenterCriterion`
- `Langlands/Representation/CuspidalSupport/RationalSummandTwistSeparation`
