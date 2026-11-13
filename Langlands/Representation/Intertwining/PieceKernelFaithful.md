# Faithfulness of normalized induction for central group-algebra kernels

Author: Worker 102. Module `Langlands.Representation.Intertwining.PieceKernelFaithful`,
namespace `Langlands.Aubert.General.RepresentedParabolic`. Universe parameters `u` (the field)
and `v` (the representation).

The kernel of a geometric-lemma piece along the split component equals the kernel of the
inner representation, before the outer parabolic induction. Renard uses this in VII.3.3 and
VII.3.5 ("car le foncteur d'induction parabolique est fidèle", printed p.239). The module adds
one non-`Prop` definition (`innerSplitComponentKernel`, an ideal) and no new `Prop`-valued
definitions. It is used by `PQCompositionRegularityReduction`.

## Declarations

- `intertwiningMap_asAlgebraHom_apply`: an intertwining map `f : ρ → τ` of representations of
  a monoid `H` commutes with the group-algebra actions of `ℂ[B]` through any monoid map
  `φ : B → H`. Proof by induction on the group-algebra element.

- `leviInduction_groupAlgebraKernel_le`: let `P = MN` be a parabolic subgroup of `G`, and let
  `b : B ⟶ M` with `aG = b ≫ l ≫ p` such that every point `aG(t)` is central in `G(F)`. For every
  smooth representation `τ` of `M(F)`, the kernel in `ℂ[B(F)]` of the normalized induction
  `i^G_P(τ)` along `aG` is contained in the kernel of `τ` along `b`.

  Proof. The inducing representation of `P(F)` restricted along the central map `j : B(F) →
  P(F)` is `τ ∘ b`: the half modulus character is trivial on central elements
  (`closedHalfCharacter_eq_one_of_mem_center`), and the Levi projection of `j t` is `b t`. The
  induced representation restricted along `aG` is the smooth induction restricted along `j`.
  Evaluation at `1` is an intertwiner from the induced representation to the inducing one, for
  the central action (`Induction.centralEvaluation`). It is surjective
  (`Induction.smoothEvaluation_surjective`). So an element `c` that acts by zero on the induced
  representation acts by zero on `τ ∘ b`.

- `leviInduction_groupAlgebraKernel_eq`: under the same hypotheses the two kernels are
  equal. The reverse inclusion is the published `groupAlgebraKernel_le_leviInduction`
  (`PieceActionQuotientFiniteness`).

- `GeometricLemmaIntersectionDatum.innerSplitComponentKernel` (definition): for an
  intersection datum `D` at `z` and `b : A ⟶ L'`, the kernel in `ℂ[A(F)]` along `b` of the
  inner representation `e^*(r^M_{P'}(σ))` of `L'(F)`. Here `r^M_{P'}` is the normalized Jacquet
  functor (`leviJacquetFunctor`) and `e : L'(F) ≃ M'(F)` is the conjugation of `D`.

- `GeometricLemmaIntersectionDatum.pieceSplitComponentKernel_eq_inner`: if `a : A ⟶ M` is a
  split component and `b ≫ D.lQ' ≫ D.q' = a`, then
  `pieceSplitComponentKernel a D σ = D.innerSplitComponentKernel b σ`. The piece is
  `i^M_{Q'}` applied to the inner representation. `a` is central in `M`, so this is
  `leviInduction_groupAlgebraKernel_eq` for the parabolic `Q'` of `M`.

## Provenance

Derived. Renard invokes faithfulness of parabolic induction without proof (VII.3.5, printed
p.239 / PDF p.245; also the proof of the lemma VII.3.3). This module proves the special case
needed: kernels of a central subgroup's group algebra. The proof (evaluation at the identity)
is standard and not taken from Renard. Source: David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, literature ID
`renard-2026-representations-groupes-reductifs-padiques`.
