# Proof of Renard VI.8.6: endomorphisms of a family with irreducible fibers

The theorem `Langlands.Renard.AlgebraicFamily.endomorphismScalar` proves the
published statement
[`EndomorphismScalarStatement.{uB, uG, uV}`](RenardFamilyEndomorphismStatement.md)
at three independent universes. It adds no hypothesis on `B`, `G`, `V`, `ρ`, `φ`
or `Ξ`. The proof needs only the standard axioms `propext`, `Classical.choice`
and `Quot.sound`.

## Relation to the source

Renard (VI.8.6, printed p. 195 / PDF p. 201) works on the fixed modules `V^K`.
They are finite projective by the VI.8.1 Proposition and free on the basic opens
of a finite cover by the VI.8.4 Theorem. On each such open, Schur's lemma and
density make the matrix of `φ` scalar. The local scalars are then glued, a step
the source does not write out (reading note 6 of
`notes/renard/algebraic-families-progress.md`).

The Lean proof takes a different route that avoids local freeness. It also
avoids the still-unproved VI.8.1 and VI.8.4 statements of
`RenardFamilyStatements`. Its ingredients are the following.

- `V^K` is a direct summand of `V`, hence finite projective.
- Linear forms `V →ₗ[B] B` separate vectors.
- Schur's lemma on the fibers at the points of `Ξ`, together with the
  Nullstellensatz, gives a linear relation between `φ` and the linear forms.
- The ideal `I ⊆ B` of values of linear forms contains an element `e` that acts
  as the identity on `V` (Nakayama's lemma).
- Writing `e` as a combination of values of linear forms produces the required
  `b`.

The gluing step of the source becomes this last algebraic step.

Each hypothesis of the statement is used as follows:

- `IsLocallyProfinite G` gives van Dantzig's theorem;
- smoothness is used for van Dantzig's theorem and for compact averaging;
- flatness of `V` and finiteness of each `V^K` make `V^K` projective;
- `IsNoetherianRing B` makes `V^K` finitely presented and `I` finitely
  generated;
- `Algebra.FiniteType ℂ B` and `IsReduced B` give the Nullstellensatz;
- density of `Ξ` and irreducibility of the fibers enter the relation between
  `φ` and the linear forms.

## Helper lemmas

All helpers are in the namespace `Langlands.Renard.AlgebraicFamily`.

- `exists_compact_mem_fixedVectors`: in a locally profinite group, every smooth
  vector is fixed by a compact open subgroup. A smooth vector is fixed by an
  open subgroup `L`. Van Dantzig's theorem, the published
  `Langlands.Topology.LocallyProfiniteProof.vanDantzig`, gives a compact open
  subgroup `K ≤ L`.
- `exists_fixedVectors_retraction`: for compact open `K`, there is a `B`-linear
  map `r : V → V^K` that restricts to the identity on `V^K`. Restricting scalars
  along `ℂ → B` (`Module.compHom` and the published
  `Jacquet.CoefficientRestriction.complexRepresentation`) gives a complex smooth
  representation. Its published compact average `Compact.averageMap` lands in
  `V^K` (`averageMap_mem_fixedVectors`) and is the identity there
  (`averageMap_id`). It commutes with multiplication by every `b : B`, since
  that multiplication is an intertwiner of the complex representation
  (`averageMap_commute`). Hence the average is `B`-linear.
- `projective_fixedVectors`: if `V` is flat and `V^K` is finite over the
  Noetherian ring `B`, then `V^K` is projective. A retract of a flat module is
  flat (`Module.Flat.of_retract`). Over a Noetherian ring a finite module is
  finitely presented, and a finitely presented flat module is projective
  (`Module.Flat.projective_of_finitePresentation`).
- `eq_zero_of_forall_linearForm`: if every linear form `ℓ : V →ₗ[B] B` kills
  `x`, then `x = 0`. Choose `K` fixing `x`. Linear forms on the projective
  module `V^K` separate points (`Module.forall_dual_apply_eq_zero_iff`). Each
  such form `f` extends to `f ∘ r` on `V`.
- `mem_linearFormIdeal_smul_top`: every `v` lies in `I • ⊤`, where `I` is
  `Ideal.span {a | ∃ ℓ x, ℓ x = a}` (written inline). Choose `K` fixing `v`.
  `Module.projective_def'` gives a dual basis `s : V^K → (V^K →₀ B)` of the
  projective module `V^K`. Then `v = ∑ₚ s (r v) p • p`, and each coefficient
  `s (r v) p` is the value at `v` of the linear form
  `Finsupp.lapply p ∘ s ∘ r`.
- `exists_mem_linearFormIdeal_smul_eq` (Nakayama): if every `v` lies in
  `I • ⊤`, some `e ∈ I` satisfies `e • v = v` for all `v`. First, `I ≤ I • I`:
  for a generator `ℓ x`, write `x ∈ I • ⊤`. Then `ℓ x` lies in
  `ℓ (I • ⊤) = I • ℓ(⊤) ≤ I • I` (`Submodule.map_smul''`). `I` is finitely
  generated since `B` is Noetherian. So
  `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul` gives `r`
  with `r - 1 ∈ I` and `r • I = 0`. Then `r • v = 0` for every `v ∈ I • ⊤`,
  and `e = 1 - r` works.
- `exists_eq_smul_of_linearForm_relation`: assume `ℓ x • φ m = ℓ (φ x) • m`
  for all `ℓ, x, m`, and some `e ∈ I` acts as the identity. Then `φ = b • id`
  for some `b`. By induction on `a ∈ I` (`Submodule.span_induction`), each
  `a ∈ I` has some `b_a` with `a • φ m = b_a • m` for all `m`. For a generator
  `ℓ x`, take `b_a = ℓ (φ x)`. Sums and multiples are handled by additivity.
  For `a = e`, `φ m = e • φ m = b_e • m`.
- `exists_fiber_scalar` (Schur's lemma at an irreducible fiber): let
  `χ : B →ₐ[ℂ] ℂ` have an irreducible fiber `W = ℂ ⊗[B] V`, with `φ`
  commuting with `ρ`. There is `c : ℂ` with `χ (ℓ (φ v)) = c * χ (ℓ v)` for
  all `ℓ` and `v`. The steps are:
  1. An irreducible representation is nonzero, so some `1 ⊗ v₀` is nonzero.
  2. Choose a compact open `K` fixing `v₀`. The map `ℂ ⊗[B] V^K → W` is
     injective because the base change of `r` is a left inverse.
  3. `ℂ ⊗[B] V^K` is a nonzero finite-dimensional complex space. By
     `Module.End.exists_eigenvalue`, the base change of the restriction of `φ`
     to `V^K` has an eigenvector. Its image in `W` is an eigenvector of
     `φ_W = φ.baseChange ℂ` with some eigenvalue `c`.
  4. `φ_W - c` is an intertwiner of the irreducible `W` with nonzero kernel,
     so it is zero by `Representation.IsIrreducible.injective_or_eq_zero`.
  5. Apply the `B`-linear map `ℂ ⊗[B] V → ℂ`, `z ⊗ w ↦ χ (ℓ w) z`, to
     `φ_W (1 ⊗ v) = c • (1 ⊗ v)`.

  Only admissibility (finite `V^K`) is used, with no countability or finite
  dimensionality of the fiber.

## Main theorem

`endomorphismScalar` introduces the binders of the statement and proceeds in
three steps.

1. **Separation by `Ξ`.** If `b` vanishes at every `χ ∈ Ξ`, density gives
   `χ b = 0` for all points. The published Nullstellensatz
   `GroupScheme.KostantRosenlicht.eq_zero_of_forall_algHom` then gives `b = 0`;
   it applies because `B` is reduced and of finite type over `ℂ`.
2. **Relation.** Fix `ℓ, x, m`. By `eq_zero_of_forall_linearForm`, it suffices
   that `ℓ' (ℓ x • φ m - ℓ (φ x) • m) = ℓ x * ℓ' (φ m) - ℓ (φ x) * ℓ' m`
   vanishes for every `ℓ'`. By step 1 it suffices to check this at each
   `χ ∈ Ξ`. There `exists_fiber_scalar` gives `c`, and the value is
   `χ (ℓ x) c χ (ℓ' m) - c χ (ℓ x) χ (ℓ' m) = 0`.
3. **Gluing.** `mem_linearFormIdeal_smul_top` and
   `exists_mem_linearFormIdeal_smul_eq` give `e ∈ I` acting as the identity.
   `exists_eq_smul_of_linearForm_relation` with the relation of step 2 then
   gives `b` with `φ v = b • v` for all `v`.

## Authorship

Worker 950 wrote the Lean proof and this explanation.
