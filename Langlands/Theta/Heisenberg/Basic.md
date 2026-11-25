# The Heisenberg group of a bilinear form

**GKT §1.1** (the Heisenberg group, 1.1.1, p. 17) and the action (2.1) of isometries (§2.1.1,
p. 47).

The module `Langlands.Theta.Heisenberg.Basic` defines the Heisenberg group of a bilinear form over
a commutative ring in which `2` is invertible, its centre, the action of isometries, and its
topology. It is the first layer of the subject `Langlands/Theta/`: the Stone–von Neumann theorem
over a nonarchimedean local field (`Theta/Heisenberg/StoneVonNeumann`), the Schrödinger
representations (`Theta/Heisenberg/Schrodinger`) and the Weil representations are stated on it.

This group is not the group `J¹(β, 𝔄)` of a simple stratum that
`Langlands.BushnellKutzko.HeisenbergRepresentationStatement` is about.

## Content

Let `R` be a commutative ring with `Invertible (2 : R)`, `W` an `R`-module and
`B : LinearMap.BilinForm R W`. `HeisenbergGroup B` is the set of pairs `⟨vec, cen⟩ ∈ W × R` with

`(w, t) · (w', t') = (w + w', t + t' + ½ B(w, w'))`, unit `(0, 0)`, inverse `(-w, -t + ½ B(w, w))`.

The group axioms use only the bilinearity of `B`. The elements `central t = (0, t)` commute with
everything and `central (s + t) = central s * central t`; every element is
`central g.cen * ofVec g.vec` with `ofVec w = (w, 0)`, and
`ofVec x * ofVec y = central (½ B(x, y)) * ofVec (x + y)`. When `B` is alternating,
`g h = central (B(g, h)) · h g` (`mul_eq_central_mul`), so `ofVec x` and `ofVec y` do not commute
when `B(x, y) ≠ 0` (for non-degenerate `B` the elements `central t` are therefore the whole
centre; that statement itself is not in the file). This is
the Heisenberg group of the symplectic module `(W, B)` in the form of Weil, *Sur certains groupes
d'opérateurs unitaires*, Acta Math. 111 (1964), chapter I, and of Mœglin–Vignéras–Waldspurger,
*Correspondances de Howe sur un corps p-adique*, chapter 2, section I (page references to be
added); the normalization `½ B` makes `(w, t) ↦ t` a section of the centre with `(w, 0)⁻¹ = (-w, 0)`.

An `R`-linear automorphism `e` of `W` with `B(e x, e y) = B(x, y)` acts by the group automorphism
`mapEquiv e he : (w, t) ↦ (e w, t)`, which fixes the centre; `mapEquiv` is compatible with
composition (`mapEquiv_trans`) and the identity (`mapEquiv_refl`). For the isometry group
`LinearMap.BilinForm.isometryGroup B` (`Langlands/LinearAlgebra/Symplectic.lean`) this is the
homomorphism `isometryAction B : isometryGroup B →* MulAut (HeisenbergGroup B)`, the action (2.1)
of GKT, trivial on the centre (`isometryAction_central`).

With topologies on `R` and `W`, the group carries the topology induced by `(vec, cen)`, so that
`homeomorphProd : HeisenbergGroup B ≃ₜ W × R`. It is a topological group as soon as `R` is a
topological ring, `W` a topological group and `(x, y) ↦ B(x, y)` continuous
(`isTopologicalGroup`); for a finite module with its module topology over a topological ring the
continuity of `B` is automatic, and the group is a topological group by an instance (this covers
finite-dimensional spaces over local fields and the adèles).

## Source and licence

Lines 11–51 and 543–554 of
`src/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean`
of the repository <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`
(structure `Heisenberg`, its group law, topology, `mul_eq_central_mul`, `mul_ne_mul`,
`Heisenberg.isTopologicalGroup`). The repository has no licence file; the text is used with
attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespace `GlobalTheory.Published.Heisenberg` → `Langlands.HeisenbergGroup`; the structure
  `Heisenberg B` → `HeisenbergGroup B` (fields `vec`, `cen` unchanged).
- Over a commutative ring with `[Invertible (2 : R)]` in place of a field with `(2 : F) ≠ 0`; the
  law is written with `⅟2 *` in place of `/ 2`, and the proof of `mul_eq_central_mul` uses
  `⅟2 + ⅟2 = 1` in place of `field_simp`. The hypothesis `h2` of `mul_eq_central_mul` and
  `mul_ne_mul` disappears.
- `mul_ne_mul` is stated as `not_commute_ofVec`.
- `isTopologicalGroup` is proved from the continuity of `B` alone (the source proved it for a
  finite-dimensional space over a nonarchimedean local field, by the same computation); the
  finite-module case is an instance.
- Universes: `R` and `W` are in arbitrary universes (the source: `Type`).
- New: `central`, `ofVec` and their lemmas, `central_mul_ofVec`, `ofVec_mul_ofVec`,
  `central_add`, `central_mul_comm`, `mapEquiv` and its lemmas, `isometryAction` and its lemmas,
  `homeomorphProd`,
  `continuous_vec`, `continuous_cen`, `continuous_mk`, `continuous_ofVec`, `continuous_central`.

## Declarations

- `HeisenbergGroup B` (structure, `@[ext]`), fields `vec`, `cen`; `instance : Group`.
- `mul_vec`, `mul_cen`, `one_vec`, `one_cen`, `inv_vec`, `inv_cen` (simp).
- `central`, `ofVec`, `central_vec`, `central_cen`, `ofVec_vec`, `ofVec_cen`, `central_zero`,
  `ofVec_zero`, `central_add`, `central_mul_comm`, `central_mul_ofVec`, `ofVec_mul_ofVec`.
- `mul_eq_central_mul`, `not_commute_ofVec`.
- `mapEquiv`, `mapEquiv_apply`, `mapEquiv_central`, `mapEquiv_ofVec`, `mapEquiv_refl`,
  `mapEquiv_trans`.
- `isometryAction`, `isometryAction_apply`, `isometryAction_central`, `isometryAction_ofVec`.
- `instance : TopologicalSpace`, `homeomorphProd`, `homeomorphProd_apply`, `continuous_vec`,
  `continuous_cen`, `continuous_mk`, `continuous_ofVec`, `continuous_central`,
  `isTopologicalGroup`, `instance : IsTopologicalGroup` (finite module, module topology).

## Dependencies

`Langlands.LinearAlgebra.Symplectic`; Mathlib: `Algebra.Group.MinimalAxioms`, `LinearAlgebra.BilinearForm.Properties`,
`Topology.Algebra.Module.ModuleTopology`, `Tactic.LinearCombination`.
