/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveAffineTargetNoetherian
import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveAffineTargetApproximation

/-!
# Affineness of a finite surjective image

Source: literature/stacks-project/limits.tex, Limits, Lemma 01ZT (label lemma-affine)
(blueprint: lem-weil-pbc-finite-surjective-affine-target).
-/

@[expose] public section

universe u

open CategoryTheory
namespace AlgebraicGeometry

/-- If a finite morphism is surjective and its source is affine, then its target is affine.
Source: Stacks Project, Limits, Lemma 01ZT (label lemma-affine), with proof by
Noetherian approximation and the Noetherian case.
(blueprint: lem-weil-pbc-finite-surjective-affine-target).

Proof (the node's nine steps, with `Y` denoting its `S`):
1. The structure maps to Spec ℤ compose uniquely. Since X is affine it is quasi-compact
   and separated; surjectivity makes Y quasi-compact. Finiteness implies integrality and
   universal closedness, so separatedness descends to Y. Its closed diagonal is affine
   and quasi-compact, hence Y is quasi-separated
   [lem-weil-pbc-morphism-into-affine-scheme, lem-weil-pbc-affine-morphism-permanence,
   lem-weil-pbc-qcqs-over-affine, def-weil-surjective-morphism,
   lem-weil-pbc-finite-iff-integral-lft, pqf-lem-integral-univclosed,
   lem-weil-pbc-surjective-universally-closed-separated,
   lem-weil-pbc-closed-immersion-integral-separated-uc, definition-ind-etale-pro-etale-weakly--3].
2. Express the integral f as a directed limit of finite, finitely presented Y-schemes
   with affine transitions. These schemes are qcqs; since their limit X is affine,
   some stage is affine. Its map to Y is surjective since f factors through it.
   Replace X and f by that stage to assume finite presentation
   [lem-weil-pbc-integral-morphism-limit-of-finite, def-weil-finite-integral-morphism,
   lem-weil-pbc-affine-morphism-permanence, lem-weil-pbc-qcqs-morphism-permanence,
   lem-weil-pbc-limit-affine-stage, def-weil-surjective-morphism].
3. Approximate qcqs Y by schemes Y_i of finite type over ℤ with affine transitions,
   and reindex by a nonempty directed set. Each Y_i is Noetherian and qcqs
   [theorem-nagata-s-compactification-theorem--1, theorem-nagata-s-compactification-theorem--1,
   lem-weil-pbc-cofiltered-limit-directed-reindex, lem-weil-pbc-finite-type-over-noetherian,
   pqf-def-locnoeth, lem-weil-pbc-locally-noetherian-quasi-separated].
4. Descend f to a finitely presented g₀ : X₀ → Y₀. Restrict to the cofinal tail and
   set X_i = X₀ ×_{Y₀} Y_i. These are qcqs with affine transitions, and their limit
   is X, compatibly with f
   [proposition-jacobian-over-ground-field--1, def-sbc-locally-finite-presentation,
   def-pc-fibre-product, lem-weil-pbc-colimit-initial-full-subcategory,
   lem-weil-pbc-scheme-over-limit, lem-weil-pbc-qcqs-morphism-permanence].
5. Descend finiteness of f to some g_i; finite presentation supplies local finite type.
   All later g_i are finite by base change
   [def-sbc-locally-finite-presentation, def-weil-finite-type-morphism,
   lem-weil-pbc-descend-finite, def-pc-fibre-product,
   lem-weil-pbc-finite-morphism-permanence].
6. Descend surjectivity of f to some g_i using local finite presentation. All later
   g_i are surjective by base change. This supplies a step implicit in Stacks' proof
   [lem-weil-pbc-descend-surjective, lem-weil-pbc-surjective-base-change].
7. Since the limit X is affine, the qcqs X_i are affine for all sufficiently large i
   [def-pc-scheme, lem-weil-pbc-limit-affine-stage].
8. Choose a common upper bound for these three stages. Then g_i is finite and
   surjective, X_i is affine, and Y_i is Noetherian. The Noetherian case makes Y_i affine
   [lem-weil-pbc-finite-surjective-affine-target-noetherian].
9. The projection Y → Y_i is affine because the transition maps are affine; its target
   is affine, so Y is affine
   [lem-weil-pbc-limit-affine-transition, lem-weil-pbc-affine-morphism-permanence]. -/
theorem isAffine_of_isFinite_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [Surjective f] [IsAffine X] : IsAffine Y := by
  obtain ⟨a⟩ := exists_noetherian_affine_factor f
  have : IsNoetherian a.Z := a.noetherian_Z
  have : IsFinite a.g := a.finite_g
  have : Surjective a.g := a.surjective_g
  have : IsAffine a.W := a.affine_W
  have : IsAffine a.Z := isAffine_of_isFinite_surjective_of_isNoetherian a.g
  have : IsAffineHom a.q := a.affine_q
  exact isAffine_of_isAffineHom a.q

end AlgebraicGeometry
