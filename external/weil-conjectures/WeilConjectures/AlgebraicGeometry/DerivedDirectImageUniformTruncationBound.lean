/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import WeilConjectures.AlgebraicGeometry.UniformDirectImageBoundCore
import WeilConjectures.AlgebraicGeometry.DirectImageTruncationTailBound
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Uniform truncation bound for derived direct image

Source: Stacks Project, Tag 08D5, part (2) and the final truncation argument
(blueprint: lem-pc-derived-direct-image-uniform-truncation-bound).
-/

@[expose] public section

universe u wX wS

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For a quasi-compact, quasi-separated morphism to a quasi-compact scheme, the
unbounded derived direct image has a uniform upper cohomological bound on objects of
`D_QCoh(𝒪_X)` with no positive cohomology. For every such derived object without the
upper-bound restriction, the canonical map to its sufficiently low lower truncation
induces an isomorphism on any fixed cohomology sheaf after derived direct image.
Source: Stacks Project, Tag 08D5, part (2) and proof
(blueprint: lem-pc-derived-direct-image-uniform-truncation-bound).

Proof:
1. By `lem-pc-finite-support-hi` (Tag 01XJ), choose a uniform bound on higher direct
   images of quasi-coherent modules, valid after base change, and enlarge it to a
   positive integer N. In particular it applies over every affine open U of S.
2. The higher direct images over U are quasi-coherent and vanish in degrees at least
   N. By `pqf-lem-affine-vanishing` and `lem-pc-leray-degenerate-sections`, the higher
   derived functors of sections over f⁻¹(U) vanish in those degrees on quasi-coherent
   modules. These are cohomology by `pqf-def-cohomology`. Sections commute with
   countable products by the universal property of products, since sections are
   Hom from the structure sheaf.
3. Apply `lem-pc-unbounded-derived-functor-cohomological-bound` with upper bound zero
   to derived sections over f⁻¹(U). By `lem-pc-derived-sections-pushforward-comparison`
   these equal derived sections of Rf_*E over U. Restrictions are computed using a
   K-injective representative, whose restriction stays K-injective by
   `lem-sc-derived-k-injective-restrict-open`. Vanishing on the affine basis makes
   the cohomology sheaf zero: it is the sheafification of the presheaf of cohomology
   of sections of a K-injective representative. This gives the uniform bound.
4. Use the standard truncation triangle from
   `def-sbc-standard-tstructure-derived-category`, with first term
   T = τ_{≤ -n-1}E. The shift T[-n-1] has no positive cohomology. By step 3 and shift
   compatibility of `lemma-coherent-base-change-invertible-sheaves`, H^j(Rf_*T) vanishes whenever
   j+n+1 ≥ N. For n ≥ N-q this kills both H^q(Rf_*T) and H^{q+1}(Rf_*T).
   The long exact cohomology sequence therefore makes the displayed canonical
   truncation map an isomorphism in degree q, for all sufficiently large n. -/
theorem exists_schemeDerivedDirectImage_uniform_truncation_bound
    {X S : Scheme.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] [CompactSpace S] :
    (∃ N : ℤ, 0 < N ∧
      ∀ E : schemeDerivedQCohCategory X,
        (∀ m : ℤ, 0 < m → IsZero
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) m).obj E.obj)) →
        ∀ m : ℤ, N ≤ m → IsZero ((schemeHigherDirectImage f m).obj E.obj)) ∧
    (∀ (E : schemeDerivedQCohCategory X) (q : ℤ),
      ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n →
        IsIso ((schemeHigherDirectImage f q).map
          ((DerivedCategory.TStructure.t.truncGEπ (-n)).app E.obj))) := by
  obtain ⟨N, hpos, hN⟩ := uniform_bound_core f
  refine ⟨⟨N, hpos, hN⟩, ?_⟩
  intro E q
  refine ⟨N - q, ?_⟩
  intro n hn
  let T := (schemeDerivedDirectImage f).mapTriangle.obj
    ((DerivedCategory.TStructure.t.triangleLTGE (-n)).obj E.obj)
  have hT : T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles :=
    (schemeDerivedDirectImage f).map_distinguished _
      (DerivedCategory.TStructure.t.triangleLTGE_distinguished (-n) E.obj)
  have hz : IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q).obj T.obj₁) :=
    directImage_truncation_tail_bound f N hN E n q (by omega)
  have hz' : IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (q + 1)).obj T.obj₁) :=
    directImage_truncation_tail_bound f N hN E n (q + 1) (by omega)
  change IsIso ((DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q).map T.mor₂)
  exact DerivedCategory.isIso_homologyMap_mor₂ T hT q (q + 1) rfl hz hz'

end AlgebraicGeometry
