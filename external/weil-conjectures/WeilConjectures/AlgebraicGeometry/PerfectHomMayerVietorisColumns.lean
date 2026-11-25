/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import WeilConjectures.AlgebraicGeometry.PerfectHomPushPullCocone
public import WeilConjectures.AlgebraicGeometry.PerfectHomMayerVietorisDiagram
public import WeilConjectures.AlgebraicGeometry.PerfectHomLocalComparison
public import WeilConjectures.AlgebraicGeometry.PerfectHomTriangleRow
import WeilConjectures.AlgebraicGeometry.PerfectHomMayerVietorisGeometricColumnsEven
import WeilConjectures.AlgebraicGeometry.PerfectHomMayerVietorisGeometricColumnsOdd

/-! # Local comparisons for the outer columns of geometric triangle diagrams

Source: Stacks Project, Tags 09RE and 08BW.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-geometric-columns).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Pretriangulated TopologicalSpace
namespace AlgebraicGeometry

/-- Outer-column recognition for the actual geometric Mayer--Vietoris construction.
The input consists of a representing cocone natural in every testing object and a
family whose outer objects and maps are explicitly open direct images and restrictions.
In particular this statement does not apply to arbitrary distinguished triangle cocones.
It asserts nothing about distinguishedness or the central Hom comparison.

Source: Stacks Project, perfect.tex Tag 09RE, Mayer--Vietoris induction;
cohomology.tex Tag 08BW.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-geometric-columns).

Proof:
1. Let U' and V' be the preimages under t, and W' their intersection. Since t is
   an open immersion with image U union V, the composites U'.toScheme -> X and
   V'.toScheme -> X have images U and V; the intersection has image U intersection V.
   These opens are compact: Y is qcqs over Spec(R_i), X is quasi-separated, and
   a morphism from a compact scheme to a quasi-separated scheme is quasi-compact.
   Their structural maps are locally finitely presented and qcqs. Pullback and
   restriction of P,Q are perfect, and so are their shifts by -1.
2. The stageEquiv maps and stageNatural identify F_j with Rpi_j* Lpi_j*Q by
   Yoneda and derived adjunction. The transition and cocone equations, for every
   testing object, identify the representing maps uniquely with the adjoints of
   perfectStageMap and perfectLimitMap. This identifies the whole cocone, not merely
   Hom from one fixed P. Restrict to each of the three opens using the canonical
   restriction/direct-image comparison; it is pinned by its right-derived unit.
   The underived comparison is restriction of sections, so the same Yoneda equations
   identify the restricted transition and cocone maps with canonical local transport.
3. The definition of A.triangle and the component formulas for A.map show that
   columns 1 and 4 are Hom into the intersection direct image, with shifts -1 and 0.
   Columns 0 and 3 are Hom into the two-open biproduct, with those same shifts.
   Open adjunction and the direct-image shift comparison give natural stage and
   apex equivalences to the restricted perfect Hom sets (or their binary products).
   This step uses only the outer components, so the choice of natural boundary and
   the choice of restriction adjunction do not affect the result.
4. Apply perfect_hom_stage_colimit to each restricted pair. The forgetful functor
   from abelian groups preserves filtered colimits. The stage equivalences therefore
   extend to equivalences of the source colimits, pinned on all stage inclusions.
   For the two-open terms filtered colimits of sets commute with binary products,
   giving the product of the two local colimits. The apex equivalences and the
   cocone equations identify each single comparison with PerfectHomLocalComparison.
   Use PerfectHomLocalMap.basic on U,V and U intersection V, prod on the two-open
   columns, and equiv for the adjunction, shift and colimit equivalences.
   Empty opens yield zero Hom groups and require no extra case or continuity claim. -/
theorem perfect_hom_mayerVietoris_geometric_columns
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (X : Scheme.{u}) (s₀ : X ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s₀] [QuasiCompact s₀] [QuasiSeparated s₀]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsAffineOpen V)
    (Y : Scheme.{u}) (t : Y ⟶ X) [IsOpenImmersion t]
    (ht : t.opensRange = U ⊔ V)
    (s : Y ⟶ Spec (R.obj i)) (hs : s = t ≫ s₀)
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ W : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))]
    (P Q : schemeDerivedCategory Y) (hP : Y.IsPerfect P) (hQ : Y.IsPerfect Q)
    (F : Set.Ici i ⥤ schemeDerivedCategory Y) (d : Cocone F)
    (h : PerfectHomPushPullData R c s Q F d)
    (A : PerfectHomMVFamily Y (t ⁻¹ᵁ U) (t ⁻¹ᵁ V)) :
    ∀ (r : Fin 5), r.val ≠ 2 →
      PerfectHomLocalMap R c i X s₀ U V
        (colimit.desc
          ((A.diagram F h.stageQCoh ⋙ perfectHomTriangleRowFunctor Y P).flip.obj r)
          ⟨(perfectHomTriangleRow Y P (A.cocone F d h.stageQCoh h.limitQCoh).pt).obj r,
            (perfectHomTriangleRowCoconeMap Y P (A.diagram F h.stageQCoh)
              (A.cocone F d h.stageQCoh h.limitQCoh)).app r⟩) := by
  intro r hr
  have cases : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 ∨ r.val = 3 ∨ r.val = 4 := by omega
  rcases cases with h0 | h1 | h2 | h3 | h4
  · apply perfect_hom_mayerVietoris_geometric_columns_even R c i X s₀ U V hU hV Y t ht s hs
      P Q hP hQ F d h A r
    exact Or.inl h0
  · apply perfect_hom_mayerVietoris_geometric_columns_odd R c i X s₀ U V hU hV Y t ht s hs
      P Q hP hQ F d h A r
    exact Or.inl h1
  · omega
  · apply perfect_hom_mayerVietoris_geometric_columns_even R c i X s₀ U V hU hV Y t ht s hs
      P Q hP hQ F d h A r
    exact Or.inr h3
  · apply perfect_hom_mayerVietoris_geometric_columns_odd R c i X s₀ U V hU hV Y t ht s hs
      P Q hP hQ F d h A r
    exact Or.inr h4

end AlgebraicGeometry
