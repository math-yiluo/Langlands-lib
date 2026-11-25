/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import WeilConjectures.AlgebraicGeometry.SectionRingSingleQuotientChart
import WeilConjectures.AlgebraicGeometry.SectionRingQuotientChartOverlap

/-! # Compatible local quotient morphisms for the section ring

Source: Stacks Project, Properties, Tag 01PZ; Constructions, Tags 01N8 and 01NK.
-/

@[expose] public section

universe v w
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Local quotient morphisms on nonvanishing opens agree on overlaps. Their fraction
identities are equations of sections on the ambient image of each local chart
preimage. No covering hypothesis or global morphism is asserted here.
Source: Stacks Project, Properties, Tag 01PZ, proof; Constructions, Tags 01N8 and 01NK.
(blueprint: lem-sc-ample-proj-compatible-quotient-charts).

Proof: A section of positive degree d trivializes L^{tensor d} on its nonvanishing
open. Its tensor powers therefore give unique division of degree nd sections by s^n.
These quotients respect the equivalence relation on homogeneous fractions: multiply
an equality by a sufficiently large power of s, then cancel the free generator.
Tensor multiplication gives a unital ring homomorphism from S_(s) to functions on
this open. The affine morphism correspondence and D_+(s) = Spec S_(s) give the local
morphism to Proj. For sections s,t of degrees d,e, the quotient t^d/s^e is invertible
exactly where t is nonvanishing, by the residue-field criterion and d > 0. Thus the
inverse image of D_+(t) is the intersection of the two nonvanishing opens. Both maps
on that intersection factor through D_+(st), where their ring maps send a/(st)^n
to the quotient by (st)^n. The identities a t^k/(st)^k = a/s^k and
b s^k/(st)^k = b/t^k prove agreement. For any other positive-degree chart t, the
same calculation on its inverse image gives the fraction identity with denominator
t, after restricting to the original open. All these statements hold on an empty
open, where sections are unique; n = 0 is the tensor-unit coefficient map. -/
theorem exists_sectionRing_compatible_quotient_charts
    (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (I : Type w) (d : I → ℕ) (s : ∀ i, sectionRingGrade L (d i))
    (hd : ∀ i, 0 < d i) (U : I → X.Opens)
    (hU : ∀ i, (U i : Set X) =
      nonvanishingLocus (L.tensorPow (d i)) ((s i).val (d i))) :
    ∃ g : ∀ i, (U i).toScheme ⟶ Proj (sectionRingGrade L),
      (∀ i j, X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ g i =
        X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ g j) ∧
      ∀ i (e : ℕ) (_he : 0 < e) (t : sectionRingGrade L e)
        (n : ℕ) (ξ : sectionRingGrade L (n • e)),
        (show Γ(X, (U i).ι ''ᵁ (g i ⁻¹ᵁ
            Proj.basicOpen (sectionRingGrade L) t.val)) from
          (g i).app (Proj.basicOpen (sectionRingGrade L) t.val)
          (Proj.awayToSection (sectionRingGrade L) t.val
            (HomogeneousLocalization.Away.mk (sectionRingGrade L) t.property n
              ξ.val ξ.property))) •
          (L.tensorPow (n • e)).presheaf.map (homOfLE
            (le_top : (U i).ι ''ᵁ (g i ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
              ⊤)).op ((t.val ^ n) (n • e)) =
        (L.tensorPow (n • e)).presheaf.map (homOfLE
          (le_top : (U i).ι ''ᵁ (g i ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
            ⊤)).op (ξ.val (n • e)) := by
  classical
  have hchart (i : I) :=
    exists_sectionRing_single_quotient_chart X L (d i) (s i) (hd i) (U i) (hU i)
  choose g hg using hchart
  refine ⟨g, ?_, hg⟩
  intro i j
  exact sectionRing_quotient_charts_overlap X L (d i) (d j) (s i) (s j)
    (hd i) (hd j) (U i) (U j) (hU i) (hU j) (g i) (g j) (hg i) (hg j)

end AlgebraicGeometry.Scheme.Modules
