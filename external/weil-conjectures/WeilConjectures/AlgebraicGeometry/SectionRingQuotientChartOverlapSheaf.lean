/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import WeilConjectures.AlgebraicGeometry.SectionRingChartDenominatorGenerator
import Mathlib.AlgebraicGeometry.Gluing

/-! # Sheaf components of section-ring quotient charts

Source: Stacks Project, Constructions, Tags 01N8 and 01NK, uniqueness arguments.
(blueprint: lem-sc-section-ring-quotient-chart-overlap-sheaf-map).
-/

@[expose] public section

universe v
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

private theorem fraction_equation_restrict
    (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (U : X.Opens) (g : U.toScheme ⟶ Proj (sectionRingGrade L))
    (r : ℕ) (a : sectionRingGrade L r) (n : ℕ)
    (ξ : sectionRingGrade L (n • r))
    (heq :
      (show Γ(X, U.ι ''ᵁ (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) a.val)) from
        g.app (Proj.basicOpen (sectionRingGrade L) a.val)
        (Proj.awayToSection (sectionRingGrade L) a.val
          (HomogeneousLocalization.Away.mk (sectionRingGrade L) a.property n
            ξ.val ξ.property))) •
        (L.tensorPow (n • r)).presheaf.map (homOfLE
          (le_top : U.ι ''ᵁ (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) a.val) ≤ ⊤)).op
          ((a.val ^ n) (n • r)) =
      (L.tensorPow (n • r)).presheaf.map (homOfLE
          (le_top : U.ι ''ᵁ (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) a.val) ≤ ⊤)).op
            (ξ.val (n • r)))
    (Q : X.Opens)
    (hQ : Q ≤ U.ι ''ᵁ (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) a.val)) :
    (X.presheaf.map (homOfLE hQ).op
      (g.app (Proj.basicOpen (sectionRingGrade L) a.val)
        (Proj.awayToSection (sectionRingGrade L) a.val
          (HomogeneousLocalization.Away.mk (sectionRingGrade L) a.property n
            ξ.val ξ.property)))) •
        (L.tensorPow (n • r)).presheaf.map (homOfLE (le_top : Q ≤ ⊤)).op
          ((a.val ^ n) (n • r)) =
      (L.tensorPow (n • r)).presheaf.map (homOfLE (le_top : Q ≤ ⊤)).op (ξ.val (n • r)) := by
  have h := congrArg ((L.tensorPow (n • r)).presheaf.map (homOfLE hQ).op) heq
  simpa [presheaf_map_map_apply] using h

-- The unchanged interface contains symmetric nonvanishing assumptions; the proof only needs U.
/-- After identifying the underlying maps, their pullbacks agree on every target open.
The equality includes the restriction transport induced by that identification.
Source: Stacks Project, Constructions, Tags 01N8 and 01NK, uniqueness arguments.
(blueprint: lem-sc-section-ring-quotient-chart-overlap-sheaf-map).

Proof: Write F and H for the two restrictions to U intersect V. Fix a point of
this overlap and a positive-degree homogeneous a of degree r whose chart contains
its common image under F and H. The fraction equations imply that a is
nonvanishing near the point: apply the equation with denominator a, exponent d
and numerator s^r (or exponent e and numerator t^r), and pass to the residue
field. A nonzero numerator forces the denominator power, and hence a, to be
nonvanishing. The locus is open, and a trivializes L^{tensor(r)} on it.
Restrict hg and hh to the intersection of the two inverse-image a-charts with
the overlap. Tensor powers of this free generator are free generators, so the
equations with denominator a imply equality of the scalar pullbacks of every
homogeneous fraction xi/a^n: both multiplied by a^n equal the restriction of xi.
For n = 0 the generator is the tensor unit and the same cancellation applies.
Every element of the degree-zero homogeneous localization S_(a) has such a
representative. Thus the induced ring maps from S_(a) to sections on this source
open agree. The affine morphism correspondence for D_+(a) identifies the two
restricted maps, including their sheaf components. These source opens cover the
overlap, so equality of pullbacks of any section on any target open follows by
sheaf locality on its inverse image. The equality of underlying maps identifies
these inverse images; in Lean the displayed eqToHom restriction is that transport.
Empty inverse images have unique sections. Nilpotents are retained: cancellation
uses a free generator, not reducedness or cancellation in the section ring. -/
theorem sectionRing_overlap_sheaf_map
    (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) (hd : 0 < d) (U V : X.Opens)
    (hU : (U : Set X) = nonvanishingLocus (L.tensorPow d) (s.val d))
    (g : U.toScheme ⟶ Proj (sectionRingGrade L))
    (h : V.toScheme ⟶ Proj (sectionRingGrade L))
    (hg : ∀ (e : ℕ), 0 < e → ∀ (t : sectionRingGrade L e)
          (n : ℕ) (ξ : sectionRingGrade L (n • e)),
          (show Γ(X, U.ι ''ᵁ (g ⁻¹ᵁ
              Proj.basicOpen (sectionRingGrade L) t.val)) from
            g.app (Proj.basicOpen (sectionRingGrade L) t.val)
            (Proj.awayToSection (sectionRingGrade L) t.val
              (HomogeneousLocalization.Away.mk (sectionRingGrade L) t.property n
                ξ.val ξ.property))) •
            (L.tensorPow (n • e)).presheaf.map (homOfLE
              (le_top : U.ι ''ᵁ (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
                ⊤)).op ((t.val ^ n) (n • e)) =
          (L.tensorPow (n • e)).presheaf.map (homOfLE
            (le_top : U.ι ''ᵁ (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
              ⊤)).op (ξ.val (n • e)))
    (hh : ∀ (e : ℕ), 0 < e → ∀ (t : sectionRingGrade L e)
          (n : ℕ) (ξ : sectionRingGrade L (n • e)),
          (show Γ(X, V.ι ''ᵁ (h ⁻¹ᵁ
              Proj.basicOpen (sectionRingGrade L) t.val)) from
            h.app (Proj.basicOpen (sectionRingGrade L) t.val)
            (Proj.awayToSection (sectionRingGrade L) t.val
              (HomogeneousLocalization.Away.mk (sectionRingGrade L) t.property n
                ξ.val ξ.property))) •
            (L.tensorPow (n • e)).presheaf.map (homOfLE
              (le_top : V.ι ''ᵁ (h ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
                ⊤)).op ((t.val ^ n) (n • e)) =
          (L.tensorPow (n • e)).presheaf.map (homOfLE
            (le_top : V.ι ''ᵁ (h ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
              ⊤)).op (ξ.val (n • e)))
    (hbase : (X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ g).base =
      (X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ h).base) :
    ∀ W, (X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ g).app W ≫
      (U ⊓ V).toScheme.presheaf.map
        (eqToHom congr((TopologicalSpace.Opens.map $hbase.symm).obj W)).op =
      (X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ h).app W := by
  let F := X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ g
  let H := X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ h
  have hlocal (r : ℕ) (a : sectionRingGrade L r) (hr : 0 < r) :
      (F ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) a.val).ι ≫ F =
        (F ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) a.val).ι ≫ H := by
    let C := Proj.basicOpen (sectionRingGrade L) a.val
    let P := F ⁻¹ᵁ C
    let Q := (U ⊓ V).ι ''ᵁ P
    have hP : P ≤ H ⁻¹ᵁ C := by
      change (TopologicalSpace.Opens.map F.base).obj C ≤
        (TopologicalSpace.Opens.map H.base).obj C
      rw [show F.base = H.base from hbase]
    have hQU : Q ≤ U.ι ''ᵁ (g ⁻¹ᵁ C) := by
      dsimp [Q, P, F]
      exact X.ι_image_homOfLE_le_ι_image inf_le_left _
    have hQV : Q ≤ V.ι ''ᵁ (h ⁻¹ᵁ C) := by
      exact ((U ⊓ V).ι.image_mono hP).trans
        (by
          change (U ⊓ V).ι ''ᵁ (H ⁻¹ᵁ C) ≤ _
          dsimp [H]
          exact X.ι_image_homOfLE_le_ι_image inf_le_right _)
    have hgen := sectionRing_chart_denominator_generator X L d s hd U hU g hg r a hr Q hQU
    have hmaps : F.appLE C P le_rfl = H.appLE C P hP := by
      have := Proj.basicOpenIsoAway (sectionRingGrade L) a.val a.property hr
      have : IsIso (Proj.awayToSection (sectionRingGrade L) a.val) := by
        change IsIso (Proj.basicOpenIsoAway (sectionRingGrade L) a.val a.property hr).hom
        infer_instance
      apply (cancel_epi (Proj.awayToSection (sectionRingGrade L) a.val)).mp
      ext z
      obtain ⟨n, ξ, hξ, rfl⟩ :=
        HomogeneousLocalization.Away.mk_surjective (sectionRingGrade L) a.property z
      apply (hgen n).smul_left_injective
      have hgu := fraction_equation_restrict X L U g r a n ⟨ξ, hξ⟩
        (hg r hr a n ⟨ξ, hξ⟩) Q hQU
      have hhv := fraction_equation_restrict X L V h r a n ⟨ξ, hξ⟩
        (hh r hr a n ⟨ξ, hξ⟩) Q hQV
      simp only [F, H, C, Q, Scheme.Hom.comp_appLE, Scheme.homOfLE_appLE,
        CommRingCat.hom_comp, RingHom.comp_apply]
      convert hgu.trans hhv.symm using 1
    have : IsAffine C.toScheme := (Proj.isAffineOpen_basicOpen
      (sectionRingGrade L) a.val a.property hr)
    have hres : F.resLE C P le_rfl = H.resLE C P hP := by
      apply ext_of_isAffine
      simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, hmaps]
    calc
      P.ι ≫ F = F.resLE C P le_rfl ≫ C.ι := (F.resLE_comp_ι le_rfl).symm
      _ = H.resLE C P hP ≫ C.ι := by rw [hres]
      _ = P.ι ≫ H := H.resLE_comp_ι hP
  have heq : F = H := by
    apply Scheme.hom_ext_of_forall
    intro x
    let i := (Proj.affineOpenCover (sectionRingGrade L)).idx (F x)
    have hx := (Proj.affineOpenCover (sectionRingGrade L)).covers (F x)
    have hxC : F x ∈ Proj.basicOpen (sectionRingGrade L) i.2.val := by
      change F x ∈ (Proj.awayι (sectionRingGrade L) i.2.val i.2.property i.1.property).opensRange
        at hx
      simpa only [Proj.opensRange_awayι] using hx
    exact ⟨F ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) i.2.val, hxC,
      hlocal i.1 i.2 i.1.property⟩
  change ∀ W, F.app W ≫ (U ⊓ V).toScheme.presheaf.map
    (eqToHom congr((TopologicalSpace.Opens.map $hbase.symm).obj W)).op = H.app W
  intro W
  have h := Scheme.Hom.congr_app heq W
  rw [h]
  simp only [Category.assoc, ← Functor.map_comp, ← op_comp, eqToHom_trans,
    eqToHom_refl, op_id]
  change H.app W ≫ X.presheaf.map (𝟙 _) = H.app W
  rw [CategoryTheory.Functor.map_id]
  exact Category.comp_id (H.app W)

end AlgebraicGeometry.Scheme.Modules
