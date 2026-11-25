/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineProjChartIsomorphism
import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.TensorObj
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible

/-!
# Standard generators of the transported polynomial Proj twist

Source: Stacks Project, Constructions, Lemma 01M7 (2),(3), and the chart and
transition steps of blueprint lem-sc-p1-proj-shifted-free-twist.
(blueprint: lem-sc-p1-proj-twist-transported-data)
-/

@[expose] public section

universe v

open CategoryTheory

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem chart_preimage (k : Type v) [Field k]
    (C : ProjectiveLine.ProjChartIsomorphism k) (i : ULift.{v} (Fin 2)) :
    C.iso.inv ⁻¹ᵁ basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k)
        (MvPolynomial.X i.down) = ProjectiveSpace.standardOpen _ (Spec (.of k)) i := by
  classical
  have hcov : (⨆ i : ULift.{v} (Fin 2),
      basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X i.down)) =
        ⊤ := by
    have h := iSup_basicOpen_eq_top' (MvPolynomial.homogeneousSubmodule (Fin 2) k)
      MvPolynomial.X (fun i ↦ ⟨1, MvPolynomial.isHomogeneous_X k i⟩)
      (MvPolynomial.adjoin_range_X_eq_top (Fin 2) k)
    refine top_le_iff.mp fun x hx ↦ ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (h.ge hx)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩
  have hp : C.iso.hom = linearProjection (MvPolynomial.homogeneousSubmodule (Fin 2) k)
      (fun j : ULift.{v} (Fin 2) ↦ MvPolynomial.X j.down)
      (fun j ↦ MvPolynomial.X_mem_homogeneousSubmodule_one k j.down) hcov := by
    apply (linearCover (MvPolynomial.homogeneousSubmodule (Fin 2) k)
      (fun j : ULift.{v} (Fin 2) ↦ MvPolynomial.X j.down)
      (fun j ↦ MvPolynomial.X_mem_homogeneousSubmodule_one k j.down) hcov).hom_ext
    intro j
    exact (C.chart_eq j).trans (awayι_linearProjection _ _ _ hcov j).symm
  have h := linearProjection_preimage_standardOpen
    (MvPolynomial.homogeneousSubmodule (Fin 2) k)
    (fun j : ULift.{v} (Fin 2) ↦ MvPolynomial.X j.down)
    (fun j ↦ MvPolynomial.X_mem_homogeneousSubmodule_one k j.down) hcov i
  rw [← hp] at h
  rw [← h, ← Scheme.Hom.comp_preimage, C.iso.inv_hom_id, Scheme.Hom.id_preimage]


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma appLE_congr {X Y : Scheme.{v}} {f g : X ⟶ Y} (h : f = g)
    (U V e) : f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem chart_coordinate (k : Type v) [Field k]
    (C : ProjectiveLine.ProjChartIsomorphism k) (i j : ULift.{v} (Fin 2)) :
    let A := MvPolynomial.homogeneousSubmodule (Fin 2) k
    let r := HomogeneousLocalization.Away.mk A
      (MvPolynomial.X_mem_homogeneousSubmodule_one k i.down) 1
      (MvPolynomial.X j.down) (by simpa only [one_smul] using
        MvPolynomial.X_mem_homogeneousSubmodule_one k j.down)
    C.iso.inv.appLE (basicOpen A (MvPolynomial.X i.down))
      (ProjectiveSpace.standardOpen _ (Spec (.of k)) i) (chart_preimage k C i).ge
        (awayToSection A (MvPolynomial.X i.down) r) =
      ProjectiveSpace.coordRatio _ (Spec (.of k)) i j := by
  classical
  dsimp only
  let A := MvPolynomial.homogeneousSubmodule (Fin 2) k
  let U := basicOpen A (MvPolynomial.X i.down)
  let V := ProjectiveSpace.standardOpen _ (Spec (.of k)) i
  let a := awayι A (MvPolynomial.X i.down)
    (MvPolynomial.X_mem_homogeneousSubmodule_one k i.down) Nat.one_pos
  have ha : ⊤ ≤ a ⁻¹ᵁ U := by
    dsimp only [U, a]
    rw [← opensRange_awayι A _ (MvPolynomial.X_mem_homogeneousSubmodule_one k i.down)
      Nat.one_pos]
    exact (Scheme.Hom.preimage_opensRange _).ge
  have hp : U ≤ C.iso.hom ⁻¹ᵁ V := by
    dsimp only [U, V, A]
    rw [← chart_preimage k C i, ← Scheme.Hom.comp_preimage, C.iso.hom_inv_id]
    simp
  have hv : ⊤ ≤ (a ≫ C.iso.hom) ⁻¹ᵁ V :=
    ha.trans (a.preimage_mono hp)
  have hc := ProjectiveSpace.homOfSections_appLE_coordRatio
    (a ≫ toSpecBase A)
    (linearChartSection A (fun l : ULift.{v} (Fin 2) ↦ MvPolynomial.X l.down)
      (fun l ↦ MvPolynomial.X_mem_homogeneousSubmodule_one k l.down) i)
    (span_range_linearChartSection A _ _ i)
    (linearChartSection_self A _ _ i) j
    (show ⊤ ≤ linearChartHom A
      (fun l : ULift.{v} (Fin 2) ↦ MvPolynomial.X l.down)
      (fun l ↦ MvPolynomial.X_mem_homogeneousSubmodule_one k l.down) i ⁻¹ᵁ V by
        rw [← C.chart_eq i]; exact hv)
  have he := awayToSection_awayι_appLE A
    (MvPolynomial.X_mem_homogeneousSubmodule_one k i.down) Nat.one_pos
  have : IsIso (awayToSection A (MvPolynomial.X i.down)) := by
    change IsIso (basicOpenIsoAway A (MvPolynomial.X i.down)
      (MvPolynomial.X_mem_homogeneousSubmodule_one k i.down) Nat.one_pos).hom
    infer_instance
  have : IsIso (a.appLE U ⊤ ha) := by
    rw [← IsIso.eq_inv_comp] at he
    rw [he]
    infer_instance
  have hh : C.iso.hom.appLE V U hp ≫ a.appLE U ⊤ ha =
      (a ≫ C.iso.hom).appLE V ⊤ hv := by
    rw [Scheme.Hom.appLE_comp_appLE]
  have hforward : C.iso.hom.appLE V U hp
      (ProjectiveSpace.coordRatio _ (Spec (.of k)) i j) =
      awayToSection A (MvPolynomial.X i.down)
        (HomogeneousLocalization.Away.mk A
          (MvPolynomial.X_mem_homogeneousSubmodule_one k i.down) 1
          (MvPolynomial.X j.down) (by simpa only [one_smul] using
            MvPolynomial.X_mem_homogeneousSubmodule_one k j.down)) := by
    apply (ConcreteCategory.bijective_of_isIso (a.appLE U ⊤ ha)).1
    rw [← CommRingCat.comp_apply, hh]
    rw [appLE_congr (C.chart_eq i)]
    rw [← CommRingCat.comp_apply, he]
    exact hc
  rw [← hforward, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
    appLE_congr C.iso.inv_hom_id]
  change (Scheme.Hom.appLE (𝟙 _) V V le_rfl) _ = _
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
  change ((ProjectiveLine (Spec (.of k))).presheaf.map (𝟙 _)) _ = _
  rw [CategoryTheory.Functor.map_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem polynomial_transition (R : Type v) [CommRing R] (n : Type) (i j : n) (d : ℤ) :
    let A := MvPolynomial.homogeneousSubmodule n (R)
    let U := Proj.basicOpen A (MvPolynomial.X i) ⊓ Proj.basicOpen A (MvPolynomial.X j)
    ∃ c : Γ(Proj A, U)ˣ,
      c.val = (Proj A).presheaf.map (homOfLE inf_le_right).op
        (Proj.awayToSection A (MvPolynomial.X j) (HomogeneousLocalization.Away.mk A
          (MvPolynomial.X_mem_homogeneousSubmodule_one R j) 1 (MvPolynomial.X i)
          (by simpa only [A, one_smul] using
            MvPolynomial.X_mem_homogeneousSubmodule_one R i))) ∧
      (Proj.twist A d).presheaf.map (homOfLE inf_le_left).op
          (Proj.twistPowSection d (MvPolynomial.X_mem_homogeneousSubmodule_one _ i)) =
        (c ^ d).val • (Proj.twist A d).presheaf.map (homOfLE inf_le_right).op
          (Proj.twistPowSection d (MvPolynomial.X_mem_homogeneousSubmodule_one _ j)) := by
  classical
  dsimp only
  let A := MvPolynomial.homogeneousSubmodule n (R)
  let U := Proj.basicOpen A (MvPolynomial.X i) ⊓ Proj.basicOpen A (MvPolynomial.X j)
  let r : Γ(Proj A, U) := (Proj A).presheaf.map (homOfLE inf_le_right).op
    (Proj.awayToSection A (MvPolynomial.X j) (HomogeneousLocalization.Away.mk A
          (MvPolynomial.X_mem_homogeneousSubmodule_one R j) 1 (MvPolynomial.X i)
          (by simpa only [A, one_smul] using
            MvPolynomial.X_mem_homogeneousSubmodule_one R i)))
  let s : Γ(Proj A, U) := (Proj A).presheaf.map (homOfLE inf_le_left).op
    (Proj.awayToSection A (MvPolynomial.X i) (HomogeneousLocalization.Away.mk A
          (MvPolynomial.X_mem_homogeneousSubmodule_one R i) 1 (MvPolynomial.X j)
          (by simpa only [A, one_smul] using
            MvPolynomial.X_mem_homogeneousSubmodule_one R j)))
  have hr (x : U) : (r.1 x).val = Localization.mk (MvPolynomial.X i)
      ⟨MvPolynomial.X j, x.2.2⟩ := by
    change ((Proj.awayToSection A (MvPolynomial.X j)
      (HomogeneousLocalization.Away.mk A
          (MvPolynomial.X_mem_homogeneousSubmodule_one R j) 1 (MvPolynomial.X i)
          (by simpa only [A, one_smul] using
            MvPolynomial.X_mem_homogeneousSubmodule_one R i))).1 ⟨x.1, x.2.2⟩).val = _
    erw [ProjectiveSpectrum.Proj.awayToSection_apply]
    rw [HomogeneousLocalization.Away.val_mk,
      Localization.mk_eq_mk', IsLocalization.map_mk', RingHom.id_apply,
      ← Localization.mk_eq_mk']
    simp
  have hs (x : U) : (s.1 x).val = Localization.mk (MvPolynomial.X j)
      ⟨MvPolynomial.X i, x.2.1⟩ := by
    change ((Proj.awayToSection A (MvPolynomial.X i)
      (HomogeneousLocalization.Away.mk A
          (MvPolynomial.X_mem_homogeneousSubmodule_one R i) 1 (MvPolynomial.X j)
          (by simpa only [A, one_smul] using
            MvPolynomial.X_mem_homogeneousSubmodule_one R j))).1 ⟨x.1, x.2.1⟩).val = _
    erw [ProjectiveSpectrum.Proj.awayToSection_apply]
    rw [HomogeneousLocalization.Away.val_mk,
      Localization.mk_eq_mk', IsLocalization.map_mk', RingHom.id_apply,
      ← Localization.mk_eq_mk']
    simp
  have hrs : r * s = 1 := by
    apply Subtype.ext
    funext x
    apply HomogeneousLocalization.val_injective
    change (r.1 x * s.1 x).val =
      (1 : HomogeneousLocalization A x.1.asHomogeneousIdeal.toIdeal.primeCompl).val
    rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one]
    rw [hr, hs, Localization.mk_mul, ← Localization.mk_one,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]; ring⟩
  let c : Γ(Proj A, U)ˣ := ⟨r, s, hrs, by rw [mul_comm, hrs]⟩
  refine ⟨c, rfl, ?_⟩
  apply Subtype.ext
  funext x
  apply Subtype.ext
  rw [Proj.coe_twist_smul_apply, Proj.twist_presheaf_map_apply,
    Proj.twist_presheaf_map_apply, Proj.val_twistPowSection_apply,
    Proj.val_twistPowSection_apply]
  cases d with
  | ofNat m =>
    change Localization.mk (MvPolynomial.X i ^ (m : ℤ).toNat) _ =
      (r.1 x ^ m).val * Localization.mk (MvPolynomial.X j ^ (m : ℤ).toNat) _
    rw [HomogeneousLocalization.val_pow, hr, Localization.mk_pow, Localization.mk_mul,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul]
    change MvPolynomial.X j ^ m * MvPolynomial.X j ^ (-Int.ofNat m).toNat *
      MvPolynomial.X i ^ m = MvPolynomial.X i ^ (-Int.ofNat m).toNat *
        (MvPolynomial.X i ^ m * MvPolynomial.X j ^ m)
    have h : (-Int.ofNat m).toNat = 0 := Int.toNat_of_nonpos (neg_nonpos.mpr (Int.natCast_nonneg m))
    rw [h, pow_zero, pow_zero, mul_one, one_mul]
    exact mul_comm _ _
  | negSucc m =>
    simp only [Int.negSucc_eq, zpow_neg]
    change Localization.mk (MvPolynomial.X i ^ (-(m + 1 : ℕ) : ℤ).toNat) _ =
      (s.1 x ^ (m + 1)).val *
        Localization.mk (MvPolynomial.X j ^ (-(m + 1 : ℕ) : ℤ).toNat) _
    rw [HomogeneousLocalization.val_pow, hs, Localization.mk_pow, Localization.mk_mul,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul]
    simp only [SubmonoidClass.coe_pow, Int.toNat_neg_natCast, pow_zero, mul_one]
    have h : (- -(↑m + 1 : ℤ)).toNat = m + 1 := by omega
    rw [h]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The overlap relation for the pulled-back polynomial twist generators.
Source: Stacks Project, Constructions, Lemma 01M7 (2),(3).
(blueprint: lem-sc-p1-proj-twist-transported-data).
This is the chart and integer-power calculation: transport the identity
`x₀^d = (x₀/x₁)^d x₁^d` through the inverse chart isomorphism and identify
`x₀/x₁` with the projective-line transition unit using `C.chart_eq`.
-/
private theorem transported_map_g₀ (k : Type v) [Field k] (d : ℤ)
    (C : ProjectiveLine.ProjChartIsomorphism k) :
    let M := twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) d
    let N := (Scheme.Modules.pullback C.iso.inv).obj M
    let g (i : ULift.{v} (Fin 2)) : Γ(N,
        ProjectiveSpace.standardOpen _ (Spec (.of k)) i) :=
      N.presheaf.map (homOfLE (chart_preimage k C i).ge).op
        (Scheme.Modules.pullbackSection C.iso.inv
          (twistPowSection d (MvPolynomial.X_mem_homogeneousSubmodule_one k i.down)))
    N.presheaf.map (homOfLE inf_le_left).op (g ⟨0⟩) =
      (ProjectiveSpace.transitionUnit (ULift.{v} (Fin 2)) (Spec (.of k)) d ⟨0⟩ ⟨1⟩).1 •
        N.presheaf.map (homOfLE inf_le_right).op (g ⟨1⟩) := by
  classical
  dsimp only
  let M := twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) d
  let N := (Scheme.Modules.pullback C.iso.inv).obj M
  let A := MvPolynomial.homogeneousSubmodule (Fin 2) k
  let U := basicOpen A (MvPolynomial.X (0 : Fin 2)) ⊓
    basicOpen A (MvPolynomial.X (1 : Fin 2))
  let V := ProjectiveSpace.standardOpen (ULift.{v} (Fin 2)) (Spec (.of k)) ⟨0⟩ ⊓
    ProjectiveSpace.standardOpen (ULift.{v} (Fin 2)) (Spec (.of k)) ⟨1⟩
  have hV : V ≤ C.iso.inv ⁻¹ᵁ U := by
    rw [Scheme.Hom.preimage_inf, chart_preimage k C ⟨0⟩, chart_preimage k C ⟨1⟩]
  obtain ⟨c, hc, htrans⟩ := polynomial_transition k (Fin 2) 0 1 d
  have hcoeff : C.iso.inv.appLE U V hV c.val =
      ProjectiveSpace.ratio (ULift.{v} (Fin 2)) (Spec (.of k)) ⟨0⟩ ⟨1⟩ := by
    rw [hc]
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    have h := chart_coordinate k C ⟨1⟩ ⟨0⟩
    have h' := congrArg (fun z ↦ (ProjectiveLine (Spec (.of k))).presheaf.map
      (homOfLE (inf_le_right : V ≤ ProjectiveSpace.standardOpen _ (Spec (.of k)) ⟨1⟩)).op z) h
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map] at h'
    convert h' using 1
    simp only [ProjectiveSpace.ratio, ProjectiveSpace.coordRatio,
      ProjectiveSpace.awayRatio, MvPolynomial.awayXRatio, Scheme.Hom.appLE,
      CommRingCat.comp_apply]
    rfl
  have hpow : C.iso.inv.appLE U V hV (c ^ d).val =
      (ProjectiveSpace.transitionUnit (ULift.{v} (Fin 2)) (Spec (.of k)) d ⟨0⟩ ⟨1⟩).val := by
    change (Units.map (C.iso.inv.appLE U V hV).hom.toMonoidHom (c ^ d)).val = _
    have hu : Units.map (C.iso.inv.appLE U V hV).hom.toMonoidHom c =
        ProjectiveSpace.ratioUnit (ULift.{v} (Fin 2)) (Spec (.of k)) ⟨0⟩ ⟨1⟩ :=
      Units.ext hcoeff
    rw [map_zpow, hu]
    rfl
  have h := congrArg (Scheme.Modules.pullbackSection C.iso.inv) htrans
  rw [Scheme.Modules.pullbackSection_map, Scheme.Modules.pullbackSection_smul,
    Scheme.Modules.pullbackSection_map] at h
  have h' := congrArg (N.presheaf.map (homOfLE hV).op) h
  rw [Scheme.Modules.map_smul, Scheme.Modules.presheaf_map_homOfLE_map_homOfLE,
    Scheme.Modules.presheaf_map_homOfLE_map_homOfLE] at h'
  change N.presheaf.map _ _ = _ • N.presheaf.map _ _ at h'
  rw [show (ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE hV).op
      (C.iso.inv.app U (c ^ d).val) =
        C.iso.inv.appLE U V hV (c ^ d).val from rfl, hpow] at h'
  simpa only [Scheme.Modules.presheaf_map_homOfLE_map_homOfLE] using h'


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transporting the polynomial Proj twist to the glued line gives the prescribed
local generators and transition relation; no comparison with another module is asserted.
Source: Stacks Project, Constructions, Lemma 01M7 (2),(3), and blueprint
lem-sc-p1-proj-shifted-free-twist, chart and overlap steps.
(blueprint: lem-sc-p1-proj-twist-transported-data)

Proof: write P = Proj k[x₀,x₁], Q = P¹_k, and M = O_P(d). On D₊(xᵢ), a section
of M is locally a homogeneous fraction of degree d. The element xᵢ is a unit in
the homogeneous localization. Its d-th power therefore makes sense for every integer d.
Multiplication by xᵢ^(-d) identifies the degree-d part with the degree-zero part,
with inverse multiplication by xᵢ^d. The fraction descriptions are compatible with
restriction, so these inverse maps identify M with the structure module on every
subopen of D₊(xᵢ), and xᵢ^d is its generator.
The equations C.chart_eq identify D₊(xᵢ) with the i-th standard chart of Q, and
identify x₁/x₀ with t. Pullback along C.iso.inv preserves these trivializations
and their free generators.
The induced structure-ring maps are isomorphisms on corresponding opens. On each of these
charts it sends the displayed free rank-one module to the free rank-one structure
module. Take gᵢ to be the image of xᵢ^d under this operation. For every subopen V
of the i-th chart the pulled-back trivializations give bijectivity of
a ↦ a • gᵢ|_V (Scheme.Modules.IsFreeGenerator.pullback_unit_app).
On the overlap, both x₀ and x₁ are units, and the identity
x₀^d = (x₀/x₁)^d x₁^d holds for all integer d. Transporting this equality along
the same ring and module maps gives g₀ = transitionUnit(d,0,1) • g₁.
These sections, the two bijectivity statements, and this equality are exactly the
five fields of TwistData. At d = 0 the generators are 1; at negative d the same
argument uses inverse powers of units, so no positivity hypothesis is needed. -/
theorem nonempty_twistData_pullback_inv (k : Type v) [Field k]
    (d : ℤ) (C : ProjectiveLine.ProjChartIsomorphism k) :
    Nonempty (ProjectiveLine.TwistData (Spec (.of k)) d
      ((Scheme.Modules.pullback C.iso.inv).obj
        (twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) d))) := by
  classical
  let M := twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) d
  let N := (Scheme.Modules.pullback C.iso.inv).obj M
  let g (i : ULift.{v} (Fin 2)) : Γ(N,
      ProjectiveSpace.standardOpen _ (Spec (.of k)) i) :=
    N.presheaf.map (homOfLE (chart_preimage k C i).ge).op
      (Scheme.Modules.pullbackSection C.iso.inv
        (twistPowSection d (MvPolynomial.X_mem_homogeneousSubmodule_one k i.down)))
  have hg (i : ULift.{v} (Fin 2)) : Scheme.Modules.IsFreeGenerator (g i) :=
    ((isFreeGenerator_twistPowSection d
      (MvPolynomial.X_mem_homogeneousSubmodule_one k i.down)).pullback_unit_app
        C.iso.inv).map (chart_preimage k C i).ge
  refine ⟨{ g₀ := g ⟨0⟩
            g₁ := g ⟨1⟩
            bijective_smul_g₀ := hg ⟨0⟩
            bijective_smul_g₁ := hg ⟨1⟩
            map_g₀ := ?_ }⟩
  exact transported_map_g₀ k d C

end AlgebraicGeometry.Proj
