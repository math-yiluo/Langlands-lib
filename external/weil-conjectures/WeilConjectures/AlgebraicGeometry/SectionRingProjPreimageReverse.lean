/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import WeilConjectures.AlgebraicGeometry.NonvanishingGeneratingLocus
import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-! # Reverse implication for the section-ring chart formula

Source: Stacks Project, Constructions, Tag 01N8; Properties, Tag 01PZ
(blueprint: lem-sc-ample-proj-canonical-map-preimage-reverse).
-/

@[expose] public section

universe v
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

private theorem sectionRing_component_mul {X : Scheme.{v}} (L : X.Modules)
    [L.IsInvertible] {i j : ℕ} (a : sectionRingGrade L i) (b : sectionRingGrade L j) :
    (a.val * b.val) (i + j) =
      (L.tensorPowAddIso i j).inv.app ⊤ (tmulSection (a.val i) (b.val j)) := by
  obtain ⟨a, ha⟩ := a.property
  obtain ⟨b, hb⟩ := b.property
  simp only [← ha, ← hb, DirectSum.of_mul_of, DirectSum.of_eq_same]
  rfl

private theorem sectionRing_generatesAt_mul {X : Scheme.{v}} (L : X.Modules)
    [L.IsInvertible] {i j : ℕ} (a : sectionRingGrade L i) (b : sectionRingGrade L j)
    (x : X) (ha : GeneratesAt (a.val i) x) (hb : GeneratesAt (b.val j) x) :
    GeneratesAt ((a.val * b.val) (i + j)) x := by
  obtain ⟨U, hxU, hU⟩ := ha
  obtain ⟨V, hxV, hV⟩ := hb
  refine ⟨U ⊓ V, ⟨hxU, hxV⟩, ?_⟩
  rw [sectionRing_component_mul]
  erw [← Hom.app_presheaf_map, tmulSection_map]
  have h := ((hU.map inf_le_left).tmulSection (hV.map inf_le_right)).app_hom
    (L.tensorPowAddIso i j).symm
  simpa only [presheaf_map_homOfLE_map_homOfLE, Iso.symm_hom] using h

private theorem sectionRing_power_nonvanishing {X : Scheme.{v}} (L : X.Modules)
    [L.IsInvertible] {d : ℕ} (s : sectionRingGrade L d) (n : ℕ) (hn : 0 < n)
    (x : X) (hs : x ∈ nonvanishingLocus (L.tensorPow d) (s.val d)) :
    x ∈ nonvanishingLocus (L.tensorPow (n • d)) ((s.val ^ n) (n • d)) := by
  have hs' := (mem_nonvanishingLocus_iff_generatesAt _ _ _).mp hs
  apply (mem_nonvanishingLocus_iff_generatesAt _ _ _).mpr
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn' : n = 0
    · subst n
      rw [show (0 + 1) • d = d from one_nsmul d, pow_one]
      exact hs'
    · rw [succ_nsmul, pow_succ]
      exact sectionRing_generatesAt_mul L
        ⟨s.val ^ n, SetLike.pow_mem_graded n s.property⟩ s x (ih (Nat.pos_of_ne_zero hn')) hs'

private theorem scalar_isUnit_of_nonvanishing {X : Scheme.{v}} (M : X.Modules)
    {U : X.Opens} (a : Γ(X, U)) (t : Γ(M, U)) (s : Γ(M, ⊤))
    (h : a • t = M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s)
    (x : X) (hx : x ∈ U) (hs : x ∈ nonvanishingLocus M s) :
    IsUnit (X.presheaf.germ U x hx a) := by
  by_contra ha
  have ha' : X.presheaf.germ U x hx a ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rwa [IsLocalRing.mem_maximalIdeal]
  apply hs
  rw [← TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE le_top) x hx s]
  erw [← h]
  erw [PresheafOfModules.germ_smul (R := X.presheaf) M.val]
  exact Submodule.smul_mem_smul ha' Submodule.mem_top

private theorem chart_fraction_numerator_notMem
    {A : Type v} [CommRing A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    {e : ℕ} (t : 𝒜 e) (n : ℕ) (ξ : 𝒜 (n • e))
    (y : Proj 𝒜) (hy : y ∈ Proj.basicOpen 𝒜 t.val)
    (hu : IsUnit ((Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 t.val) y hy
      (Proj.awayToSection 𝒜 t.val (HomogeneousLocalization.Away.mk 𝒜 t.property n
        ξ.val ξ.property)))) : ξ.val ∉ y.asHomogeneousIdeal := by
  have ht : t.val ∈ y.asHomogeneousIdeal.toIdeal.primeCompl := hy
  let z := HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr ht)
    (HomogeneousLocalization.Away.mk 𝒜 t.property n ξ.val ξ.property)
  have hz : IsUnit z := by
    have h := hu.map (Proj.stalkIso' 𝒜 y).toCommRingCatIso.hom.hom
    have hg := CommRingCat.hom_ext_iff.mp
      (ProjectiveSpectrum.Proj.awayToSection_germ 𝒜 t.val y hy)
    have hg' := DFunLike.congr_fun hg
      (HomogeneousLocalization.Away.mk 𝒜 t.property n ξ.val ξ.property)
    change (Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 t.val) y hy
      (Proj.awayToSection 𝒜 t.val (HomogeneousLocalization.Away.mk 𝒜 t.property n
        ξ.val ξ.property)) = (Proj.stalkIso' 𝒜 y).toCommRingCatIso.inv z at hg'
    rw [hg'] at h
    change IsUnit ((Proj.stalkIso' 𝒜 y) ((Proj.stalkIso' 𝒜 y).symm z)) at h
    rwa [RingEquiv.apply_symm_apply] at h
  have hzval := (HomogeneousLocalization.isUnit_iff_isUnit_val 𝒜
    y.asHomogeneousIdeal.toIdeal z).mpr hz
  change IsUnit (Localization.mk ξ.val
    ⟨t.val ^ n, (Submonoid.powers_le.mpr ht) ⟨n, rfl⟩⟩) at hzval
  rw [Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff] at hzval
  exact hzval

private theorem exists_sectionRing_chart {X : Scheme.{v}} (L : X.Modules) [L.IsInvertible]
    (y : Proj (sectionRingGrade L)) :
    ∃ (e : ℕ) (t : sectionRingGrade L e),
      0 < e ∧ y ∈ Proj.basicOpen (sectionRingGrade L) t.val := by
  classical
  by_contra! h
  apply y.not_irrelevant_le
  rw [HomogeneousIdeal.irrelevant_le]
  intro e he t ht
  exact not_not.mp (h e ⟨t, ht⟩ he)

/-- If a homogeneous section is nonvanishing at a point, the point lies in the inverse
image of its basic open. Choose a positive-degree denominator chart through the point;
the fraction identity makes the corresponding quotient a unit in the local ring.
Source: Stacks Project, Constructions, Tag 01N8; Properties, Tag 01PZ
(blueprint: lem-sc-ample-proj-canonical-map-preimage-reverse).

Proof: write y = f(x). The homogeneous prime y does not contain the irrelevant
ideal, so choose a positive-degree homogeneous t, of degree e, outside that prime.
Thus y lies in D_+(t). Trivialize L near x and pass to the residue-field fibre.
The value of s^e is nonzero, since s is nonvanishing and e > 0. Specialize hformula
on the t-chart to n = d and numerator s^e, using e*d = d*e to match degrees.
It gives alpha times the value of t^d equals the nonzero value of s^e. Hence alpha
and the value of t^d are both nonzero. Here alpha is the residue of the pullback of
the chart function s^e/t^d. Thus its pullback germ is a unit in O_X,x. The stalk
homomorphism O_Proj,y to O_X,x is local and reflects units, so the original germ of
s^e/t^d is a unit. The Proj stalk identification with homogeneous localization and
the unit criterion in localization at a prime imply that s^e is outside the prime y.
Primality, or just closure of an ideal under multiplication, implies that s is outside
y as well. This is y in D_+(s). The hypothesis hx is harmless and is not needed for
this direction. All positive-power tests occur over residue fields, including for
nonreduced X. -/
theorem sectionRing_proj_mem_basicOpen_reverse (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (f : X ⟶ Proj (sectionRingGrade L))
    (hformula : ∀ (d : ℕ) (_hd : 0 < d) (s : sectionRingGrade L d),
        ∀ (n : ℕ) (ξ : sectionRingGrade L (n • d)),
          (f.app (Proj.basicOpen (sectionRingGrade L) s.val)
            (Proj.awayToSection (sectionRingGrade L) s.val
              (HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
                ξ.val ξ.property))) •
            (L.tensorPow (n • d)).presheaf.map (homOfLE
              (le_top : f ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) s.val ≤ ⊤)).op
              ((s.val ^ n) (n • d)) =
          (L.tensorPow (n • d)).presheaf.map (homOfLE
              (le_top : f ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) s.val ≤ ⊤)).op
            (ξ.val (n • d)))
    (x : X)
    (hx : ∃ (e : ℕ) (t : sectionRingGrade L e),
      0 < e ∧ x ∈ nonvanishingLocus (L.tensorPow e) (t.val e))
    (d : ℕ) (hd : 0 < d) (s : sectionRingGrade L d) :
    x ∈ nonvanishingLocus (L.tensorPow d) (s.val d) →
      x ∈ f ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) s.val := by
  have _ := hx
  have _ := hd
  intro hs
  obtain ⟨e, t, he, hxt⟩ := exists_sectionRing_chart L (f x)
  have hdeg : e • d = d • e := Nat.mul_comm e d
  let ξ : sectionRingGrade L (d • e) :=
    ⟨s.val ^ e, by simpa only [hdeg] using SetLike.pow_mem_graded e s.property⟩
  have hξ : x ∈ nonvanishingLocus (L.tensorPow (d • e)) (ξ.val (d • e)) := by
    have hp := sectionRing_power_nonvanishing L s e he x hs
    rw [hdeg] at hp
    exact hp
  let q := Proj.awayToSection (sectionRingGrade L) t.val
    (HomogeneousLocalization.Away.mk (sectionRingGrade L) t.property d ξ.val ξ.property)
  have hfunit : IsUnit (X.presheaf.germ
      (f ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) x hxt
      (f.app (Proj.basicOpen (sectionRingGrade L) t.val) q)) :=
    scalar_isUnit_of_nonvanishing (L.tensorPow (d • e)) _ _ _
      (hformula e he t d ξ) x hxt hξ
  have hq : IsUnit ((Proj (sectionRingGrade L)).presheaf.germ
      (Proj.basicOpen (sectionRingGrade L) t.val) (f x) hxt q) := by
    apply (isUnit_map_iff (f.stalkMap x).hom _).mp
    rwa [f.germ_stalkMap_apply]
  have hnot := chart_fraction_numerator_notMem (sectionRingGrade L) t d ξ (f x) hxt hq
  change f x ∈ Proj.basicOpen (sectionRingGrade L) s.val
  rw [← Proj.basicOpen_pow (sectionRingGrade L) s.val e he]
  exact hnot

end AlgebraicGeometry.Scheme.Modules
