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

/-! # Forward implication for the section-ring chart formula

Source: Stacks Project, Constructions, Tag 01N8; Properties, Tag 01PZ
(blueprint: lem-sc-ample-proj-canonical-map-preimage-forward).
-/

@[expose] public section

universe v
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

private theorem nonvanishing_iso {X : Scheme.{v}} {M N : X.Modules}
    [M.IsInvertible] [N.IsInvertible] (e : M ≅ N) (s : Γ(M, ⊤)) (x : X) :
    x ∈ nonvanishingLocus N (e.hom.app ⊤ s) ↔ x ∈ nonvanishingLocus M s := by
  rw [mem_nonvanishingLocus_iff_generatesAt, mem_nonvanishingLocus_iff_generatesAt]
  have transport {P Q : X.Modules} (a : P ≅ Q) (t : Γ(P, ⊤))
      (h : GeneratesAt t x) : GeneratesAt (a.hom.app ⊤ t) x := by
    obtain ⟨U, hxU, ht⟩ := h
    refine ⟨U, hxU, ?_⟩
    rw [← Hom.app_presheaf_map]
    exact ht.app_hom a
  constructor
  · intro h
    have h' := transport e.symm (e.hom.app ⊤ s) h
    simpa only [Iso.symm_hom, inv_app_hom_app_apply_of_iso] using h'
  · exact transport e s

private theorem nonvanishing_tensor {X : Scheme.{v}} (M N : X.Modules)
    [M.IsInvertible] [N.IsInvertible] (s : Γ(M, ⊤)) (t : Γ(N, ⊤)) :
    nonvanishingLocus (MonoidalCategory.tensorObj M N) (tmulSection s t) =
      nonvanishingLocus M s ∩ nonvanishingLocus N t := by
  have := IsInvertible.sheafOfModules_isInvertible M
  have := IsInvertible.sheafOfModules_isInvertible N
  ext x
  obtain ⟨U, hxU, _, ⟨e, he⟩, g, hg⟩ := exists_isFreeGenerator₂ M N
    (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨a, ha⟩ := he.exists_smul_eq (M.presheaf.map (homOfLE le_top).op s)
  obtain ⟨b, hb⟩ := hg.exists_smul_eq (N.presheaf.map (homOfLE le_top).op t)
  have hp : (MonoidalCategory.tensorObj M N).presheaf.map (homOfLE le_top).op (tmulSection s t) =
      (a * b) • tmulSection e g := by
    rw [tmulSection_map, ← ha, ← hb, smul_tmulSection, tmulSection_smul, smul_smul]
  change x ∈ nonvanishingLocus (MonoidalCategory.tensorObj M N) _ ↔
    x ∈ nonvanishingLocus M s ∧ x ∈ nonvanishingLocus N t
  rw [mem_nonvanishingLocus_iff_generatesAt,
    mem_nonvanishingLocus_iff_generatesAt, mem_nonvanishingLocus_iff_generatesAt,
    generatesAt_iff_mem_basicOpen (he.tmulSection hg) hp hxU,
    generatesAt_iff_mem_basicOpen he ha.symm hxU,
    generatesAt_iff_mem_basicOpen hg hb.symm hxU, X.basicOpen_mul]
  rfl

private theorem sectionRing_mul_component {X : Scheme.{v}} (L : X.Modules)
    [L.IsInvertible] {i j : ℕ} (a : sectionRingGrade L i) (b : sectionRingGrade L j) :
    (a.val * b.val) (i + j) =
      (L.tensorPowAddIso i j).inv.app ⊤ (tmulSection (a.val i) (b.val j)) := by
  obtain ⟨a', ha⟩ := a.property
  obtain ⟨b', hb⟩ := b.property
  rw [← ha, ← hb, DirectSum.of_mul_of, DirectSum.of_eq_same,
    DirectSum.of_eq_same, DirectSum.of_eq_same]
  rfl

private theorem nonvanishing_power {X : Scheme.{v}} (L : X.Modules) [L.IsInvertible]
    {d : ℕ} (s : sectionRingGrade L d) (n : ℕ) (hn : 0 < n) (x : X) :
    x ∈ nonvanishingLocus (L.tensorPow (n • d)) ((s.val ^ n) (n • d)) ↔
      x ∈ nonvanishingLocus (L.tensorPow d) (s.val d) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : n = 0
    · subst n
      have hh : (0 + 1) • d = d := Nat.one_mul d
      rw [hh, pow_one]
    · have hn' : 0 < n := Nat.pos_of_ne_zero h
      let a : sectionRingGrade L (n • d) := ⟨s.val ^ n, SetLike.pow_mem_graded n s.property⟩
      have hm := sectionRing_mul_component L a s
      have he := nonvanishing_iso (L.tensorPowAddIso (n • d) d).symm
        (tmulSection (a.val (n • d)) (s.val d)) x
      rw [nonvanishing_tensor] at he
      rw [add_nsmul, one_nsmul, pow_succ]
      change x ∈ nonvanishingLocus (L.tensorPow (n • d + d))
        ((a.val * s.val) (n • d + d)) ↔ _
      rw [hm]
      simpa only [Iso.symm_hom, a, Set.mem_inter_iff, ih hn', and_self] using he

private theorem nonvanishing_of_local_smul {X : Scheme.{v}} (M : X.Modules)
    (a b : Γ(M, ⊤)) (U : X.Opens) (r : Γ(X, U)) (x : X) (hx : x ∈ U)
    (h : r • M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a =
      M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op b)
    (hb : x ∈ nonvanishingLocus M b) : x ∈ nonvanishingLocus M a := by
  change _ ∉ _ at hb ⊢
  intro ha
  apply hb
  have hg := congrArg (TopCat.Presheaf.germ M.val.presheaf U x hx) h
  erw [PresheafOfModules.germ_smul (R := X.presheaf) M.val,
    TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at hg
  rw [← hg]
  exact Submodule.smul_mem _ _ ha

/-- If a point lies in the inverse image of a homogeneous basic open, the section is
nonvanishing there. The proof uses the fraction identity with a section already known
to be nonvanishing at the point; in the residue-field fibre, a nonzero numerator cannot
be a multiple of a vanishing denominator.
Source: Stacks Project, Constructions, Tag 01N8; Properties, Tag 01PZ
(blueprint: lem-sc-ample-proj-canonical-map-preimage-forward).

Proof: the nonvanishing/local-generation equivalence shows that an isomorphism
preserves nonvanishing. Trivialize two invertible modules simultaneously and write
their sections as a times a basis and b times a basis. Their tensor has coefficient
a*b, and the basic-open multiplication formula identifies its nonvanishing locus
with the intersection of the two original loci. Homogeneous section-ring
multiplication is this tensor section transported through tensorPowAddIso, as
DirectSum.of_mul_of shows after extracting the single-component representatives.
Induction now shows that every positive section-ring power has the same
nonvanishing locus as its base section.
Choose e > 0 and t nonvanishing at x from hx. Form the homogeneous numerator t^d
in degree e*d using d*e = e*d; its degree-e*d component is nonvanishing at x.
Specialize hformula to n = e and this numerator. Take germs at x on the inverse
image of D_+(s). Germs commute with restriction and scalar multiplication. If the
germ of s^e belonged to the maximal ideal times its stalk, its scalar multiple
would also belong there, contradicting nonvanishing of t^d. Thus s^e is
nonvanishing, and positive-power invariance gives nonvanishing of s.
No reducedness, ampleness or quasi-compactness assumption is needed. -/
theorem sectionRing_proj_mem_basicOpen_forward (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
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
    x ∈ f ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) s.val →
      x ∈ nonvanishingLocus (L.tensorPow d) (s.val d) := by
  intro hxs
  obtain ⟨e, t, he, hxt⟩ := hx
  have hdeg : d • e = e • d := by
    change d * e = e * d
    exact Nat.mul_comm d e
  let ξ : sectionRingGrade L (e • d) :=
    ⟨t.val ^ d, hdeg ▸ SetLike.pow_mem_graded d t.property⟩
  have ht := (nonvanishing_power L t d hd x).mpr hxt
  have ht' : x ∈ nonvanishingLocus (L.tensorPow (e • d)) (ξ.val (e • d)) :=
    by
      dsimp only [ξ]
      rw [← hdeg]
      exact ht
  have hs := nonvanishing_of_local_smul (L.tensorPow (e • d))
    ((s.val ^ e) (e • d)) (ξ.val (e • d))
    (f ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) s.val)
    (f.app (Proj.basicOpen (sectionRingGrade L) s.val)
      (Proj.awayToSection (sectionRingGrade L) s.val
        (HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property e
          ξ.val ξ.property))) x hxs (hformula d hd s e ξ) ht'
  exact (nonvanishing_power L s e he x).mp hs

end AlgebraicGeometry.Scheme.Modules
