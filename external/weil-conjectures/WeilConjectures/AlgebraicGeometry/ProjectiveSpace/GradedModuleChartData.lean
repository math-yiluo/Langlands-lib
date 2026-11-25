/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import WeilConjectures.Algebra.Module.DegreeZeroFractions
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

import WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExists
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Chart data for a graded polynomial module

## References

* Stacks Project, Tag 01M6 and Lemma 01M7
* Stacks Project, construction before Definition 01M6 and Lemma 01M7
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace LocalizedModule HomogeneousLocalization
open MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

private local instance chartDataScalars {S M : Type u} [CommRing S] [AddCommGroup M]
    [Module S M] (H : ℕ → AddSubgroup S) [GradedRing H] (f : S) :
    Module (HomogeneousLocalization.Away H f) (LocalizedModule.Away f M) :=
  Module.compHom (LocalizedModule.Away f M)
    (algebraMap (HomogeneousLocalization.Away H f) (Localization.Away f))

private theorem range_chart_inclusion {R N B : Type u} [Semiring R]
    [AddCommMonoid N] [Module R N] [AddCommMonoid B]
    (Z : Submodule R N) (e : B ≃+ Z) :
    Set.range (Z.subtype.toAddMonoidHom.comp e.toAddMonoidHom) = (Z : Set N) := by
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    exact (e s).property
  · intro hx
    refine ⟨e.symm ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)

set_option backward.isDefEq.respectTransparency false in
/-- Push charts forward along the identity graded ring map between the two polynomial
presentations. -/
private theorem graded_module_chart_regrading
    (k : Type u) [Field k] (A : ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (H : ℕ → AddSubgroup (MvPolynomial (Fin 2) k)) [GradedRing H]
    (hH : ∀ n, H n = (homogeneousSubmodule (Fin 2) k n).toAddSubgroup)
    (Z : ∀ f : {p : MvPolynomial (Fin 2) k × ℕ // 0 < p.2 ∧ p.1 ∈ H p.2},
      Submodule (HomogeneousLocalization.Away H f.val.1)
        (LocalizedModule.Away f.val.1 A))
    (rho : ∀ (f g : {p : MvPolynomial (Fin 2) k × ℕ // 0 < p.2 ∧ p.1 ∈ H p.2}),
      basicOpen H g.val.1 ≤ basicOpen H f.val.1 → Z f →+ Z g)
    (F : (Proj H).Modules)
    (alpha : ∀ f : {p : MvPolynomial (Fin 2) k × ℕ // 0 < p.2 ∧ p.1 ∈ H p.2},
      F.val.obj (op (basicOpen H f.val.1)) ≃+ Z f)
    (hscalar : ∀ (f : {p : MvPolynomial (Fin 2) k × ℕ // 0 < p.2 ∧ p.1 ∈ H p.2})
      (r : HomogeneousLocalization.Away H f.val.1)
      (s : F.val.obj (op (basicOpen H f.val.1))),
      (alpha f (awayToSection H f.val.1 r • s) : LocalizedModule.Away f.val.1 A) =
        algebraMap (HomogeneousLocalization.Away H f.val.1)
          (Localization.Away f.val.1) r • (alpha f s : LocalizedModule.Away f.val.1 A))
    (hrestrict : ∀ (f g : {p : MvPolynomial (Fin 2) k × ℕ // 0 < p.2 ∧ p.1 ∈ H p.2})
      (i : basicOpen H g.val.1 ≤ basicOpen H f.val.1)
      (s : F.val.obj (op (basicOpen H f.val.1))),
      alpha g (F.val.map (homOfLE i).op s) = rho f g i (alpha f s)) :
    ∃ (E : (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
      (beta : ∀ f : {p : MvPolynomial (Fin 2) k × ℕ // 0 < p.2 ∧ p.1 ∈ H p.2},
        E.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f.val.1)) ≃+ Z f),
      (∀ (f : {p : MvPolynomial (Fin 2) k × ℕ // 0 < p.2 ∧ p.1 ∈ H p.2})
        (r : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f.val.1)
        (s : E.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f.val.1))),
        (beta f (awayToSection (homogeneousSubmodule (Fin 2) k) f.val.1 r • s) :
          LocalizedModule.Away f.val.1 A) =
          algebraMap
            (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f.val.1)
            (Localization.Away f.val.1) r • (beta f s : LocalizedModule.Away f.val.1 A)) ∧
      (∀ (f g : {p : MvPolynomial (Fin 2) k × ℕ // 0 < p.2 ∧ p.1 ∈ H p.2})
        (i : basicOpen (homogeneousSubmodule (Fin 2) k) g.val.1 ≤
          basicOpen (homogeneousSubmodule (Fin 2) k) f.val.1)
        (j : basicOpen H g.val.1 ≤ basicOpen H f.val.1)
        (s : E.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f.val.1))),
        beta g (E.val.map (homOfLE i).op s) = rho f g j (beta f s)) := by
  let phi : homogeneousSubmodule (Fin 2) k →+*ᵍ H :=
    { RingHom.id (MvPolynomial (Fin 2) k) with
      map_mem := by
        intro n x hx
        change x ∈ H n
        rw [hH]
        exact hx }
  have hphi : HomogeneousIdeal.irrelevant H ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 2) k)).map phi := by
    change (HomogeneousIdeal.irrelevant H).toIdeal ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 2) k)).toIdeal.map
        phi.toRingHom
    apply (HomogeneousIdeal.toIdeal_irrelevant_le H).mpr
    intro n hn x hx
    rw [hH] at hx
    exact Ideal.mem_map_of_mem phi.toRingHom
      (HomogeneousIdeal.mem_irrelevant_of_mem (homogeneousSubmodule (Fin 2) k) hn hx)
  let pi := AlgebraicGeometry.Proj.map phi hphi
  let E := (Scheme.Modules.pushforward pi).obj F
  let beta := fun f ↦ alpha f
  refine ⟨E, beta, ?_, ?_⟩
  · intro f r s
    let r' := HomogeneousLocalization.Away.map phi f.val.1 r
    have hsec := ConcreteCategory.congr_hom
      (awayToSection_comp_appLE phi hphi
        (show f.val.1 ∈ homogeneousSubmodule (Fin 2) k f.val.2 by
          have hf := f.property.2
          rw [hH] at hf
          exact hf)) r
    change pi.appLE (basicOpen (homogeneousSubmodule (Fin 2) k) f.val.1)
      (pi ⁻¹ᵁ basicOpen (homogeneousSubmodule (Fin 2) k) f.val.1) le_rfl
      (awayToSection (homogeneousSubmodule (Fin 2) k) f.val.1 r) =
      awayToSection H f.val.1 r' at hsec
    rw [Scheme.Hom.appLE_eq_app] at hsec
    let s' : F.val.obj (op (basicOpen H f.val.1)) := s
    change (alpha f (pi.app _ (awayToSection _ f.val.1 r) • s') :
      LocalizedModule.Away f.val.1 A) = _
    rw [hsec, hscalar]
    congr 1
    have hf : f.val.1 ∈ homogeneousSubmodule (Fin 2) k f.val.2 := by
      have hf := f.property.2
      rw [hH] at hf
      exact hf
    obtain ⟨n, x, hx, rfl⟩ := r.mk_surjective _ hf
    simp only [r', HomogeneousLocalization.Away.map_mk,
      HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk]
    rfl
  · intro f g i j s
    exact hrestrict f g j s

/-- An integer-graded polynomial module has an associated sheaf with explicit chart data. -/
theorem graded_module_chart_data_exists (k : Type u) [Field k]
    (A : ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (𝒢 : ℤ → AddSubgroup A) (h𝒢 : DirectSum.IsInternal 𝒢)
    (hsmul : ∀ (n : ℕ) (j : ℤ) (s : MvPolynomial (Fin 2) k) (x : A),
      s ∈ homogeneousSubmodule (Fin 2) k n → x ∈ 𝒢 j → s • x ∈ 𝒢 ((n : ℤ) + j)) :
    ∃ E : (Proj (homogeneousSubmodule (Fin 2) k)).Modules,
    ∃ (alpha : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ),
      0 < d → f ∈ homogeneousSubmodule (Fin 2) k d →
      E.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
        LocalizedModule.Away f A),
      (∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d),
        Function.Injective (alpha f d hd hf) ∧
        Set.range (alpha f d hd hf) = degreeZeroFractions
          (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
          (fun n : ℕ ↦ (𝒢 n : Set A)) (Submonoid.powers f)) ∧
      (∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
        (r : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
        (s : E.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
        alpha f d hd hf (awayToSection (homogeneousSubmodule (Fin 2) k) f r • s) =
          algebraMap (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
            (Localization.Away f) r • alpha f d hd hf s) ∧
      (∀ (f g : MvPolynomial (Fin 2) k) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
        (hg : g ∈ homogeneousSubmodule (Fin 2) k b)
        (inc : basicOpen (homogeneousSubmodule (Fin 2) k) g ≤
          basicOpen (homogeneousSubmodule (Fin 2) k) f)
        (e c : ℕ) (a : MvPolynomial (Fin 2) k),
        0 < e → a ∈ homogeneousSubmodule (Fin 2) k c → g ^ e = a * f →
        ∀ (m : ℕ) (y : A)
          (s : E.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
          alpha f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
          alpha g b hb hg (E.val.map (homOfLE inc).op s) =
            mk (a ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g)) := by
  let H : ℕ → AddSubgroup (MvPolynomial (Fin 2) k) :=
    fun n ↦ (homogeneousSubmodule (Fin 2) k n).toAddSubgroup
  let instH : GradedRing H :=
    { MvPolynomial.gradedAlgebra (σ := Fin 2) (R := k) with }
  obtain ⟨Z, hZ, rhoS, rho, hlaws, hid, hcomp, hbij, F, alpha,
    hscalar, hrestrict, _⟩ := gradedModuleSheaf_exists H 𝒢 h𝒢 hsmul
  obtain ⟨E, beta, hbscalar, hbrestrict⟩ :=
    graded_module_chart_regrading k A H (fun _ ↦ rfl) Z rho F alpha
      (fun f r s ↦ congrArg Subtype.val (hscalar f r s)) hrestrict
  let idx := fun (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
    (hf : f ∈ homogeneousSubmodule (Fin 2) k d) ↦
      (⟨(f, d), hd, hf⟩ : {p : MvPolynomial (Fin 2) k × ℕ //
        0 < p.2 ∧ p.1 ∈ H p.2})
  let chart := fun f d hd hf ↦
    ((Z (idx f d hd hf)).subtype.toAddMonoidHom).comp
      (beta (idx f d hd hf)).toAddMonoidHom
  refine ⟨E, chart, ?_, ?_, ?_⟩
  · intro f d hd hf
    constructor
    · exact Subtype.val_injective.comp (beta (idx f d hd hf)).injective
    · have hrange := range_chart_inclusion (Z (idx f d hd hf))
        (beta (idx f d hd hf))
      exact hrange.trans (hZ (idx f d hd hf))
  · intro f d hd hf r s
    exact hbscalar (idx f d hd hf) r s
  · intro f g d b hd hb hf hg inc e c a he ha hrel m y s hs
    have incH : basicOpen H g ≤ basicOpen H f := by
      rw [← basicOpen_pow H g e he, hrel, basicOpen_mul]
      exact inf_le_right
    have hr := hbrestrict (idx f d hd hf) (idx g b hb hg) inc incH s
    change (beta (idx g b hb hg) (E.val.map (homOfLE inc).op s) :
      LocalizedModule.Away g A) = _
    exact (congrArg Subtype.val hr).trans
      ((hlaws (idx f d hd hf) (idx g b hb hg) incH).2.2
        e c a he ha hrel m y (beta (idx f d hd hf) s) hs)

end AlgebraicGeometry.Proj
