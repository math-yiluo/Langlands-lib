/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
import WeilConjectures.AlgebraicGeometry.ProjectiveLineTwistMultiplication
import WeilConjectures.AlgebraicGeometry.Modules.HomSection

@[expose] public section
universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

private lemma twist_cast_val (k : Type u) [Field k] {m r : ℤ} (h : m = r)
    (U : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Opens)
    (t : Γ(Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) m, U)) (x : U) :
    (((eqToHom (congrArg (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)) h)).app
      U t).1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) = (t.1 x) := by
  subst r
  rfl

/-- Tensor-power isomorphisms and multiplication identities for a homogeneous section.
Source: Stacks Project, Constructions, Tags 01MS, 01MU and 01NG; equation-multiply.
Proof: On D_+(x_i), the twist O(m) is free with basis x_i^m for every integer m.
Multiplication of homogeneous fractions maps the tensor of the bases to x_i^(m+r),
so the multiplication maps are isomorphisms and agree on overlaps. Starting with
O = O(0), iterate them to obtain a_n, and compose multiplication with id tensor a_n
to obtain b_mn. The local coefficient of the section f is f/x_i^d, whose nth tensor
power is (f/x_i^d)^n. The identifications therefore send the tensor-power section
and its product with any local section of O(m) to multiplication by f^n. Equality
on the chart cover proves both morphism identities globally. At n=0 these are the
unit isomorphisms and multiplication by 1; for f=0 positive powers are zero.
Negative m uses the same local basis and the fraction multiplication rule.
(blueprint: lem-sc-p1-homogeneous-section-tensor-powers-data) -/
theorem proj_homogeneous_section_tensor_powers_data (k : Type u) [Field k]
    {d : ℕ} (hd : 0 < d) {f : MvPolynomial (Fin 2) k}
    (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k d) :
    let L := Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (0 + (d : ℤ))
    ∃ (a : ∀ n : ℕ, L.tensorPow n ≅
          Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)
            (0 + ((n • d : ℕ) : ℤ)))
        (b : ∀ (m : ℤ) (n : ℕ),
          Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) m ⊗ L.tensorPow n ≅
            Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)
              (m + ((n • d : ℕ) : ℤ))),
        (∀ n : ℕ, tensorPowSection
            (homOfGlobalSection L ((Proj.unitToTwist hf).app ⊤ (unitSectionsEquiv ⊤ 1)))
            n ≫ (a n).hom =
          Proj.unitToTwist (SetLike.pow_mem_graded n hf)) ∧
        (∀ (m : ℤ) (n : ℕ),
          (ρ_ (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) m)).inv ≫
            Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) m ◁
              tensorPowSection
                (homOfGlobalSection L ((Proj.unitToTwist hf).app ⊤ (unitSectionsEquiv ⊤ 1)))
                n ≫ (b m n).hom =
            Proj.twistMul m (SetLike.pow_mem_graded n hf)) := by
  classical
  have _hd := hd
  dsimp only
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k
  let L := Proj.twist 𝒜 (0 + (d : ℤ))
  let s := Proj.unitToTwist hf
  have hs : homOfGlobalSection L (s.app ⊤ (unitSectionsEquiv ⊤ 1)) = s := by
    apply unit_hom_ext
    rw [homOfGlobalSection_app_one, presheaf_map_id_apply]
    rfl
  rw [hs]
  obtain ⟨hL, μ, hμ, hval, hrest⟩ := projectiveLine_twist_multiplication k
  clear hL hrest hd
  let (m r : ℤ) : IsIso (μ m r) := hμ m r
  have ha (n : ℕ) : ∃ a : L.tensorPow n ≅ Proj.twist 𝒜 (0 + ((n • d : ℕ) : ℤ)),
      ∀ (U : (Proj 𝒜).Opens) (x : U),
        ((a.hom.app U (tensorPowSectionOne s n U)).1 x :
          Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) = Localization.mk (f ^ n) 1 := by
    induction n with
    | zero =>
      have h0 : (0 + ((0 • d : ℕ) : ℤ)) = 0 := by simp
      rw [h0]
      let e : 𝟙_ (Proj 𝒜).Modules ≅ Proj.twist 𝒜 0 :=
        { hom := (Proj.unitIsoTwistZero (𝒜 := 𝒜)).hom
          inv := (Proj.unitIsoTwistZero (𝒜 := 𝒜)).inv
          hom_inv_id := (Proj.unitIsoTwistZero (𝒜 := 𝒜)).hom_inv_id
          inv_hom_id := (Proj.unitIsoTwistZero (𝒜 := 𝒜)).inv_hom_id }
      refine ⟨e, ?_⟩
      intro U x
      simp only [tensorPowSectionOne_zero]
      change ((HomogeneousLocalization.degreePart.zeroEquiv ((1 : Γ(Proj 𝒜, U)).1 x)) :
        Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) = Localization.mk (f ^ 0) 1
      simp [Localization.mk_one_eq_algebraMap]
    | succ n ih =>
      obtain ⟨a, ha⟩ := ih
      have he : (0 + (d : ℤ)) + (0 + ((n • d : ℕ) : ℤ)) =
          0 + (((n + 1) • d : ℕ) : ℤ) := by
        simp [Nat.cast_add, add_mul, add_comm]
      let e := whiskerLeftIso L a ≪≫ asIso (μ (0 + (d : ℤ))
        (0 + ((n • d : ℕ) : ℤ))) ≪≫ eqToIso (congrArg (Proj.twist 𝒜) he)
      refine ⟨e, ?_⟩
      intro U x
      simp only [e, Iso.trans_hom, whiskerLeftIso_hom, asIso_hom, eqToIso.hom,
        Hom.comp_app, ConcreteCategory.comp_apply]
      rw [twist_cast_val k he]
      rw [tensorPowSectionOne_succ]
      erw [whiskerLeft_app_tmulSection (X := Proj 𝒜) (M := L) a.hom
        (s.app U (unitSectionsEquiv U 1)) (tensorPowSectionOne s n U)]
      rw [hval (0 + (d : ℤ)) (0 + ((n • d : ℕ) : ℤ)) U
        (s.app U (unitSectionsEquiv U 1)) (a.hom.app U (tensorPowSectionOne s n U)) x,
        ha U x]
      change (((s.app U (unitSectionsEquiv U 1)).1 x :
        Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal)) * Localization.mk (f ^ n) 1 = _
      rw [Proj.val_unitToTwist_app_apply]
      have h1 : ((unitSectionsEquiv U 1).1 x).val = 1 := by
        change ((1 : Γ(Proj 𝒜, U)).1 x).val = 1
        exact HomogeneousLocalization.val_one
      rw [h1]
      change (1 : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) *
        Localization.mk f 1 * Localization.mk (f ^ n) 1 = Localization.mk (f ^ (n + 1)) 1
      simp only [one_mul, Localization.mk_one_eq_algebraMap, ← map_mul, pow_succ']
  choose a ha using ha
  dsimp only [𝒜, L] at a ha
  let b (m : ℤ) (n : ℕ) := whiskerLeftIso (Proj.twist 𝒜 m) (a n) ≪≫
    asIso (μ m (0 + ((n • d : ℕ) : ℤ))) ≪≫
      eqToIso (congrArg (Proj.twist 𝒜) (by omega :
        m + (0 + ((n • d : ℕ) : ℤ)) = m + ((n • d : ℕ) : ℤ)))
  refine ⟨a, b, ?_, ?_⟩
  · intro n
    apply unit_hom_ext
    change (a n).hom.app ⊤ (tensorPowSectionOne s n ⊤) = _
    apply Subtype.ext
    funext x
    apply Subtype.ext
    exact (ha n ⊤ x).trans (Proj.val_unitToTwist_app_top
      (SetLike.pow_mem_graded n hf) x).symm
  · intro m n
    ext U t : 3
    simp only [b, Iso.trans_hom, whiskerLeftIso_hom, asIso_hom, eqToIso.hom]
    simp only [Hom.comp_app, ConcreteCategory.comp_apply]
    rw [rightUnitor_inv_app, whiskerLeft_app_tmulSection, whiskerLeft_app_tmulSection]
    apply Subtype.ext
    funext x
    apply Subtype.ext
    rw [twist_cast_val k (by omega :
      m + (0 + ((n • d : ℕ) : ℤ)) = m + ((n • d : ℕ) : ℤ))]
    exact (hval m (0 + ((n • d : ℕ) : ℤ)) U t
      ((a n).hom.app U (tensorPowSectionOne s n U)) x).trans
      (congrArg (fun z : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal ↦
        (t.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) * z) (ha n U x))
end AlgebraicGeometry
