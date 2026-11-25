/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

/-!
# Scalar calculation on homogeneous chart representatives

Source: Stacks Project, Proposition 0BXD, final paragraph.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite TopologicalSpace LocalizedModule
open HomogeneousLocalization MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem restrict_phi_heq
    (k : Type u) [Field k]
    (G : (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    (M : ModuleCat.{u} (MvPolynomial (Fin 2) k)) (𝓜 : ℤ → AddSubgroup M)
    (φ : ∀ z : ℤ, 0 ≤ z →
      (𝓜 z ≃+ Γ(G ⊗ twist (homogeneousSubmodule (Fin 2) k) z, ⊤)))
    (U : (Proj (homogeneousSubmodule (Fin 2) k)).Opens)
    (z w : ℤ) (hz : 0 ≤ z) (hw : 0 ≤ w) (x : M)
    (hx : x ∈ 𝓜 z) (hx' : x ∈ 𝓜 w) (h : z = w) :
    HEq ((G ⊗ twist (homogeneousSubmodule (Fin 2) k) z).presheaf.map
      (homOfLE le_top : U ⟶ ⊤).op (φ z hz ⟨x, hx⟩))
      ((G ⊗ twist (homogeneousSubmodule (Fin 2) k) w).presheaf.map
        (homOfLE le_top : U ⟶ ⊤).op (φ w hw ⟨x, hx'⟩)) := by
  subst w
  rfl

private theorem twist_section_heq
    (k : Type u) [Field k]
    (U : (Proj (homogeneousSubmodule (Fin 2) k)).Opens)
    (z w : ℤ) (h : z = w)
    (s : Γ(twist (homogeneousSubmodule (Fin 2) k) z, U))
    (t : Γ(twist (homogeneousSubmodule (Fin 2) k) w, U))
    (hst : ∀ x : U,
      (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
      (t.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal)) : HEq s t := by
  subst w
  apply heq_of_eq
  exact Subtype.ext (funext fun x ↦ Subtype.ext (hst x))

private theorem tmul_twist_heq
    (k : Type u) [Field k]
    (G : (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    (U : (Proj (homogeneousSubmodule (Fin 2) k)).Opens)
    (z w : ℤ) (h : z = w) (s : Γ(G, U))
    (t : Γ(twist (homogeneousSubmodule (Fin 2) k) z, U))
    (t' : Γ(twist (homogeneousSubmodule (Fin 2) k) w, U)) (ht : HEq t t') :
    HEq (Scheme.Modules.tmulSection s t) (Scheme.Modules.tmulSection s t') := by
  subst w
  cases ht
  rfl

/-- A chart characterized by clearing homogeneous denominators respects homogeneous
localization scalars.
Source: Stacks Project, Proposition 0BXD, final paragraph; step 2 of
lem-sc-p1-serre-section-module-charts.
(blueprint: lem-sc-p1-serre-section-module-chart-scalar)

Proof: the numerator y and scalar numerator a have degrees m*d and l*d. By hsmul,
a*y has degree (l+m)*d. Compatibility hphi identifies phi(a*y) with multiplication
by a on phi(y), and naturality restricts this identity to D+(f). By the hypothesis
hs and the characterization, phi(y) restricts to f^m times s. The definition of
awayToSection on a/f^l identifies its action with multiplication by a divided by
f^l. Hence phi(a*y) restricts to f^(l+m) times (a/f^l)*s. The characterization of
alpha in degree (l+m)*d gives the desired fraction. If f=0 the localization is zero
and the formula holds there as well. The argument includes l=0 and m=0, using the
zeroth twisting isomorphism and the right unitor. -/
theorem serreSectionModuleChartScalar
    (k : Type u) [Field k]
    (G : (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    (M : ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (𝓜 : ℤ → AddSubgroup M)
    (hsmul : ∀ (n : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : M),
      a ∈ homogeneousSubmodule (Fin 2) k n → y ∈ 𝓜 z → a • y ∈ 𝓜 (n + z))
    (φ : ∀ z : ℤ, 0 ≤ z →
        (𝓜 z ≃+ Γ(G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k) z, ⊤)))
    (hφ : ∀ (z : ℤ) (hz : 0 ≤ z) (e : ℕ) (hze : 0 ≤ z + e) (a : MvPolynomial (Fin 2) k)
        (ha : a ∈ homogeneousSubmodule (Fin 2) k e)
        (y : 𝓜 z) (hay : a • (y : M) ∈ 𝓜 (z + e)),
        φ (z + e) hze ⟨a • (y : M), hay⟩ =
          Scheme.Modules.Hom.app (G ◁ Proj.twistMul z ha) ⊤ (φ z hz y))
    (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
    (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
    (alpha : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
      LocalizedModule.Away f M)
    (hnorm : ∀ (m : ℕ) (y : 𝓜 (0 + ((m • d : ℕ) : ℤ)))
        (s : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
      alpha s = mk (y : M) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) ↔
        (G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k)
          (0 + ((m • d : ℕ) : ℤ))).presheaf.map
            (homOfLE le_top : basicOpen (homogeneousSubmodule (Fin 2) k) f ⟶ ⊤).op
            (φ _ (by positivity) y) =
          Scheme.Modules.Hom.app
            ((ρ_ G).inv ≫ G ◁ Proj.unitToTwist (SetLike.pow_mem_graded m hf))
            (basicOpen (homogeneousSubmodule (Fin 2) k) f) s)
    (l : ℕ) (a : MvPolynomial (Fin 2) k)
    (ha : a ∈ homogeneousSubmodule (Fin 2) k (l • d))
    (m : ℕ) (y : 𝓜 (0 + ((m • d : ℕ) : ℤ)))
    (s : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)))
    (hs : alpha s = mk (y : M) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f)) :
    alpha (awayToSection (homogeneousSubmodule (Fin 2) k) f
      (HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin 2) k) hf l a ha) • s) =
        mk (a • (y : M)) (⟨f ^ (l + m), ⟨l + m, rfl⟩⟩ : Submonoid.powers f) := by
  have _hd := hd
  have hdeg : (0 + (((l + m) • d : ℕ) : ℤ)) =
      (0 + ((m • d : ℕ) : ℤ)) + ((l • d : ℕ) : ℤ) := by
    simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_add]
    ring
  have hay : a • (y : M) ∈ 𝓜 (0 + (((l + m) • d : ℕ) : ℤ)) := by
    rw [hdeg, add_comm]
    exact hsmul _ _ _ _ ha y.property
  apply (hnorm (l + m) ⟨a • (y : M), hay⟩ _).mpr
  have hcompat := hφ _ (by positivity) (l • d) (by positivity) a ha y
    (by simpa only [hdeg] using hay)
  have hlocal := (hnorm m y s).mp hs
  apply eq_of_heq
  have htrans := restrict_phi_heq k G M 𝓜 φ
    (basicOpen (homogeneousSubmodule (Fin 2) k) f)
    _ _ (by positivity) (by positivity) (a • (y : M)) hay
    (by simpa only [hdeg] using hay) hdeg
  refine htrans.trans ?_
  rw [hcompat, ← Scheme.Modules.Hom.app_presheaf_map, hlocal]
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.rightUnitor_inv_app, Scheme.Modules.whiskerLeft_app_tmulSection]
  rw [Scheme.Modules.smul_tmulSection, ← Scheme.Modules.tmulSection_smul]
  apply tmul_twist_heq k G _ _ _ hdeg.symm
  apply twist_section_heq k _ _ _ hdeg.symm
  intro x
  change ((1 : HomogeneousLocalization.AtPrime (homogeneousSubmodule (Fin 2) k)
    x.1.asHomogeneousIdeal.toIdeal).val * Localization.mk (f ^ m) 1) *
      Localization.mk a 1 =
    ((awayToSection (homogeneousSubmodule (Fin 2) k) f
      (Away.mk (homogeneousSubmodule (Fin 2) k) hf l a ha)).1 x).val *
      ((1 : HomogeneousLocalization.AtPrime (homogeneousSubmodule (Fin 2) k)
        x.1.asHomogeneousIdeal.toIdeal).val * Localization.mk (f ^ (l + m)) 1)
  rw [HomogeneousLocalization.val_one, one_mul, one_mul]
  erw [ProjectiveSpectrum.Proj.awayToSection_apply]
  simp only [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk',
    IsLocalization.map_mk', RingHom.id_apply]
  rw [← IsLocalization.mk'_mul, ← IsLocalization.mk'_mul,
    IsLocalization.mk'_eq_iff_eq]
  simp [pow_add, mul_comm, mul_left_comm]

end AlgebraicGeometry.Proj
