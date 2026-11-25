/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous

import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

/-!
# Addition of represented homogeneous fractions

Source: Stacks Project, Proposition 0BXD, final paragraph.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite TopologicalSpace LocalizedModule
open HomogeneousLocalization MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

section

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]
private lemma val_eqToHom_twist {i j : ℤ} (h : i = j) {U : (Proj 𝒜).Opens}
    (s : Γ(twist 𝒜 i, U)) (x : U) :
    (((Scheme.Modules.Hom.app (eqToHom (congrArg (twist 𝒜) h)) U s).1 x) :
      Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) = s.1 x := by
  subst h
  rfl
private lemma unitToTwist_comp_mul {i j : ℕ} {f g : A}
    (hf : f ∈ 𝒜 i) (hg : g ∈ 𝒜 j) :
    unitToTwist hf ≫ twistMul (0 + (i : ℤ)) hg ≫
      eqToHom (by congr 1; push_cast; ring) = unitToTwist (SetLike.mul_mem_graded hf hg) := by
  ext U s : 3
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [val_eqToHom_twist (by simp only [Nat.cast_add, zero_add])]
  change ((s.1 x).val * Localization.mk f 1) * Localization.mk g 1 =
    (s.1 x).val * Localization.mk (f * g) 1
  simp only [mul_assoc, Localization.mk_mul, one_mul]

private lemma unitToTwist_comp_mul' {i j l : ℕ} {f g h : A}
    (hf : f ∈ 𝒜 i) (hg : g ∈ 𝒜 j) (hh : h ∈ 𝒜 l)
    (hij : i + j = l) (hfg : f * g = h) :
    unitToTwist hf ≫ twistMul (0 + (i : ℤ)) hg ≫
      eqToHom (congrArg (twist 𝒜) (by omega : 0 + (i : ℤ) + j = 0 + (l : ℤ))) =
      unitToTwist hh := by
  subst l h
  exact unitToTwist_comp_mul hf hg

private lemma tensor_eqToHom_twist (G : (Proj 𝒜).Modules) {i j : ℤ} (h : i = j) :
    eqToHom (congrArg (fun z ↦ G ⊗ twist 𝒜 z) h) =
      G ◁ eqToHom (congrArg (twist 𝒜) h) := by
  subst h
  simp

end

private lemma transport_phi
    {k : Type u} [Field k]
    (G : (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    (M : ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (𝓜 : ℤ → AddSubgroup M)
    (φ : ∀ z : ℤ, 0 ≤ z →
      (𝓜 z ≃+ Γ(G ⊗ twist (homogeneousSubmodule (Fin 2) k) z, ⊤)))
    {z z' : ℤ} (h : z = z') (hz : 0 ≤ z) (hz' : 0 ≤ z')
    (y : M) (hy : y ∈ 𝓜 z) (hy' : y ∈ 𝓜 z') :
    (eqToHom (congrArg (fun i ↦ G ⊗ twist (homogeneousSubmodule (Fin 2) k) i) h)).app ⊤
      (φ z hz ⟨y, hy⟩) = φ z' hz' ⟨y, hy'⟩ := by
  subst h
  rfl

/-- The relation between homogeneous fractions and sections preserves addition.
Source: Stacks Project, Proposition 0BXD, final paragraph.
(blueprint: lem-sc-p1-serre-section-module-fraction-add)

Proof: Take witnesses y/f^m and z/f^n. The numerator f^n*y+f^m*z is homogeneous
of degree (m+n)*d by graded scalar compatibility. LocalizedModule.mk_add_mk
identifies its fraction with the sum of the original fractions. Additivity
of phi and restriction, compatibility of phi with homogeneous multiplication,
and composition of twist multiplication identify its restriction with
f^(m+n)*(s+t). Thus this numerator and denominator witness the sum relation.
The calculation also holds for f=0 and for m or n zero. -/
theorem serreSectionModuleFractionAdd
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
    (f : MvPolynomial (Fin 2) k) (d : ℕ)
    (hf : f ∈ homogeneousSubmodule (Fin 2) k d) :
    let Rel := fun (x : LocalizedModule.Away f M)
      (s : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))) ↦
      ∃ (m : ℕ) (y : 𝓜 (0 + ((m • d : ℕ) : ℤ))),
        x = mk (y : M) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) ∧
        (G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k)
          (0 + ((m • d : ℕ) : ℤ))).presheaf.map
            (homOfLE le_top : basicOpen (homogeneousSubmodule (Fin 2) k) f ⟶ ⊤).op
            (φ _ (by positivity) y) =
          Scheme.Modules.Hom.app
            ((ρ_ G).inv ≫ G ◁ Proj.unitToTwist (SetLike.pow_mem_graded m hf))
            (basicOpen (homogeneousSubmodule (Fin 2) k) f) s
    ∀ x z s t, Rel x s → Rel z t → Rel (x + z) (s + t) := by
  dsimp only
  intro x z s t hx hz
  obtain ⟨m, y, rfl, hy⟩ := hx
  obtain ⟨n, w, rfl, hw⟩ := hz
  have hdeg : (0 + ((m • d : ℕ) : ℤ)) + ((n • d : ℕ) : ℤ) =
      0 + (((m + n) • d : ℕ) : ℤ) := by simp [add_mul]
  have hym : f ^ n • (y : M) ∈ 𝓜 (0 + (((m + n) • d : ℕ) : ℤ)) := by
    rw [← hdeg]
    simpa only [add_comm] using hsmul (n • d) _ (f ^ n) y
      (SetLike.pow_mem_graded n hf) y.property
  have hwm : f ^ m • (w : M) ∈ 𝓜 (0 + (((m + n) • d : ℕ) : ℤ)) := by
    have h := hsmul (m • d) _ (f ^ m) w (SetLike.pow_mem_graded m hf) w.property
    convert h using 1
    simp [add_mul, add_comm]
  let v : 𝓜 (0 + (((m + n) • d : ℕ) : ℤ)) :=
    ⟨f ^ n • (y : M) + f ^ m • (w : M), (𝓜 _).add_mem hym hwm⟩
  refine ⟨m + n, v, ?_, ?_⟩
  · rw [mk_add_mk]
    change mk (f ^ n • (y : M) + f ^ m • (w : M)) _ = mk (v : M) _
    congr 1
    apply Subtype.ext
    exact (pow_add f m n).symm
  · have hprod (m n l : ℕ) (hl : m + n = l) (y : 𝓜 (0 + ((m • d : ℕ) : ℤ)))
        (s : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)))
        (hy : (G ⊗ twist (homogeneousSubmodule (Fin 2) k)
          (0 + ((m • d : ℕ) : ℤ))).presheaf.map
          (homOfLE le_top : basicOpen (homogeneousSubmodule (Fin 2) k) f ⟶ ⊤).op
          (φ _ (by positivity) y) =
          (((ρ_ G).inv ≫ G ◁ unitToTwist (SetLike.pow_mem_graded m hf)).app
            (basicOpen (homogeneousSubmodule (Fin 2) k) f)) s)
        (hym : f ^ n • (y : M) ∈ 𝓜 (0 + ((l • d : ℕ) : ℤ))) :
        (G ⊗ twist (homogeneousSubmodule (Fin 2) k)
          (0 + ((l • d : ℕ) : ℤ))).presheaf.map
          (homOfLE le_top : basicOpen (homogeneousSubmodule (Fin 2) k) f ⟶ ⊤).op
          (φ _ (by positivity) ⟨f ^ n • (y : M), hym⟩) =
          (((ρ_ G).inv ≫ G ◁ unitToTwist (SetLike.pow_mem_graded l hf)).app
            (basicOpen (homogeneousSubmodule (Fin 2) k) f)) s := by
      subst l
      have hdeg : (0 + ((m • d : ℕ) : ℤ)) + ((n • d : ℕ) : ℤ) =
          0 + (((m + n) • d : ℕ) : ℤ) := by simp [add_mul]
      have hp := hφ _ (by positivity) (n • d) (by positivity) (f ^ n)
        (SetLike.pow_mem_graded n hf) y
        (by rw [hdeg]; exact hym)
      let castMap := eqToHom
        (congrArg (fun i ↦ G ⊗ twist (homogeneousSubmodule (Fin 2) k) i) hdeg)
      have hp' := congrArg (fun b ↦ castMap.app ⊤ b) hp
      rw [transport_phi G M 𝓜 φ hdeg (by positivity) (by positivity)
        (f ^ n • (y : M)) (by rw [hdeg]; exact hym) hym] at hp'
      have hpy : (G ⊗ twist (homogeneousSubmodule (Fin 2) k)
          (0 + (((m + n) • d : ℕ) : ℤ))).presheaf.map
          (homOfLE le_top : basicOpen (homogeneousSubmodule (Fin 2) k) f ⟶ ⊤).op
          (φ _ (by positivity) ⟨f ^ n • (y : M), hym⟩) =
        (((ρ_ G).inv ≫ G ◁ unitToTwist (SetLike.pow_mem_graded m hf) ≫
          G ◁ twistMul (0 + ((m • d : ℕ) : ℤ)) (SetLike.pow_mem_graded n hf) ≫
          castMap).app (basicOpen (homogeneousSubmodule (Fin 2) k) f)) s := by
        rw [hp', ← Scheme.Modules.Hom.app_presheaf_map,
          ← Scheme.Modules.Hom.app_presheaf_map, hy]
        simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
      have hcomp : (ρ_ G).inv ≫ G ◁ unitToTwist (SetLike.pow_mem_graded m hf) ≫
          G ◁ twistMul (0 + ((m • d : ℕ) : ℤ)) (SetLike.pow_mem_graded n hf) ≫
          castMap = (ρ_ G).inv ≫ G ◁ unitToTwist (SetLike.pow_mem_graded (m + n) hf) := by
        dsimp only [castMap]
        rw [tensor_eqToHom_twist G hdeg, ← whiskerLeft_comp, ← whiskerLeft_comp,
          unitToTwist_comp_mul' (SetLike.pow_mem_graded m hf)
            (SetLike.pow_mem_graded n hf) (SetLike.pow_mem_graded (m + n) hf)
            (by simp [add_mul]) (pow_add f m n).symm]
      rw [hcomp] at hpy
      exact hpy
    have hpy := hprod m n (m + n) rfl y s hy hym
    have hwp := hprod n m (m + n) (Nat.add_comm n m) w t hw hwm
    change (G ⊗ twist (homogeneousSubmodule (Fin 2) k)
      (0 + (((m + n) • d : ℕ) : ℤ))).presheaf.map
      (homOfLE le_top : basicOpen (homogeneousSubmodule (Fin 2) k) f ⟶ ⊤).op
      (φ _ _ (⟨f ^ n • (y : M), hym⟩ + ⟨f ^ m • (w : M), hwm⟩)) = _
    rw [map_add, map_add, hpy, hwp, map_add]

end AlgebraicGeometry.Proj
