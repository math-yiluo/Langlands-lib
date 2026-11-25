/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Restriction calculation on homogeneous chart representatives

Source: Stacks Project, Proposition 0BXD, final paragraph.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite TopologicalSpace LocalizedModule
open HomogeneousLocalization MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

private lemma twist_eqToHom_val
    (k : Type u) [Field k] (i j : ℤ) (h : i = j)
    (U : (Proj (homogeneousSubmodule (Fin 2) k)).Opens)
    (s : Γ(Proj.twist (homogeneousSubmodule (Fin 2) k) i, U)) (x : U) :
    (((eqToHom (congrArg (Proj.twist (homogeneousSubmodule (Fin 2) k)) h)).app U s).1 x :
      Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
      (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) := by
  subst j
  rfl

private lemma unitToTwist_mul_comp
    (k : Type u) [Field k] (p q : ℕ) (f a : MvPolynomial (Fin 2) k)
    (hf : f ∈ homogeneousSubmodule (Fin 2) k p)
    (ha : a ∈ homogeneousSubmodule (Fin 2) k q) :
    Proj.unitToTwist hf ≫ Proj.twistMul (0 + (p : ℤ)) ha ≫
        eqToHom (by simp [Nat.cast_add]) =
      Proj.unitToTwist (SetLike.mul_mem_graded hf ha) := by
  ext U s : 3
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [twist_eqToHom_val k _ _ (by simp [Nat.cast_add])]
  change ((s.1 x).val * Localization.mk f 1) * Localization.mk a 1 =
    (s.1 x).val * Localization.mk (f * a) 1
  rw [mul_assoc, Localization.mk_mul]
  simp

/-- Multiplying the section attached to f by a is the section attached to their product,
including the transport of the twisting degree and tensoring with an arbitrary module.
Source: Stacks Project, Proposition 0BXD, final paragraph.

Proof: evaluate unitToTwist and twistMul at each open and then each point. The first
map sends a local function r to r*f, and the second sends that value to (r*f)*a.
Associativity and f*a=g identify it with r*g. Equality of degrees gives the indicated
transport; eliminate that equality to check that transport is the identity on values.
Apply the functor G tensor -, which preserves composition and identity transports,
and precompose by the inverse right unitor. This argument covers zero polynomials and
zero degrees as well, since it uses only multiplication, not division. -/
private lemma serreTwistMultiplicationProduct
    (k : Type u) [Field k]
    (G : (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    (p q r : ℕ) (f a g : MvPolynomial (Fin 2) k)
    (hf : f ∈ homogeneousSubmodule (Fin 2) k p)
    (ha : a ∈ homogeneousSubmodule (Fin 2) k q)
    (hg : g ∈ homogeneousSubmodule (Fin 2) k r)
    (hdeg : (0 + (p : ℤ)) + (q : ℤ) = 0 + (r : ℤ)) (hprod : f * a = g) :
    ((ρ_ G).inv ≫ G ◁ Proj.unitToTwist hf) ≫
        G ◁ Proj.twistMul (0 + (p : ℤ)) ha ≫
        eqToHom (congrArg (fun z ↦ G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k) z)
          hdeg) =
      (ρ_ G).inv ≫ G ◁ Proj.unitToTwist hg  := by
  have hr : r = p + q := by omega
  subst r
  subst g
  have ht := unitToTwist_mul_comp k p q f a hf ha
  have hw := congrArg (fun t ↦ G ◁ t) ht
  simp only [MonoidalCategory.whiskerLeft_comp] at hw
  rw [MonoidalCategory.whiskerLeft_eqToHom] at hw
  simpa only [Category.assoc] using congrArg (fun t ↦ (ρ_ G).inv ≫ t) hw


private lemma phi_transport
    (k : Type u) [Field k] (G : (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    (M : ModuleCat.{u} (MvPolynomial (Fin 2) k)) (𝓜 : ℤ → AddSubgroup M)
    (φ : ∀ z : ℤ, 0 ≤ z →
      (𝓜 z ≃+ Γ(G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k) z, ⊤)))
    (i j : ℤ) (h : i = j) (hi : 0 ≤ i) (hj : 0 ≤ j)
    (v : M) (hvi : v ∈ 𝓜 i) (hvj : v ∈ 𝓜 j) :
    (eqToHom (congrArg (fun z ↦ G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k) z)
      h)).app ⊤ (φ i hi ⟨v, hvi⟩) = φ j hj ⟨v, hvj⟩ := by
  subst j
  rfl

/-- Canonical charts commute with restriction on homogeneous representatives.
Source: Stacks Project, Proposition 0BXD, final paragraph; the homogeneous calculation
in step 3 of lem-sc-p1-serre-section-module-charts.
(blueprint: lem-sc-p1-serre-section-module-chart-restriction)

Proof: for y of degree m*d the characterization of alpha_f identifies the restriction
of phi(y) with multiplication of s by f^m. Restrict this equality to D+(g). Multiply
by a^m and use hphi to identify the numerator with phi(a^m*y). When f,g,a are nonzero,
uniqueness of homogeneous degree in g^e=a*f gives e*b=c+d. Thus a^m*y has degree
e*m*b, and (a*f)^m=g^(e*m) identifies the multiplication on the right with the
one in the characterization of alpha_g. That characterization gives the displayed
fraction formula. If a=0 or f=0, the relation forces g=0 (the polynomial ring is a
domain and e>0); the target chart and target localization are zero. If g=0 directly,
the same zero argument applies. The case m=0 uses the zeroth power, unitToTwistZero
and the right unitor, so the argument also covers denominator one. -/
theorem serreSectionModuleChartRestriction
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
    (f g : MvPolynomial (Fin 2) k) (d b : ℕ)
    (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
    (hg : g ∈ homogeneousSubmodule (Fin 2) k b)
    (alphaF : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
      LocalizedModule.Away f M)
    (alphaG : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) g)) →+
      LocalizedModule.Away g M)
    (hnormF : ∀ (m : ℕ) (y : 𝓜 (0 + ((m • d : ℕ) : ℤ)))
        (s : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
      alphaF s = mk (y : M) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) ↔
        (G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k)
          (0 + ((m • d : ℕ) : ℤ))).presheaf.map
            (homOfLE le_top : basicOpen (homogeneousSubmodule (Fin 2) k) f ⟶ ⊤).op
            (φ _ (by positivity) y) =
          Scheme.Modules.Hom.app
            ((ρ_ G).inv ≫ G ◁ Proj.unitToTwist (SetLike.pow_mem_graded m hf))
            (basicOpen (homogeneousSubmodule (Fin 2) k) f) s)
    (hnormG : ∀ (m : ℕ) (y : 𝓜 (0 + ((m • b : ℕ) : ℤ)))
        (s : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) g))),
      alphaG s = mk (y : M) (⟨g ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers g) ↔
        (G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k)
          (0 + ((m • b : ℕ) : ℤ))).presheaf.map
            (homOfLE le_top : basicOpen (homogeneousSubmodule (Fin 2) k) g ⟶ ⊤).op
            (φ _ (by positivity) y) =
          Scheme.Modules.Hom.app
            ((ρ_ G).inv ≫ G ◁ Proj.unitToTwist (SetLike.pow_mem_graded m hg))
            (basicOpen (homogeneousSubmodule (Fin 2) k) g) s)
    (inc : basicOpen (homogeneousSubmodule (Fin 2) k) g ≤
      basicOpen (homogeneousSubmodule (Fin 2) k) f)
    (e c : ℕ) (a : MvPolynomial (Fin 2) k)
    (ha : a ∈ homogeneousSubmodule (Fin 2) k c) (hrel : g ^ e = a * f)
    (m : ℕ) (y : 𝓜 (0 + ((m • d : ℕ) : ℤ)))
    (s : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)))
    (hs : alphaF s = mk (y : M) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f)) :
    alphaG (G.val.map (homOfLE inc).op s) =
      mk (a ^ m • (y : M)) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g) := by
  classical
  by_cases hg0 : g = 0
  · subst g
    let : Subsingleton (LocalizedModule.Away (0 : MvPolynomial (Fin 2) k) M) :=
      LocalizedModule.subsingleton (by exact ⟨1, by simp⟩)
    exact Subsingleton.elim _ _
  have hgp : g ^ e ≠ 0 := pow_ne_zero _ hg0
  have hdeg : e * b = c + d := by
    have hp := SetLike.pow_mem_graded e hg
    have hmul := SetLike.mul_mem_graded ha hf
    rw [← hrel] at hmul
    simpa [nsmul_eq_mul] using MvPolynomial.IsHomogeneous.inj_right hp hmul hgp
  have ham := SetLike.pow_mem_graded m ha
  have hay : a ^ m • (y : M) ∈ 𝓜 (0 + (((e * m) • b : ℕ) : ℤ)) := by
    have ht := hsmul (m • c) (0 + ((m • d : ℕ) : ℤ)) (a ^ m) y ham y.2
    convert ht using 1
    congr 1
    simp only [nsmul_eq_mul, Nat.cast_mul, zero_add]
    have hi : (e : ℤ) * b = c + d := by exact_mod_cast hdeg
    norm_cast at *
    nlinarith [congrArg (fun t : ℕ ↦ m * t) hdeg]
  apply (hnormG (e * m) ⟨a ^ m • (y : M), hay⟩ _).mpr
  have hs' := (hnormF m y s).mp hs
  have hay' : a ^ m • (y : M) ∈ 𝓜
      ((0 + ((m • d : ℕ) : ℤ)) + ((m • c : ℕ) : ℤ)) := by
    simpa [add_comm] using hsmul (m • c) _ (a ^ m) y ham y.2
  have hindex : (0 + ((m • d : ℕ) : ℤ)) + ((m • c : ℕ) : ℤ) =
      0 + (((e * m) • b : ℕ) : ℤ) := by
    simp only [nsmul_eq_mul, Nat.cast_mul, zero_add]
    norm_cast
    nlinarith [congrArg (fun t : ℕ ↦ m * t) hdeg]
  have hphi := hφ _ (by positivity) (m • c) (by positivity) (a ^ m) ham y hay'
  have ht := phi_transport k G M 𝓜 φ _ _ hindex (by positivity) (by positivity)
    (a ^ m • (y : M)) hay' hay
  rw [hphi] at ht
  rw [← ht]
  rw [← Scheme.Modules.Hom.app_presheaf_map]
  rw [← Scheme.Modules.Hom.app_presheaf_map]
  have hsres := congrArg
    ((G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k)
      (0 + ((m • d : ℕ) : ℤ))).presheaf.map (homOfLE inc).op) hs'
  rw [Scheme.Modules.presheaf_map_map_apply] at hsres
  rw [← Scheme.Modules.Hom.app_presheaf_map] at hsres
  have hh : (homOfLE inc ≫
      (homOfLE le_top : basicOpen (homogeneousSubmodule (Fin 2) k) f ⟶ ⊤)) =
      (homOfLE le_top : basicOpen (homogeneousSubmodule (Fin 2) k) g ⟶ ⊤) :=
    Subsingleton.elim _ _
  rw [hh] at hsres
  rw [hsres]
  change (eqToHom (congrArg
    (fun z ↦ G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k) z) hindex)).app _
      ((G ◁ Proj.twistMul (0 + ((m • d : ℕ) : ℤ)) ham).app _
        (((ρ_ G).inv ≫ G ◁ Proj.unitToTwist (SetLike.pow_mem_graded m hf)).app _
          (G.presheaf.map (homOfLE inc).op s))) = _
  have hpow : f ^ m * a ^ m = g ^ (e * m) := by
    rw [← mul_pow, mul_comm f a, ← hrel, ← pow_mul]
  have hm := serreTwistMultiplicationProduct k G (m • d) (m • c) ((e * m) • b)
    (f ^ m) (a ^ m) (g ^ (e * m)) (SetLike.pow_mem_graded m hf) ham
    (SetLike.pow_mem_graded (e * m) hg) hindex hpow
  have h := congrArg (fun t ↦ t.app (basicOpen (homogeneousSubmodule (Fin 2) k) g)
    (G.presheaf.map (homOfLE inc).op s)) hm
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h
  convert h using 1 <;> rfl

end AlgebraicGeometry.Proj
