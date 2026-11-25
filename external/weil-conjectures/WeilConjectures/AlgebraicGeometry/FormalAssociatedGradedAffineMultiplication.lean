/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormalKernelGradedPieces
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.LinearAlgebra.Quotient.Bilinear
import WeilConjectures.AlgebraicGeometry.FormalPolynomialPowerLifts

/-! # Multiplication of associated graded pieces on the affine basis

Source: Stacks Tags 087Z, 01I8 and 01IC.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- On an affine open the power inclusion has range equal to the ideal power. -/
theorem power_affine_range {X : Scheme.{u}} (I : X.IdealSheafData)
    (V : X.affineOpens) (n : ℕ) :
    Set.range ((Scheme.idealSheafPower I.toModulesι n).2.app V.1) =
      {a | a ∈ I.ideal V ^ n} := by
  cases n with
  | zero =>
    simp only [Scheme.idealSheafPower, Scheme.Modules.Hom.id_app, pow_zero]
    ext a
    simp
  | succ n =>
    have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
      SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
    exact ((Scheme.Modules.ideal_times_quasiCoherent_affine_sections I
      (SheafOfModules.unit X.ringCatSheaf)).2.2.2.1 V).2.2.2 (n + 1) (Nat.succ_pos n)

/-- On an affine open the product of two power sections lifts to their sum power. -/
theorem power_affine_product {X : Scheme.{u}} (I : X.IdealSheafData)
    (m n : ℕ) (V : X.affineOpens)
    (a : Γ((Scheme.idealSheafPower I.toModulesι m).1, V.1))
    (b : Γ((Scheme.idealSheafPower I.toModulesι n).1, V.1)) :
    ∃ c : Γ((Scheme.idealSheafPower I.toModulesι (m + n)).1, V.1),
      (Scheme.idealSheafPower I.toModulesι (m + n)).2.app V.1 c =
        (@id Γ(X, V.1) ((Scheme.idealSheafPower I.toModulesι m).2.app V.1 a)) *
          (@id Γ(X, V.1) ((Scheme.idealSheafPower I.toModulesι n).2.app V.1 b)) := by
  have ha : (@id Γ(X, V.1)
      ((Scheme.idealSheafPower I.toModulesι m).2.app V.1 a)) ∈ I.ideal V ^ m := by
    change _ ∈ {a | a ∈ I.ideal V ^ m}
    rw [← power_affine_range I V m]
    exact ⟨a, rfl⟩
  have hb : (@id Γ(X, V.1)
      ((Scheme.idealSheafPower I.toModulesι n).2.app V.1 b)) ∈ I.ideal V ^ n := by
    change _ ∈ {a | a ∈ I.ideal V ^ n}
    rw [← power_affine_range I V n]
    exact ⟨b, rfl⟩
  have hab := Ideal.mul_mem_mul ha hb
  rw [← pow_add] at hab
  have hmem : (@id Γ(X, V.1) ((Scheme.idealSheafPower I.toModulesι m).2.app V.1 a)) *
      (@id Γ(X, V.1) ((Scheme.idealSheafPower I.toModulesι n).2.app V.1 b)) ∈
      Set.range ((Scheme.idealSheafPower I.toModulesι (m + n)).2.app V.1) := by
    rw [power_affine_range I V (m + n)]
    exact hab
  exact hmem

private theorem projection_surjective {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) (V : X.affineOpens) :
    Function.Surjective ((formalAssociatedGradedπ I n).app V.1) := by
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have : (Scheme.idealSheafPower I.toModulesι n).1.IsQuasicoherent := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
    · exact (Scheme.Modules.ideal_times_quasiCoherent_affine_sections I
        (SheafOfModules.unit X.ringCatSheaf)).2.2.1 n hn
  exact ((Scheme.Modules.ideal_times_quasiCoherent_affine_sections I
    (Scheme.idealSheafPower I.toModulesι n).1).2.2.2.1 V).2.1

private theorem projection_kernel {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) (V : X.affineOpens)
    (a : Γ((Scheme.idealSheafPower I.toModulesι n).1, V.1)) :
    (formalAssociatedGradedπ I n).app V.1 a = 0 ↔
      (@id Γ(X, V.1) ((Scheme.idealSheafPower I.toModulesι n).2.app V.1 a)) ∈
        I.ideal V ^ (n + 1) := by
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have : (Scheme.idealSheafPower I.toModulesι n).1.IsQuasicoherent := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
    · exact (Scheme.Modules.ideal_times_quasiCoherent_affine_sections I
        (SheafOfModules.unit X.ringCatSheaf)).2.2.1 n hn
  have hker := ((Scheme.Modules.ideal_times_quasiCoherent_affine_sections I
    (Scheme.idealSheafPower I.toModulesι n).1).2.2.2.1 V).2.2.1 a
  change (formalAssociatedGradedπ I n).app V.1 a = 0 ↔
    a ∈ I.ideal V • (⊤ : Submodule Γ(X, V.1)
      Γ((Scheme.idealSheafPower I.toModulesι n).1, V.1)) at hker
  rw [hker]
  let im : Γ((Scheme.idealSheafPower I.toModulesι n).1, V.1) →ₗ[Γ(X, V.1)] Γ(X, V.1) :=
    ((Scheme.idealSheafPower I.toModulesι n).2.val.app (op V.1)).hom
  have hr : (LinearMap.range im : Ideal Γ(X, V.1)) = I.ideal V ^ n := by
    apply SetLike.coe_injective
    exact power_affine_range I V n
  have hmap : Submodule.map im (I.ideal V • ⊤) = I.ideal V ^ (n + 1) := by
    rw [Submodule.map_smul'', Submodule.map_top, hr, Ideal.smul_eq_mul, pow_succ']
  constructor
  · intro ha
    rw [← hmap]
    exact Submodule.mem_map_of_mem ha
  · intro ha
    rw [← hmap] at ha
    obtain ⟨b, hb, hba⟩ := ha
    exact formalPolynomial_power_injective I.toModulesι n V.1 hba ▸ hb

/-- Multiplication of representatives descends on the affine basis.
Source: Stacks Tags 087Z, 01I8 and 01IC.
(blueprint: lem-weil-pbc-formal-associated-graded-affine-multiplication).

Proof: Put R = Gamma(X,V) and J = I.ideal V. The affine power range theorem
identifies the monic inclusion of the m-th power with J^m (degree zero is R).
The affine quotient theorem gives a surjective projection with kernel
J times J^m, which maps under that inclusion to J^(m+1). Thus its quotient is
J^m/J^(m+1). Multiply representatives into J^(m+n), then project to its
quotient. If the first input changes by J^(m+1), its product changes by
J^(m+n+1); the same holds for the second input. Lift this bilinear map through
both quotient projections (LinearMap.liftQ₂), transporting along the affine
quotient identifications. This proves the displayed identity for every lift c
of the product, since the power inclusion is injective. Restrictions between
affine opens commute with the inclusions, quotient projections and ring
multiplication. Surjectivity of the two source projections therefore proves
naturality on all inputs. Degree zero, the zero ideal, the unit ideal and the
empty affine open all satisfy the same power and quotient computations. -/
theorem formalAssociatedGraded_affine_multiplication_exists {X : Scheme.{u}}
    (I : X.IdealSheafData) (m n : ℕ) :
    ∃ beta : ∀ V : X.affineOpens,
      (formalAssociatedGradedPiece I m).val.obj (op V.1) →ₗ[Γ(X, V.1)]
        (formalAssociatedGradedPiece I n).val.obj (op V.1) →ₗ[Γ(X, V.1)]
          (formalAssociatedGradedPiece I (m + n)).val.obj (op V.1),
      (∀ (V W : X.affineOpens) (h : W.1 ≤ V.1)
        (a : (formalAssociatedGradedPiece I m).val.obj (op V.1))
        (b : (formalAssociatedGradedPiece I n).val.obj (op V.1)),
        (formalAssociatedGradedPiece I (m + n)).val.map (homOfLE h).op (beta V a b) =
          beta W ((formalAssociatedGradedPiece I m).val.map (homOfLE h).op a)
            ((formalAssociatedGradedPiece I n).val.map (homOfLE h).op b)) ∧
      (∀ (V : X.affineOpens)
        (a : (Scheme.idealSheafPower I.toModulesι m).1.val.obj (op V.1))
        (b : (Scheme.idealSheafPower I.toModulesι n).1.val.obj (op V.1))
        (c : (Scheme.idealSheafPower I.toModulesι (m + n)).1.val.obj (op V.1)),
        (Scheme.idealSheafPower I.toModulesι (m + n)).2.val.app (op V.1) c =
          (@id Γ(X, V.1) ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op V.1) a)) *
            (@id Γ(X, V.1) ((Scheme.idealSheafPower I.toModulesι n).2.val.app (op V.1) b)) →
        beta V ((formalAssociatedGradedπ I m).val.app (op V.1) a)
          ((formalAssociatedGradedπ I n).val.app (op V.1) b) =
            (formalAssociatedGradedπ I (m + n)).val.app (op V.1) c) := by
  classical
  have hV (V : X.affineOpens) :
      ∃ beta : (formalAssociatedGradedPiece I m).val.obj (op V.1) →ₗ[Γ(X, V.1)]
          (formalAssociatedGradedPiece I n).val.obj (op V.1) →ₗ[Γ(X, V.1)]
            (formalAssociatedGradedPiece I (m + n)).val.obj (op V.1),
        ∀ (a : Γ((Scheme.idealSheafPower I.toModulesι m).1, V.1))
          (b : Γ((Scheme.idealSheafPower I.toModulesι n).1, V.1))
          (c : Γ((Scheme.idealSheafPower I.toModulesι (m + n)).1, V.1)),
          (Scheme.idealSheafPower I.toModulesι (m + n)).2.app V.1 c =
            (@id Γ(X, V.1) ((Scheme.idealSheafPower I.toModulesι m).2.app V.1 a)) *
              (@id Γ(X, V.1) ((Scheme.idealSheafPower I.toModulesι n).2.app V.1 b)) →
          beta ((formalAssociatedGradedπ I m).app V.1 a)
            ((formalAssociatedGradedπ I n).app V.1 b) =
              (formalAssociatedGradedπ I (m + n)).app V.1 c := by
    let R := Γ(X, V.1)
    let A := Γ((Scheme.idealSheafPower I.toModulesι m).1, V.1)
    let B := Γ((Scheme.idealSheafPower I.toModulesι n).1, V.1)
    let C := Γ((Scheme.idealSheafPower I.toModulesι (m + n)).1, V.1)
    let im : A →ₗ[R] R := ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op V.1)).hom
    let jn : B →ₗ[R] R := ((Scheme.idealSheafPower I.toModulesι n).2.val.app (op V.1)).hom
    let k : C →ₗ[R] R :=
      ((Scheme.idealSheafPower I.toModulesι (m + n)).2.val.app (op V.1)).hom
    let pm : Γ((Scheme.idealSheafPower I.toModulesι m).1, V.1) →ₗ[R]
        Γ(formalAssociatedGradedPiece I m, V.1) :=
      ((formalAssociatedGradedπ I m).val.app (op V.1)).hom
    let pn : Γ((Scheme.idealSheafPower I.toModulesι n).1, V.1) →ₗ[R]
        Γ(formalAssociatedGradedPiece I n, V.1) :=
      ((formalAssociatedGradedπ I n).val.app (op V.1)).hom
    let pk : Γ((Scheme.idealSheafPower I.toModulesι (m + n)).1, V.1) →ₗ[R]
        Γ(formalAssociatedGradedPiece I (m + n), V.1) :=
      ((formalAssociatedGradedπ I (m + n)).val.app (op V.1)).hom
    have hp (a : A) (b : B) := power_affine_product I m n V a b
    choose prod hprod using hp
    change ∀ (a : A) (b : B), k (prod a b) = im a * jn b at hprod
    have hk : Function.Injective k := formalPolynomial_power_injective I.toModulesι (m + n) V.1
    let mult : A →ₗ[R] B →ₗ[R] C := LinearMap.mk₂ R prod
      (by intro a a' b; apply hk; simp only [map_add, hprod, add_mul])
      (by intro r a b; apply hk; simp only [map_smul, hprod, smul_eq_mul, mul_assoc])
      (by intro a b b'; apply hk; simp only [map_add, hprod, mul_add])
      (by intro r a b; apply hk; simp only [map_smul, hprod, smul_eq_mul]; ring)
    let f := mult.compr₂ pk
    have hleft : LinearMap.ker pm ≤ LinearMap.ker f := by
      intro a ha
      apply LinearMap.ext
      intro b
      change pk (prod a b) = 0
      apply (projection_kernel I (m + n) V (prod a b)).mpr
      change k (prod a b) ∈ I.ideal V ^ (m + n + 1)
      rw [hprod]
      have ha' := (projection_kernel I m V a).mp ha
      change im a ∈ I.ideal V ^ (m + 1) at ha'
      have hb' : jn b ∈ I.ideal V ^ n := by
        change _ ∈ {x | x ∈ I.ideal V ^ n}
        rw [← power_affine_range I V n]
        exact ⟨b, rfl⟩
      have h := Ideal.mul_mem_mul ha' hb'
      rw [← pow_add] at h
      have hexp : m + 1 + n = m + n + 1 := by omega
      simpa only [hexp] using h
    have hright : LinearMap.ker pn ≤ LinearMap.ker f.flip := by
      intro b hb
      apply LinearMap.ext
      intro a
      change pk (prod a b) = 0
      apply (projection_kernel I (m + n) V (prod a b)).mpr
      change k (prod a b) ∈ I.ideal V ^ (m + n + 1)
      rw [hprod]
      have hb' := (projection_kernel I n V b).mp hb
      change jn b ∈ I.ideal V ^ (n + 1) at hb'
      have ha' : im a ∈ I.ideal V ^ m := by
        change _ ∈ {x | x ∈ I.ideal V ^ m}
        rw [← power_affine_range I V m]
        exact ⟨a, rfl⟩
      have h := Ideal.mul_mem_mul ha' hb'
      rw [← pow_add] at h
      simpa only [Nat.add_assoc] using h
    let fq := f.liftQ₂ (LinearMap.ker pm) (LinearMap.ker pn) hleft hright
    let em := pm.quotKerEquivOfSurjective (projection_surjective I m V)
    let en := pn.quotKerEquivOfSurjective (projection_surjective I n V)
    let beta := (fq.compl₂ en.symm.toLinearMap).comp em.symm.toLinearMap
    refine ⟨beta, ?_⟩
    intro a b c hc
    have hpc : prod a b = c := hk ((hprod a b).trans hc.symm)
    change fq (em.symm (pm a)) (en.symm (pn b)) = pk c
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply,
      LinearMap.quotKerEquivOfSurjective_symm_apply, LinearMap.liftQ₂_mk]
    change pk (prod a b) = pk c
    rw [hpc]
  choose beta hrep using hV
  refine ⟨beta, ?_, hrep⟩
  intro V W h a b
  obtain ⟨a', rfl⟩ := projection_surjective I m V a
  obtain ⟨b', rfl⟩ := projection_surjective I n V b
  obtain ⟨c, hc⟩ := power_affine_product I m n V a' b'
  rw [hrep V a' b' c hc]
  change (formalAssociatedGradedPiece I (m + n)).presheaf.map (homOfLE h).op
      ((formalAssociatedGradedπ I (m + n)).app V.1 c) =
    beta W ((formalAssociatedGradedPiece I m).presheaf.map (homOfLE h).op
      ((formalAssociatedGradedπ I m).app V.1 a'))
      ((formalAssociatedGradedPiece I n).presheaf.map (homOfLE h).op
        ((formalAssociatedGradedπ I n).app V.1 b'))
  erw [← PresheafOfModules.naturality_apply,
    ← PresheafOfModules.naturality_apply,
    ← PresheafOfModules.naturality_apply]
  symm
  apply hrep W
  erw [PresheafOfModules.naturality_apply,
    PresheafOfModules.naturality_apply,
    PresheafOfModules.naturality_apply, hc]
  exact map_mul (X.presheaf.map (homOfLE h).op).hom _ _


end AlgebraicGeometry
