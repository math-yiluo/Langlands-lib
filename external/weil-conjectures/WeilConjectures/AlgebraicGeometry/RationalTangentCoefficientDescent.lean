/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Linear descent of tangent coefficients

Source: Stacks Project, Tags 0B2D and 0B2E
(blueprint: lem-sc-rational-tangent-coefficient-descent).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The coefficient of each tangent vector descends to a cotangent functional.
Source: Stacks Project, Tags 0B2D and 0B2E, with base `Spec k`
(blueprint: lem-sc-rational-tangent-coefficient-descent).

Proof:
1. The closed-point restriction of a tangent vector gives the residue map upon reducing its
   stalk homomorphism modulo epsilon: reconstruct the spectrum morphism from its stalk map
   and cancel the monomorphism from the local spectrum to `X`. Apply the inverse of the
   bijective structural residue map `r` to the second dual-number coordinate. The resulting
   function `D` is additive, by addition of coordinates.
2. The condition that the vector is over `Spec k` says that the structural field map `s`
   is sent to the constant dual numbers. Thus `D (s c) = 0` for every `c` in `k`.
   Multiplication of coordinates gives the residue-valued Leibniz rule for `D`.
3. On the maximal ideal, this rule kills products of two ideal elements, and additivity kills
   their finite sums. Hence `D` descends to the quotient by the square ideal. Multiplication
   by the structural copy of `k` shows that the descended functional is `k`-linear.
4. Perform this explicit construction for each tangent vector; its formulas give the
   stated function into the cotangent dual. -/
theorem exists_rationalTangent_coefficient_descent
    (k : Type u) [Field k] (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) (x : X) :
    let R := X.presheaf.stalk x
    let K := X.residueField x
    let s : k →+* R := (StructureSheaf.toStalk k (p x) ≫ p.stalkMap x).hom
    let r : k →+* K :=
      (StructureSheaf.toStalk k (p x) ≫ p.stalkMap x ≫ X.residue x).hom
    Function.Bijective r →
    letI : Module K (IsLocalRing.CotangentSpace R) :=
      inferInstanceAs (Module (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R))
    letI : Module k (IsLocalRing.CotangentSpace R) :=
      Module.compHom (IsLocalRing.CotangentSpace R) r
    ∃ L : schemeTangentSpace k X p x → (IsLocalRing.CotangentSpace R →ₗ[k] k),
      ∀ θ : schemeTangentSpace k X p x,
        ∃ hx : θ.val (IsLocalRing.closedPoint (DualNumber K)) = x,
          let sharp : R →+* DualNumber K :=
            (eqToHom (congrArg (fun y : X ↦ X.presheaf.stalk y) hx.symm) ≫
              Scheme.stalkClosedPointTo θ.val).hom
          ∃ D : R →+ k,
            (∀ a : R, sharp a =
              TrivSqZeroExt.inl ((X.residue x).hom a) + TrivSqZeroExt.inr (r (D a))) ∧
            (∀ a : IsLocalRing.maximalIdeal R,
              L θ ((IsLocalRing.maximalIdeal R).toCotangent a) = D a) ∧
            (∀ c : k, D (s c) = 0) := by
  dsimp only
  intro hr
  let R := X.presheaf.stalk x
  let K := X.residueField x
  let s : k →+* R := (StructureSheaf.toStalk k (p x) ≫ p.stalkMap x).hom
  let r : k →+* K :=
    (StructureSheaf.toStalk k (p x) ≫ p.stalkMap x ≫ X.residue x).hom
  let res : R →+* K := (X.residue x).hom
  let : Module K (IsLocalRing.CotangentSpace R) :=
    inferInstanceAs (Module (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R))
  let : Module k (IsLocalRing.CotangentSpace R) :=
    Module.compHom (IsLocalRing.CotangentSpace R) r
  let : Algebra R K := inferInstanceAs (Algebra R (IsLocalRing.ResidueField R))
  let : IsScalarTower R K (IsLocalRing.CotangentSpace R) :=
    inferInstanceAs (IsScalarTower R (IsLocalRing.ResidueField R)
      (IsLocalRing.CotangentSpace R))
  let e := RingEquiv.ofBijective r hr
  let fst : DualNumber K →+* K := (TrivSqZeroExt.fstHom K K K).toRingHom
  have : IsLocalHom fst := ⟨fun a ha ↦ TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha⟩
  have hθ (θ : schemeTangentSpace k X p x) :
      ∃ ℓ : IsLocalRing.CotangentSpace R →ₗ[k] k,
        ∃ hx : θ.val (IsLocalRing.closedPoint (DualNumber K)) = x,
          let sharp : R →+* DualNumber K :=
            (eqToHom (congrArg (fun y : X ↦ X.presheaf.stalk y) hx.symm) ≫
              Scheme.stalkClosedPointTo θ.val).hom
          ∃ D : R →+ k,
            (∀ a : R, sharp a =
              TrivSqZeroExt.inl (res a) + TrivSqZeroExt.inr (r (D a))) ∧
            (∀ a : IsLocalRing.maximalIdeal R,
              ℓ ((IsLocalRing.maximalIdeal R).toCotangent a) = D a) ∧
            (∀ c : k, D (s c) = 0) := by
    have hx : θ.val (IsLocalRing.closedPoint (DualNumber K)) = x := by
      have h := congrArg (fun f : Spec K ⟶ X ↦ f (IsLocalRing.closedPoint K)) θ.property.1
      change (Spec.map (CommRingCat.ofHom fst) ≫ θ.val) _ = _ at h
      rw [Scheme.Hom.comp_apply, Spec_closedPoint] at h
      exact h.trans (Scheme.fromSpecResidueField_apply x _)
    let sharp : R →+* DualNumber K :=
      (eqToHom (congrArg (fun y : X ↦ X.presheaf.stalk y) hx.symm) ≫
        Scheme.stalkClosedPointTo θ.val).hom
    have hrepr : θ.val = Spec.map (CommRingCat.ofHom sharp) ≫ X.fromSpecStalk x := by
      dsimp only [sharp]
      have H (y : X) (hy : θ.val (IsLocalRing.closedPoint (DualNumber K)) = y) :
          θ.val = Spec.map (eqToHom
            (congrArg (fun z : X ↦ X.presheaf.stalk z) hy.symm) ≫
            Scheme.stalkClosedPointTo θ.val) ≫ X.fromSpecStalk y := by
        subst y
        simpa using (Scheme.Spec_stalkClosedPointTo_fromSpecStalk θ.val).symm
      exact H x hx
    have hfst (a : R) : (sharp a).fst = res a := by
      have h := θ.property.1
      rw [hrepr] at h
      change Spec.map (CommRingCat.ofHom fst) ≫
        (Spec.map (CommRingCat.ofHom sharp) ≫ X.fromSpecStalk x) =
          Spec.map (X.residue x) ≫ X.fromSpecStalk x at h
      rw [← Spec.map_comp_assoc, cancel_mono, Spec.map_inj] at h
      exact congrArg (fun f : R ⟶ K ↦ f.hom a) h
    have hstruct (a : k) : sharp (s a) = TrivSqZeroExt.inl (r a) := by
      have h := θ.property.2
      rw [hrepr] at h
      dsimp only [Scheme.fromSpecResidueField] at h
      simp only [Category.assoc] at h
      rw [← Scheme.SpecMap_stalkMap_fromSpecStalk p, Spec.fromSpecStalk_eq'] at h
      simp only [← Spec.map_comp] at h
      rw [Spec.map_inj] at h
      exact congrArg (fun f : CommRingCat.of k ⟶ CommRingCat.of (DualNumber K) ↦ f.hom a) h
    let D : R →+ k :=
      { toFun := fun a ↦ e.symm (sharp a).snd
        map_zero' := by simp
        map_add' := fun a a' ↦ by simp }
    have hD (a : R) : sharp a =
        TrivSqZeroExt.inl (res a) + TrivSqZeroExt.inr (r (D a)) := by
      apply TrivSqZeroExt.ext
      · simpa using hfst a
      · change (sharp a).snd = 0 + e (e.symm (sharp a).snd)
        rw [e.apply_symm_apply, zero_add]
    have hDk (a : k) : D (s a) = 0 := by
      change e.symm (sharp (s a)).snd = 0
      rw [hstruct, TrivSqZeroExt.snd_inl, map_zero]
    let F : IsLocalRing.maximalIdeal R →ₛₗ[res] K :=
      { toFun := fun a ↦ (sharp a).snd
        map_add' := fun a a' ↦ by simp
        map_smul' := fun a b ↦ by
          have hb : res b = 0 := (IsLocalRing.residue_eq_zero_iff (b : R)).mpr b.2
          change (sharp (a * b)).snd = res a • (sharp b).snd
          simp [TrivSqZeroExt.snd_mul, hfst, hb] }
    have hF : (IsLocalRing.maximalIdeal R • ⊤ :
        Submodule R (IsLocalRing.maximalIdeal R)) ≤ LinearMap.ker F := by
      apply Submodule.smul_le.mpr
      intro a ha b _
      rw [LinearMap.mem_ker, F.map_smulₛₗ]
      have hres : res a = 0 := (IsLocalRing.residue_eq_zero_iff a).mpr ha
      rw [hres, zero_smul]
    let G := Submodule.liftQ _ F hF
    let ℓ : IsLocalRing.CotangentSpace R →ₗ[k] k :=
      { toFun := fun v ↦ e.symm (G v)
        map_add' := fun v w ↦ by simp
        map_smul' := fun a v ↦ by
          have hsmul : a • v = s a • v := by
            change r a • v = s a • v
            exact IsScalarTower.algebraMap_smul K (s a) v
          rw [hsmul, G.map_smulₛₗ]
          change e.symm (r a * G v) = a * e.symm (G v)
          rw [map_mul]
          change e.symm (e a) * e.symm (G v) = a * e.symm (G v)
          rw [e.symm_apply_apply] }
    refine ⟨ℓ, hx, D, hD, ?_, hDk⟩
    intro a
    rfl
  classical
  refine ⟨fun θ ↦ (hθ θ).choose, ?_⟩
  intro θ
  exact (hθ θ).choose_spec


end AlgebraicGeometry
