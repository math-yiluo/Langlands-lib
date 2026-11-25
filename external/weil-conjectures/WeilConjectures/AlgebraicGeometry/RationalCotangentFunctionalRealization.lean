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
# Realization of cotangent functionals

Source: Stacks Project, Tags 0B2D and 0B2E
(blueprint: lem-sc-rational-cotangent-functional-realization).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

private theorem stalk_transport_cancel (X : Scheme.{u}) (x y : X) (h : x = y) :
    eqToHom (congrArg (fun z : X ↦ X.presheaf.stalk z) h.symm) ≫
      (X.presheaf.stalkCongr (by rw [h]; rfl)).hom = 𝟙 (X.presheaf.stalk y) := by
  subst y
  simp

/-- Every cotangent functional is realized by a dual-number tangent vector.
This is only the inverse construction; it asserts neither a linear map on tangent vectors
nor its injectivity.
Source: Stacks Project, Tags 0B2D and 0B2E, with base `Spec k`
(blueprint: lem-sc-rational-cotangent-functional-realization).

Proof:
1. Let `s : k → R` be the structural field map and let `c(a)` be the inverse under `r`
   of the residue of `a`. The element `a - s (c(a))` belongs to the maximal ideal, since its
   residue is zero. Apply the given functional to its cotangent class to define `D(a)`.
2. This function is additive and vanishes on `s(k)`. Write `a = s(c(a)) + a'` and
   `b = s(c(b)) + b'` with `a', b'` in the maximal ideal. Their product `a' b'` has zero
   cotangent class. Expanding the product and using linearity gives the residue-valued
   Leibniz identity. Thus `a ↦ inl (residue a) + inr (r (D(a)))` is a ring homomorphism.
3. This homomorphism is local: the maximal ideal maps into the epsilon ideal, and an element
   with nonzero residue maps to a unit. The Spec-local-ring correspondence gives a morphism
   to `X` taking the closed point to `x`. Reducing the homomorphism gives the canonical residue
   map, so the morphism restricts to `X.fromSpecResidueField x`. Its restriction on `s(k)`
   consists of constants; hence the morphism is over `Spec k`, and is a tangent vector.
4. For `a` in the maximal ideal, `c(a) = 0`, so the constructed coefficient is exactly the
   prescribed functional on the class of `a`. The stalk map of the constructed morphism is
   the local homomorphism used in the construction, by the inverse identity in the
   Spec-local-ring correspondence. This gives both displayed formulas. -/
theorem exists_rationalCotangent_tangent_realization
    (k : Type u) [Field k] (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) (x : X) :
    let R := X.presheaf.stalk x
    let K := X.residueField x
    let r : k →+* K :=
      (StructureSheaf.toStalk k (p x) ≫ p.stalkMap x ≫ X.residue x).hom
    Function.Bijective r →
    letI : Module K (IsLocalRing.CotangentSpace R) :=
      inferInstanceAs (Module (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R))
    letI : Module k (IsLocalRing.CotangentSpace R) :=
      Module.compHom (IsLocalRing.CotangentSpace R) r
    ∀ ℓ : IsLocalRing.CotangentSpace R →ₗ[k] k,
      ∃ θ : schemeTangentSpace k X p x,
        ∃ hx : θ.val (IsLocalRing.closedPoint (DualNumber K)) = x,
          let sharp : R →+* DualNumber K :=
            (eqToHom (congrArg (fun y : X ↦ X.presheaf.stalk y) hx.symm) ≫
              Scheme.stalkClosedPointTo θ.val).hom
          ∃ D : R → k,
            (∀ a : R, sharp a =
              TrivSqZeroExt.inl ((X.residue x).hom a) + TrivSqZeroExt.inr (r (D a))) ∧
            (∀ a : IsLocalRing.maximalIdeal R,
              ℓ ((IsLocalRing.maximalIdeal R).toCotangent a) = D a) := by
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
  intro ℓ
  let e := RingEquiv.ofBijective r hr
  let c : R →+* k := e.symm.toRingHom.comp res
  have hc (a : R) : r (c a) = res a := e.apply_symm_apply _
  have hcs (a : k) : c (s a) = a := by
    apply hr.1
    rw [hc]
    rfl
  have hb (a : R) : a - s (c a) ∈ IsLocalRing.maximalIdeal R := by
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    change res (a - s (c a)) = 0
    rw [map_sub]
    change res a - r (c a) = 0
    rw [hc, sub_self]
  let b : R →+ IsLocalRing.maximalIdeal R :=
    { toFun := fun a ↦ ⟨a - s (c a), hb a⟩
      map_zero' := by ext; simp
      map_add' := fun a a' ↦ by
        apply Subtype.ext
        change a + a' - s (c (a + a')) = (a - s (c a)) + (a' - s (c a'))
        simp only [map_add]
        abel }
  let D : R →+ k := ℓ.toAddMonoidHom.comp
    ((IsLocalRing.maximalIdeal R).toCotangent.toAddMonoidHom.comp b)
  let : Algebra R K := inferInstanceAs (Algebra R (IsLocalRing.ResidueField R))
  let : IsScalarTower R K (IsLocalRing.CotangentSpace R) :=
    inferInstanceAs (IsScalarTower R (IsLocalRing.ResidueField R)
      (IsLocalRing.CotangentSpace R))
  have hsmul (a : k) (v : IsLocalRing.CotangentSpace R) : a • v = s a • v := by
    change r a • v = s a • v
    exact IsScalarTower.algebraMap_smul K (s a) v
  have hmul (a a' : R) : D (a * a') = c a * D a' + c a' * D a := by
    have hquot : (IsLocalRing.maximalIdeal R).toCotangent (b (a * a')) =
        c a • (IsLocalRing.maximalIdeal R).toCotangent (b a') +
        c a' • (IsLocalRing.maximalIdeal R).toCotangent (b a) := by
      rw [hsmul, hsmul,
        ← (IsLocalRing.maximalIdeal R).toCotangent.map_smul,
        ← (IsLocalRing.maximalIdeal R).toCotangent.map_smul,
        ← (IsLocalRing.maximalIdeal R).toCotangent.map_add, Ideal.toCotangent_eq]
      change a * a' - s (c (a * a')) -
        (s (c a) * (a' - s (c a')) + s (c a') * (a - s (c a))) ∈
          IsLocalRing.maximalIdeal R ^ 2
      have heq : a * a' - s (c (a * a')) -
          (s (c a) * (a' - s (c a')) + s (c a') * (a - s (c a))) =
            (a - s (c a)) * (a' - s (c a')) := by
        simp only [map_mul]
        ring
      rw [heq, pow_two]
      exact Ideal.mul_mem_mul (hb a) (hb a')
    change ℓ ((IsLocalRing.maximalIdeal R).toCotangent (b (a * a'))) = _
    rw [hquot, map_add, map_smul, map_smul]
    rfl
  have hDs (a : k) : D (s a) = 0 := by
    have hb0 : b (s a) = 0 := by
      ext
      change s a - s (c (s a)) = 0
      rw [hcs, sub_self]
    change ℓ ((IsLocalRing.maximalIdeal R).toCotangent (b (s a))) = 0
    rw [hb0, map_zero, map_zero]
  let sharp : R →+* DualNumber K :=
    { toFun := fun a ↦ TrivSqZeroExt.inl (res a) + TrivSqZeroExt.inr (r (D a))
      map_zero' := by simp
      map_one' := by
        have hD1 : D 1 = 0 := by simpa using hDs 1
        ext <;> simp [hD1]
      map_add' := fun a a' ↦ by ext <;> simp
      map_mul' := fun a a' ↦ by
        ext
        · simp
        · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
            TrivSqZeroExt.snd_inr, zero_add, TrivSqZeroExt.snd_mul,
            TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
            add_zero, hmul, map_add, map_mul, hc, smul_eq_mul]
          simp only [op_smul_eq_mul]
          ring }
  have hfst (a : R) : (sharp a).fst = res a := by simp [sharp]
  have : IsLocalHom sharp :=
    ⟨fun a ha ↦ (IsLocalRing.residue_ne_zero_iff_isUnit a).mp (by
      change res a ≠ 0
      rw [← hfst]
      exact isUnit_iff_ne_zero.mp (TrivSqZeroExt.isUnit_iff_isUnit_fst.mp ha))⟩
  let f : Spec (.of (DualNumber K)) ⟶ X :=
    Spec.map (CommRingCat.ofHom sharp) ≫ X.fromSpecStalk x
  have hx : f (IsLocalRing.closedPoint (DualNumber K)) = x := by
    change (Spec.map (CommRingCat.ofHom sharp) ≫ X.fromSpecStalk x) _ = x
    rw [Scheme.Hom.comp_apply, Spec_closedPoint]
    exact Scheme.fromSpecStalk_closedPoint
  have hf : f ≫ p =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom K K)) ≫
        X.fromSpecResidueField x ≫ p := by
    dsimp only [f, Scheme.fromSpecResidueField]
    simp only [Category.assoc]
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk p, Spec.fromSpecStalk_eq']
    simp only [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change sharp (s a) = TrivSqZeroExt.inl (res (s a))
    simp [sharp, hDs]
  have hclosed : Spec.map
      (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ f =
        X.fromSpecResidueField x := by
    dsimp [f, Scheme.fromSpecResidueField]
    rw [← Spec.map_comp_assoc]
    congr 2
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact hfst
  let θ : schemeTangentSpace k X p x := ⟨f, hclosed, hf⟩
  have hsharp :
      (eqToHom (congrArg (fun y : X ↦ X.presheaf.stalk y) hx.symm) ≫
        Scheme.stalkClosedPointTo f).hom = sharp := by
    have hpair := (SpecToEquivOfLocalRing X (.of (DualNumber K))).apply_symm_apply
      ⟨x, CommRingCat.ofHom sharp, inferInstance⟩
    obtain ⟨hpoint, hmap⟩ := SpecToEquivOfLocalRing_eq_iff.mp hpair
    change f (IsLocalRing.closedPoint (DualNumber K)) = x at hpoint
    change Scheme.stalkClosedPointTo f = _ at hmap
    change _ = (CommRingCat.ofHom sharp).hom
    apply congrArg CommRingCat.Hom.hom
    rw [hmap, ← Category.assoc, stalk_transport_cancel X _ x hpoint, Category.id_comp]
  refine ⟨θ, hx, D, ?_, ?_⟩
  · intro a
    change _ = sharp a
    rw [hsharp]
  · intro a
    have hca : c a = 0 := by
      change e.symm (res a) = 0
      have ha : res a = 0 := (IsLocalRing.residue_eq_zero_iff (a : R)).mpr a.2
      rw [ha, map_zero]
    have hba : b a = a := by
      ext
      change (a : R) - s (c a) = a
      rw [hca, map_zero, sub_zero]
    change _ = ℓ ((IsLocalRing.maximalIdeal R).toCotangent (b a))
    rw [hba]


end AlgebraicGeometry
