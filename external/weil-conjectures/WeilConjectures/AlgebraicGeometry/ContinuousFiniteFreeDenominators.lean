/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
public import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import WeilConjectures.AlgebraicGeometry.ContinuousRegularFunctions
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-! # Clearing denominators in finite continuous coefficient matrices -/

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A rational regular-module endomorphism on a compact scheme has one integral
numerator after multiplication by a power of ℓ.
Source: Bhatt--Scholze, Section 6.8, continuous coefficient localization.
(auxiliary; not a blueprint node)

Proof. Evaluate the endomorphism on the global unit to obtain its continuous
coefficient. Compactness bounds this function by one power of ℓ, so localization
of continuous functions supplies an integral numerator. Multiplication by this
numerator gives an integral regular endomorphism. The coefficient realizations
and the regular-module extension isomorphism identify its extension with the
specified multiple of the original morphism. This also works on the empty scheme. -/
theorem integralRegular_clear_denominators (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (X : Scheme.{u}) [CompactSpace X]
    (q : Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E) X) ⟶
      Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E) X)) :
    ∃ (k : ℕ) (p : Mod.regular (condensedRingObj (integralCoeff ℓ E) X) ⟶
        Mod.regular (condensedRingObj (integralCoeff ℓ E) X)),
      (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).map p ≫
          (Mod.regularExtensionIso (coefficientMap (integralScalarMap ℓ E) X)).hom =
        (Mod.regularExtensionIso (coefficientMap (integralScalarMap ℓ E) X)).hom ≫
          (ℓ ^ k • q) := by
  classical
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[ℓ]
  let R := condensedRingObj (integralCoeff ℓ E) X
  let S := condensedRingObj (Profinite.continuousMapRingObj E) X
  let φ := coefficientMap (integralScalarMap ℓ E) X
  let O := continuousIntegers ℓ E
  let e := chartComparison X O
  let eE := chartComparison X E
  let G := (Mod.comapEquivalenceOfIsIso (inv eE)).functor
  let jE := Mod.regularIsoOfIsIso eE
  let qE := jE.inv ≫ G.map q ≫ jE.hom
  let c := regularCoefficient X E qE
  let ψ := O.subtype.compLeftContinuous X continuous_subtype_val
  let := ψ.toAlgebra
  have hloc := continuousIntegralFunctions_isLocalization ℓ E X
  obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj (ContinuousMap.const X (ℓ : O)) c
  have ha' (x : X) : c x * (ℓ : E) ^ k = (a x : E) := by
    have h := congrArg (fun z : C(X, E) ↦ z x) ha
    change c x * ((ℓ : O) : E) ^ k = (a x : E) at h
    simpa only [SubringClass.coe_natCast] using h
  let F := (Mod.comapEquivalenceOfIsIso (inv e)).functor
  have : F.IsEquivalence := (Mod.comapEquivalenceOfIsIso (inv e)).isEquivalence_functor
  let jO := Mod.regularIsoOfIsIso e
  let pO := continuousMultiplier X O a
  let p := F.preimage (jO.hom ≫ pO ≫ jO.inv)
  have hFp : F.map p = jO.hom ≫ pO ≫ jO.inv := Functor.map_preimage _ _
  have hpO : p.hom ≫ e = e ≫ pO.hom := by
    have hh := congrArg (fun z ↦ z.hom) hFp
    change p.hom = e ≫ pO.hom ≫ inv e at hh
    rw [hh, Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hqE : q.hom ≫ eE = eE ≫ qE.hom := by
    change q.hom ≫ eE = eE ≫ (inv eE ≫ q.hom ≫ eE)
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  have hcont : pO.hom ≫ integralFunctionInclusion ℓ E X =
      integralFunctionInclusion ℓ E X ≫ (ℓ ^ k • qE).hom := by
    ext U b
    apply ULift.ext
    ext x
    change ((b.down x * a (U.unop.hom x) : O) : E) =
      ((ℓ ^ k) • (qE.hom.hom.app U
        (ULift.up ⟨fun y ↦ (b.down y : E),
          continuous_subtype_val.comp b.down.continuous⟩))).down x
    change (b.down x : E) * (a (U.unop.hom x) : E) =
      (ℓ ^ k) • (qE.hom.hom.app U
        (ULift.up ⟨fun y ↦ (b.down y : E),
          continuous_subtype_val.comp b.down.continuous⟩)).down x
    rw [continuousRegular_apply]
    rw [← ha', nsmul_eq_mul, Nat.cast_pow]
    change (b.down x : E) *
      (regularCoefficient X E qE (U.unop.hom x) * (ℓ : E) ^ k) =
      (ℓ : E) ^ k * ((b.down x : E) * regularCoefficient X E qE (U.unop.hom x))
    ring
  have he : φ ≫ eE = e ≫ integralFunctionInclusion ℓ E X :=
    chartComparison_naturality X O E O.subtype continuous_subtype_val
  have hqEn : (ℓ ^ k • q).hom ≫ eE = eE ≫ (ℓ ^ k • qE).hom := by
    change (ℓ ^ k • q.hom) ≫ eE = eE ≫ (ℓ ^ k • qE.hom)
    simpa only [Preadditive.nsmul_comp, Preadditive.comp_nsmul]
      using congrArg (fun z ↦ ℓ ^ k • z) hqE
  have hsquare : p.hom ≫ φ = φ ≫ (ℓ ^ k • q).hom := by
    apply (cancel_mono eE).1
    calc
      (p.hom ≫ φ) ≫ eE = p.hom ≫ e ≫ integralFunctionInclusion ℓ E X := by
        rw [Category.assoc, he]
      _ = e ≫ pO.hom ≫ integralFunctionInclusion ℓ E X := by
        rw [← Category.assoc, hpO, Category.assoc]
      _ = e ≫ integralFunctionInclusion ℓ E X ≫ (ℓ ^ k • qE).hom := by rw [hcont]
      _ = (φ ≫ (ℓ ^ k • q).hom) ≫ eE := by
        rw [Category.assoc, hqEn]
        simpa only [Category.assoc] using
          congrArg (fun z ↦ z ≫ (ℓ ^ k • qE).hom) he.symm
  exact ⟨k, p, Mod.regularExtensionIso_naturality φ p (ℓ ^ k • q) hsquare⟩

private theorem finiteBiproduct_clear_denominators
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasFiniteBiproducts C] [HasFiniteBiproducts D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteBiproducts F]
    (A : C) (B : D) (e : F.obj A ≅ B) (ℓ : ℕ)
    (h : ∀ q : B ⟶ B, ∃ (k : ℕ) (p : A ⟶ A),
      F.map p ≫ e.hom = e.hom ≫ (ℓ ^ k • q))
    (n m : ℕ) (f : F.obj (⨁ fun _ : Fin n ↦ A) ⟶
      F.obj (⨁ fun _ : Fin m ↦ A)) :
    ∃ (k : ℕ) (g : (⨁ fun _ : Fin n ↦ A) ⟶ (⨁ fun _ : Fin m ↦ A)),
      F.map g = ℓ ^ k • f := by
  classical
  let en := F.mapBiproduct (fun _ : Fin n ↦ A) ≪≫ biproduct.mapIso (fun _ ↦ e)
  let em := F.mapBiproduct (fun _ : Fin m ↦ A) ≪≫ biproduct.mapIso (fun _ ↦ e)
  let q := en.inv ≫ f ≫ em.hom
  let qij (i : Fin n) (j : Fin m) := biproduct.components q i j
  choose kij pij hpij using fun i j ↦ h (qij i j)
  let k := Finset.univ.sup (fun z : Fin n × Fin m ↦ kij z.1 z.2)
  have hk (i : Fin n) (j : Fin m) : kij i j ≤ k :=
    Finset.le_sup (f := fun z : Fin n × Fin m ↦ kij z.1 z.2) (Finset.mem_univ (i, j))
  let gij (i : Fin n) (j : Fin m) := ℓ ^ (k - kij i j) • pij i j
  have hgij (i : Fin n) (j : Fin m) :
      F.map (gij i j) ≫ e.hom = e.hom ≫ (ℓ ^ k • qij i j) := by
    dsimp only [gij]
    rw [F.map_nsmul, Preadditive.nsmul_comp, hpij, Preadditive.comp_nsmul,
      smul_smul, ← pow_add, Nat.sub_add_cancel (hk i j)]
    rw [Preadditive.comp_nsmul]
  let g := biproduct.matrix gij
  refine ⟨k, g, ?_⟩
  have hi (i : Fin n) : biproduct.ι (fun _ : Fin n ↦ B) i ≫ en.inv =
      e.inv ≫ F.map (biproduct.ι (fun _ : Fin n ↦ A) i) := by
    simp [en]
  have hj (j : Fin m) : em.hom ≫ biproduct.π (fun _ : Fin m ↦ B) j =
      F.map (biproduct.π (fun _ : Fin m ↦ A) j) ≫ e.hom := by
    simp [em]
  have heq : en.inv ≫ F.map g ≫ em.hom = ℓ ^ k • q := by
    apply biproduct.hom_ext'
    intro i
    apply biproduct.hom_ext
    intro j
    simp only [Category.assoc, Preadditive.nsmul_comp, Preadditive.comp_nsmul]
    rw [← Category.assoc, hi, Category.assoc, hj]
    simp only [← Category.assoc, ← F.map_comp]
    simp only [Category.assoc]
    change e.inv ≫ F.map (biproduct.ι (fun _ : Fin n ↦ A) i ≫ g ≫
      biproduct.π (fun _ : Fin m ↦ A) j) ≫ e.hom = _
    change e.inv ≫ F.map (biproduct.components (biproduct.matrix gij) i j) ≫ e.hom = _
    rw [biproduct.matrix_components, Category.assoc, hgij]
    simp only [Iso.inv_hom_id_assoc]
    simp only [qij, biproduct.components, q, Category.assoc]
  apply (cancel_epi en.inv).1
  apply (cancel_mono em.hom).1
  simpa only [Category.assoc, Preadditive.nsmul_comp, Preadditive.comp_nsmul, q] using heq

/-- Every map between rationalizations of standard finite free integral modules
on a compact scheme has an integral numerator.
Source: Bhatt--Scholze, Section 6.8, continuous coefficient localization.
(auxiliary; not a blueprint node)

Proof. Apply the regular-module denominator lemma to each matrix coefficient.
Take the maximum of the finitely many resulting exponents, multiply each integral
numerator by the missing power, and assemble the integral matrix using finite
biproducts. The biproduct comparison for scalar extension proves the asserted
identity coefficient by coefficient. Empty matrices use exponent zero. -/
theorem integralFiniteFree_clear_denominators (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (X : Scheme.{u}) [CompactSpace X] (n m : ℕ)
    (f : (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj
        (Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n) ⟶
      (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj
        (Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) m)) :
    ∃ (k : ℕ) (g : Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n ⟶
        Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) m),
      (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).map g =
        ℓ ^ k • f := by
  exact finiteBiproduct_clear_denominators
    (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)) _ _
    (Mod.regularExtensionIso (coefficientMap (integralScalarMap ℓ E) X)) ℓ
    (integralRegular_clear_denominators ℓ E X) n m f

end AlgebraicGeometry.ProEtale.CondensedRing
