/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.GenericFiber.PurelyInseparableModel
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField

/-!
# Integral morphisms to normal schemes which are purely inseparable at the generic point

Let `f : Y ⟶ X` be an integral morphism of integral schemes with `X` normal, mapping the generic
point to the generic point, such that the extension of function fields is purely inseparable.
Then `f` is a universal homeomorphism: over an affine open `Spec A` of `X` with preimage
`Spec B`, every `b ∈ B` has a power `b ^ q ^ n` lying in the fraction field of `A` and integral
over `A`, hence in `A`.

## Main results

- `AlgebraicGeometry.exists_pow_mem_range_of_isIntegrallyClosed`: the algebraic core.
- `AlgebraicGeometry.Scheme.Hom.isUniversalHomeomorphism_of_isPurelyInseparable`: the main
  statement.
- `AlgebraicGeometry.Scheme.Hom.isUniversalHomeomorphism_of_universallyInjective_comp`: a
  dominant integral morphism of integral schemes with normal target is a universal
  homeomorphism as soon as it is universally injective over a nonempty open of the source.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Let `A ⊆ B` be integral with `A` integrally closed with fraction field `K`, and let `B` embed
into a field `L` over `K` such that a `q ^ n`-th power of every element of `L` lies in `K`. Then a
`q ^ n`-th power of every element of `B` lies in `A`. -/
theorem exists_pow_mem_range_of_isIntegrallyClosed {A B K L : Type*} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [CommRing B] [Field K] [Field L] [Algebra A B] [Algebra A K]
    [IsFractionRing A K] [Algebra B L] [Algebra K L] [Algebra A L] [IsScalarTower A B L]
    [IsScalarTower A K L] [Algebra.IsIntegral A B] (hBL : Function.Injective (algebraMap B L))
    {q : ℕ} (h : ∀ y : L, ∃ n, y ^ q ^ n ∈ (algebraMap K L).range) (b : B) :
    ∃ n, b ^ q ^ n ∈ (algebraMap A B).range := by
  obtain ⟨n, k, hk⟩ := h (algebraMap B L b)
  have hint : _root_.IsIntegral A (IsScalarTower.toAlgHom A K L k) := by
    rw [IsScalarTower.coe_toAlgHom', hk, ← map_pow]
    exact (Algebra.IsIntegral.isIntegral (b ^ q ^ n)).map (IsScalarTower.toAlgHom A B L)
  obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    ((isIntegral_algHom_iff (IsScalarTower.toAlgHom A K L) (algebraMap K L).injective).mp hint)
  refine ⟨n, a, hBL ?_⟩
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A K L, hk, map_pow]

/-- Evaluation at the generic point of sections over a nonempty affine open `U` of an integral
scheme exhibits the residue field at the generic point as the fraction field of `Γ(X, U)`. -/
theorem isFractionRing_evaluation_of_eq_genericPoint {X : Scheme.{u}} [IsIntegral X]
    {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x = genericPoint X) (hxU : x ∈ U) :
    letI := (X.evaluation U x hxU).hom.toAlgebra
    IsFractionRing Γ(X, U) (X.residueField x) := by
  subst hx
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  let := (X.evaluation U _ hxU).hom.toAlgebra
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  let er : X.functionField ≃+* X.residueField (genericPoint X) :=
    RingEquiv.ofBijective (X.residue (genericPoint X)).hom
      ⟨RingHom.injective (R := X.functionField) _, X.residue_surjective (genericPoint X)⟩
  let ea : X.functionField ≃ₐ[Γ(X, U)] X.residueField (genericPoint X) :=
    { er with commutes' _ := rfl }
  exact IsFractionRing.of_algEquiv ea

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The affine-local version of `isUniversalHomeomorphism_of_isPurelyInseparable`: for an affine
open `U` of `X` and a nonempty open `V ≤ f ⁻¹ᵁ U` of `Y` such that `Γ(X, U) ⟶ Γ(Y, V)` is
integral, `Spec Γ(Y, V) ⟶ Spec Γ(X, U)` is a universal homeomorphism. -/
theorem isUniversalHomeomorphism_SpecMap_appLE_of_isPurelyInseparable
    [IsIntegral X] [IsIntegral Y] (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hf : f (genericPoint Y) = genericPoint X)
    (hres : (f.residueFieldMap (genericPoint Y)).hom.IsPurelyInseparable)
    {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens}
    (hV : (V : Set Y).Nonempty)
    (e : V ≤ f ⁻¹ᵁ U) [IsIntegralHom (Spec.map (f.appLE U V e))] :
    IsUniversalHomeomorphism (Spec.map (f.appLE U V e)) := by
  have hηV : genericPoint Y ∈ V :=
    ((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  have hxU : f (genericPoint Y) ∈ U := e hηV
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  let := (f.appLE U V e).hom.toAlgebra
  let := (X.evaluation U _ hxU).hom.toAlgebra
  let := (Y.evaluation V _ hηV).hom.toAlgebra
  let := (f.residueFieldMap (genericPoint Y)).hom.toAlgebra
  let := (f.appLE U V e ≫ Y.evaluation V _ hηV).hom.toAlgebra
  have : IsScalarTower Γ(X, U) Γ(Y, V) (Y.residueField (genericPoint Y)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hsq : X.evaluation U _ hxU ≫ f.residueFieldMap (genericPoint Y) =
      f.appLE U V e ≫ Y.evaluation V _ hηV := by
    rw [evaluation_naturality, Scheme.Hom.appLE, Category.assoc, ← Scheme.germ_residue,
      ← Scheme.germ_residue, TopCat.Presheaf.germ_res_assoc]
  have : IsScalarTower Γ(X, U) (X.residueField (f (genericPoint Y)))
      (Y.residueField (genericPoint Y)) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hsq).symm
  have := isFractionRing_evaluation_of_eq_genericPoint hU hf hxU
  have := Scheme.isIntegrallyClosed_of_isIntegrallyClosed_stalk hX U
  have hBL : Function.Injective (algebraMap Γ(Y, V) (Y.residueField (genericPoint Y))) :=
    (RingHom.injective (R := Y.functionField) (Y.residue (genericPoint Y)).hom).comp
      (germ_injective_of_isIntegral _ _ hηV)
  have : Algebra.IsIntegral Γ(X, U) Γ(Y, V) :=
    (algebraMap_isIntegral_iff (R := Γ(X, U)) (A := Γ(Y, V))).mp
      (IsIntegralHom.SpecMap_iff.mp ‹_›)
  have : FaithfulSMul Γ(X, U) Γ(Y, V) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    refine Function.Injective.of_comp
      (f := algebraMap Γ(Y, V) (Y.residueField (genericPoint Y))) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq Γ(X, U)
      (X.residueField (f (genericPoint Y)))]
    exact (algebraMap (X.residueField (f (genericPoint Y))) _).injective.comp
      (IsFractionRing.injective _ _)
  let q := ringExpChar (X.residueField (f (genericPoint Y)))
  have : ExpChar (Y.residueField (genericPoint Y)) q :=
    expChar_of_injective_algebraMap
      (algebraMap (X.residueField (f (genericPoint Y))) _).injective q
  have : ExpChar Γ(Y, V) q := (algebraMap Γ(Y, V) _).expChar hBL q
  have : IsPurelyInseparable (X.residueField (f (genericPoint Y)))
      (Y.residueField (genericPoint Y)) := hres
  exact Algebra.IsUniversalHomeomorphism.isUniversalHomeomorphism (A := Γ(X, U)) (B := Γ(Y, V))
    (self := Algebra.IsUniversalHomeomorphism.of_pow_mem q
      (exists_pow_mem_range_of_isIntegrallyClosed hBL
        fun y ↦ IsPurelyInseparable.pow_mem (X.residueField (f (genericPoint Y))) q y))

/-- An integral morphism `f : Y ⟶ X` of integral schemes, with `X` normal, mapping the generic
point to the generic point and inducing a purely inseparable extension of function fields, is a
universal homeomorphism. -/
theorem isUniversalHomeomorphism_of_isPurelyInseparable [IsIntegralHom f] [IsIntegral X]
    [IsIntegral Y] (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hf : f (genericPoint Y) = genericPoint X)
    (hres : (f.residueFieldMap (genericPoint Y)).hom.IsPurelyInseparable) :
    IsUniversalHomeomorphism f := by
  have : Surjective f := by
    refine ⟨fun x ↦ ?_⟩
    have hx : genericPoint X ⤳ x := (genericPoint_spec X).specializes (Set.mem_univ x)
    exact hx.mem_closed f.isClosedMap.isClosed_range ⟨_, hf⟩
  have : UniversallyInjective f := by
    have H (x : X) : ∃ U ∈ X.affineOpens, x ∈ U ∧ U ≤ ⊤ :=
      Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (Set.mem_univ x)
    choose U hU hxU _ using H
    refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @UniversallyInjective) U
      (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxU x⟩) fun x ↦ ?_
    have hU' : IsAffineOpen (f ⁻¹ᵁ U x) := (hU x).preimage f
    have : IsAffine (U x) := hU x
    have : IsAffine (f ⁻¹ᵁ U x) := hU'
    have hint := (MorphismProperty.arrow_mk_iso_iff @IsIntegralHom
      (arrowIsoSpecΓOfIsAffine (f ∣_ U x))).mp inferInstance
    refine (MorphismProperty.arrow_mk_iso_iff @UniversallyInjective
      (arrowIsoSpecΓOfIsAffine (f ∣_ U x))).mpr ?_
    simp only [Scheme.Hom.appTop, morphismRestrict_app'] at hint ⊢
    obtain ⟨y, hy⟩ := f.surjective x
    refine (isUniversalHomeomorphism_SpecMap_appLE_of_isPurelyInseparable f hX hf hres
      ?_ ⟨y, ?_⟩ _).toUniversallyInjective
    · rw [Scheme.Opens.ι_image_top]
      exact hU x
    · simpa [hy] using hxU x
  exact { }

/-- A dominant integral morphism `f : Y ⟶ X` of integral schemes with `X` normal is a universal
homeomorphism if it is universally injective over some nonempty open `W` of `Y`: the residue
field extension at the generic point of `Y` is then purely inseparable. -/
theorem isUniversalHomeomorphism_of_universallyInjective_comp {W : Scheme.{u}} [IsIntegralHom f]
    [IsDominant f] [IsIntegral X] [IsIntegral Y]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (t : W ⟶ Y) [IsOpenImmersion t] [Nonempty W] [UniversallyInjective (t ≫ f)] :
    IsUniversalHomeomorphism f := by
  have : IsIntegral W := isIntegral_of_isOpenImmersion t
  have hf : f (genericPoint Y) = genericPoint X := by
    refine ((genericPoint_spec Y).image f.continuous).eq ?_
    rw [Set.image_univ, f.denseRange.closure_range]
    exact genericPoint_spec X
  refine f.isUniversalHomeomorphism_of_isPurelyInseparable hX hf ?_
  have htfae := (tfae_universallyInjective (t ≫ f)).out 1 3
  have hres := (htfae.mp ‹_›).2 (genericPoint W)
  rw [Scheme.residueFieldMap_comp] at hres
  rw [← genericPoint_eq_of_isOpenImmersion t]
  algebraize [(f.residueFieldMap (t (genericPoint W))).hom,
    (t.residueFieldMap (genericPoint W)).hom]
  let := (f.residueFieldMap (t (genericPoint W)) ≫
    t.residueFieldMap (genericPoint W)).hom.toAlgebra
  have : IsScalarTower (X.residueField (f (t (genericPoint W))))
      (Y.residueField (t (genericPoint W))) (W.residueField (genericPoint W)) :=
    .of_algebraMap_eq' rfl
  have : IsPurelyInseparable (X.residueField (f (t (genericPoint W))))
      (W.residueField (genericPoint W)) := hres
  exact IsPurelyInseparable.tower_bot (X.residueField (f (t (genericPoint W))))
    (Y.residueField (t (genericPoint W))) (W.residueField (genericPoint W))

end Scheme.Hom

end AlgebraicGeometry
