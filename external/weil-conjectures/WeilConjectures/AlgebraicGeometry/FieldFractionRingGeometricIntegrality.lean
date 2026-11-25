/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.RingTheory.Localization.FractionRing

import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # Geometric integrality depends only on the function field

Source: Stacks Project, Tags 0559, 035W and 054Q.
-/

@[expose] public section
universe u
open CategoryTheory Topology Limits
open scoped TensorProduct
namespace AlgebraicGeometry

private theorem fraction_tensor_domain
    (K E B : Type u) [Field K] [Field E] [CommRing B] [IsDomain B]
    [Algebra K E] [Algebra K B] [IsDomain (E ⊗[K] B)] :
    IsDomain (E ⊗[K] FractionRing B) := by
  let L := FractionRing B
  let f : E ⊗[K] B →ₐ[K] E ⊗[K] L :=
    Algebra.TensorProduct.map (AlgHom.id K E) (IsScalarTower.toAlgHom K B L)
  let : Algebra (E ⊗[K] B) (E ⊗[K] L) := f.toRingHom.toAlgebra
  have : IsScalarTower E (E ⊗[K] B) (E ⊗[K] L) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    simp [f, RingHom.algebraMap_toAlgebra]
    rfl
  have hloc : IsLocalization
      ((nonZeroDivisors B).map (Algebra.TensorProduct.includeRight (R := K) (A := E)))
      (E ⊗[K] L) := by
    apply IsLocalization.tensorProduct_tensorProduct_right K E (nonZeroDivisors B) L
    ext x
    simp [f, RingHom.algebraMap_toAlgebra]
  have : FaithfulSMul K E :=
    (faithfulSMul_iff_algebraMap_injective K E).mpr (algebraMap K E).injective
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight (R := K) (A := E) (B := B)) := by
    exact Module.Flat.tensorProduct_mk_injective K B E
  apply IsLocalization.isDomain_of_le_nonZeroDivisors (E ⊗[K] L)
    (M := (nonZeroDivisors B).map
      (Algebra.TensorProduct.includeRight (R := K) (A := E)))
  rintro x ⟨b, hb, rfl⟩
  apply mem_nonZeroDivisors_of_ne_zero
  intro h
  apply nonZeroDivisors.ne_zero hb
  apply hinj
  simpa using h

private theorem affine_baseChange_integral_iff
    {K E : Type u} [Field K] [Field E] {X : Scheme.{u}} [IsAffine X]
    (p : X ⟶ Spec (.of K)) (φ : K →+* E) :
    let : Algebra K Γ(X, ⊤) :=
      (p.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
    let : Algebra K E := φ.toAlgebra
    IsIntegral (pullback p (Spec.map (CommRingCat.ofHom φ))) ↔
      IsDomain (E ⊗[K] Γ(X, ⊤)) := by
  dsimp only
  let f := p.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  let : Algebra K Γ(X, ⊤) := f.toAlgebra
  let : Algebra K E := φ.toAlgebra
  have hp : X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom f) = p := by
    have h : X.isoSpec.inv ≫ p = Spec.map (CommRingCat.ofHom f) := by
      rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
      rfl
    rw [← h]
    simp
  let y := Spec.map (CommRingCat.ofHom φ)
  have h : IsPullback (pullback.fst p y ≫ X.isoSpec.hom) (pullback.snd p y)
      (Spec.map (CommRingCat.ofHom f)) y :=
    (IsPullback.of_hasPullback p y).of_iso (Iso.refl _) X.isoSpec
      (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simpa using hp.symm) (by simp)
  let e := h.isoPullback ≪≫ pullbackSpecIso K Γ(X, ⊤) E ≪≫
    Scheme.Spec.mapIso
      ((Algebra.TensorProduct.comm K E Γ(X, ⊤)).toRingEquiv.toCommRingCatIso.op)
  have hi : IsIntegral (pullback p y) ↔ IsIntegral (Spec (.of (E ⊗[K] Γ(X, ⊤)))) := by
    exact ⟨fun h ↦ @IsIntegral.of_isIso _ _ h e.hom inferInstance,
      fun h ↦ @IsIntegral.of_isIso _ _ h e.inv inferInstance⟩
  exact hi.trans (affine_isIntegral_iff _)

/-- Geometric integrality of integral affine schemes over a field transfers along
an isomorphism of fraction fields which fixes the base sections.

Source: Stacks Project, Tag 0559, first proof, geometric integrality of L;
Tags 035W and 054Q (geometric reducedness and irreducibility at generic points).
Proof: Write B and C for the two section domains and identify their fraction fields
with L using e. The compatibility he identifies the actions of K on this field.
For every field extension E/K, E tensor_K B is a domain by geometric integrality
of X and the affine base-change formula. Its localization at B minus zero is
E tensor_K L, which is again a nonzero domain: these denominators remain nonzero,
since B embeds in its scalar extension. The inclusion C -> L is K-linear because
of he and Gamma(Spec K)=K. Flatness of the K-vector space E preserves its
injectivity, so E tensor_K C embeds into E tensor_K L and is a nonzero domain.
Its spectrum is the base change of Y to E and hence is integral. Every map from
a field spectrum to Spec K is such a field extension. Thus q is geometrically
integral, implying both geometric irreducibility and geometric reducedness.
The integral hypotheses exclude empty spectra and ensure the fraction rings
are fields. No normality, smoothness or perfection assumption is needed.
(blueprint: lem-sbc-field-fraction-ring-geometric-integrality) -/
theorem geometrically_integral_of_fractionRing_equiv
    {K : Type u} [Field K] {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ Spec (.of K)) (q : Y ⟶ Spec (.of K))
    (hgeom : GeometricallyIrreducible p) (hred : GeometricallyReduced p)
    (e : FractionRing Γ(X, ⊤) ≃+* FractionRing Γ(Y, ⊤))
    (he : ∀ a : Γ(Spec (.of K), ⊤),
      e (algebraMap Γ(X, ⊤) (FractionRing Γ(X, ⊤)) (p.appTop.hom a)) =
        algebraMap Γ(Y, ⊤) (FractionRing Γ(Y, ⊤)) (q.appTop.hom a)) :
    GeometricallyIrreducible q ∧ GeometricallyReduced q := by
  let B := Γ(X, ⊤)
  let C := Γ(Y, ⊤)
  let : Algebra K B :=
    (p.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  let : Algebra K C :=
    (q.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  let L := FractionRing B
  let M := FractionRing C
  let ea : L ≃ₐ[K] M :=
    { e with commutes' := fun a ↦ he ((Scheme.ΓSpecIso (.of K)).inv.hom a) }
  have : GeometricallyIrreducible p := hgeom
  have : GeometricallyReduced p := hred
  have hp : GeometricallyIntegral p :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible p
  have : ObjectProperty.IsClosedUnderIsomorphisms (@IsIntegral : Scheme.{u} → Prop) := by
    constructor
    intro X Y i h
    exact @IsIntegral.of_isIso _ _ h i.hom inferInstance
  have hq : GeometricallyIntegral q := by
    rw [geometricallyIntegral_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
    intro E _ y
    obtain ⟨φ, rfl⟩ := Spec.map_surjective y
    let : Algebra K E := φ.hom.toAlgebra
    have hB : IsDomain (E ⊗[K] B) :=
      (affine_baseChange_integral_iff p φ.hom).mp
        (hp.geometrically_isIntegral _ _ _ (.of_hasPullback _ _))
    have hL : IsDomain (E ⊗[K] L) := fraction_tensor_domain K E B
    let g : C →ₐ[K] L := ea.symm.toAlgHom.comp (IsScalarTower.toAlgHom K C M)
    have hg : Function.Injective g := ea.symm.injective.comp (IsFractionRing.injective C M)
    let gt : E ⊗[K] C →ₐ[K] E ⊗[K] L :=
      Algebra.TensorProduct.map (AlgHom.id K E) g
    have hgt : Function.Injective gt :=
      Module.Flat.lTensor_preserves_injective_linearMap g.toLinearMap hg
    have hC : IsDomain (E ⊗[K] C) := hgt.isDomain gt
    exact (affine_baseChange_integral_iff q φ.hom).mpr hC
  have : GeometricallyIntegral q := hq
  exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry
