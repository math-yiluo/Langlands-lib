/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.BertiniAux
public import WeilConjectures.AlgebraicGeometry.ConstantFieldGeometricFiber
public import WeilConjectures.AlgebraicGeometry.CurveCoverBase
public import WeilConjectures.AlgebraicGeometry.GeometricallyConnectedCheckAfterExtension
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.RingTheory.ConstantField

/-!
# The constant field of a smooth irreducible affine scheme over a finite field

Let `V` be an irreducible affine scheme, smooth over a finite field `k₀`. Its ring of functions
`A` is an integrally closed domain, and the integral closure `k'` of `k₀` in `A`, the *constant
field* of `V`, is a finite extension of `k₀`. The scheme `V` is smooth and geometrically
connected (even geometrically irreducible) over `k'`
(`AlgebraicGeometry.exists_constantField_of_smooth`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The ring of functions of an affine integral scheme whose local rings are integrally closed is
integrally closed. -/
lemma isIntegrallyClosed_of_isIntegrallyClosed_stalk (R : Type u) [CommRing R] [IsDomain R]
    (hint : ∀ x : Spec (.of R), IsIntegrallyClosed ((Spec (.of R)).presheaf.stalk x)) :
    IsIntegrallyClosed R := by
  refine IsIntegrallyClosed.of_localization_maximal fun P _ hP ↦ ?_
  let y : PrimeSpectrum R := ⟨P, hP.isPrime⟩
  let : Algebra R ((Spec (.of R)).presheaf.stalk y) := StructureSheaf.stalkAlgebra R y
  have : IsLocalization.AtPrime ((Spec (.of R)).presheaf.stalk y) P :=
    StructureSheaf.IsLocalization.to_stalk R y
  have := hint y
  exact .of_equiv (IsLocalization.algEquiv P.primeCompl
    ((Spec (.of R)).presheaf.stalk y) (Localization.AtPrime P)).toRingEquiv

/-- **The constant field of a smooth irreducible affine scheme** over a finite field `k₀`: there
is a finite extension `k'` of `k₀` and a factorisation `V ⟶ Spec k' ⟶ Spec k₀` of the structure
morphism through which `V` is smooth and geometrically connected over `k'`. The field `k'` is the
integral closure of `k₀` in the ring of functions of `V`. -/
theorem exists_constantField_of_smooth {k₀ : Type u} [Field k₀] [Finite k₀] {V : Scheme.{u}}
    (f : V ⟶ Spec (.of k₀)) [IsAffine V] [IrreducibleSpace V] [Smooth f] :
    ∃ (k' : Type u) (_ : Field k') (_ : Finite k') (_ : Algebra k₀ k')
      (c : V ⟶ Spec (.of k')),
      c ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k')) = f ∧ Smooth c ∧
        GeometricallyConnected c := by
  obtain ⟨R, _, _, e, he⟩ := exists_iso_Spec_of_isAffine f
  set g := Spec.map (CommRingCat.ofHom (algebraMap k₀ R))
  have hs : Smooth g := by
    have : Smooth (e.hom ≫ g) := he ▸ inferInstance
    exact (MorphismProperty.cancel_left_of_respectsIso @Smooth e.hom g).mp this
  have : IrreducibleSpace (Spec (.of R)) :=
    (Scheme.homeoOfIso e).surjective.irreducibleSpace (Scheme.homeoOfIso e).continuous
  have : IsIntegral (Spec (.of R)) := isIntegral_of_smooth_of_irreducibleSpace g
  have : IsDomain R := (affine_isIntegral_iff (.of R)).1 inferInstance
  have := IsRegular.of_smooth g
  have : IsIntegrallyClosed R := isIntegrallyClosed_of_isIntegrallyClosed_stalk R
    fun x ↦ IsRegular.isIntegrallyClosed_stalk x
  have hsR : Algebra.Smooth k₀ R := by
    have := (HasRingHomProperty.Spec_iff (P := @Smooth)).1 hs
    exact (RingHom.smooth_algebraMap).1 this
  let k' := Algebra.TensorProduct.ConstantField k₀ R
  have : Finite k' := Algebra.TensorProduct.finite_constantField
  have : Algebra.FormallyUnramified k₀ k' := Algebra.FormallyUnramified.of_isSeparable k₀ k'
  have hs' : Algebra.Smooth k' R := by
    have : Algebra.FormallySmooth k' R := Algebra.FormallySmooth.of_restrictScalars k₀ k' R
    have : Algebra.FiniteType k' R := Algebra.FiniteType.of_restrictScalars_finiteType k₀ k' R
    exact ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  set c' := Spec.map (CommRingCat.ofHom (algebraMap k' R))
  have hc' : Smooth c' := (HasRingHomProperty.Spec_iff (P := @Smooth)).2
    ((RingHom.smooth_algebraMap).2 hs')
  have hgc : GeometricallyConnected c' := by
    let : (Spec (.of R)).Over (Spec (.of k')) := ⟨c'⟩
    have hirr : IrreducibleSpace c'.geometricFiber :=
      irreducibleSpace_geometricFiber_constantField (k₀ := k₀) (A := R)
    refine (geometricallyConnected_iff_of_fieldExtension (k' := AlgebraicClosure k')
      (Spec (.of R))).2 ?_
    exact @GeometricallyConnected.of_connectedSpace_of_isSepClosed _ _ _ _ _
      (inferInstanceAs (ConnectedSpace c'.geometricFiber))
  refine ⟨k', inferInstance, inferInstance, inferInstance, e.hom ≫ c', ?_, inferInstance,
    (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected e.hom c').2 hgc⟩
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq, he]

end AlgebraicGeometry
