/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.MvPolynomial.Basic

public import Mathlib.RingTheory.Localization.FractionRing

import WeilConjectures.AlgebraicGeometry.FieldHypersurfaceFunctionFieldModel
import WeilConjectures.AlgebraicGeometry.GenericPolynomialHypersurfaceDescent

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry


private theorem integral_of_geometrically_integral_field
    {K : Type u} [Field K] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of K))
    (hgeom : GeometricallyIrreducible p) (hred : GeometricallyReduced p) : IsIntegral Y := by
  have : GeometricallyIrreducible p := hgeom
  have : GeometricallyReduced p := hred
  have : IrreducibleSpace Y := GeometricallyIrreducible.irreducibleSpace_of_subsingleton p
  have : IsReduced Y := GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian p
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

private theorem hypersurface_model_transport
    {Y W Z T : Scheme.{u}} (p : Y ⟶ T) (w : W ⟶ T) (q : Z ⟶ T)
    (i : W ≅ Z) (hi : i.hom ≫ q = w)
    (hgeom : GeometricallyIrreducible q) (hred : GeometricallyReduced q)
    (hZ : IsIntegral Z) (hft : LocallyOfFiniteType q)
    (e : FractionRing Γ(Y, ⊤) ≃+* FractionRing Γ(Z, ⊤))
    (he : ∀ a : Γ(T, ⊤),
      e (algebraMap Γ(Y, ⊤) (FractionRing Γ(Y, ⊤)) (p.appTop.hom a)) =
        algebraMap Γ(Z, ⊤) (FractionRing Γ(Z, ⊤)) (q.appTop.hom a)) :
    GeometricallyIrreducible w ∧ GeometricallyReduced w ∧
      IsIntegral W ∧ LocallyOfFiniteType w ∧
      ∃ e' : FractionRing Γ(Y, ⊤) ≃+* FractionRing Γ(W, ⊤),
        ∀ a : Γ(T, ⊤),
          e' (algebraMap Γ(Y, ⊤) (FractionRing Γ(Y, ⊤)) (p.appTop.hom a)) =
            algebraMap Γ(W, ⊤) (FractionRing Γ(W, ⊤)) (w.appTop.hom a) := by
  have hgeomW : GeometricallyIrreducible w := by
    rw [← hi]
    exact (MorphismProperty.cancel_left_of_respectsIso
      @GeometricallyIrreducible i.hom q).mpr hgeom
  have hredW : GeometricallyReduced w := by
    rw [← hi]
    exact (MorphismProperty.cancel_left_of_respectsIso
      @GeometricallyReduced i.hom q).mpr hred
  have : IsIntegral Z := hZ
  have hW : IsIntegral W := IsIntegral.of_isIso i.inv
  have hftW : LocallyOfFiniteType w := by
    rw [← hi]
    exact (MorphismProperty.cancel_left_of_respectsIso
      @LocallyOfFiniteType i.hom q).mpr hft
  let r : Γ(Z, ⊤) ≃+* Γ(W, ⊤) :=
    (Scheme.Γ.mapIso i.op).commRingCatIsoToRingEquiv
  let er : FractionRing Γ(Z, ⊤) ≃+* FractionRing Γ(W, ⊤) :=
    IsFractionRing.ringEquivOfRingEquiv r
  refine ⟨hgeomW, hredW, hW, hftW, e.trans er, ?_⟩
  intro a
  change er (e _) = _
  rw [he a, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  congr 1
  change i.hom.appTop.hom (q.appTop.hom a) = _
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hi]

/-- Construct a geometrically integral hypersurface with the same generic fraction ring.
The fraction-ring isomorphism fixes sections of the spectrum of the residue field.

Source: Stacks Project, Tag 0559, first proof, field generators and polynomial quotient.
Proof: Write A for the domain of base sections and K for its fraction field, identified
with the residue field at the generic point. The generic fibre is the spectrum of a
finitely generated geometrically integral K-algebra B. Its fraction field L is a
finitely generated separably generated extension of K. Choose a separating
transcendence basis and a primitive element for the remaining finite separable
extension. Its minimal polynomial over the rational function field, after removing
content, gives a primitive polynomial Q over K in these variables and one additional
variable. Its quotient is a domain with fraction field L. After extension to an
algebraic closure of K, the same quotient injects into the localization of the
geometrically integral field extension L; hence it remains a domain. Clear the
finitely many coefficient denominators by a nonzero element of A to get P over A.
This scalar is invertible over K, so the generic quotient and its fraction field are
unchanged. Polynomial algebras in finitely many variables and their principal
quotients are finitely presented, hence their generic structure maps are locally
of finite type. The two generic section rings are domains and their fraction rings
are K-isomorphic, giving the stated isomorphism and compatibility. For a purely
transcendental L, use the additional variable with equation T, including L = K.

(blueprint: lem-sbc-generic-fibre-hypersurface-function-field-model) -/
theorem exists_generic_fibre_hypersurface_function_field_model
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] [IsIntegral S]
    (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (η : S) (hη : IsGenericPoint η Set.univ)
    (hgeom : GeometricallyIrreducible (f.fiberToSpecResidueField η))
    (hred : GeometricallyReduced (f.fiberToSpecResidueField η)) :
    ∃ (n : ℕ) (P : MvPolynomial (Fin n) Γ(S, ⊤)),
      let H := Spec (.of (MvPolynomial (Fin n) Γ(S, ⊤) ⧸ Ideal.span {P}))
      let g : H ⟶ S := Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk (Ideal.span {P})).comp MvPolynomial.C)) ≫ S.isoSpec.inv
      GeometricallyIrreducible (g.fiberToSpecResidueField η) ∧
        GeometricallyReduced (g.fiberToSpecResidueField η) ∧
        IsIntegral (f.fiber η) ∧ IsIntegral (g.fiber η) ∧
        LocallyOfFiniteType (g.fiberToSpecResidueField η) ∧
        ∃ e : FractionRing Γ(f.fiber η, ⊤) ≃+* FractionRing Γ(g.fiber η, ⊤),
          ∀ a : Γ(Spec (.of (S.residueField η)), ⊤),
            e (algebraMap Γ(f.fiber η, ⊤) (FractionRing Γ(f.fiber η, ⊤))
              ((f.fiberToSpecResidueField η).appTop.hom a)) =
            algebraMap Γ(g.fiber η, ⊤) (FractionRing Γ(g.fiber η, ⊤))
              ((g.fiberToSpecResidueField η).appTop.hom a) := by
  have : LocallyOfFiniteType (f.fiberToSpecResidueField η) :=
    show LocallyOfFiniteType (Limits.pullback.snd f (S.fromSpecResidueField η)) from
      inferInstance
  obtain ⟨n, Q, hgeomQ, hredQ, e, he⟩ :=
    exists_field_hypersurface_function_field_model (f.fiberToSpecResidueField η) hgeom hred
  obtain ⟨P, i, hi⟩ := exists_base_hypersurface_of_generic_polynomial η hη Q
  let H := Spec (.of (MvPolynomial (Fin n) Γ(S, ⊤) ⧸ Ideal.span {P}))
  let g : H ⟶ S := Spec.map (CommRingCat.ofHom
    ((Ideal.Quotient.mk (Ideal.span {P})).comp MvPolynomial.C)) ≫ S.isoSpec.inv
  let Z := Spec (.of (MvPolynomial (Fin n) (S.residueField η) ⧸ Ideal.span {Q}))
  let q : Z ⟶ Spec (.of (S.residueField η)) := Spec.map (CommRingCat.ofHom
    ((Ideal.Quotient.mk (Ideal.span {Q})).comp MvPolynomial.C))
  have hX : IsIntegral (f.fiber η) :=
    integral_of_geometrically_integral_field (f.fiberToSpecResidueField η) hgeom hred
  have hZ : IsIntegral Z := integral_of_geometrically_integral_field q hgeomQ hredQ
  have hftQ : LocallyOfFiniteType q := by
    apply HasRingHomProperty.Spec_iff.mpr
    change RingHom.FiniteType
      (algebraMap (S.residueField η)
        (MvPolynomial (Fin n) (S.residueField η) ⧸ Ideal.span {Q}))
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  obtain ⟨hgeomG, hredG, hG, hftG, e', he'⟩ :=
    hypersurface_model_transport (f.fiberToSpecResidueField η)
      (g.fiberToSpecResidueField η) q i hi hgeomQ hredQ hZ hftQ e he
  exact ⟨n, P, hgeomG, hredG, hX, hG, hftG, e', he'⟩

end AlgebraicGeometry
