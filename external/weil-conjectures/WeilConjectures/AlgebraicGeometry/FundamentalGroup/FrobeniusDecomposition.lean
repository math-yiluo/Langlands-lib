/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.DecompositionGroup
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusRestriction

/-!
# Frobenius lifts in the decomposition group

In the situation of `AlgebraicGeometry.Scheme.FiniteEtale.galoisToAut_hom_app_eq_of_mem_inertia`,
let the special geometric point `Spec κ ⟶ Spec B ⟶ Y` lie over a point `x` with finite residue
field, `κ` being an algebraic closure of `κ(x)`. An element `σ` of `Gal(Ω / K)` inducing on `κ`
the inverse of the arithmetic Frobenius `y ↦ y ^ #κ(x)` maps to a Frobenius element at `x`
(`AlgebraicGeometry.Scheme.FiniteEtale.isFrobeniusElement_galoisToFundamentalGroup`): through the
specialization, it acts on the fibres as the geometric Frobenius at the special point.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {Y : Scheme.{u}} [ConnectedSpace Y] {R K Ω : Type u} [CommRing R] [IsDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [Algebra R Ω]
  [IsScalarTower R K Ω] [IsGalois K Ω] [IsSepClosed Ω] (a : Spec (.of R) ⟶ Y)
  {κ : Type u} [Field κ] [IsSepClosed κ] [Algebra (integralClosure R Ω) κ]
  (x : Y) [Finite (Y.residueField x)] [Algebra (Y.residueField x) κ]
  [IsAlgClosure (Y.residueField x) κ]
  {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] {s : Spec (.of Ω') ⟶ Y}
  (G : Type u) [Group G] [∀ P, MulAction G ((fiber s).obj P)] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [IsFundamentalGroup (fiber s) G]

omit [IsDomain R] [IsFractionRing R K] [IsGalois K Ω] in
/-- **The residue Frobenius lift is a Frobenius element.** Let the special geometric point
`Spec κ ⟶ Spec B ⟶ Y` factor through `Spec κ(x) ⟶ Y`, with `κ` an algebraic closure of `κ(x)`,
and let `σ ∈ Gal(Ω / K)` induce on `κ` the inverse `σκ` of the arithmetic Frobenius. Then the image
of `σ` in `π₁(Y, s)` along any path is a Frobenius element at `x`. -/
theorem isFrobeniusElement_galoisToFundamentalGroup
    (hpt : pointOfAlgebra κ (integralClosurePoint Ω a) =
      Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField x) κ)) ≫ Y.fromSpecResidueField x)
    (σ : Ω ≃ₐ[K] Ω) (σκ : κ ≃+* κ)
    (hσκ : (algebraMap (integralClosure R Ω) κ).comp
      (galoisIntegralClosure (R := R) σ : integralClosure R Ω →+* integralClosure R Ω) =
        (σκ : κ →+* κ).comp (algebraMap (integralClosure R Ω) κ))
    (hfrob : ∀ y, σκ y ^ Nat.card (Y.residueField x) = y)
    (τ : fiber (pointOfAlgebra Ω (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ a)) ≅ fiber s) :
    IsFrobeniusElement s G x
      (galoisToFundamentalGroup (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ a) τ G σ) := by
  let ap := integralClosurePoint Ω a
  have hΩ := pointOfAlgebra_integralClosurePoint (K := K) (Ω := Ω) a
  -- the algebraic closure `κ` of `κ(x)`
  let eAlg : AlgebraicClosure (Y.residueField x) ≃ₐ[Y.residueField x] κ :=
    IsAlgClosure.equiv (Y.residueField x) _ κ
  let E : Spec (.of κ) ≅ Spec (.of (AlgebraicClosure (Y.residueField x))) :=
    Scheme.Spec.mapIso eAlg.toRingEquiv.toCommRingCatIso.op
  have hE : E.hom ≫ residueFieldPoint Y x = pointOfAlgebra κ ap := by
    rw [hpt, residueFieldPoint_eq, ← Category.assoc]
    congr 1
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    congr 2
    ext c
    exact eAlg.commutes c
  let eF := fiberIsoOfIso E hE
  let sp := asIso (specialization Ω κ ap)
  let eq : fiber (pointOfAlgebra Ω ap) ≅
      fiber (pointOfAlgebra Ω (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ a)) :=
    fiberIsoOfIso (Iso.refl _) (by rw [Iso.refl_hom, Category.id_comp, hΩ])
  refine ⟨eF ≪≫ sp.symm ≪≫ eq ≪≫ τ, fun P z ↦ ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, ConcreteCategory.comp_apply]
  rw [galoisToFundamentalGroup_smul]
  congr 1
  -- the key identity `σκ ∘ e = e ∘ Frob⁻¹`
  have hσκq (c : κ) : σκ (c ^ Nat.card (Y.residueField x)) = c := by
    obtain ⟨d, rfl⟩ := σκ.surjective c
    rw [hfrob]
  have hring : E.hom ≫ Spec.map (CommRingCat.ofHom
      (arithmeticFrobeniusAt x).symm.toRingEquiv.toRingHom) =
      Spec.map (CommRingCat.ofHom σκ.toRingHom) ≫ E.hom := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun w ↦ ?_)
    obtain ⟨v, rfl⟩ := (arithmeticFrobeniusAt x).surjective w
    change eAlg ((arithmeticFrobeniusAt x).symm (arithmeticFrobeniusAt x v)) =
      σκ (eAlg (arithmeticFrobeniusAt x v))
    rw [AlgEquiv.symm_apply_apply, arithmeticFrobeniusAt_apply, map_pow, hσκq]
  have heΩ : (specMapIso σ.toRingEquiv).hom ≫ pointOfAlgebra Ω ap = pointOfAlgebra Ω ap := by
    rw [hΩ]
    exact specMapIso_hom_comp_pointOfAlgebra _ σ
  have heκ : (specMapIso σκ).hom ≫ pointOfAlgebra κ ap = pointOfAlgebra κ ap := by
    rw [← hE, ← Category.assoc, specMapIso_hom, ← hring, Category.assoc, ← specMapIso_hom,
      specMapIso_hom_comp_residueFieldPoint]
  let w := sp.inv.app P (eF.hom.app P z)
  have key := specialization_app_fiberPrecompIso ap (galoisIntegralClosure σ) σ.toRingEquiv σκ
    (specMap_galoisIntegralClosure_comp a σ) (by ext; rfl) hσκ heΩ heκ P w
  have hspw : sp.hom.app P w = eF.hom.app P z :=
    ConcreteCategory.congr_hom (sp.inv_hom_id_app P) _
  have hκ : (fiberPrecompIso _ (specMapIso σκ) heκ).hom.app P (eF.hom.app P z) =
      eF.hom.app P ((geometricFrobeniusAt x).hom.app P z) := by
    apply fiber_ext
    rw [fiberPrecompIso_hom_app_left, fiberIsoOfIso_hom_app_left, fiberIsoOfIso_hom_app_left]
    unfold geometricFrobeniusAt
    rw [fiberPrecompIso_hom_app_left, specMapIso_hom, specMapIso_hom, ← Category.assoc, ← hring,
      Category.assoc]
  have hspw' : (specialization Ω κ ap).app P w = eF.hom.app P z := hspw
  rw [hspw', hκ] at key
  have hpre : (fiberPrecompIso _ (specMapIso σ.toRingEquiv) heΩ).hom.app P w =
      sp.inv.app P (eF.hom.app P ((geometricFrobeniusAt x).hom.app P z)) := by
    rw [← key]
    exact (ConcreteCategory.congr_hom (sp.hom_inv_id_app P) _).symm
  apply fiber_ext
  rw [galoisToAut_hom_app_left, fiberIsoOfIso_hom_app_left, fiberIsoOfIso_hom_app_left,
    ← congrArg Over.Hom.left hpre, fiberPrecompIso_hom_app_left]
  simp only [Iso.refl_hom, Category.id_comp]
  rfl

section Affine

open scoped Pointwise

variable {C : Scheme.{u}} [IsIntegral C] [ConnectedSpace C] {W : C.Opens} (hW : IsAffineOpen W)
  [Nonempty W] [IsIntegrallyClosed Γ(C, W)]
  {Ω : Type u} [Field Ω] [Algebra C.functionField Ω] [Algebra Γ(C, W) Ω]
  [IsScalarTower Γ(C, W) C.functionField Ω] [IsGalois C.functionField Ω] [IsSepClosed Ω]
  (z : C) (hz : z ∈ W) [Finite (C.residueField z)] [(hW.primeIdealOf ⟨z, hz⟩).asIdeal.IsMaximal]
  (Q : Ideal (integralClosure Γ(C, W) Ω)) [Q.IsMaximal]
  [Q.LiesOver (hW.primeIdealOf ⟨z, hz⟩).asIdeal]
  {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] {s : Spec (.of Ω') ⟶ C}
  (G : Type u) [Group G] [∀ P, MulAction G ((fiber s).obj P)] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [IsFundamentalGroup (fiber s) G]

include hz Q in
/-- **Frobenius lifts exist in the decomposition group.** Let `W` be an affine open of an integral
scheme `C` with integrally closed ring of sections, `z ∈ W` a closed point with finite residue
field and `Q` a maximal ideal over `z` of the integral closure of `Γ(C, W)` in a separable closure
`Ω` of the function field. Then some element of the decomposition group of `Q` maps to a
Frobenius element at `z` in `π₁(C, s)`, along any path. -/
theorem exists_mem_stabilizer_isFrobeniusElement
    (τ : fiber (pointOfAlgebra Ω (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(C, W) C.functionField)) ≫ hW.fromSpec)) ≅ fiber s) :
    ∃ σ ∈ MulAction.stabilizer Gal(Ω/C.functionField) Q,
      IsFrobeniusElement s G z (galoisToFundamentalGroup _ τ G σ) := by
  have : IsFractionRing Γ(C, W) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C W hW
  have : IsIntegrallyClosedIn Γ(C, W) C.functionField :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn C.functionField).1 inferInstance
  let m := (hW.primeIdealOf ⟨z, hz⟩).asIdeal
  let := Ideal.Quotient.field Q
  have := Ideal.isSepClosed_quotient_integralClosure (R := Γ(C, W)) C.functionField Q
  -- the residue field at `z` is `Γ(C, W) ⧸ m`
  let z' : W := ⟨z, hz⟩
  let _ : Algebra Γ(C, W) (C.presheaf.stalk z') := TopCat.Presheaf.algebra_section_stalk _ z'
  have := hW.isLocalization_stalk z'
  let e : Γ(C, W) ⧸ m ≃+* C.residueField z :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal m (C.presheaf.stalk z')).toRingEquiv
  have : Finite (Γ(C, W) ⧸ m) := Finite.of_equiv _ e.symm.toEquiv
  let : Fintype (Γ(C, W) ⧸ m) := Fintype.ofFinite _
  let _ : Algebra (C.residueField z) (integralClosure Γ(C, W) Ω ⧸ Q) :=
    ((algebraMap (Γ(C, W) ⧸ m) (integralClosure Γ(C, W) Ω ⧸ Q)).comp e.symm.toRingHom).toAlgebra
  have he : (algebraMap (C.residueField z) (integralClosure Γ(C, W) Ω ⧸ Q)).comp e.toRingHom =
      algebraMap (Γ(C, W) ⧸ m) (integralClosure Γ(C, W) Ω ⧸ Q) := by
    ext x
    change algebraMap _ _ (e.symm (e x)) = _
    rw [e.symm_apply_apply]
    rfl
  have : Algebra.IsIntegral (C.residueField z) (integralClosure Γ(C, W) Ω ⧸ Q) :=
    ⟨fun x ↦ by
      simpa using (Algebra.IsIntegral.isIntegral (R := Γ(C, W) ⧸ m) x).map_of_comp_eq
        e.toRingHom (RingHom.id _) (by rw [he]; rfl)⟩
  have halg : Algebra.IsAlgebraic (C.residueField z) (integralClosure Γ(C, W) Ω ⧸ Q) :=
    ⟨fun x ↦ (Algebra.IsIntegral.isIntegral x).isAlgebraic⟩
  have : PerfectField (C.residueField z) := PerfectField.ofFinite
  have : PerfectField (integralClosure Γ(C, W) Ω ⧸ Q) :=
    Algebra.IsAlgebraic.perfectField (C.residueField z)
  have : Module.IsTorsionFree (C.residueField z) (integralClosure Γ(C, W) Ω ⧸ Q) :=
    DivisionSemiring.to_moduleIsTorsionFree
  have : IsAlgClosure (C.residueField z) (integralClosure Γ(C, W) Ω ⧸ Q) :=
    ⟨IsSepClosed.isAlgClosed_of_perfectField _, halg⟩
  -- the special point lies over `z`
  have hpt : pointOfAlgebra (integralClosure Γ(C, W) Ω ⧸ Q) (integralClosurePoint Ω hW.fromSpec) =
      Spec.map (CommRingCat.ofHom (algebraMap (C.residueField z)
        (integralClosure Γ(C, W) Ω ⧸ Q))) ≫ C.fromSpecResidueField z := by
    rw [Scheme.fromSpecResidueField, ← hW.fromSpecStalk_eq_fromSpecStalk hz,
      IsAffineOpen.fromSpecStalk]
    simp only [pointOfAlgebra, integralClosurePoint, ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext r
    have hr : C.residue z (C.presheaf.germ W z hz r) = e (Ideal.Quotient.mk m r) := rfl
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
    erw [hr]
    change _ = algebraMap (Γ(C, W) ⧸ m) _ (e.symm (e (Ideal.Quotient.mk m r)))
    rw [e.symm_apply_apply]
    rfl
  -- a lift of the inverse Frobenius
  let := Ideal.Quotient.field m
  have : Algebra.IsAlgebraic (Γ(C, W) ⧸ m) (integralClosure Γ(C, W) Ω ⧸ Q) :=
    ⟨fun x ↦ (Algebra.IsIntegral.isIntegral x).isAlgebraic⟩
  let F := FiniteField.frobeniusAlgEquivOfAlgebraic (Γ(C, W) ⧸ m)
    (integralClosure Γ(C, W) Ω ⧸ Q)
  obtain ⟨⟨σ, hσ⟩, hσF⟩ := Ideal.Quotient.stabilizerHom_surjective_integralClosure
    (K := C.functionField) m Q F⁻¹
  refine ⟨σ, hσ, isFrobeniusElement_galoisToFundamentalGroup hW.fromSpec z G hpt σ
    (F⁻¹ : _ ≃ₐ[_] _).toRingEquiv ?_ ?_ τ⟩
  · ext b
    change _ = F⁻¹ (Ideal.Quotient.mk Q b)
    rw [← hσF, Ideal.Quotient.stabilizerHom_apply]
    rfl
  · intro y
    have hcard : Nat.card (C.residueField z) = Fintype.card (Γ(C, W) ⧸ m) := by
      rw [← Nat.card_eq_fintype_card]
      exact Nat.card_congr e.symm.toEquiv
    rw [hcard]
    change ((F⁻¹ : _ ≃ₐ[_] _) y) ^ Fintype.card (Γ(C, W) ⧸ m) = y
    have h := congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic (Γ(C, W) ⧸ m)
      (integralClosure Γ(C, W) Ω ⧸ Q)) ((F⁻¹ : _ ≃ₐ[_] _) y)
    exact h.symm.trans (F.apply_symm_apply y)

end Affine

end AlgebraicGeometry.Scheme.FiniteEtale
