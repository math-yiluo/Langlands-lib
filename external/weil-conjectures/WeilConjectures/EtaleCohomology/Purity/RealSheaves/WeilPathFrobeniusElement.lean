/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusRestriction
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPath

/-!
# Local Frobenius elements from paths on the geometric curve

Let `x` be a closed point of the curve `C₀`, of degree `m = [κ(x) : K]`, and `x̄` the geometric
point of `C = C₀ ×_K K̄` over it (`AlgebraicGeometry.Scheme.Hom.geometricFiberPointOfFinitePoint`),
which satisfies `x̄ ≫ Frᵐ = σᵐ ≫ x̄` for the geometric Frobenius `σ` of `K̄`. For a path
`π : F_x̄ ≅ F_t` the loop

`F_t ≅ F_x̄ ≅ F_{σᵐ ≫ x̄} = F_{x̄ ≫ Frᵐ} ≅ F_{t ≫ Frᵐ}`

(reparametrisation, then the path induced by `π` along `Frᵐ`) pushes down to a Frobenius element
at `x` of `π₁(C₀, s)` (`AlgebraicGeometry.WeilGroup.BasePointData.isFrobeniusElement_downAut`).
On the stalk of a Weil sheaf this loop is the transport of the local Frobenius `Fₓ` along `π`.
-/

@[expose] public section

universe u

open CategoryTheory PreGaloisCategory

namespace AlgebraicGeometry.Scheme.Hom

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} (p : C ⟶ Spec (.of K))

/-- The geometric point over a closed point `x` is, as a point of `C₀`, the geometric point
`x̄ : Spec κ(x)‾ ⟶ C₀` over `x` up to a ring isomorphism `j : κ(x)‾ ≃ K̄`, and `j` carries the
inverse arithmetic Frobenius of `κ(x)‾` to the `[κ(x) : K]`-th power of the geometric
Frobenius of `K̄`. -/
theorem exists_ringEquiv_geometricFiberPointOfFinitePoint (x : C.finitePoints) :
    haveI : Finite (C.residueField x.1) := x.2
    letI := Fintype.ofFinite K
    ∃ j : AlgebraicClosure (C.residueField x.1) ≃+* AlgebraicClosure K,
      Spec.map (CommRingCat.ofHom j.toRingHom) ≫
          Scheme.FiniteEtale.residueFieldPoint C x.1 =
        p.geometricFiberPointOfFinitePoint x ≫ p.geometricFiberProj ∧
      ∀ a, j ((Scheme.FiniteEtale.arithmeticFrobeniusAt x.1).symm a) =
        (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) ^
          p.degreeOver x.1) (j a) := by
  let := Fintype.ofFinite K
  let := (p.residueFieldAlgebraMap x.1).toAlgebra
  have : Finite (C.residueField x.1) := x.2
  have : Module.Finite K (C.residueField x.1) := Module.Finite.of_finite
  let ι : C.residueField x.1 →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  have hx : p.geometricFiberPointOfFinitePoint x ≫ p.geometricFiberProj =
      Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ C.fromSpecResidueField x.1 :=
    p.geometricFiberPoint_comp_geometricFiberProj ι _ (p.specMap_residueFieldAlgebraMap x.1).symm
  let : Algebra (C.residueField x.1) (AlgebraicClosure K) := ι.toRingHom.toAlgebra
  have : IsScalarTower K (C.residueField x.1) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (ι.commutes c).symm
  have : Algebra.IsAlgebraic (C.residueField x.1) (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.tower_top (K := K) (C.residueField x.1)
  have : IsAlgClosure (C.residueField x.1) (AlgebraicClosure K) := ⟨inferInstance, inferInstance⟩
  let j := IsAlgClosure.equiv (C.residueField x.1) (AlgebraicClosure (C.residueField x.1))
    (AlgebraicClosure K)
  refine ⟨j.toRingEquiv, ?_, fun a ↦ ?_⟩
  · rw [hx, Scheme.FiniteEtale.residueFieldPoint_eq, ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext a
    exact j.commutes a
  · have hcard : Nat.card (C.residueField x.1) = Fintype.card K ^ p.degreeOver x.1 := by
      rw [← Nat.card_eq_fintype_card]
      exact Module.natCard_eq_pow_finrank (K := K) (V := C.residueField x.1)
    set b := (Scheme.FiniteEtale.arithmeticFrobeniusAt x.1).symm a
    have hb : a = b ^ Nat.card (C.residueField x.1) := by
      rw [← Scheme.FiniteEtale.arithmeticFrobeniusAt_apply, AlgEquiv.apply_symm_apply]
    rw [FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_eq_inv, inv_pow, AlgEquiv.aut_inv,
      AlgEquiv.eq_symm_apply, AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    dsimp only
    rw [hb, ← hcard]
    exact (map_pow j.toRingEquiv b _).symm

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- Transport along an equality of fibre functors coming from an equality of geometric points
does not change the underlying morphism of a point. -/
lemma eqToHom_fiber_app_left {y z : Spec (.of Ω) ⟶ Y} (hyz : y = z) (h : fiber y = fiber z)
    (P : Y.FiniteEtale) (x : (fiber y).obj P) : ((eqToHom h).app P x).left = x.left := by
  subst hyz
  rfl

/-- Pushing forward a path induced along `f` by a morphism `g` with `f ≫ g = g` gives the path
pushed forward by `g`, up to the identifications of the base points. -/
lemma pullbackPathIso_pullbackPathIso_of_comp_self {Z : Scheme.{u}} (f : Y ⟶ Y) (g : Y ⟶ Z)
    (hfg : f ≫ g = g) {y z : Spec (.of Ω) ⟶ Y} (τ : fiber y ≅ fiber z) :
    pullbackPathIso g (pullbackPathIso f τ) =
      eqToIso (by rw [Category.assoc, hfg]) ≪≫ pullbackPathIso g τ ≪≫
        eqToIso (by rw [Category.assoc, hfg]) := by
  have h := pullbackPathIso_comp f g τ
  rw [pullbackPathIso_congr hfg] at h
  have h' := congrArg Iso.hom h
  simp only [Iso.trans_hom, eqToIso.hom] at h'
  rw [eqToHom_comp_iff, comp_eqToHom_iff] at h'
  ext1
  simp only [Iso.trans_hom, eqToIso.hom, h', eqToHom_trans_assoc, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id, Category.id_comp]

end AlgebraicGeometry.Scheme.FiniteEtale

namespace AlgebraicGeometry.WeilGroup.BasePointData

open Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  {W : WeilGroup p} (B : BasePointData W)

/-- The loop `F_t ≅ F_x̄ ≅ F_{σᵐ ≫ x̄} = F_{x̄ ≫ Frᵐ} ≅ F_{t ≫ Frᵐ}` at a closed point `x` of
degree `m`, for a path `π : F_x̄ ≅ F_t`. -/
noncomputable def frobeniusLoop (x : C.finitePoints)
    (π : fiber (p.geometricFiberPointOfFinitePoint x) ≅ fiber B.t) :
    fiber B.t ≅ fiber (B.t ≫ (p.geometricGaloisFrobenius ^ p.degreeOver x.1).asIso.hom) :=
  π.symm ≪≫ (fiberReparamIso (specGeometricFrobenius K ^ p.degreeOver x.1).asIso _).symm ≪≫
    eqToIso (congrArg fiber
      (p.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow x).symm) ≪≫
    pullbackPathIso (p.geometricGaloisFrobenius ^ p.degreeOver x.1).asIso.hom π

/-- The endpoint `t ≫ Frᵐ` of the local Frobenius loop has the same image in `C₀` as `t`. -/
lemma frobeniusLoop_comp_geometricFiberProj (x : C.finitePoints) :
    (B.t ≫ (p.geometricGaloisFrobenius ^ p.degreeOver x.1).asIso.hom) ≫ p.geometricFiberProj =
      B.t ≫ p.geometricFiberProj := by
  rw [Category.assoc, Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj]

omit [IsCurve p] in
/-- The image `x̄ ≫ proj` in `C₀` of the geometric point over `x` is fixed by `σᵐ`,
`m = [κ(x) : K]`. -/
lemma specGeometricFrobenius_pow_comp_geometricFiberPointOfFinitePoint (x : C.finitePoints) :
    (specGeometricFrobenius K ^ p.degreeOver x.1).asIso.hom ≫
        p.geometricFiberPointOfFinitePoint x ≫ p.geometricFiberProj =
      p.geometricFiberPointOfFinitePoint x ≫ p.geometricFiberProj := by
  rw [← Category.assoc, ← p.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow,
    Category.assoc, Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj]

/-- The push-down of the local Frobenius loop is the conjugate by the pushed-down path `π` of
the precomposition with `σᵐ` on the fibre functor at `x̄ ≫ proj`. -/
lemma pullbackPathIso_frobeniusLoop (x : C.finitePoints)
    (π : fiber (p.geometricFiberPointOfFinitePoint x) ≅ fiber B.t) :
    pullbackPathIso p.geometricFiberProj (B.frobeniusLoop x π) ≪≫
        eqToIso (congrArg fiber (B.frobeniusLoop_comp_geometricFiberProj x)) =
      (pullbackPathIso p.geometricFiberProj π).symm ≪≫
        fiberPrecompIso _ (specGeometricFrobenius K ^ p.degreeOver x.1).asIso
          (specGeometricFrobenius_pow_comp_geometricFiberPointOfFinitePoint x) ≪≫
        pullbackPathIso p.geometricFiberProj π := by
  rw [frobeniusLoop, pullbackPathIso_trans, pullbackPathIso_trans, pullbackPathIso_trans,
    pullbackPathIso_symm, pullbackPathIso_symm, pullbackPathIso_fiberReparamIso,
    pullbackPathIso_eqToIso, pullbackPathIso_pullbackPathIso_of_comp_self _ _
      (Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj _ _)]
  swap
  · exact (p.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow x).symm
  simp only [Iso.trans_assoc]
  congr 1
  ext1
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, eqToIso.hom, eqToIso.inv,
    eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  refine (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ (pullbackPathIso p.geometricFiberProj π).hom) ?_)
  ext P w
  apply fiber_ext
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, fiberPrecompIso_hom_app_left]
  exact eqToHom_fiber_app_left (specGeometricFrobenius_pow_comp_geometricFiberPointOfFinitePoint x)
    _ P _

/-- **The local Frobenius loop is a Frobenius element**: the push-down to `π₁(C₀, s)` of the loop
`AlgebraicGeometry.WeilGroup.BasePointData.frobeniusLoop` at a closed point `x` is a Frobenius
element at `x`. -/
theorem isFrobeniusElement_downAut (x : C.finitePoints)
    (π : fiber (p.geometricFiberPointOfFinitePoint x) ≅ fiber B.t) :
    haveI := W.connectedSpace
    haveI : Finite (C.residueField x.1) := x.2
    IsFrobeniusElement W.basePoint W.fundamentalGroup x.1
      (B.downAut (B.frobeniusLoop x π) (B.frobeniusLoop_comp_geometricFiberProj x)) := by
  have := W.connectedSpace
  have : Finite (C.residueField x.1) := x.2
  let := Fintype.ofFinite K
  obtain ⟨j, hj, hfrob⟩ := p.exists_ringEquiv_geometricFiberPointOfFinitePoint x
  let τ₀ : fiber (residueFieldPoint C x.1) ≅
      fiber (p.geometricFiberPointOfFinitePoint x ≫ p.geometricFiberProj) :=
    fiberIsoOfIso (Scheme.Spec.mapIso j.toCommRingCatIso.op) hj
  refine ⟨τ₀ ≪≫ pullbackPathIso p.geometricFiberProj π ≪≫ B.path, fun P y ↦ ?_⟩
  rw [← toAut_hom_app_apply, ← toAutMulEquiv_apply, downAut, toAutMulEquiv_toπ,
    pullbackPathIso_frobeniusLoop]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, ConcreteCategory.comp_apply,
    Iso.hom_inv_id_app_apply]
  congr 2
  apply fiber_ext
  simp only [τ₀, geometricFrobeniusAt, fiberPrecompIso_hom_app_left, fiberIsoOfIso_hom_app_left]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  change _ ≫ Spec.map (CommRingCat.ofHom j.toRingHom) = Spec.map (CommRingCat.ofHom j.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (arithmeticFrobeniusAt x.1).symm.toRingEquiv.toRingHom)
  rw [specGeometricFrobenius_pow_hom, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  exact (hfrob a).symm

end AlgebraicGeometry.WeilGroup.BasePointData
