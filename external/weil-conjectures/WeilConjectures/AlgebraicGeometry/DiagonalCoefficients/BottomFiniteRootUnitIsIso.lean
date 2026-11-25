/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists

import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import Mathlib.NumberTheory.Padics.RingHoms

/-! # The finite root unit for the bottom coefficient field

Source: diagonal coefficient changes, integral root-limit identification.
(blueprint: lem-diagonal-bottom-finite-root-unit-is-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] upperStarFromPoint

-- Integer representatives normalize the inverse of the specified tensor insertion.
private theorem cyclic_tensor_insertion_isIso (N : ℕ)
    (M : AddCommGrpCat.{u + 1}) (hM : ∀ m : M, N • m = 0) :
    IsIso (AddCommGrpCat.ofHom
      (TensorProduct.mk ℤ (ULift.{u + 1} (ZMod N)) M 1).toAddMonoidHom) := by
  let : Module (ZMod N) M := AddCommGroup.zmodModule hM
  let : Module (ULift.{u + 1} (ZMod N)) M := ULift.module
  let R := ULift.{u + 1} (ZMod N)
  let f : R →+ (M →ₗ[ℤ] M) :=
    { toFun := fun r ↦
        (show M →+ M from
          { toFun := fun m ↦ r • m
            map_zero' := smul_zero r
            map_add' := smul_add r }).toIntLinearMap
      map_zero' := by ext m; exact zero_smul R m
      map_add' := fun r s ↦ by ext m; exact add_smul r s m }
  let v := TensorProduct.lift f.toIntLinearMap
  let i := AddCommGrpCat.ofHom (TensorProduct.mk ℤ R M 1).toAddMonoidHom
  let j := AddCommGrpCat.ofHom v.toAddMonoidHom
  have hij : i ≫ j = 𝟙 M := by
    ext m
    change v (1 ⊗ₜ[ℤ] m) = m
    exact one_smul R m
  have hji : j ≫ i = 𝟙 (AddCommGrpCat.of (R ⊗[ℤ] M)) := by
    apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro r m
    change (1 : R) ⊗ₜ[ℤ] (r • m) = r ⊗ₜ[ℤ] m
    obtain ⟨z, hz⟩ := ZMod.intCast_surjective r.down
    have hr : r = (z : R) := ULift.ext hz.symm
    rw [hr, Int.cast_smul_eq_zsmul, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', Int.smul_one_eq_cast]
  exact ⟨⟨j, hij, hji⟩⟩

-- A strong monoidal functor preserves invertibility of the unit tensor map.
private theorem monoidal_unit_tensor_isIso
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] (A : C) [MonObj A] (P : C)
    [IsIso (MonObj.one (X := A) ▷ P)] :
    let := F.monObjObj A
    IsIso (MonObj.one (X := F.obj A) ▷ F.obj P) := by
  let := F.monObjObj A
  have h : F.map (MonObj.one (X := A)) ▷ F.obj P =
      Functor.LaxMonoidal.μ F (𝟙_ C) P ≫ F.map (MonObj.one (X := A) ▷ P) ≫
        (Functor.Monoidal.μIso F A P).inv := by
    apply (cancel_mono (Functor.LaxMonoidal.μ F A P)).mp
    simp only [Category.assoc, Functor.Monoidal.μIso_inv,
      Functor.Monoidal.δ_μ, Category.comp_id, Functor.LaxMonoidal.μ_natural_left]
  change IsIso ((Functor.LaxMonoidal.ε F ≫ F.map (MonObj.one (X := A))) ▷ F.obj P)
  rw [comp_whiskerRight, h]
  infer_instance

private theorem unit_tensor_transport
    {C : Type*} [Category C] [MonoidalCategory C]
    (A : C) [MonObj A] {M M' : C} (e : M ≅ M')
    [IsIso (MonObj.one (X := A) ▷ M)] :
    IsIso (MonObj.one (X := A) ▷ M') := by
  have : IsIso ((𝟙_ C) ◁ e.hom ≫ MonObj.one (X := A) ▷ M') := by
    rw [whisker_exchange]
    infer_instance
  exact IsIso.of_isIso_comp_left ((𝟙_ C) ◁ e.hom) _

private theorem constant_cyclic_unit_isIso (X : Scheme.{u}) (N : ℕ)
    (M : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (hM : ∀ U (m : M.obj.obj U), N • m = 0) :
    IsIso (MonObj.one (X := Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} (ZMod N))))) ▷ M) := by
  let J := Scheme.ProEt.topology X
  let A := (Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} (ZMod N))) ⋙
    forget₂ RingCat.{u + 1} Ab.{u + 1}
  let P := M.obj
  let i : P ⟶ A ⊗ P := (λ_ P).inv ≫ MonObj.one (X := A) ▷ P
  have hi (U : X.ProEtᵒᵖ) : IsIso (i.app U) := by
    have heq : i.app U = AddCommGrpCat.ofHom
        (TensorProduct.mk ℤ (ULift.{u + 1} (ZMod N)) (P.obj U) 1).toAddMonoidHom := by
      apply (cancel_epi (λ_ (P.obj U)).hom).mp
      change (λ_ (P.obj U)).hom ≫ (λ_ (P.obj U)).inv ≫
        ((MonObj.one (X := A)).app U ▷ P.obj U) = _
      rw [Iso.hom_inv_id_assoc]
      apply AddCommGrpCat.hom_ext_toIntLinearMap
      apply TensorProduct.ext'
      intro z m
      change (z.down : ULift.{u + 1} (ZMod N)) ⊗ₜ[ℤ] m =
        (1 : ULift.{u + 1} (ZMod N)) ⊗ₜ[ℤ] (z.down • m)
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Int.smul_one_eq_cast]
    rw [heq]
    exact cyclic_tensor_insertion_isIso N (P.obj U) (hM U)
  have : IsIso i := NatIso.isIso_of_isIso_app i
  have : IsIso (MonObj.one (X := A) ▷ P) :=
    IsIso.of_isIso_comp_left (λ_ P).inv _
  have hF := monoidal_unit_tensor_isIso (presheafToSheaf J Ab.{u + 1}) A P
  let R := Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} J
    ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} (ZMod N))))
  have : IsIso (MonObj.one (X := R) ▷ (presheafToSheaf J Ab.{u + 1}).obj P) := hF
  exact unit_tensor_transport R (M := (presheafToSheaf J Ab.{u + 1}).obj P)
    (asIso ((sheafificationAdjunction J Ab.{u + 1}).counit.app M))

-- Transport the usual p-adic quotient isomorphism along the bottom integer-ring map.
private theorem bottom_quotient_equiv (l : ℕ) [Fact l.Prime] (n : ℕ) :
    Nonempty (spEllQuotient l ⟨⊥, inferInstance⟩ n ≃+* ZMod (l ^ (n + 1))) := by
  obtain ⟨_, e, _⟩ := Profinite.base_coefficient_condensed_identification.{0} l
  let I : Ideal ℤ_[l] := Ideal.span {(l : ℤ_[l]) ^ (n + 1)}
  let J := spTateEllIdeal l ⟨⊥, inferInstance⟩ n
  have hIJ : J = I.map e.toRingHom := by
    simp only [I, J, spTateEllIdeal, Ideal.map_span, Set.image_singleton,
      map_pow, map_natCast]
  let eQ := Ideal.quotientEquiv I J e hIJ
  let eZ : ℤ_[l] ⧸ I ≃+* ZMod (l ^ (n + 1)) :=
    (Ideal.quotEquivOfEq (PadicInt.ker_toZModPow (p := l) (n + 1)).symm).trans
      ((PadicInt.toZModPow (p := l) (n + 1)).quotientKerEquivOfSurjective
        (ZMod.ringHom_surjective _))
  exact ⟨eQ.symm.trans eZ⟩

private theorem bottom_coefficient_iso (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (n : ℕ) :
    ∃ e : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj
          (RingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))) ≅
      condensedRingObj (spEllPointRingObj l ⟨⊥, inferInstance⟩ n) X,
      IsMonHom e.hom := by
  let E : PadicAlgCl.FiniteIntermediateField l := ⟨⊥, inferInstance⟩
  let B := spEllQuotient l E n
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := ⟨rfl⟩
  let : IsTopologicalRing B := DiscreteTopology.topologicalRing
  let : Finite B := (spEllQuotient_finite_continuous l E n).1
  obtain ⟨eB⟩ := bottom_quotient_equiv l n
  let e : ULift.{u + 1} (ZMod (l ^ (n + 1))) ≃+* ULift.{u + 1} B :=
    ULift.ringEquiv.trans (eB.symm.trans ULift.ringEquiv.symm)
  let q := (Functor.const X.ProEtᵒᵖ).mapIso e.toRingCatIso
  let qA := Functor.isoWhiskerRight q (forget₂ RingCat.{u + 1} Ab.{u + 1})
  let qS := (presheafToSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).mapIso qA
  have hq : IsMonHom qS.hom := by
    dsimp only [qS, Functor.mapIso_hom, qA, Functor.isoWhiskerRight_hom]
    infer_instance
  obtain ⟨eR, heR⟩ := Profinite.finiteDiscreteCondensedRing_constant.{u} B
  obtain ⟨eX, heX⟩ := finiteDiscreteSchemeRing_constant.{u} B X eR heR
  let := heX
  refine ⟨qS ≪≫ eX, ?_⟩
  change IsMonHom (qS.hom ≫ eX.hom)
  infer_instance

/-- The free-module unit on a finite root sheaf is invertible for the bottom field.

Source: blueprint latest, sec-proetale-coefficients/sk-def-sp-tate-twist/_section.md,
finite-level tensor formula, and the bottom-field coefficient convention.
(blueprint: lem-diagonal-bottom-finite-root-unit-is-iso).

Proof: the integers of the bottom intermediate field are canonically Z_l.
Their quotient by l^(n+1) is Z/l^(n+1), including its unital ring structure.
The associated finite condensed coefficient pulls back to the constant residue
ring. The root sheaf is annihilated by l^(n+1). Tensoring its underlying abelian
sheaf with this residue ring over Z is therefore the identity: locally a scalar
is an integer residue, and the inverse sends a tensor x to that integer multiple
of x. Annihilation makes this independent of the representative. The inverse
is balanced, natural, and inverse to the free-module unit. Sheafification
preserves these inverse identities. This uses neither a choice of a primitive
root nor invertibility of l on the scheme, and includes the empty scheme. -/
theorem bottomFiniteRootUnit_isIso (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (n : ℕ) :
    IsIso ((Mod.freeForgetAdjunction
      (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (spEllPointRingObj l ⟨⊥, inferInstance⟩ n) X)).unit.app
        (Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1)))) := by
  obtain ⟨e, he⟩ := bottom_coefficient_iso l X n
  let := he
  let M := Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1))
  have h := constant_cyclic_unit_isIso X (l ^ (n + 1)) M
    (Scheme.proEtaleRootsOfUnity_nsmul X (l ^ (n + 1)))
  have : IsIso (MonObj.one (X :=
      condensedRingObj (spEllPointRingObj l ⟨⊥, inferInstance⟩ n) X) ▷ M) := by
    rw [← IsMonHom.one_hom e.hom, comp_whiskerRight]
    infer_instance
  change IsIso ((λ_ M).inv ≫ MonObj.one ▷ M ≫ 𝟙 _)
  infer_instance

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
