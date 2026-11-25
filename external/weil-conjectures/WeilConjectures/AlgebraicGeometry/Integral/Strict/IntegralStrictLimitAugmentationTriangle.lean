/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Principal
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import WeilConjectures.AlgebraicGeometry.Integral.IntegralOrdinaryAugmentationReduction
import all WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalDerivedReductionExists

/-! # The prime-invertible cone of the strict quotient augmentation

## References

* Stacks Project, Tag 099M, using its Koszul-tower proof
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace AlgebraicGeometry.ProEtale

private theorem counit_isIso_on_regular
    (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb W)]
    (I : DiagonalDerivedReduction ℓ (𝟭 (DiagonalAb W)))
    (P : CochainComplex (DiagonalAb W) ℤ)
    (hP : ∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) :
    IsIso (I.ε.app P) := by
  let good : CochainComplex (DiagonalAb W) ℤ → Prop := fun K ↦
    ∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (K.X i))
  have res : ∀ K : CochainComplex (DiagonalAb W) ℤ,
      ∃ (L : CochainComplex (DiagonalAb W) ℤ) (p : L ⟶ K), good L ∧ QuasiIso p := by
    intro K
    obtain ⟨L, p, hp, hflat, _⟩ := CochainComplex.exists_quasiIso_flat_kFlat K
    refine ⟨L, p, ?_, hp⟩
    intro n i
    exact flat_multiplication_mono _
      (integerUnit_mono W _ (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero)) _ (hflat i)
  obtain ⟨T, β, hu, _, _, hc⟩ := cochainDerivedFullExists I.ordinary.E good res (by
    intro K L p hp hK hL
    have : QuasiIso p := hp
    exact reductionTower_quasiIso ℓ (𝟭 (DiagonalAb W)) I.ordinary p hK hL)
  have := I.universal
  have := hu
  have := hc P hP
  let e := Functor.leftDerivedUnique T I.T I.ε β
    (HomologicalComplex.quasiIso (DiagonalAb W) (.up ℤ))
  have he : e.hom.app (DerivedCategory.Q.obj P) ≫ β.app P = I.ε.app P := by
    dsimp only [e, Functor.leftDerivedUnique, Functor.leftDerivedNatIso]
    simpa only [Iso.refl_hom, NatTrans.id_app, Category.comp_id] using
      Functor.leftDerivedNatTrans_app I.T T I.ε β
      (HomologicalComplex.quasiIso (DiagonalAb W) (.up ℤ)) (𝟙 _) P
  rw [← he]
  infer_instance

private theorem integral_prime_regular (ℓ : ℕ) [Fact ℓ.Prime] :
    (ℓ : ULift.{u + 1} ℤ) ∈ nonZeroDivisors (ULift.{u + 1} ℤ) := by
  rw [mem_nonZeroDivisors_iff]
  have hleft : ∀ x : ULift.{u + 1} ℤ, (ℓ : ULift.{u + 1} ℤ) * x = 0 → x = 0 := by
    intro x hx
    apply ULift.ext
    have h : (ℓ : ℤ) * x.down = 0 := congrArg ULift.down hx
    exact (mul_eq_zero.mp h).resolve_left
      (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)
  exact ⟨hleft, fun x hx ↦ hleft x ((mul_comm _ _).trans hx)⟩

/-- The strict limit admits a natural augmentation with prime-invertible cone.
No completeness assertion about the target is included. -/
theorem integral_strict_limit_augmentation_triangle (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb W)]
    (I : DiagonalDerivedReduction ℓ (𝟭 (DiagonalAb W)))
    (RZ : DerivedCategory (ℕᵒᵖ ⥤ DiagonalAb W) ⥤ DerivedCategory (DiagonalAb W))
    (ηZ : (lim : (ℕᵒᵖ ⥤ DiagonalAb W) ⥤ DiagonalAb W).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RZ)
    (hRZ : RZ.IsRightDerivedFunctor ηZ
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ DiagonalAb W) (.up ℤ)))
    (e : DiagonalAb W ≌
      Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
    [e.functor.Additive] [e.inverse.Additive] :
    ∃ η : e.mapDerivedCategory.functor ⟶ (I.T ⋙ RZ) ⋙ e.mapDerivedCategory.functor,
      ∀ K : DerivedCategory (DiagonalAb W),
        ∃ (X : DerivedCategory
            (Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))))
          (g : (((I.T ⋙ RZ) ⋙ e.mapDerivedCategory.functor).obj K) ⟶ X)
          (h : X ⟶ (e.mapDerivedCategory.functor.obj K)⟦(1 : ℤ)⟧),
          Triangle.mk (η.app K) g h ∈ distTriang _ ∧
            DerivedCategory.smulInvertible (Scheme.ProEt.topology W)
              (ℓ : ULift.{u + 1} ℤ) X := by
  let E := e.mapDerivedCategory.functor
  let M := DerivedCategory.reductionModIdeal (Scheme.ProEt.topology W)
    (Ideal.span {(ℓ : ULift.{u + 1} ℤ)})
  obtain ⟨a, ha⟩ := exists_integralStrictAugmentation ℓ I RZ ηZ
  let η : E ⟶ (I.T ⋙ RZ) ⋙ E := Functor.whiskerRight a E
  have hregular (P : CochainComplex (DiagonalAb W) ℤ)
      (hP : ∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) :
      IsIso (M.map (η.app (DerivedCategory.Q.obj P))) := by
    have := counit_isIso_on_regular ℓ W I P hP
    have hh := integral_ordinary_augmentation_reduction ℓ W I.ordinary RZ ηZ hRZ e P hP
    have hfac := ha P
    have hcomp : IsIso (M.map (E.map
        (a.app (DerivedCategory.Q.obj P) ≫ RZ.map (I.ε.app P)))) := by
      rw [hfac]
      exact hh
    rw [E.map_comp, M.map_comp] at hcomp
    change IsIso (M.map (η.app (DerivedCategory.Q.obj P)) ≫
      M.map (E.map (RZ.map (I.ε.app P)))) at hcomp
    let := hcomp
    exact IsIso.of_isIso_comp_right _ (M.map (E.map (RZ.map (I.ε.app P))))
  have hall (K : DerivedCategory (DiagonalAb W)) : IsIso (M.map (η.app K)) := by
    let Q := DerivedCategory.Q (C := DiagonalAb W)
    obtain ⟨P, p, hp, hflat, _⟩ :=
      CochainComplex.exists_quasiIso_flat_kFlat (Q.objPreimage K)
    have : QuasiIso p := hp
    let i : Q.obj P ≅ K := asIso (Q.map p) ≪≫ Q.objObjPreimageIso K
    have hP (n : ℕ) (j : ℤ) : Mono (ℓ ^ (n + 1) • 𝟙 (P.X j)) :=
      flat_multiplication_mono _
        (integerUnit_mono W _ (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero)) _ (hflat j)
    have := hregular P hP
    have hn : E.map i.hom ≫ η.app K =
        η.app (Q.obj P) ≫ ((I.T ⋙ RZ) ⋙ E).map i.hom := η.naturality i.hom
    have heq : M.map (η.app K) =
        M.map (E.map i.inv) ≫ M.map (η.app (Q.obj P)) ≫
          M.map (((I.T ⋙ RZ) ⋙ E).map i.hom) := by
      rw [← M.map_comp, ← M.map_comp, ← hn, ← Category.assoc,
        ← E.map_comp, Iso.inv_hom_id, E.map_id, Category.id_comp]
    rw [heq]
    infer_instance
  refine ⟨η, fun K ↦ ?_⟩
  obtain ⟨X, g, h, hT⟩ := distinguished_cocone_triangle (η.app K)
  refine ⟨X, g, h, hT, ?_⟩
  have hzero : IsZero (M.obj X) :=
    (Triangle.isZero₃_iff_isIso₁ _ (M.map_distinguished _ hT)).2 (hall K)
  exact DerivedCategory.isIso_smul_id_of_isZero_reductionModIdeal
    (integral_prime_regular ℓ) X hzero

end AlgebraicGeometry.ProEtale
