/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerEtaleDescentData
import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerScalarRestriction
import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerLocalizedRealization
import WeilConjectures.AlgebraicGeometry.Etale.EtaleNormalizationCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison

/-! # Descending and realizing normalization arrows after descent of the levels

## References

* Stacks Project, Tags 099Z and 09B1 (bounded-below full faithfulness), 06YY (scalar extension),
  03DA and 0H7J (restriction and inverse image)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard
  pbcDerivedRestrict constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow etaleIsomorphismNormalizationArrow
  lisseTowerAlgebraArrow lisseTowerFixedRealization

private theorem etaleRealization_map_bijective
    {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (C C' : DerivedCategory
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))))
    (hC' : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj C')) :
    Function.Bijective (fun k : C ⟶ C' ↦ (lisseTowerEtaleRealization f d n).map k) := by
  obtain ⟨a, b, hab⟩ := hC'
  have hge : C'.IsGE a := (DerivedCategory.isGE_iff C' a).2 fun q hq ↦ hab q (Or.inl hq)
  have hplus : DerivedCategory.TStructure.t.plus C' := ⟨a, hge⟩
  exact ((Functor.FullyFaithful.ofFullyFaithful
    (lisseTowerFixedRealization f d n)).map_bijective _ _).comp
      (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map C C' hplus)

/-- Normalization arrows descend once the etale levels and their comparison are given.
The statement neither constructs etale levels nor asks for finite locally constant
cohomology, algebraic local markings, or inhabited Isom stalks. -/
theorem lisse_tower_etale_normalization_descent
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (M : AdicTower X d)
    (U : Y.ProEt)
    (D : ∀ n : ℕ, DerivedCategory
      (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))))
    (hbounded : ∀ n : ℕ, ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (D n)))
    (e : ∀ n : ℕ, (lisseTowerFixedRealization (U.hom ≫ g) d n).obj
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) U.left).mapDerivedCategory.obj (D n)) ≅
      (adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj (M.level n)) :
    Nonempty (LisseTowerEtaleNormalization X Y g d M U D) := by
  classical
  choose c hc using fun n ↦ (lisseTower_scalar_restriction (U.hom ≫ g) d n).exists
  have lift_step (n : ℕ) : ∃ δ : D (n + 1) ⟶
      (normalizationRestrict U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)).obj
        (D n),
      (lisseTowerEtaleRealization (U.hom ≫ g) d (n + 1)).map δ ≫
          (lisseTowerEtaleScalarIso (U.hom ≫ g) d n (c n)).hom.app (D n) ≫
          (pbcDerivedRestrict ((adicTowerInverseImage (U.hom ≫ g)).map
            (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).map (e n).hom =
        (e (n + 1)).hom ≫
          adicTowerRestrictedTransition d (U.hom ≫ g) M (n + 1) n (Nat.le_succ n) := by
    let R := pbcDerivedRestrict ((adicTowerInverseImage (U.hom ≫ g)).map
      (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
    let t := adicTowerRestrictedTransition d (U.hom ≫ g) M (n + 1) n (Nat.le_succ n)
    let k := (e (n + 1)).hom ≫ t ≫ R.map (e n).inv ≫
      (lisseTowerEtaleScalarIso (U.hom ≫ g) d n (c n)).inv.app (D n)
    have hres : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((normalizationRestrict U.left.smallEtaleTopology
            (lisseTowerEtaleQuotient d n)).obj (D n))) := by
      obtain ⟨a, b, hab⟩ := hbounded n
      exact ⟨a, b, fun q hq ↦ Functor.isZero_homologyFunctor_mapDerivedCategory_obj
        (sheafCompose U.left.smallEtaleTopology
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n)))
        (hab q hq)⟩
    obtain ⟨δ, hδ⟩ := (etaleRealization_map_bijective (U.hom ≫ g) d (n + 1)
      (D (n + 1)) _ hres).surjective k
    refine ⟨δ, ?_⟩
    dsimp only at hδ
    erw [hδ]
    change ((e (n + 1)).hom ≫ t ≫ R.map (e n).inv ≫
      (lisseTowerEtaleScalarIso (U.hom ≫ g) d n (c n)).inv.app (D n)) ≫
        (lisseTowerEtaleScalarIso (U.hom ≫ g) d n (c n)).hom.app (D n) ≫
        R.map (e n).hom = _
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    erw [← R.map_comp, Iso.inv_hom_id, R.map_id, Category.comp_id]
  choose δ hδ using lift_step
  obtain ⟨L⟩ := lisseTower_localized_realization X Y g d M U D c
    (fun n ↦ (hc n).1) δ e hδ
  refine ⟨{
    delta := δ
    local_delta := fun n ↦ by
      have hr := (hc n).2.1
      unfold LisseTowerScalarSquareReflects at hr
      have hu := hr M (D (n + 1)) (D n) (hbounded (n + 1)) (hbounded n)
        (e (n + 1)) (e n) (δ n) (hδ n)
      exact {
        universal := hu
        coherence := etaleNormalization_coherence U.left (lisseTowerEtaleQuotient d n)
          (δ n) }
    local_constant_universal := ?_
    constant_coherence := ?_
    realization := lisseTowerLocalRealization g d U
    model := L.model
    actual := L.actual
    scalar := L.scalar
    actual_normalized := L.actual_normalized
    model_normalized := L.model_normalized }⟩
  · intro n E E' k hk V
    have hk' := (hc n).2.2
    unfold LisseTowerConstantLocalUniversal at hk'
    exact hk' E E' k hk V
  · intro n E E' k V Z f
    exact etaleNormalization_coherence U.left (lisseTowerEtaleQuotient d n)
      (normalizationConstantArrow U.left.smallEtaleTopology
        (lisseTowerEtaleQuotient d n) k) f

end AlgebraicGeometry.Scheme
