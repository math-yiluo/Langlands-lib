/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # The map from canonical cycles to a complex
Source: Stacks Project, Tag 05TC (2).
(blueprint: new-lem-pc-derived-cycles-map-homology).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace DerivedCategory
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The chain map whose only nonzero component is the canonical cycle inclusion.
Source: Stacks Project, Tag 05TC (2).
(blueprint: new-lem-pc-derived-cycles-map-homology). -/
noncomputable def cyclesChainMap (n : ℤ) (K : CochainComplex C ℤ) :
    (CochainComplex.singleFunctor C n).obj ((K.sc n).cycles) ⟶ K :=
  HomologicalComplex.mkHomFromSingle (K.sc n).iCycles (fun j _ ↦ K.iCycles_d n j)

/-- The localized cycle map, with source the specified derived single functor.
Source: Stacks Project, Tag 05TC (2).
(blueprint: new-lem-pc-derived-cycles-map-homology). -/
noncomputable def cyclesDerivedMap (n : ℤ) (K : CochainComplex C ℤ) :
    (singleFunctor C n).obj ((K.sc n).cycles) ⟶ Q.obj K :=
  (singleFunctorIsoCompQ C n).hom.app ((K.sc n).cycles) ≫ Q.map (cyclesChainMap n K)

/-- The cycle map induces precisely the canonical quotient on homology.
Source: Stacks Project, Tag 05TC (2).
(blueprint: new-lem-pc-derived-cycles-map-homology).

Proof: Apply naturality of the localization/homology factor isomorphism to
cyclesChainMap. At degree n its component is the cycle inclusion, preceded
by the identification of the single complex's term with the cycles object.
The induced map on cycles is therefore the inverse single/cycles
identification. Naturality of homologyπ makes its induced homology map the
canonical quotient of K, preceded by the inverse single/homology
identification. The derived single/homology isomorphism is defined using
these same localization and single comparisons; cancel them to obtain the
formula. -/
theorem cyclesDerivedMap_homology (n : ℤ) (K : CochainComplex C ℤ) :
    (singleFunctorCompHomologyFunctorIso C n).inv.app ((K.sc n).cycles) ≫
      (homologyFunctor C n).map (cyclesDerivedMap n K) =
    (K.sc n).homologyπ ≫ (homologyFunctorFactors C n).inv.app K := by
  simp only [cyclesDerivedMap, Functor.map_comp]
  simp only [Functor.id_obj, Functor.comp_obj, singleFunctorCompHomologyFunctorIso,
    Iso.trans_inv, Functor.isoWhiskerLeft_inv, Category.assoc,
    Functor.isoWhiskerRight_inv, Functor.mapIso_inv, SingleFunctors.evaluation_map,
    singleFunctorsPostcompQIso_inv_hom, NatTrans.comp_app,
    HomologicalComplex.homologyFunctorSingleIso_inv_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, NatTrans.id_app,
    Category.id_comp, singleFunctorIsoCompQ, Iso.refl_hom]
  erw [(homologyFunctor C n).map_id, Category.id_comp]
  erw [Category.id_comp]
  erw [← (homologyFunctorFactors C n).inv.naturality (cyclesChainMap n K)]
  rw [← Category.assoc, cancel_mono]
  rw [← cancel_epi (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) n
    ((K.sc n).cycles)).hom]
  rw [← Category.assoc, ← HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ]
  erw [Iso.hom_inv_id_assoc]
  change HomologicalComplex.homologyπ _ n ≫
    HomologicalComplex.homologyMap (cyclesChainMap n K) n = _
  rw [HomologicalComplex.homologyπ_naturality]
  congr 1
  apply (cancel_mono (K.iCycles n)).mp
  simp only [cyclesChainMap, HomologicalComplex.cyclesMap_i,
    HomologicalComplex.singleObjCyclesSelfIso_hom,
    HomologicalComplex.mkHomFromSingle_f, Category.assoc]
  rfl

end DerivedCategory
