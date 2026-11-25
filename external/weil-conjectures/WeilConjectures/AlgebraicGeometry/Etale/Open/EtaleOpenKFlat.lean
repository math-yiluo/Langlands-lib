/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs
import WeilConjectures.AlgebraicGeometry.Etale.Constant.EtaleConstantModuleTensor
import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumTensorTotalization
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-! # Extension by zero preserves unbounded K-flat complexes

Source: Stacks Tags 0E8I, 06YN, and 0GKF. The proof transports arbitrary acyclic
ringed-site tensor tests through the canonical constant-module equivalences and
the signed total-tensor projection isomorphism. No quasi-compactness is required.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme
open Etale
private def totalTensor (C : Type*) [Category C] [Abelian C]
    [MonoidalCategory C] [(curriedTensor C).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor C).obj M).PreservesZeroMorphisms] [HasCoproducts.{0} C] :
    CochainComplex C ℤ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  (curriedTensor C).map₂CochainComplex

private def tensorComparisonCurried {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (E : C ⥤ D)
    (e : E.prod E ⋙ tensor D ≅ tensor C ⋙ E) :
    (Functor.postcompose₂.obj E).obj (curriedTensor C) ≅
      (((Functor.whiskeringLeft₂ D).obj E).obj E).obj (curriedTensor D) := by
  refine NatIso.ofComponents (fun M ↦ NatIso.ofComponents
    (fun N ↦ (e.app (M, N)).symm) ?_) ?_
  · intro N N' g
    simpa using e.inv.naturality (X := (M, N)) (Y := (M, N')) (𝟙 M, g)
  · intro M M' f
    ext N
    simpa using e.inv.naturality (X := (M, N)) (Y := (M', N)) (f, 𝟙 N)

private theorem totalTensorRealization
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [MonoidalCategory C] [MonoidalCategory D]
    [(curriedTensor C).PreservesZeroMorphisms]
    [∀ X, ((curriedTensor C).obj X).PreservesZeroMorphisms]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ X, ((curriedTensor D).obj X).PreservesZeroMorphisms]
    [HasCoproducts.{0} C] [HasCoproducts.{0} D]
    (E : C ⥤ D) [E.IsEquivalence] [E.Additive]
    (τ : (Functor.postcompose₂.obj E).obj (curriedTensor C) ≅
      (((Functor.whiskeringLeft₂ D).obj E).obj E).obj (curriedTensor D))
    (P Q : CochainComplex C ℤ) :
    Nonempty (((totalTensor D).obj ((E.mapHomologicalComplex (.up ℤ)).obj P)).obj
      ((E.mapHomologicalComplex (.up ℤ)).obj Q) ≅
        (E.mapHomologicalComplex (.up ℤ)).obj (((totalTensor C).obj P).obj Q)) := by
  exact ⟨(asIso (HomologicalComplex.mapBifunctorComparison
    τ.hom (.up ℤ) P Q)).symm⟩

private theorem totalTensorRealizationAlongEquality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [MonoidalCategory C] [MonoidalCategory D]
    [(curriedTensor C).PreservesZeroMorphisms]
    [∀ X, ((curriedTensor C).obj X).PreservesZeroMorphisms]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ X, ((curriedTensor D).obj X).PreservesZeroMorphisms]
    [HasCoproducts.{0} C] [HasCoproducts.{0} D]
    (E : C ⥤ D) [E.IsEquivalence] [E.Additive]
    (τ : (Functor.postcompose₂.obj E).obj (curriedTensor C) ≅
      (((Functor.whiskeringLeft₂ D).obj E).obj E).obj (curriedTensor D))
    (EC : CochainComplex C ℤ ⥤ CochainComplex D ℤ)
    (hEC : EC = E.mapHomologicalComplex (.up ℤ))
    (P Q : CochainComplex C ℤ) :
    Nonempty (((totalTensor D).obj (EC.obj P)).obj (EC.obj Q) ≅
      EC.obj (((totalTensor C).obj P).obj Q)) := by
  subst EC
  exact totalTensorRealization E τ P Q

private theorem realizationComplex_eq (T : Scheme.{u}) (A : Type (u + 1))
    [CommRing A]
    (E : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤ EtaleSumTensorTestModule T A)
    [E.PreservesZeroMorphisms] (hE : E = etaleSumTensorTestRealization T A) :
    etaleSumTensorTestRealizationComplex T A = E.mapHomologicalComplex (.up ℤ) := by
  subst E
  rfl

private theorem tensorTestTotalRealization (T : Scheme.{u}) (A : Type (u + 1))
    [CommRing A]
    (P Q : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    let R := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A)
    let := SheafOfModules.isMonoidal_W_independentCoefficients R
    let := SheafOfModules.monoidalCategory R
    let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
    let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
    Nonempty (((totalTensor _).obj
      ((etaleSumTensorTestRealizationComplex T A).obj P)).obj
      ((etaleSumTensorTestRealizationComplex T A).obj Q) ≅
      (etaleSumTensorTestRealizationComplex T A).obj (((totalTensor _).obj P).obj Q)) := by
  let R := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A)
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  obtain ⟨e⟩ := etaleConstantModule_tensor_comparison T A
  let E := etaleSumTensorTestRealization T A
  let := etaleSumTensorTestRealization_isEquivalence T A
  let := Functor.additive_of_preserves_binary_products E
  exact totalTensorRealizationAlongEquality E (tensorComparisonCurried E e)
    (etaleSumTensorTestRealizationComplex T A) (realizationComplex_eq T A E rfl) P Q

private def totalBraiding {C : Type*} [Category C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C]
    [HasCoproducts.{0} C] (P Q : CochainComplex C ℤ) :
    ((totalTensor C).obj P).obj Q ≅ ((totalTensor C).obj Q).obj P :=
  HomologicalComplex₂.total.mapIso
    (CochainComplex.Monoidal.braidingBicomplexIso P Q) (.up ℤ) ≪≫
      HomologicalComplex.mapBifunctorFlipIso Q P (curriedTensor C) (.up ℤ)

private theorem acyclic_iso {C : Type*} [Category C] [Abelian C]
    {V W : CochainComplex C ℤ} (h : V.Acyclic) (e : V ≅ W) : W.Acyclic :=
  fun n ↦ (h n).of_iso e

private theorem acyclic_map {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] (E : C ⥤ D) [E.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (V : CochainComplex C ℤ) (h : V.Acyclic) :
    ((E.mapHomologicalComplex (.up ℤ)).obj V).Acyclic :=
  fun n ↦ (h n).map E

private theorem acyclic_of_map_equivalence
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (E : C ⥤ D) [E.IsEquivalence] [E.Additive]
    (Z : CochainComplex C ℤ)
    (hZ : ((E.mapHomologicalComplex (.up ℤ)).obj Z).Acyclic) : Z.Acyclic := by
  intro n
  exact ((Z.sc n).exact_map_iff_of_faithful E).mp (hZ n)

private theorem transported_tensor_test
    {CU CX DU DX : Type*} [Category CU] [Category CX] [Category DU] [Category DX]
    (TU : CU ⥤ CU ⥤ CU) (TX : CX ⥤ CX ⥤ CX)
    (SU : DU ⥤ DU ⥤ DU) (SX : DX ⥤ DX ⥤ DX)
    (EU : CU ⥤ DU) (EX : CX ⥤ DX) [EX.IsEquivalence]
    (L : CU ⥤ CX) (R : CX ⥤ CU)
    (AU : CU → Prop) (AX : CX → Prop) (BU : DU → Prop) (BX : DX → Prop)
    (hAXiso : ∀ {V W}, AX V → (V ≅ W) → AX W)
    (hBUiso : ∀ {V W}, BU V → (V ≅ W) → BU W)
    (hBXiso : ∀ {V W}, BX V → (V ≅ W) → BX W)
    (hEXref : ∀ Z, BX (EX.obj Z) → AX Z)
    (hR : ∀ Z, AX Z → AU (R.obj Z))
    (hEU : ∀ Z, AU Z → BU (EU.obj Z))
    (hEUref : ∀ Z, BU (EU.obj Z) → AU Z)
    (hL : ∀ Z, AU Z → AX (L.obj Z))
    (hEX : ∀ Z, AX Z → BX (EX.obj Z))
    (hU : ∀ P Q, Nonempty ((SU.obj (EU.obj P)).obj (EU.obj Q) ≅
      EU.obj ((TU.obj P).obj Q)))
    (hX : ∀ P Q, Nonempty ((SX.obj (EX.obj P)).obj (EX.obj Q) ≅
      EX.obj ((TX.obj P).obj Q)))
    (βU : ∀ P Q, (TU.obj P).obj Q ≅ (TU.obj Q).obj P)
    (βX : ∀ P Q, (TX.obj P).obj Q ≅ (TX.obj Q).obj P)
    (Ψ : ∀ P K, (TX.obj (L.obj P)).obj K ≅ L.obj ((TU.obj P).obj (R.obj K)))
    (P : CU) (hP : ∀ Q, BU Q → BU ((SU.obj Q).obj (EU.obj P))) :
    ∀ B, BX B → BX ((SX.obj B).obj (EX.obj (L.obj P))) := by
  intro B hB
  let K := EX.objPreimage B
  let eK : EX.obj K ≅ B := EX.objObjPreimageIso B
  have hRK := hR K (hEXref K (hBXiso hB eK.symm))
  have htest := hP (EU.obj (R.obj K)) (hEU _ hRK)
  obtain ⟨eU⟩ := hU (R.obj K) P
  have htest' := hEUref _ (hBUiso htest eU)
  have hsource := hL _ htest'
  let eproj := βX K (L.obj P) ≪≫ Ψ P K ≪≫ L.mapIso (βU P (R.obj K))
  have htarget := hEX _ (hAXiso hsource eproj.symm)
  obtain ⟨eX⟩ := hX K (L.obj P)
  have hmodel := hBXiso htarget eX.symm
  let eB := (SX.flip.obj (EX.obj (L.obj P))).mapIso eK
  exact hBXiso hmodel eB

private theorem transported_complex_tensor_test
    {CU CX DU DX : Type*} [Category CU] [Category CX] [Category DU] [Category DX]
    [Abelian CU] [Abelian CX] [Abelian DU] [Abelian DX]
    [MonoidalCategory CU] [MonoidalCategory CX]
    [MonoidalPreadditive CU] [MonoidalPreadditive CX]
    [BraidedCategory CU] [BraidedCategory CX]
    [HasCoproducts.{0} CU] [HasCoproducts.{0} CX]
    (SU : CochainComplex DU ℤ ⥤ CochainComplex DU ℤ ⥤ CochainComplex DU ℤ)
    (SX : CochainComplex DX ℤ ⥤ CochainComplex DX ℤ ⥤ CochainComplex DX ℤ)
    (EU : CU ⥤ DU) (EX : CX ⥤ DX) [EU.IsEquivalence] [EX.IsEquivalence]
    [EU.Additive] [EX.Additive]
    (EUc : CochainComplex CU ℤ ⥤ CochainComplex DU ℤ)
    (EXc : CochainComplex CX ℤ ⥤ CochainComplex DX ℤ)
    (hEUc : EUc = EU.mapHomologicalComplex (.up ℤ))
    (hEXc : EXc = EX.mapHomologicalComplex (.up ℤ))
    (L : CU ⥤ CX) (R : CX ⥤ CU) [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (hU : ∀ P Q, Nonempty ((SU.obj (EUc.obj P)).obj (EUc.obj Q) ≅
      EUc.obj (((totalTensor CU).obj P).obj Q)))
    (hX : ∀ P Q, Nonempty ((SX.obj (EXc.obj P)).obj (EXc.obj Q) ≅
      EXc.obj (((totalTensor CX).obj P).obj Q)))
    (Ψ : TotalTensorComparison (curriedTensor CU) (curriedTensor CX) L R)
    (P : CochainComplex CU ℤ)
    (hP : ∀ Q, Q.Acyclic → ((SU.obj Q).obj (EUc.obj P)).Acyclic) :
    ∀ B, B.Acyclic → ((SX.obj B).obj
      (EXc.obj ((L.mapHomologicalComplex (.up ℤ)).obj P))).Acyclic := by
  subst EUc EXc
  let : (EX.mapHomologicalComplex (.up ℤ)).IsEquivalence :=
    (EX.asEquivalence.mapHomologicalComplex (.up ℤ)).isEquivalence_functor
  exact transported_tensor_test (totalTensor CU) (totalTensor CX) SU SX
    (EU.mapHomologicalComplex (.up ℤ)) (EX.mapHomologicalComplex (.up ℤ))
    (L.mapHomologicalComplex (.up ℤ)) (R.mapHomologicalComplex (.up ℤ))
    HomologicalComplex.Acyclic HomologicalComplex.Acyclic
    HomologicalComplex.Acyclic HomologicalComplex.Acyclic
    acyclic_iso acyclic_iso acyclic_iso
    (acyclic_of_map_equivalence EX) (acyclic_map R)
    (acyclic_map EU) (acyclic_of_map_equivalence EU)
    (acyclic_map L) (acyclic_map EX) hU hX
    totalBraiding totalBraiding Ψ P hP

private theorem kflat_as_test (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    let R := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A)
    let := SheafOfModules.isMonoidal_W_independentCoefficients R
    let := SheafOfModules.monoidalCategory R
    let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
    let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
    Etale.etaleKFlat T A P ↔ ∀ Q : CochainComplex (EtaleSumTensorTestModule T A) ℤ,
      Q.Acyclic → (((totalTensor _).obj Q).obj
        ((etaleSumTensorTestRealizationComplex T A).obj P)).Acyclic := Iff.rfl

private theorem kflat_open_direct
    {A : Type (u + 1)} [CommRing A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hP : Etale.etaleKFlat U A P) : Etale.etaleKFlat X A
      (((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) j inferInstance).mapHomologicalComplex
        (.up ℤ)).obj P) := by
  let Eₓ := etaleSumTensorTestRealization X A
  let Eᵤ := etaleSumTensorTestRealization U A
  let := etaleSumTensorTestRealization_isEquivalence X A
  let := etaleSumTensorTestRealization_isEquivalence U A
  let : Eₓ.Additive := Functor.additive_of_preserves_binary_products Eₓ
  let : Eᵤ.Additive := Functor.additive_of_preserves_binary_products Eᵤ
  let L := Etale.etaleLowerShriek (ModuleCat.{u + 1} A) j inferInstance
  let adj := Etale.etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j inferInstance
  let : L.IsLeftAdjoint := adj.isLeftAdjoint
  let : L.Additive := Functor.additive_of_preserves_binary_products L
  let R := Etale.upperStar (ModuleCat.{u + 1} A) j
  let 𝓡U := (constantSheaf U.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A)
  let 𝓡X := (constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A)
  let := SheafOfModules.isMonoidal_W_independentCoefficients 𝓡U
  let := SheafOfModules.monoidalCategory 𝓡U
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients 𝓡U
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients 𝓡U
  let := SheafOfModules.isMonoidal_W_independentCoefficients 𝓡X
  let := SheafOfModules.monoidalCategory 𝓡X
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients 𝓡X
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients 𝓡X
  obtain ⟨Ψ⟩ := etale_sum_tensor_comparison A j inferInstance
  apply (kflat_as_test X A _).mpr
  have hP' := (kflat_as_test U A P).mp hP
  exact transported_complex_tensor_test (totalTensor _) (totalTensor _) Eᵤ Eₓ
    (etaleSumTensorTestRealizationComplex U A) (etaleSumTensorTestRealizationComplex X A)
    (realizationComplex_eq U A Eᵤ rfl) (realizationComplex_eq X A Eₓ rfl) L R
    (tensorTestTotalRealization U A) (tensorTestTotalRealization X A) Ψ P hP'

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

/-- Exact open extension preserves the acyclic total-tensor tests for K-flatness.
Source: Stacks 0E8I, 06YN, 0GKF (blueprint: lem-coef-etale-open-kflat).

Proof: Given an acyclic complex B on X, exact restriction makes j-star B acyclic.
K-flatness of P makes its direct-sum total tensor with j-star B acyclic. Apply
exact extension by zero. The ordinary projection isomorphism in every bidegree,
and preservation of coproducts by j-shriek, identify the resulting total complex
with the tensor of j-shriek P and B. The comparison respects both differential
summands by naturality and additivity. Signed symmetry puts the test complex
first. Transport through the exact constant-module equivalence preserves the
acyclicity and gives precisely etaleKFlat. This argument uses arbitrary direct
sums, so requires neither boundedness nor quasi-compactness of j. -/
theorem etaleOpenKFlat
    {A : Type (u + 1)} [CommRing A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hP : etaleKFlat U A P) : etaleKFlat X A
      (((j)_!open[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).obj P) := by
  exact AlgebraicGeometry.Scheme.kflat_open_direct j P hP

end AlgebraicGeometry.Etale
