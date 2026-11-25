/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization
public import WeilConjectures.CategoryTheory.Derived.DerivedSquareIndependentUniverses
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemUnboundedComparison

/-! # Exact localization of the ordinary inverse-image restriction square

Source: Zheng, Construction 4.1; Stacks 05R7 and 05RU.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

variable (O : Type (u + 1)) [CommRing O] (t : O)
  {V W : Scheme.{u}} (g : V ⟶ W) (A : StrictEtaleOrdinaryImage O t g)
  (PW : StrictEtaleEvaluation W O t) (PV : StrictEtaleEvaluation V O t)
  (B : CoefficientSystemDerivedImage (J := W.smallEtaleTopology)
    (K := V.smallEtaleTopology) O t _ _ _ A PW PV)
  {m n : ℕ} (h : m ≤ n)

/-- The exact lift of the ordinary coefficient-restriction inverse-image square.
Source: Zheng, Construction 4.1; Stacks 05R7 and 05RU.
(blueprint: def-pur-etale-brown-canonical-restriction).

The representative equation determines this isomorphism uniquely by fully faithful
precomposition with the derived localization; the choice introduces no arbitrary data. -/
def strictEtaleBrownCanonicalRestriction :
    (PW.scalar h).restriction ⋙ (B.level n).inverse ≅
      (B.level m).inverse ⋙ (PV.scalar h).restriction :=
  (exists_derivedSquare_independentUniverses
    (coefficientRestriction (J := W.smallEtaleTopology) O t h)
    (A.lift m).modules (A.lift n).modules
    (coefficientRestriction (J := V.smallEtaleTopology) O t h)
    (PW.scalar h).restriction (B.level m).inverse (B.level n).inverse
    (PV.scalar h).restriction (PW.scalar h).restrictionFactors
    (B.level m).inverseFactors (B.level n).inverseFactors
    (PV.scalar h).restrictionFactors (A.restrictInverse h)).choose

/-- The canonical lift has the prescribed cochain representative.
Source: Zheng, Construction 4.1; Stacks 05R7 and 05RU.
(blueprint: def-pur-etale-brown-canonical-restriction).
Proof: this is the lifting equation of fully faithful localization precomposition. -/
theorem strictEtaleBrownCanonicalRestriction_rep
    (K : CochainComplex (strictEtaleLevel W O t m) ℤ) :
    (strictEtaleBrownCanonicalRestriction O t g A PW PV B h).hom.app
        (DerivedCategory.Q.obj K) ≫
      (PV.scalar h).restriction.map ((B.level m).inverseFactors.hom.app K) ≫
      (PV.scalar h).restrictionFactors.hom.app
        (((A.lift m).modules.mapHomologicalComplex (.up ℤ)).obj K) =
    (B.level n).inverse.map ((PW.scalar h).restrictionFactors.hom.app K) ≫
      (B.level n).inverseFactors.hom.app
        ((Functor.mapHomologicalComplex
          (coefficientRestriction (J := W.smallEtaleTopology) O t h) (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (A.restrictInverse h) (.up ℤ)).hom.app K) :=
  (exists_derivedSquare_independentUniverses
    (coefficientRestriction (J := W.smallEtaleTopology) O t h)
    (A.lift m).modules (A.lift n).modules
    (coefficientRestriction (J := V.smallEtaleTopology) O t h)
    (PW.scalar h).restriction (B.level m).inverse (B.level n).inverse
    (PV.scalar h).restriction (PW.scalar h).restrictionFactors
    (B.level m).inverseFactors (B.level n).inverseFactors
    (PV.scalar h).restrictionFactors (A.restrictInverse h)).choose_spec K

-- Transposing the scalar adjunction exposes several localization factors.
/-- The tensor comparison is the scalar mate of the exact restriction square.
Source: Zheng, Construction 4.1; Stacks 06YY and 07A4.
(blueprint: lem-pur-etale-brown-canonical-restriction-mate).

Proof: compute the inverse scalar mate on complexes using the normalized scalar
adjunctions. On a flat-term K-flat resolution, the tensor representative equation
identifies it with the inverse of derivedTensor. Cancel the invertible scalar
comparison on this resolution. Naturality and the quasi-isomorphism from the
resolution identify the components on every derived object. -/
theorem strictEtaleBrownCanonicalRestriction_mate :
    ((mateEquiv (PW.scalar h).derivedAdj (PV.scalar h).derivedAdj).symm
      (.mk _ _ _ _ (strictEtaleBrownCanonicalRestriction O t g A PW PV B h).hom)) =
        (B.derivedTensor h).inv := by
  let δ := strictEtaleBrownCanonicalRestriction O t g A PW PV B h
  let τ := ((mateEquiv (PW.scalar h).derivedAdj (PV.scalar h).derivedAdj).symm
    (.mk _ _ _ _ δ.hom))
  have hτ (P : CochainComplex (strictEtaleLevel W O t n) ℤ) :=
    SheafOfModules.derivedLeftSquare_rep (A.lift n).modules
      (coefficientTensor (J := W.smallEtaleTopology) (O := O) (ell := t) h)
      (coefficientRestriction (J := W.smallEtaleTopology) O t h)
      (coefficientTensor (J := V.smallEtaleTopology) (O := O) (ell := t) h)
      (coefficientRestriction (J := V.smallEtaleTopology) O t h)
      (coefficientTensorAdj (J := W.smallEtaleTopology) (O := O) (ell := t) h)
      (coefficientTensorAdj (J := V.smallEtaleTopology) (O := O) (ell := t) h)
      _ _ (PW.scalar h) (PV.scalar h) (A.lift m).modules
      (B.level n).inverse (B.level m).inverse
      (B.level n).inverseFactors (B.level m).inverseFactors
      (A.restrictInverse h) δ
      (strictEtaleBrownCanonicalRestriction_rep O t g A PW PV B h)
      (B.tensor h).symm
      (SheafOfModules.tensorSquare_transpose (A.lift n).modules
        (coefficientTensor (J := W.smallEtaleTopology) (O := O) (ell := t) h)
        (coefficientRestriction (J := W.smallEtaleTopology) O t h)
        (coefficientTensor (J := V.smallEtaleTopology) (O := O) (ell := t) h)
        (coefficientRestriction (J := V.smallEtaleTopology) O t h)
        (A.lift m).modules
        (coefficientTensorAdj (J := W.smallEtaleTopology) (O := O) (ell := t) h)
        (coefficientTensorAdj (J := V.smallEtaleTopology) (O := O) (ell := t) h)
        (A.restrictInverse h) (B.tensor h) (B.tensor_unit h)) P
  have he (P : CochainComplex (strictEtaleLevel W O t n) ℤ)
      (hP : P.IsKFlatIndependentCoefficients)
      (hf : ∀ i : ℤ, IsFlatOnSite (J := W.smallEtaleTopology)
        (R := coefficientQuotientSheaf (J := W.smallEtaleTopology) O t n) (P.X i)) :
      τ.app (DerivedCategory.Q.obj P) =
        (B.derivedTensor h).inv.app (DerivedCategory.Q.obj P) := by
    have := (PW.scalar h).computes P hP
    have hh := hτ P
    change τ.app _ ≫ _ ≫ _ = _ at hh
    apply (cancel_epi ((B.derivedTensor h).hom.app (DerivedCategory.Q.obj P))).1
    rw [Iso.hom_inv_id_app]
    apply (cancel_mono ((B.level m).inverse.map ((PW.scalar h).counit.app P) ≫
      (B.level m).inverseFactors.hom.app
        ((Functor.mapHomologicalComplex
          (coefficientTensor (J := W.smallEtaleTopology) (O := O) (ell := t) h)
          (.up ℤ)).obj P))).1
    simp only [Category.id_comp, Category.assoc]
    rw [hh]
    have hr := B.derivedTensor_rep h P hP hf
    change (B.derivedTensor h).hom.app (DerivedCategory.Q.obj P) ≫
      (PV.scalar h).derived.map ((B.level n).inverseFactors.hom.app P) ≫
      (PV.scalar h).counit.app
        (((A.lift n).modules.mapHomologicalComplex (.up ℤ)).obj P) = _ at hr
    rw [reassoc_of% hr]
    simp only [← DerivedCategory.Q.map_comp]
    rw [show (NatIso.mapHomologicalComplex (B.construction.scalar.tensor h)
      (.up ℤ)).hom.app P ≫
        (NatIso.mapHomologicalComplex (B.tensor h).symm (.up ℤ)).hom.app P = 𝟙 _ from
      (NatIso.mapHomologicalComplex (B.tensor h) (.up ℤ)).hom_inv_id_app P]
    erw [DerivedCategory.Q.map_id, Category.comp_id]
  apply NatTrans.ext
  funext X
  obtain ⟨P, q, hP, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := coefficientQuotientSheaf (J := W.smallEtaleTopology) O t n)
      (DerivedCategory.Q.objPreimage X : CochainComplex (strictEtaleLevel W O t n) ℤ)
  have := hq
  let e : DerivedCategory.Q.obj P ≅ X :=
    asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso X
  apply (cancel_epi (((B.level n).inverse ⋙ (PV.scalar h).derived).map e.hom)).1
  rw [τ.naturality, (B.derivedTensor h).inv.naturality,
    he P hP (fun j ↦ (exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso _ (P.X j)).symm (hf j))]

end AlgebraicGeometry
