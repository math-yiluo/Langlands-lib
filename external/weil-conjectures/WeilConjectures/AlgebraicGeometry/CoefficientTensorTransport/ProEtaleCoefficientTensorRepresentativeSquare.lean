/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.AlgebraicGeometry.CoefficientTensorTransport.ProEtaleCoefficientPullback
public import WeilConjectures.AlgebraicGeometry.CoefficientTensorChain.ProEtaleCoefficientTensorChainData
import WeilConjectures.AlgebraicGeometry.CoefficientTensorTransport.ProEtaleTensorRepresentativeNormalization

/-! # Compatibility on flat K-flat representative pairs

(blueprint: lem-pbc-coefficient-restriction-tensor-representative-square)
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CoefficientTensorTransport

attribute [local implicit_reducible] pbcDerivedRestrict
  Functor.map₂HomologicalComplex
  SheafOfModules.restrictScalars

attribute [local irreducible] Functor.mapDerivedCategory
  proEtaleRingDerivedPullbackFactors CoefficientTensorChain.complexPullback
  pullback SheafOfModules.monoidalCategory proEtaleCanonicalTensorComparison
  proEtaleTensorPullbackTotalIso

-- Paste the representative equations before specializing to derived tensor totalizations.
private theorem map_tensor_representative_paste
    {D E J K : Type*} [Category* D] [Category* E] [Category* J] [Category* K]
    (U : D ⥤ E) (B : J ⥤ D) (Z : K ⥤ E) (V : J ⥤ K)
    (γ : B ⋙ U ⟶ V ⋙ Z)
    {W X Y T : D} {p₀ p₁ : J} {q₀ q₁ q₂ : K} {u₀ u₁ u₂ i₀ i₁ : E}
    (r : W ⟶ X) (a : X ⟶ B.obj p₀) (e : W ⟶ Y)
    (m : Y ⟶ T) (s : T ⟶ B.obj p₁) (d : p₀ ⟶ p₁)
    (b : V.obj p₀ ⟶ q₀) (i : q₀ ⟶ q₁) (v : V.obj p₁ ⟶ q₂) (t : q₂ ⟶ q₁)
    (e₀ : U.obj Y ⟶ u₀) (e₁ : U.obj T ⟶ u₁) (n : u₀ ⟶ u₁)
    (σ : u₁ ⟶ u₂) (sU : u₂ ⟶ Z.obj q₂) (β : u₀ ⟶ i₀)
    (mI : i₀ ⟶ i₁) (tI : u₂ ⟶ i₁) (sI : i₁ ⟶ Z.obj q₁)
    (hc : r ≫ a ≫ B.map d = e ≫ m ≫ s)
    (hpair : b ≫ i = V.map d ≫ v ≫ t)
    (hu : U.map s ≫ γ.app p₁ ≫ Z.map v = e₁ ≫ σ ≫ sU)
    (hm : U.map m ≫ e₁ = e₀ ≫ n)
    (hrep : sU ≫ Z.map t = tI ≫ sI)
    (hchain : β ≫ mI = n ≫ σ ≫ tI) :
    U.map r ≫ (U.map a ≫ γ.app p₀ ≫ Z.map b) ≫ Z.map i =
      U.map e ≫ e₀ ≫ β ≫ mI ≫ sI := by
  simp only [Category.assoc]
  rw [← Z.map_comp, hpair, Z.map_comp, Z.map_comp]
  rw [← reassoc_of% (γ.naturality d)]
  rw [← U.map_comp_assoc, ← U.map_comp_assoc, Category.assoc, hc,
    U.map_comp, U.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hu, reassoc_of% hm, hrep, ← reassoc_of% hchain]

/-- Compatibility for a flat K-flat pair, given the normalized restriction comparison.

Source: Stacks Tags 03EL, 07A4 and 07A6.
(blueprint: lem-pbc-coefficient-restriction-tensor-representative-square)

Proof: normalize both geometric tensor maps on representatives. Naturality of their
factorizations moves the canonical coefficient pullback comparison past the tensor
representative. The normalization of gamma rewrites the other side. Naturality of
z's representative and the localized chain square identify the resulting composites.
Cancel the invertible representative and the two pullback factorizations. -/
theorem representative_square {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (aY : ProEtaleTensorModel Y R)
    (z : ProEtaleTensorModel X
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))
    (aX : ProEtaleTensorModel X S)
    (o : SheafOfModules.RingIsoTensorTransport (J := ProEt.topology X)
      (R := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (S := S) c)
    (hU : ∀ P : CochainComplex (proEtaleRingModules X S) ℤ,
      proEtaleFlatRepresentatives X S P →
        proEtaleFlatRepresentatives X
          ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
          (((pbcRestrict c.hom).mapHomologicalComplex (.up ℤ)).obj P))
    (gamma : aX.tensor ⋙ pbcDerivedRestrict c.hom ≅
      ((pbcDerivedRestrict c.hom).prod (pbcDerivedRestrict c.hom)) ⋙ z.tensor)
    (hgamma : ∀ (P Q : CochainComplex (proEtaleRingModules X S) ℤ)
      (hp : proEtaleFlatRepresentatives X S P) (hq : proEtaleFlatRepresentatives X S Q),
      (pbcDerivedRestrict c.hom).map (aX.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
        gamma.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        z.tensor.map (Prod.mkHom ((pbcRestrict c.hom).mapDerivedCategoryFactors.hom.app P)
          ((pbcRestrict c.hom).mapDerivedCategoryFactors.hom.app Q)) =
      (pbcRestrict c.hom).mapDerivedCategoryFactors.hom.app
        ((CoefficientTensorChain.total X S).obj (P, Q)) ≫
      DerivedCategory.Q.map ((CoefficientTensorChain.tensorIso f R S c o).hom.app (P, Q)) ≫
      z.representative.hom.app
        (⟨((pbcRestrict c.hom).mapHomologicalComplex (.up ℤ)).obj P, hU P hp⟩,
          ⟨((pbcRestrict c.hom).mapHomologicalComplex (.up ℤ)).obj Q, hU Q hq⟩))
    (P Q : CochainComplex (proEtaleRingModules Y R) ℤ)
    (hp : proEtaleFlatRepresentatives Y R P) (hq : proEtaleFlatRepresentatives Y R Q) :
        (pullback f R S c).hom.app
          (aY.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
            (proEtaleCanonicalTensorComparison f R
              ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
              (Iso.refl _) aY z).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
          (pbcDerivedRestrict c.hom).map
              ((proEtaleCanonicalTensorComparison f R S c aY aX).hom.app
                (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
            gamma.hom.app ((proEtaleRingDerivedPullback f R S c).obj (DerivedCategory.Q.obj P),
              (proEtaleRingDerivedPullback f R S c).obj (DerivedCategory.Q.obj Q)) ≫
            z.tensor.map (Prod.mkHom
              ((pullback f R S c).hom.app (DerivedCategory.Q.obj P))
              ((pullback f R S c).hom.app (DerivedCategory.Q.obj Q))) := by
  let A := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R
  let U := (pbcRestrict c.hom).mapHomologicalComplex (.up ℤ)
  let C := (proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)
  let I := (proEtaleRingModulePullback f R A (Iso.refl _)).mapHomologicalComplex (.up ℤ)
  let UD := pbcDerivedRestrict c.hom
  let CD := proEtaleRingDerivedPullback f R S c
  let ID := proEtaleRingDerivedPullback f R A (Iso.refl _)
  let b := pullback f R S c
  let ac := proEtaleCanonicalTensorComparison f R S c aY aX
  let ai := proEtaleCanonicalTensorComparison f R A (Iso.refl _) aY z
  let sigma := CoefficientTensorChain.tensorIso f R S c o
  let left := b.hom.app (aY.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
    ai.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)
  let right := UD.map (ac.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
    gamma.hom.app (CD.obj (DerivedCategory.Q.obj P), CD.obj (DerivedCategory.Q.obj Q)) ≫
      z.tensor.map (Prod.mkHom (b.hom.app (DerivedCategory.Q.obj P))
        (b.hom.app (DerivedCategory.Q.obj Q)))
  change left = right
  obtain ⟨hpC, hqC, hc⟩ := canonical_tensor_representative f R S c aY aX P Q hp hq
  obtain ⟨hpI, hqI, hi⟩ := canonical_tensor_representative f R A (Iso.refl _) aY z P Q hp hq
  have hu := hgamma (C.obj P) (C.obj Q) hpC hqC
  let T := (CoefficientTensorChain.total Y R).obj (P, Q)
  let eC := (proEtaleRingDerivedPullbackFactors f R S c).hom
  let eI := (proEtaleRingDerivedPullbackFactors f R A (Iso.refl _)).hom
  let eU := (pbcRestrict c.hom).mapDerivedCategoryFactors.hom
  let beta := (CoefficientTensorChain.complexPullback f R S c).hom
  let r : DerivedCategory.Q.obj T ⟶
      aY.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) :=
    aY.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)
  let rc : DerivedCategory.Q.obj ((CoefficientTensorChain.total X S).obj (C.obj P, C.obj Q)) ⟶
      aX.tensor.obj (DerivedCategory.Q.obj (C.obj P), DerivedCategory.Q.obj (C.obj Q)) :=
    aX.representative.hom.app (⟨C.obj P, hpC⟩, ⟨C.obj Q, hqC⟩)
  let ri : DerivedCategory.Q.obj ((CoefficientTensorChain.total X A).obj (I.obj P, I.obj Q)) ⟶
      z.tensor.obj (DerivedCategory.Q.obj (I.obj P), DerivedCategory.Q.obj (I.obj Q)) :=
    z.representative.hom.app (⟨I.obj P, hpI⟩, ⟨I.obj Q, hqI⟩)
  let ru : DerivedCategory.Q.obj
      ((CoefficientTensorChain.total X A).obj (U.obj (C.obj P), U.obj (C.obj Q))) ⟶
      z.tensor.obj (DerivedCategory.Q.obj (U.obj (C.obj P)),
        DerivedCategory.Q.obj (U.obj (C.obj Q))) :=
    z.representative.hom.app
      (⟨U.obj (C.obj P), hU _ hpC⟩, ⟨U.obj (C.obj Q), hU _ hqC⟩)
  let mc : DerivedCategory.Q.obj (C.obj T) ⟶ DerivedCategory.Q.obj
      ((CoefficientTensorChain.total X S).obj (C.obj P, C.obj Q)) :=
    DerivedCategory.Q.map (proEtaleTensorPullbackTotalIso f R S c P Q).inv
  let mi : DerivedCategory.Q.obj (I.obj T) ⟶ DerivedCategory.Q.obj
      ((CoefficientTensorChain.total X A).obj (I.obj P, I.obj Q)) :=
    DerivedCategory.Q.map (proEtaleTensorPullbackTotalIso f R A (Iso.refl _) P Q).inv
  let dc := Prod.mkHom (eC.app P) (eC.app Q)
  let di := Prod.mkHom (eI.app P) (eI.app Q)
  let du := Prod.mkHom (eU.app (C.obj P)) (eU.app (C.obj Q))
  let db := Prod.mkHom (b.hom.app (DerivedCategory.Q.obj P))
    (b.hom.app (DerivedCategory.Q.obj Q))
  let dt := Prod.mkHom (DerivedCategory.Q.map (beta.app P))
    (DerivedCategory.Q.map (beta.app Q))
  change CD.map r ≫ ac.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
    aX.tensor.map dc = eC.app T ≫ mc ≫ rc at hc
  change ID.map r ≫ ai.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
    z.tensor.map di = eI.app T ≫ mi ≫ ri at hi
  change UD.map rc ≫ gamma.hom.app
    (DerivedCategory.Q.obj (C.obj P), DerivedCategory.Q.obj (C.obj Q)) ≫
    z.tensor.map du = eU.app ((CoefficientTensorChain.total X S).obj (C.obj P, C.obj Q)) ≫
      DerivedCategory.Q.map (sigma.hom.app (C.obj P, C.obj Q)) ≫ ru at hu
  have hb (K : CochainComplex (proEtaleRingModules Y R) ℤ) :
      b.hom.app (DerivedCategory.Q.obj K) ≫ eI.app K =
        UD.map (eC.app K) ≫ eU.app (C.obj K) ≫ DerivedCategory.Q.map (beta.app K) :=
    pullback_factors f R S c K
  have hm : UD.map mc ≫
      eU.app ((CoefficientTensorChain.total X S).obj (C.obj P, C.obj Q)) =
      eU.app (C.obj T) ≫
        DerivedCategory.Q.map (U.map (proEtaleTensorPullbackTotalIso f R S c P Q).inv) :=
    eU.naturality (proEtaleTensorPullbackTotalIso f R S c P Q).inv
  have hpair : db ≫ di = (UD.prod UD).map dc ≫ du ≫ dt :=
    pullback_pair_factors f R S c P Q
  have hrep : ru ≫ z.tensor.map dt =
      DerivedCategory.Q.map ((CoefficientTensorChain.total X A).map
        (Prod.mkHom (beta.app P) (beta.app Q))) ≫ ri := by
    exact tensor_representative_naturality A z (hU _ hpC) (hU _ hqC) hpI hqI
      (beta.app P) (beta.app Q)
  have hchain : DerivedCategory.Q.map (beta.app T) ≫ mi =
      DerivedCategory.Q.map (U.map (proEtaleTensorPullbackTotalIso f R S c P Q).inv) ≫
        DerivedCategory.Q.map (sigma.hom.app (C.obj P, C.obj Q)) ≫
        DerivedCategory.Q.map ((CoefficientTensorChain.total X A).map
          (Prod.mkHom (beta.app P) (beta.app Q))) :=
    CoefficientTensorChain.restriction_tensor_localized_square f R S c o P Q
  have hleft : UD.map (CD.map r) ≫
      left ≫ z.tensor.map di =
      UD.map (eC.app T) ≫ eU.app (C.obj T) ≫
        DerivedCategory.Q.map (beta.app T) ≫ mi ≫ ri := by
    dsimp only [left]
    simp only [Category.assoc]
    erw [reassoc_of% (b.hom.naturality r), hi, reassoc_of% (hb T)]
  have hright : UD.map (CD.map r) ≫
      right ≫ z.tensor.map di =
      UD.map (eC.app T) ≫ eU.app (C.obj T) ≫
        DerivedCategory.Q.map (beta.app T) ≫ mi ≫ ri := by
    exact map_tensor_representative_paste UD aX.tensor z.tensor (UD.prod UD) gamma.hom
      (CD.map r) (ac.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
      (eC.app T) mc rc dc db di du dt (eU.app (C.obj T))
      (eU.app ((CoefficientTensorChain.total X S).obj (C.obj P, C.obj Q)))
      (DerivedCategory.Q.map (U.map (proEtaleTensorPullbackTotalIso f R S c P Q).inv))
      (DerivedCategory.Q.map (sigma.hom.app (C.obj P, C.obj Q))) ru
      (DerivedCategory.Q.map (beta.app T)) mi
      (DerivedCategory.Q.map ((CoefficientTensorChain.total X A).map
        (Prod.mkHom (beta.app P) (beta.app Q)))) ri hc hpair hu hm hrep hchain
  have hdi : IsIso di :=
    show IsIso ((Iso.prod ((proEtaleRingDerivedPullbackFactors f R A (Iso.refl _)).app P)
      ((proEtaleRingDerivedPullbackFactors f R A (Iso.refl _)).app Q)).hom) from inferInstance
  apply (cancel_epi (UD.map (CD.map r))).1
  apply (cancel_mono (z.tensor.map di)).1
  simpa only [Category.assoc] using hleft.trans hright.symm

end AlgebraicGeometry.Scheme.CoefficientTensorTransport
