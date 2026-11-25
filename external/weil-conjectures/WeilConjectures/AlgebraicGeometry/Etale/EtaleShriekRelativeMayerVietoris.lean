/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.Etale.EtaleShriekQcqsComposition
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenCoverShriekTriangle

/-!
# Relative Mayer--Vietoris for etale compact support

Source: Stacks Project, more-etale.tex, Tag 0GKN, lemma-relative-mayer-vietoris,
finite-ring bounded-below specialization
(blueprint: lem-weil-pbc-etale-shriek-relative-mayer-vietoris).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Etale

/-- Relative Mayer--Vietoris for any chosen compactifications.
Source: Stacks Project, Tag 0GKN, lemma-relative-mayer-vietoris.
(blueprint: lem-weil-pbc-etale-shriek-relative-mayer-vietoris).

Proof:
1. Compact opens in a quasi-separated scheme have compact intersection. The open
   subschemes inherit quasi-separatedness. Thus the qcqs shriek-composition
   theorem applies to each of the three open inclusions followed by f.
2. For an open inclusion T.ι, use its compactification with proper part the
   identity. The derived identity-pushforward comparison identifies its shriek
   with the exact extension-by-zero functor on D⁺. Composition then identifies
   extension by zero followed by the candidate for cX with the candidate for cT.
3. Apply the existing triangulated functor associated to cX to the absolute
   open-cover extension-by-zero triangle. Additivity identifies the middle
   biproduct. Transport its vertices through the three composition isomorphisms,
   and its last arrow through the shifted intersection isomorphism. The resulting
   triangle is isomorphic to a distinguished triangle, hence distinguished.
-/
theorem exists_distinguished_relativeMayerVietoris
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    (hcover : U ⊔ V = ⊤)
    (cU : Compactification (U.ι ≫ f)) (cV : Compactification (V.ι ≫ f))
    (cW : Compactification ((U ⊓ V).ι ≫ f)) (cX : Compactification f)
    (K : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃ (α : (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cW).obj
        (((upperStar (ModuleCat.{u + 1} Λ) (U ⊓ V).ι).mapDerivedCategoryPlus).obj K) ⟶
      ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cU).obj
        (((upperStar (ModuleCat.{u + 1} Λ) U.ι).mapDerivedCategoryPlus).obj K) ⊞
      (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cV).obj
        (((upperStar (ModuleCat.{u + 1} Λ) V.ι).mapDerivedCategoryPlus).obj K)))
      (β : ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cU).obj
        (((upperStar (ModuleCat.{u + 1} Λ) U.ι).mapDerivedCategoryPlus).obj K) ⊞
      (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cV).obj
        (((upperStar (ModuleCat.{u + 1} Λ) V.ι).mapDerivedCategoryPlus).obj K)) ⟶
        (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cX).obj K)
      (δ : (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cX).obj K ⟶
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cW).obj
        (((upperStar (ModuleCat.{u + 1} Λ) (U ⊓ V).ι).mapDerivedCategoryPlus).obj K))⟦(1 : ℤ)⟧),
      Triangle.mk α β δ ∈ distTriang
        (_root_.DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) := by
  have hW : IsCompact ((U ⊓ V : X.Opens) : Set X) :=
    hU.inter_of_isOpen hV U.isOpen V.isOpen
  let F := rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cX
  have : F.Additive := inferInstance
  have : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  have hcomp (T : X.Opens) (hT : IsCompact (T : Set X))
      (cT : Compactification (T.ι ≫ f)) :
      Nonempty
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) T.ι).mapDerivedCategoryPlus ⋙ F ≅
          rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cT) := by
    have : CompactSpace T := isCompact_iff_compactSpace.mp hT
    have : QuasiSeparatedSpace T := T.ι.isOpenEmbedding.quasiSeparatedSpace
    obtain ⟨e⟩ := nonempty_iso_etaleShriek_qcqs_compactification_comp
      Λ T.ι f (Compactification.ofIsOpenImmersion T.ι) cX cT
    let eid := Functor.rightDerivedFunctorPlusNatIso
      (lowerStarId (ModuleCat.{u + 1} Λ) X) ≪≫
      Functor.rightDerivedFunctorPlusIdIso _
    let eopen :
        rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ)
          (Compactification.ofIsOpenImmersion T.ι) ≅
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) T.ι).mapDerivedCategoryPlus :=
      Functor.isoWhiskerLeft _ eid ≪≫ Functor.rightUnitor _
    exact ⟨Functor.isoWhiskerRight eopen.symm F ≪≫ e⟩
  obtain ⟨eU⟩ := hcomp U hU cU
  obtain ⟨eV⟩ := hcomp V hV cV
  obtain ⟨eW⟩ := hcomp (U ⊓ V) hW cW
  obtain ⟨α, β, δ, hdist⟩ := exists_distinguished_openCover_lowerShriek Λ U V hcover K
  let T := F.mapTriangle.obj (Triangle.mk α β δ)
  have hT : T ∈ distTriang _ := F.map_distinguished _ hdist
  let iW := eW.app
    (((upperStar (ModuleCat.{u + 1} Λ) (U ⊓ V).ι).mapDerivedCategoryPlus).obj K)
  let iB := F.mapBiprod
    ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) U.ι).mapDerivedCategoryPlus.obj
      (((upperStar (ModuleCat.{u + 1} Λ) U.ι).mapDerivedCategoryPlus).obj K))
    ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) V.ι).mapDerivedCategoryPlus.obj
      (((upperStar (ModuleCat.{u + 1} Λ) V.ι).mapDerivedCategoryPlus).obj K)) ≪≫ biprod.mapIso
    (eU.app (((upperStar (ModuleCat.{u + 1} Λ) U.ι).mapDerivedCategoryPlus).obj K))
    (eV.app (((upperStar (ModuleCat.{u + 1} Λ) V.ι).mapDerivedCategoryPlus).obj K))
  refine ⟨iW.inv ≫ T.mor₁ ≫ iB.hom, iB.inv ≫ T.mor₂,
    T.mor₃ ≫ (shiftFunctor _ (1 : ℤ)).map iW.hom, ?_⟩
  apply isomorphic_distinguished T hT
  refine (Triangle.isoMk T (Triangle.mk _ _ _) iW iB (Iso.refl _) ?_ ?_ ?_).symm
  · simp
  · simp
  · simp

end AlgebraicGeometry.Etale
