/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.AlgebraicGeometry.AffinePerfectOpenRepresentCohomology
import WeilConjectures.AlgebraicGeometry.PerfectGenerationAffineBase
import WeilConjectures.AlgebraicGeometry.KoszulSupportedAugmentationVanishing
import Mathlib.CategoryTheory.Localization.HomEquiv

/-! # Koszul powers detect supported objects on an affine scheme

Source: Stacks Project, Derived Categories of Schemes, Tag 09IR, proof via
Lemma 36.9.6 and Tag 06Z0 (blueprint: lem-pc-koszul-affine-detection).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

-- Apply the affine generator criterion in the standard localization, then transport
-- back to the given universe using uniqueness of localization. This avoids asking
-- for new localization instances in the arbitrary universe w on every open.
set_option backward.isDefEq.respectTransparency false in
private theorem affine_unit_detects (A : Type u) [CommRing A]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (E : schemeDerivedQCohCategory (Spec (.of A)))
    (h : ∀ n : ℤ, Subsingleton
      (((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) 0).obj
        (SheafOfModules.unit (moduleRings (Spec (.of A)).toRingedSpace)))⟦n⟧ ⟶ E.obj)) :
    IsZero E.obj := by
  let S := SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)
  let M : S := SheafOfModules.unit (moduleRings (Spec (.of A)).toRingedSpace)
  let Qw : CochainComplex S ℤ ⥤ DerivedCategory S := DerivedCategory.Q
  let K := Qw.objPreimage E.obj
  let eK : Qw.obj K ≅ E.obj := Qw.objObjPreimageIso E.obj
  have hK (n : ℤ) : (K.homology n).IsQuasicoherent := by
    exact (SheafOfModules.isQuasicoherent
      (moduleRings (Spec (.of A)).toRingedSpace)).prop_of_iso
      (((DerivedCategory.homologyFunctorFactors S n).app K).symm ≪≫
        (DerivedCategory.homologyFunctor S n).mapIso eK).symm (E.property n)
  have hsingle (i : ℤ) : Subsingleton
      (Qw.obj ((CochainComplex.singleFunctor S i).obj M) ⟶ Qw.obj K) := by
    have := h (-i)
    let ei := ((DerivedCategory.singleFunctors S).shiftIso (-i) i 0 (by omega)).app M
    exact (Iso.homCongr ei eK.symm).subsingleton_congr.mp (h (-i))
  let := HasDerivedCategory.standard S
  let : ∀ V : (Spec (.of A)).Opens,
      HasDerivedCategory
        (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V)) :=
    fun _ ↦ HasDerivedCategory.standard _
  let Qs : CochainComplex S ℤ ⥤ DerivedCategory S := DerivedCategory.Q
  let Es : schemeDerivedQCohCategory (Spec (.of A)) := ⟨Qs.obj K, fun n ↦
    (SheafOfModules.isQuasicoherent
      (moduleRings (Spec (.of A)).toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctorFactors S n).app K).symm (hK n)⟩
  have hs : IsZero Es.obj := by
    apply ((perfectGeneration_affine_base (Spec (.of A))).2.2 Es).mpr
    intro n
    let ei := ((DerivedCategory.singleFunctors S).shiftIso n (-n) 0 (by omega)).app M
    have : Subsingleton (Qs.obj ((CochainComplex.singleFunctor S (-n)).obj M) ⟶ Qs.obj K) :=
      (Localization.homEquiv (HomologicalComplex.quasiIso S (.up ℤ)) Qs Qw).subsingleton_congr.mpr
        (hsingle (-n))
    exact (Iso.homCongr ei (Iso.refl (Qs.obj K))).subsingleton_congr.mpr this
  let e := Localization.uniq Qs Qw (HomologicalComplex.quasiIso S (.up ℤ))
  let : PreservesLimit (Functor.empty _) e.functor :=
    e.symm.toAdjunction.rightAdjoint_preservesLimits.preservesLimitsOfShape.preservesLimit
  let : e.functor.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  exact (e.functor.map_isZero hs).of_iso
    (((Localization.compUniqFunctor Qs Qw
      (HomologicalComplex.quasiIso S (.up ℤ))).app K) ≪≫ eK).symm

-- Only the triangle clause of represent-cohomology is used here. Obtain it in the
-- standard localization and transport its three objects and maps back along the
-- triangulated equivalence induced by the identity on the homotopy category.
set_option backward.isDefEq.respectTransparency false in
private theorem koszul_triangles (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (E : schemeDerivedQCohCategory (Spec (.of A))) (a : ℕ) :
    ∃ δ : koszulOpenKoszulObject A r f a ⟶ (koszulOpenObject A r f a)⟦(1 : ℤ)⟧,
      Pretriangulated.Triangle.mk (koszulOpenUnit A r f a)
        (koszulOpenKoszulUnit A r f a) δ ∈
          distTriang (schemeDerivedCategory (Spec (.of A))) := by
  let S := SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)
  let Qw : CochainComplex S ℤ ⥤ DerivedCategory S := DerivedCategory.Q
  let uw := koszulOpenUnit A r f a
  let vw := koszulOpenKoszulUnit A r f a
  let Hw : HomotopyCategory S (.up ℤ) ⥤ DerivedCategory S := DerivedCategory.Qh
  let cw := DerivedCategory.quotientCompQhIso S
  have : ∀ n : ℤ, (shiftFunctor (DerivedCategory S) n).Additive := fun _ ↦ inferInstance
  let K := Qw.objPreimage E.obj
  let eK : Qw.obj K ≅ E.obj := Qw.objObjPreimageIso E.obj
  have hK (n : ℤ) : (K.homology n).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent
      (moduleRings (Spec (.of A)).toRingedSpace)).prop_of_iso
      (((DerivedCategory.homologyFunctorFactors S n).app K).symm ≪≫
        (DerivedCategory.homologyFunctor S n).mapIso eK).symm (E.property n)
  let := HasDerivedCategory.standard S
  let : ∀ V : (Spec (.of A)).Opens,
      HasDerivedCategory
        (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V)) :=
    fun _ ↦ HasDerivedCategory.standard _
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
  let Qs : CochainComplex S ℤ ⥤ DerivedCategory S := DerivedCategory.Q
  let Hs : HomotopyCategory S (.up ℤ) ⥤ DerivedCategory S := DerivedCategory.Qh
  let Es : schemeDerivedQCohCategory (Spec (.of A)) := ⟨Qs.obj K, fun n ↦
    (SheafOfModules.isQuasicoherent
      (moduleRings (Spec (.of A)).toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctorFactors S n).app K).symm (hK n)⟩
  obtain ⟨δs, hTs⟩ := (affine_perfect_open_represent_cohomology A r f Es).1 a
  let W := (HomotopyCategory.subcategoryAcyclic S).trW
  let G := (Localization.uniq Hs Hw W).functor
  let := Functor.commShiftOfLocalization Hs W ℤ Hw G
  have : G.IsTriangulated := Functor.isTriangulated_of_precomp_iso
    (Localization.Lifting.iso Hs W Hw G)
  let c : Qs ⋙ G ≅ Qw :=
    Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso S).symm G ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Localization.Lifting.iso Hs W Hw G) ≪≫
      cw
  let Ts := Pretriangulated.Triangle.mk (koszulOpenUnit A r f a)
    (koszulOpenKoszulUnit A r f a) δs
  let T := G.mapTriangle.obj Ts
  have hT := G.map_distinguished Ts hTs
  let ci := c.app (koszulOpenSheafComplex A r f a)
  let co := c.app (((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).obj
    (((ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A)).extend
      ComplexShape.embeddingDownNat))
  let ck := c.app (((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).obj
    ((ExteriorAlgebra.koszulComplex A r (fun i ↦ f i ^ (a + 1))).extend
      ComplexShape.embeddingDownNat))
  let δ := ck.inv ≫ T.mor₃ ≫ ci.hom⟦(1 : ℤ)⟧'
  let Tw := Pretriangulated.Triangle.mk uw vw δ
  refine ⟨δ, ?_⟩
  change Tw ∈ distTriang _
  apply Pretriangulated.isomorphic_distinguished _ hT _
  refine (Pretriangulated.Triangle.isoMk T Tw ci co ck ?_ ?_ ?_).symm
  · exact c.hom.naturality _
  · exact c.hom.naturality _
  · change T.mor₃ ≫ ci.hom⟦(1 : ℤ)⟧' = ck.hom ≫ δ
    simp only [δ, Iso.hom_inv_id_assoc]


set_option backward.isDefEq.respectTransparency false in
/-- Koszul powers detect an object of `D_QCoh` supported on the common zero locus.
The Koszul complexes are sheafified termwise and placed in nonpositive cochain degrees;
they are the bounded finite-free, hence perfect, complexes of Stacks Tag 09IR.
Source: Stacks Project, Tag 09IR (blueprint: lem-pc-koszul-affine-detection).

Proof:
1. For each map from a shift of the structure object to E, restriction to U is zero.
   The filtered-colimit comparison for the Koszul tail system makes this map zero
   after precomposition with some shifted augmentation. This is the separate
   eventual-vanishing assertion, with no Koszul orthogonality assumption.
2. Extract the triangles I_e → O_X → K_e from represent-cohomology. Shift the
   triangle by n. Exactness of Hom(-,E) factors the map killed by I_e[n] → O_X[n]
   through K_e[n]. The diagonal positive exponent tuple e+1 gives a subsingleton
   Hom(K_e[n],E), so the factor and the original map are zero. The natural identity
   comparison of the two termwise tilde functors identifies K_e with the complex
   in the hypothesis.
3. The extended degree-zero free module sheafifies to the structure sheaf. Thus all
   maps from its shifts to E vanish. The affine generator criterion detects E = 0.
   Both this criterion and the triangle extraction are applied in standard
   localizations and transported back to the given localization universe, so no
   extra localization assumptions are added. -/
theorem isZero_of_koszul_powers_orthogonal
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (U : (Spec (.of A)).Opens)
    (hU : U = ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))]
    (E : schemeDerivedQCohCategory (Spec (.of A)))
    (hres : IsZero ((SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory.obj E.obj))
    (horth : ∀ (e : Fin r → ℕ), (∀ i, 0 < e i) → ∀ n : ℤ,
      Subsingleton
        (((DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            _ _ _ _ (tilde.functor (.of A))
            ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
            ((ExteriorAlgebra.koszulComplex A r (fun i ↦ f i ^ e i)).extend
              ComplexShape.embeddingDownNat)))⟦n⟧) ⟶ E.obj)) :
    IsZero E.obj := by
  let S := SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)
  let M := ModuleCat.of A A
  let T := (koszulOpenTilde A).mapHomologicalComplex (ComplexShape.up ℤ)
  let unitIso : koszulOpenStructure A ≅
      (DerivedCategory.singleFunctor S 0).obj
        (SheafOfModules.unit (moduleRings (Spec (.of A)).toRingedSpace)) :=
    DerivedCategory.Q.mapIso (T.mapIso
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat M 0 0 (by rfl))) ≪≫
      DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex
          (koszulOpenTilde A) (.up ℤ) 0).app M) ≪≫
      (DerivedCategory.singleFunctor S 0).mapIso (tildeSelf (R := .of A))
  apply affine_unit_detects A E
  intro n
  have hz : ∀ φ : (koszulOpenStructure A)⟦n⟧ ⟶ E.obj, φ = 0 := by
    intro φ
    obtain ⟨e, he⟩ := koszul_supported_augmentation_eventually_zero A r f U hU E hres n φ
    obtain ⟨δ, hT⟩ := koszul_triangles A r f E e
    let tri := Pretriangulated.Triangle.mk (koszulOpenUnit A r f e)
      (koszulOpenKoszulUnit A r f e) δ
    let shifted := (shiftFunctor (Pretriangulated.Triangle (schemeDerivedCategory
      (Spec (.of A)))) n).obj tri
    have he' : shifted.mor₁ ≫ φ = 0 := by
      change (n.negOnePow • (koszulOpenUnit A r f e)⟦n⟧') ≫ φ = 0
      simp only [Linear.units_smul_comp, he, smul_zero]
    obtain ⟨ψ, hψ⟩ := shifted.yoneda_exact₂ (tri.shift_distinguished hT n) φ he'
    let F : ModuleCat.{u} A ⥤ S := tilde.functor (.of A)
    let : F.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
    let t : koszulOpenTilde A ≅ F := NatIso.ofComponents
      (fun _ ↦ Iso.refl _) (by intros; simp [koszulOpenTilde, F])
    let kiso := DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex t (.up ℤ)).app
      ((ExteriorAlgebra.koszulComplex A r (fun i ↦ f i ^ (e + 1))).extend
        ComplexShape.embeddingDownNat))
    have hsub : Subsingleton ((koszulOpenKoszulObject A r f e)⟦n⟧ ⟶ E.obj) :=
      (Iso.homCongr ((shiftFunctor _ n).mapIso kiso) (Iso.refl E.obj)).subsingleton_congr.mpr
        (horth (fun _ ↦ e + 1) (fun _ ↦ Nat.zero_lt_succ e) n)
    have hψzero : ψ = 0 := @Subsingleton.elim
      ((koszulOpenKoszulObject A r f e)⟦n⟧ ⟶ E.obj) hsub ψ 0
    rw [hψ, hψzero, comp_zero]
  have : Subsingleton ((koszulOpenStructure A)⟦n⟧ ⟶ E.obj) :=
    ⟨fun φ ψ ↦ (hz φ).trans (hz ψ).symm⟩
  exact (Iso.homCongr ((shiftFunctor _ n).mapIso unitIso) (Iso.refl E.obj)).symm.subsingleton

end AlgebraicGeometry
