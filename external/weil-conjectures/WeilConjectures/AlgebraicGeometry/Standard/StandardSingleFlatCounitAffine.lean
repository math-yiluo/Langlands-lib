/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleFlatCounitPresentation
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
import WeilConjectures.AlgebraicGeometry.AffineFlatModuleTensorFlat
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility
import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSingleDirectImageComparison
import all WeilConjectures.AlgebraicGeometry.Picard.Termwise.PicardTermwiseSingleMapComposition
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechAcyclic
import WeilConjectures.AlgebraicGeometry.Cohomology.Exact
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Cohomology.InjectiveFlasque
import WeilConjectures.Topology.Sheaves.CechFlasque
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChangeIsIso
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed

/-! # Affine case of flat counit presentations

Source: Stacks Project, Tags 0A1D and 0DJ9.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry

-- Affine preimages let relative flatness control every section of the direct image.
-- Intrinsic affine-local flatness then gives exactness of tensoring with that image.
private theorem affine_pushforward_isFlat
    {X B : Scheme.{u}} (f : X ⟶ B) [IsAffineHom f]
    (N : X.Modules) (hN : N.IsFlatOver f) :
    SheafOfModules.IsFlat ((Scheme.Modules.pushforward f).obj N) := by
  apply isFlat_of_affineFlatOver_identity
  intro V W e
  have hWV : W.1 ≤ V.1 := by simpa using e
  have hpre : f ⁻¹ᵁ W.1 ≤ f ⁻¹ᵁ V.1 := f.preimage_mono hWV
  have hflat := hN V ⟨f ⁻¹ᵁ W.1, W.2.preimage f⟩ hpre
  convert hflat using 1 <;> try rfl
  ext r m
  change (N.smul ((f.app W.1).hom ((B.presheaf.map (homOfLE hWV).op).hom r))).asHom.hom m =
    (N.smul ((f.appLE V.1 (f ⁻¹ᵁ W.1) hpre).hom r)).asHom.hom m
  have heq : B.presheaf.map (homOfLE hWV).op ≫ f.app W.1 =
      f.appLE V.1 (f ⁻¹ᵁ W.1) hpre := by
    rw [f.app_eq_appLE, f.map_appLE]
  exact congrArg (fun a ↦ (N.smul a).asHom.hom m) (ConcreteCategory.congr_hom heq r)

namespace Scheme.Modules

-- Use the lower Cech dimension-shifting tools. The affine finiteness module
-- reaches this item through FiniteFreeComplex and cannot be imported here.
private theorem injective_cech_acyclic {Y : Scheme.{u}} (I : Y.Modules) [Injective I] :
    cechAcyclicOnAffines Y ((toAb Y).obj I) :=
  have := isFlasque_of_injective I
  fun _ _ _ _ _ q ↦ TopCat.Sheaf.exactAt_cechComplex_of_isFlasque _ q _

private theorem cokernel_cech_acyclic {Y : Scheme.{u}} {Q : ShortComplex Y.Modules}
    (hQ : Q.ShortExact) (h₁ : cechAcyclicOnAffines Y ((toAb Y).obj Q.X₁))
    (h₂ : cechAcyclicOnAffines Y ((toAb Y).obj Q.X₂)) :
    cechAcyclicOnAffines Y ((toAb Y).obj Q.X₃) :=
  cechAcyclicOnAffines_X₃ (S := Q.map (toAb Y)) (hQ.map_of_exact (toAb Y)) h₁ h₂

private theorem affine_pushforward_epi {Y S : Scheme.{u}} (h : Y ⟶ S)
    [IsAffineHom h] {Q : ShortComplex Y.Modules} (hQ : Q.ShortExact)
    (h₁ : cechAcyclicOnAffines Y ((toAb Y).obj Q.X₁)) :
    Epi ((Modules.pushforward h).map Q.g) := by
  refine epi_of_forall_exists_app_eq _ fun W y x hx ↦ ?_
  obtain ⟨V, hV, hxV, hVW⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens hx
  obtain ⟨z, hz⟩ := surjective_app_of_cechAcyclicOnAffines
    (hQ.map_of_exact (toAb Y)) h₁ (IsAffineOpen.preimage hV h)
    (Q.X₃.presheaf.map (homOfLE (h.preimage_mono hVW)).op y)
  exact ⟨V, hVW, hxV, z, hz⟩

private theorem affine_pushforward_rightAcyclic {Y S : Scheme.{u}} (h : Y ⟶ S)
    [IsAffineHom h] [HasInjectiveResolutions Y.Modules] (M : Y.Modules)
    [SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) M] :
    (Modules.pushforward h).rightAcyclic M := by
  have : PreservesFiniteLimits (Modules.pushforward h) :=
    have := (Modules.pullbackPushforwardAdjunction h).rightAdjoint_preservesLimits.{0, 0}
    inferInstance
  exact Functor.rightAcyclic_of_epi_map_g (Modules.pushforward h)
    (fun N ↦ cechAcyclicOnAffines Y ((toAb Y).obj N))
    (fun I _ ↦ injective_cech_acyclic I)
    (fun _ hQ h₁ h₂ ↦ cokernel_cech_acyclic hQ h₁ h₂)
    (fun _ hQ h₁ ↦ affine_pushforward_epi h hQ h₁)
    (cechAcyclicOnAffines_of_isQuasicoherent M)

end Scheme.Modules

private theorem affine_single_unit_iso
    [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X B : Scheme.{u}} (f : X ⟶ B) [IsAffineHom f]
    (N : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [N.IsQuasicoherent] :
    IsIso ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj N))) := by
  let r := (HomologicalComplex.singleMapHomologicalComplex
    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) (.up ℤ) 0).inv.app N
  have := Scheme.Modules.isGrothendieckAbelian X
  have hA := Scheme.Modules.affine_pushforward_rightAcyclic f N
  have hi := Scheme.Modules.isIso_canonicalSingleDirectImageMap f N (fun q hq ↦ by
    obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
    exact hA n)
  dsimp only [Scheme.Modules.canonicalSingleDirectImageMap] at hi
  have : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map r) ≫
      (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          ((CochainComplex.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj N))) := by
    simpa only [r, cast_eq, Scheme.Modules, Scheme.ringCatSheaf,
      DerivedCategory.singleFunctor, DerivedCategory.singleFunctors,
      HomotopyCategory.singleFunctor, HomotopyCategory.singleFunctors,
      SingleFunctors.postcomp, Functor.comp_obj] using hi
  exact IsIso.of_isIso_comp_left
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map r)) _

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
/-- The single complex of the actual affine direct image realizes the pinned comparison.
Source: Stacks Project, Tag 0A1D, affine tensor calculation; Tag 08HY,
base-change mate; Tag 0DJ9, initial affine case.

Proof: Put F = f_*N, and K = F[0]. Affine higher direct image vanishing makes
N acyclic for f_*, so the canonical right-derived unit on N[0], composed with
the single-complex comparison, is invertible. Its inverse gives e. The base
change f' is affine and g'^*N is quasi-coherent, so the same right-derived unit
there is invertible. Ordinary affine base change identifies g^*F with
f'_*g'^*N by the map sending b tensor n to b times the pulled-back section n.
Apply the single functor to that isomorphism, the canonical isomorphism between
termwise pullback of a single complex and the single of the pullback, and the
right-derived unit for f' to obtain t. To check the equation, transpose the
derived base-change mate under the g'^* / Rg'_* adjunction. Naturality of the
right-derived units and the two adjunction triangle identities reduce both
sides to the ordinary affine exchange map followed by the single pullback
counit. On affine sections this is the displayed pure-tensor formula; it is
natural in restriction and balanced over the base ring. Transport through the
canonical spectrum isomorphisms using the derived composition counit equations.
No flatness is needed: the pullback counit is retained, never inverted. This also
covers empty affines and the zero module. -/
private theorem affine_single_counit_comparison
    {X B A : Scheme.{u}} [IsAffine X] [IsAffine B] [IsAffine A]
    (f : X ⟶ B) (g : A ⟶ B)
    (N : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [N.IsQuasicoherent] :
    let := fun Z : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))
    let := HasDerivedCategory.standard A.Modules
    let := HasDerivedCategory.standard B.Modules
    let K := (CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings B.toRingedSpace)) (0 : ℤ)).obj
      ((Scheme.Modules.pushforward f).obj N)
    ∃ (e : (schemeDerivedDirectImage.{u, u + 1, u + 1} f).obj
        ((DerivedCategory.singleFunctor.{u + 1} _ 0).obj N) ≅
          DerivedCategory.Qh.{u + 1}.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj K))
      (t : DerivedCategory.Qh.{u + 1}.obj
          (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) ≅
        (schemeDerivedDirectImage.{u, u + 1, u + 1} (pullback.snd f g)).obj
          ((DerivedCategory.singleFunctor.{u + 1} _ 0).obj
            (Scheme.Modules.tensorPullbackObj (pullback.fst f g) N))),
      standardSingleBaseChangeMap f N g =
        (derivedPullback.{u, u + 1} g).map e.hom ≫
          (SingleComplexBaseChange.counit g).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj K) ≫ t.hom  := by
  classical
  let := fun Z : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings Z.toRingedSpace))
  let := HasDerivedCategory.standard A.Modules
  let := HasDerivedCategory.standard B.Modules
  let : HasDerivedCategory.{u + 1} (pullback f g).Modules := inferInstanceAs
    (HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)))
  let f' := pullback.snd f g
  let p := pullback.fst f g
  let F := Scheme.Modules.pushforward f
  let F' := Scheme.Modules.pushforward f'
  let G := Scheme.Modules.tensorPullback g
  let P := Scheme.Modules.tensorPullback p
  let C := (CochainComplex.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (0 : ℤ)).obj N
  let D := (HomotopyCategory.quotient _ (.up ℤ)).obj C
  let K := (CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings B.toRingedSpace)) (0 : ℤ)).obj (F.obj N)
  let ρ : (HomotopyCategory.quotient _ (.up ℤ)).obj K ≅
      (F.mapHomotopyCategory (.up ℤ)).obj D :=
    (HomotopyCategory.quotient _ (.up ℤ)).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app N).symm
  let σ : (P.mapHomotopyCategory (.up ℤ)).obj D ≅
      (HomotopyCategory.quotient _ (.up ℤ)).obj
        ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) (0 : ℤ)).obj
            (P.obj N)) :=
    (HomotopyCategory.quotient _ (.up ℤ)).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex P (.up ℤ) 0).app N)
  let β := Functor.rightDerivedFunctorUnit.{_, _, _, _, u + 1, u + 1}
    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom)
  let β' := Functor.rightDerivedFunctorUnit.{_, _, _, _, u + 1, u + 1}
    (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom)
  have hβ : IsIso (β.app D) := affine_single_unit_iso f N
  have : (P.obj N).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (pullback f g).ringCatSheaf).prop_of_iso
      (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction p)).leftAdjointUniq
        (Scheme.Modules.pullbackPushforwardAdjunction p)).app N).symm
      (Scheme.Modules.isQuasicoherent_pullback p N)
  have hβs : IsIso (β'.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
      ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) (0 : ℤ)).obj
            (P.obj N)))) := by
    exact affine_single_unit_iso f' (P.obj N)
  have hβ' : IsIso (β'.app ((P.mapHomotopyCategory (.up ℤ)).obj D)) := by
    exact (NatTrans.isIso_app_iff_of_iso β' σ).mpr hβs
  let e := (DerivedCategory.Qh.{u + 1}.mapIso ρ ≪≫ asIso (β.app D)).symm
  let x := (moduleHomotopyBaseChange f f' g p pullback.condition).app D
  have hx : IsIso x := by
    let α : F ⋙ G ⟶ P ⋙ F' :=
      { app := Scheme.Modules.moduleBaseChangeMap f f' g p pullback.condition
        naturality := fun _ _ a ↦ Scheme.Modules.moduleBaseChangeMap_naturality
          f f' g p pullback.condition a }
    have hα (i : ℤ) : IsIso (α.app (C.X i)) := by
      by_cases hi : i = 0
      · subst i
        have : IsIso (α.app N) := Scheme.Modules.affinePushforward_baseChange_isIso
          f f' g p (IsPullback.of_hasPullback f g) N
        exact (NatTrans.isIso_app_iff_of_iso α
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N)).mpr this
      · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 N i hi
        exact (Functor.map_isZero (F ⋙ G) hz).isIso (Functor.map_isZero (P ⋙ F') hz) _
    have (i : ℤ) : IsIso (((NatTrans.mapHomologicalComplex α (.up ℤ)).app C).f i) := hα i
    have : IsIso ((NatTrans.mapHomologicalComplex α (.up ℤ)).app C) :=
      HomologicalComplex.Hom.isIso_of_components _
    have : IsIso ((NatTrans.mapHomotopyCategory α (.up ℤ)).app D) := by
      change IsIso ((HomotopyCategory.quotient _ (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex α (.up ℤ)).app C))
      infer_instance
    dsimp only [x, moduleHomotopyBaseChange, NatTrans.comp_app]
    infer_instance
  let t := DerivedCategory.Qh.{u + 1}.mapIso
      ((G.mapHomotopyCategory (.up ℤ)).mapIso ρ) ≪≫
    DerivedCategory.Qh.{u + 1}.mapIso (asIso x) ≪≫ asIso (β'.app _) ≪≫
      (schemeDerivedDirectImage.{u, u + 1, u + 1} f').mapIso (DerivedCategory.Qh.{u + 1}.mapIso σ)
  refine ⟨e, t, ?_⟩
  let εp := (SingleComplexBaseChange.counit p)
  have hp : Scheme.picardTermwiseSingleMap p N =
      εp.app D ≫ DerivedCategory.Qh.{u + 1}.map σ.hom := by
    exact Scheme.single_map_normalize p N
  have hc := derivedBaseChange_unit_compatibility.{u, u + 1} f f' g p pullback.condition D
  let εg := SingleComplexBaseChange.counit g
  have heq : (derivedPullback.{u, u + 1} g).map e.inv ≫ standardSingleBaseChangeMap f N g =
      εg.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K) ≫ t.hom := by
    calc
      _ = (derivedPullback.{u, u + 1} g).map (DerivedCategory.Qh.{u + 1}.map ρ.hom) ≫
          ((derivedPullback.{u, u + 1} g).map (β.app D) ≫
            schemeDerivedBaseChangeMap f f' g p pullback.condition
              (DerivedCategory.Qh.{u + 1}.obj D) ≫
            (schemeDerivedDirectImage.{u, u + 1, u + 1} f').map (εp.app D)) ≫
          (schemeDerivedDirectImage.{u, u + 1, u + 1} f').map
            (DerivedCategory.Qh.{u + 1}.map σ.hom) := by
        change (derivedPullback.{u, u + 1} g).map e.inv ≫
          (schemeDerivedBaseChangeMap f f' g p pullback.condition
              (DerivedCategory.Qh.{u + 1}.obj D) ≫
            (schemeDerivedDirectImage.{u, u + 1, u + 1} f').map
              (Scheme.picardTermwiseSingleMap p N)) = _
        rw [hp]
        simp only [e, Iso.symm_inv, Iso.trans_hom, Functor.mapIso_hom,
          asIso_hom, Functor.map_comp, Category.assoc]
      _ = (derivedPullback.{u, u + 1} g).map (DerivedCategory.Qh.{u + 1}.map ρ.hom) ≫
          (εg.app ((F.mapHomotopyCategory (.up ℤ)).obj D) ≫
            DerivedCategory.Qh.{u + 1}.map x ≫ β'.app ((P.mapHomotopyCategory (.up ℤ)).obj D)) ≫
          (schemeDerivedDirectImage.{u, u + 1, u + 1} f').map
            (DerivedCategory.Qh.{u + 1}.map σ.hom) := by
        exact congrArg (fun a ↦
          (derivedPullback.{u, u + 1} g).map (DerivedCategory.Qh.{u + 1}.map ρ.hom) ≫
            a ≫ (schemeDerivedDirectImage.{u, u + 1, u + 1} f').map
              (DerivedCategory.Qh.{u + 1}.map σ.hom)) hc
      _ = _ := by
        have hn := εg.naturality ρ.hom
        dsimp only [Functor.comp_map] at hn
        dsimp only [t, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
        simp only [Category.assoc]
        erw [reassoc_of% hn]
  exact ((derivedPullback.{u, u + 1} g).mapIso e.symm).eq_inv_comp.mpr heq

/-- Affine source charts have bounded flat presentations over affine bases.
Source: Stacks Project, Tag 0A1D, affine tensor calculation; Tag 0DJ9,
initial affine case. (blueprint: lem-pc-standard-single-flat-counit-affine).

Proof: Identify the three affine schemes U, B and A with spectra of their section
rings. The one-member affine cover of U has alternating section complex N(U) in
degree zero and zero in all other degrees. Relative flatness evaluated on the
top opens makes N(U) flat over the section ring of B. Sheafify this module on B;
its stalks are localizations, so it is a flat sheaf, and take its single complex K.
Affine direct image of a quasi-coherent module is acyclic; the augmentation gives
e identifying Rp_*N[0] with QK. On the pulled-back affine chart the pure-tensor
section formula identifies ordinary g-pullback of K with the target, giving t.
The formula sends b tensor n to b times the pulled-back section n and commutes
with the augmentation. Transpose the canonical mate under the derived adjunction
for the source pullback. Naturality and the two triangle identities cancel its
units and leave that pure-tensor section map. Thus its composite with the pinned
single pullback counit is Lg*(e) followed by the pinned counit at K and t.
Transport along the affine-spectrum isomorphisms using the derived composition
comparisons; their defining counit equations preserve this equality. Bound K by
zero. If U is empty its section ring is zero and the same single complex is zero.
No flatness of g or invertibility of a counit is assumed. -/
theorem standardSingleFlatCounitOnOpen_affine
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [IsAffine B] [IsAffine A]
    (g : A ⟶ B) (U : Y.Opens) (hU : IsAffineOpen U) :
    StandardSingleFlatCounitOnOpen p g U := by
  intro N _ hN
  let : IsAffine U.toScheme := hU
  let F := (Scheme.Modules.pushforward (U.ι ≫ p)).obj N
  let K := (CochainComplex.singleFunctor B.Modules (0 : ℤ)).obj F
  have hF : SheafOfModules.IsFlat F := affine_pushforward_isFlat (U.ι ≫ p) N hN
  refine ⟨K, ⟨0, fun i hi ↦ ?_⟩, ?_, ?_⟩
  · exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  · let := SheafOfModules.monoidalCategory B.sheaf
    obtain ⟨⟨hpreadd⟩, _⟩ := SheafOfModules.tensorClosed B.sheaf
    let := hpreadd
    intro i
    by_cases hi : i = 0
    · subst i
      exact (exactFunctor _ _).prop_of_iso
        ((MonoidalCategory.curriedTensor
          (SheafOfModules.{u} (moduleRings B.toRingedSpace))).flip.mapIso
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).symm) hF
    · exact (ObjectProperty.flat_of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)).2
  · exact affine_single_counit_comparison (U.ι ≫ p) g N

end AlgebraicGeometry
