/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomPullbackComparison
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
public import WeilConjectures.AlgebraicGeometry.MixedGlobalExtension
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import all WeilConjectures.AlgebraicGeometry.AffineMorphismHomOutOfPerfect
import WeilConjectures.AlgebraicGeometry.FlatPullbackTorIndependent
import WeilConjectures.AlgebraicGeometry.MixedAffineSectionsBaseChangeMate
import WeilConjectures.AlgebraicGeometry.MixedPerfectInternalHomPullbackIsIso
import WeilConjectures.AlgebraicGeometry.PerfectRHomTensorComparison
import WeilConjectures.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherentPerfectPart

/-! # Scalar-extension comparison for global Hom over arbitrary affine bases
Source: Stacks Project, perfect.tex, Tag 0AA7.
(blueprint: lem-sc-flat-affine-global-hom-comparison).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w wA
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
noncomputable section
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

/-- Evaluation-mate pullback followed by normalized Leray.
Source: Stacks Tags 08I3 and 0B6A. -/
def mixedGlobalHomPullbackComparison
    {S T : Scheme.{u}} (h : T ⟶ S) (P Q : schemeDerivedCategory S) :
    (schemeGlobalDerivedHom S).obj (op P, Q) ⟶
      (schemeGlobalScalarRestriction h).obj
        ((schemeGlobalDerivedHom T).obj
          (op ((derivedPullback h).obj P), (derivedPullback h).obj Q)) :=
  (schemeDerivedGlobalSections S).map
      ((schemeHomPullbackAdjunction h).homEquiv _ _
        (((schemeDerivedTensorHomEquiv T)
          ((derivedPullback h).obj
            ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q)))
          ((derivedPullback h).obj P) ((derivedPullback h).obj Q)).symm
            ((mixedHomTensorPullbackIso h).inv.app
              ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q), P) ≫
              (derivedPullback h).map
                ((schemeDerivedTensorHomEquiv S)
                  ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q))
                  P Q (𝟙 _))))) ≫
    (mixedGlobalSectionsDirectImageIso h).hom.app
      ((derivedInternalHom (Opens.grothendieckTopology T) T.sheaf).obj
        (op ((derivedPullback h).obj P), (derivedPullback h).obj Q))

/-- Transpose the restricted pullback comparison under derived scalar extension.
The scalar-square iso gives its target the Y'-global-ring action.
Source: Stacks Tag 0AA7. -/
def mixedAffineGlobalHomBaseChangeMap {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (M N : schemeDerivedCategory X) :
    (mixedGlobalExtension g).obj
        ((schemeGlobalScalarRestriction f).obj ((schemeGlobalDerivedHom X).obj (op M, N))) ⟶
      (schemeGlobalScalarRestriction (pullback.snd f g)).obj
        ((schemeGlobalDerivedHom (pullback f g)).obj
          (op ((derivedPullback (pullback.fst f g)).obj M),
            (derivedPullback (pullback.fst f g)).obj N)) :=
  ((mixedGlobalExtensionAdjunction g).homEquiv _ _).symm
    ((schemeGlobalScalarRestriction f).map
        (mixedGlobalHomPullbackComparison (pullback.fst f g) M N) ≫
      (schemeGlobalScalarSquareIso f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition).hom.app _)

/-- Scalar extension of global RHom commutes with a flat square over affine bases.
Source: Stacks Project, perfect.tex, Tag 0AA7, case (1).
(blueprint: lem-sc-flat-affine-global-hom-comparison).

Proof: identify Y and Y' with spectra of their global rings using their canonical
isomorphisms. Flatness of f makes the square stalkwise Tor independent. For perfect M,
RHom(M,N) is the perfect dual of M tensored with N. Apply Tor-independent tensor base
change and restricted derived global sections. Pullback commutes with the perfect dual.
The affine equivalences identify derived extension of global scalars with pullback;
the extension/restriction adjunction identifies the resulting comparison with the
transpose defined above. The normalized tensorator and Leray units give exactly the
same map after transport back from spectra. This argument is independent of the
localization morphism universes. Empty schemes and M = 0 give the unique zero isomorphism. -/
theorem mixedAffineGlobalHomBaseChangeMap_isIso
    {X Y Y' : Scheme.{u}} [IsAffine Y] [IsAffine Y']
    [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Y) (g : Y' ⟶ Y) [Flat f]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (M N : schemeDerivedQCohCategory X) (hM : Scheme.IsPerfect X M.obj) :
    IsIso (mixedAffineGlobalHomBaseChangeMap f g M.obj N.obj) := by
  classical
  let H := (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj (op M.obj, N.obj)
  let L := (derivedInternalHom (Opens.grothendieckTopology (pullback f g : Scheme.{u}))
    (pullback f g).sheaf).obj
      (op ((derivedPullback (pullback.fst f g)).obj M.obj),
        (derivedPullback (pullback.fst f g)).obj N.obj)
  let θ : (derivedPullback (pullback.fst f g)).obj H ⟶ L :=
    ((schemeDerivedTensorHomEquiv (pullback f g))
      ((derivedPullback (pullback.fst f g)).obj H)
      ((derivedPullback (pullback.fst f g)).obj M.obj)
      ((derivedPullback (pullback.fst f g)).obj N.obj)).symm
      ((mixedHomTensorPullbackIso (pullback.fst f g)).inv.app (H, M.obj) ≫
        (derivedPullback (pullback.fst f g)).map
          ((schemeDerivedTensorHomEquiv X) H M.obj N.obj (𝟙 _)))
  have hθ : IsIso θ :=
    mixedPerfect_internalHom_pullback_isIso (pullback.fst f g) M.obj N.obj hM
  have hH : schemeDerivedQCohProperty X H :=
    rhom_supported_quasiCoherent_perfect_part X M.obj N.obj N.property hM
  have hpush : schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj H) :=
    schemeDerivedDirectImage_preserves_QCoh f H hH
  obtain ⟨adj, s, adj', hadj, _, _, hadj'⟩ := scheme_derivedInternalHom_adjunction X
  obtain ⟨D, _, _, _, hDperfect, comparison, _, hcompN, _, _⟩ :=
    perfect_rhom_tensor_comparison X M N hM adj hadj adj' hadj'
  have : IsIso (comparison N) := hcompN
  let e : D.obj ⊗ N.obj ≅ H := s D.obj N.obj ≪≫ asIso (comparison N)
  have hTor := flat_pullback_torIndependent f g
  have hbc := torIndependent_perfect_tensor_baseChange f g hTor
    D.obj N.obj hDperfect N.property
  have hnatural := baseChangeMap_naturality f (pullback.snd f g) g
    (pullback.fst f g) pullback.condition e.hom
  have : IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
      pullback.condition (D.obj ⊗ N.obj)) := hbc
  have hhom : IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g
      (pullback.fst f g) pullback.condition H) := by
    have : IsIso ((derivedPullback g).map ((schemeDerivedDirectImage f).map e.hom) ≫
        schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
          pullback.condition H) := by
      rw [hnatural]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((derivedPullback g).map ((schemeDerivedDirectImage f).map e.hom)) _
  obtain ⟨a, d, hmate⟩ := exists_mixedAffineSectionsBaseChangeMate f g H hpush
  let m := (schemeHomPullbackAdjunction (pullback.fst f g)).homEquiv H L θ
  have hm := hmate L m
  have htranspose :
      ((schemeHomPullbackAdjunction (pullback.fst f g)).homEquiv H L).symm m = θ :=
    Equiv.symm_apply_apply _ θ
  rw [htranspose] at hm
  change mixedAffineGlobalHomBaseChangeMap f g M.obj N.obj = _ at hm
  rw [hm]
  infer_instance

end AlgebraicGeometry
