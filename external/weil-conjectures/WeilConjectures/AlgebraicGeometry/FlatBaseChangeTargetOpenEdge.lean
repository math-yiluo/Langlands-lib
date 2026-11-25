/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ResolutionSectionClassOpenRestriction
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.AffineResolutionSectionBijective
import WeilConjectures.AlgebraicGeometry.ResolutionSectionScalarMap
import WeilConjectures.AlgebraicGeometry.RestrictedResolutionSectionsExist

/-! # Normalized Leray edge on a smaller target open

Source: Stacks Project, Tags 01XK, 01E4 and 01FB.
-/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives
attribute [local irreducible] resolutionSectionClass moduleCohomologyFMap
  cohomologyOpenRestriction

-- Keep section-class maps named while identifying the two module cohomology objects.
/-- The normalized target edge is bijective and respects scalars and smaller opens.
Source: Stacks Project, Tag 01XK, Lemma 30.4.6; Tag 01E4, Lemma 20.7.3;
Tag 01FB, Remark 20.14.2.
(blueprint: new-flat-base-change-target-open-edge)

Proof: Put f' = pullback.fst g f and G = tensorPullback(g') F. Restrict J to
L = f' inverse W termwise. Restriction is exact and preserves injectives, so its
augmentation is an injective resolution of G restricted to L. Identify its global
sections with J(L) by restrictAppIso at the top open. The normalized class map is
resolutionSectionClass followed by J.isoRightDerivedObj inverse evaluated on W.
The morphism f' is qcqs and G is quasi-coherent. Its higher images are quasi-coherent
and acyclic in positive degrees on affine W; affine_resolutionSectionClass_bijective
therefore makes this class map bijective. Regard it as an additive equivalence d.
resolutionSectionClass_map_smulHom gives its scalar equation. For the restriction
formula, D.target.components identifies the old section complex with J(U), and its
augmentation identifies the resolved coefficient. The composite restriction sends
J(U) to J(L) termwise. Naturality of evaluation's homology comparison, theta and
J.isoRightDerivedObj gives the claimed equality. Composition of restrictions gives
exactly cohomologyOpenRestriction, by moduleCohomologyFMap functoriality. The equality
flatBaseChangeOpenEquality supplies L ≤ U. These constructions also apply to degree
zero, empty opens and the zero module; no cohomology restriction is inverted. -/
theorem exists_flatBaseChange_target_open_edge
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (p : ℕ) (V : S.Opens) (W : S'.Opens) (hW : IsAffineOpen W)
    (eVW : W ≤ g ⁻¹ᵁ V) (D : FlatBaseChangeOpenChoices f g F I J V) :
    let G := (tensorPullback (pullback.snd g f)).obj F
    let U := (pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)
    let L := (pullback.fst g f) ⁻¹ᵁ W
    let e : L ≤ U := by
      change (pullback.fst g f) ⁻¹ᵁ W ≤ (pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)
      rw [flatBaseChangeOpenEquality f g V]
      exact (pullback.fst g f).preimage_mono eVW
    let M := (restrictFunctor L.ι).obj G
    let C := RingedSpace.moduleCohomology L.toScheme.toRingedSpace p
    let k := (pullback.fst g f).resLE W L le_rfl ≫ W.toSpecΓ
    let Q := ((pushforward (pullback.fst g f)).rightDerived p).obj G
    ∃ d : C.obj M ≃+ Γ(Q, W),
      (∀ (a : Γ(S', W)) (y : C.obj M),
        d ((C.map (M.smulHom (((Scheme.ΓSpecIso Γ(S', W)).inv ≫ k.appTop).hom a))).hom y)
          = a • d y) ∧
      (∀ y : (RingedSpace.moduleCohomology U.toScheme.toRingedSpace p).obj
          ((restrictFunctor U.ι).obj G),
        d (cohomologyOpenRestriction G U L e p y) =
          Q.presheaf.map (homOfLE eVW).op (D.targetClass p y)) := by
  classical
  intro G U L e M C k Q
  let f' := pullback.fst g f
  have : G.IsQuasicoherent := by
    let ep : tensorPullback (pullback.snd g f) ≅ pullback (pullback.snd g f) :=
      (Classical.choose (exists_tensorPullbackAdjunction (pullback.snd g f))).leftAdjointUniq
        (pullbackPushforwardAdjunction (pullback.snd g f))
    exact (SheafOfModules.isQuasicoherent (Limits.pullback g f).ringCatSheaf).prop_of_iso
      (ep.app F).symm (isQuasicoherent_pullback (pullback.snd g f) F)
  obtain ⟨R⟩ := restrictedResolutionSections_exists J L
  let c := resolutionSectionClass R.resolution
    (((pushforward f').mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex)
    W R.sections p ≫ Hom.app (J.isoRightDerivedObj (pushforward f') p).inv W
  have hc : Function.Bijective c :=
    affine_resolutionSectionClass_bijective f' G J p W hW R
  let d : C.obj M ≃+ Γ(Q, W) := AddEquiv.ofBijective c.hom hc
  refine ⟨d, ?_, ?_⟩
  · intro a y
    exact resolutionSectionClass_map_smulHom f' G J p W R a y
  · intro y
    exact resolutionSectionClass_open_restriction f' G J p (g ⁻¹ᵁ V) W eVW U
      (flatBaseChangeOpenEquality f g V) D.target R y

end AlgebraicGeometry.Scheme.Modules
