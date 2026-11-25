/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.FlatPullbackHomologySections
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeRestrictedLiftHomology

/-! # FlatBaseChangeResolutionSections

Source: Stacks Project, Cohomology, Tags 02N7, 01FB and 01E4.
-/

@[expose] public section
universe uBC
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] AlgebraicGeometry.Scheme.Modules.enoughInjectives

/-- The section formula for one augmented resolution lift.
Source: Stacks, Cohomology, Tags 02N7, 01FB, 01E4, 01EZ.
(blueprint: lem-weil-pbc-flat-base-change-resolution-sections).

Proof: Restrict t to U = f⁻¹V and use the augmentation-preserving comparisons
 in D to obtain a map of the source resolution into the direct image of the
 target resolution on W = g'⁻¹U. D.unit_square gives its augmentation equation
 with D.psi. Resolve that pushed complex by lambda into injectives. In the
 recorded construction of moduleCohomologyFMap choose lambda times the restricted
 lift as the horizontal map. Sections of lambda induce invertible homology maps
 (01EZ), so H(lambda) inverse times H(lambda t) equals H(t). Independence of the
 cohomology-map choices (`moduleCohomologyFMap_independent`) identifies this
 with the recorded map. Naturality of
 theta with respect to maps of section complexes transports this equation to
 the two resolutionSectionClass maps. Finally q is the adjoint of c, namely
 unit followed by g_*c. Exactness of g^* identifies its homology with pullback
 of homology; on each locally represented cocycle the adjoint of H(c) therefore
 sends its class to the class of q(s). Sheafification gives the same equality
 of sections. The isoRightDerivedObj maps in sourceClass, targetClass and beta
 transport that equality to precisely the displayed formula. -/
theorem flatBaseChangeResolutionBeta_sections {X S S' : Scheme.{uBC}} (f : X ⟶ S) (g : S' ⟶ S)
    [Flat g] [Flat (pullback.snd g f)] {F : X.Modules}
    (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶ ((pushforward (pullback.snd g f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex)
    (ht : I.ι.f 0 ≫ t.f 0 =
      (Classical.choose (exists_tensorPullbackAdjunction (pullback.snd g f))).unit.app F ≫
        (pushforward (pullback.snd g f)).map (J.ι.f 0))
    (p : ℕ) :
    ∀ (V : S.Opens)
        (D : FlatBaseChangeOpenChoices f g F I J V)
        (xi : (forget₂ _ AddCommGrpCat.{uBC}).obj
          ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj
            ((restrictFunctor (f ⁻¹ᵁ V).ι).obj F))),
        Hom.app ((Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv _ _
          (flatBaseChangeResolutionBeta f g I J t p)) V
          (D.sourceClass p xi) =
        D.targetClass p
          (moduleCohomologyFMap ((pullback.snd g f).resLE (f ⁻¹ᵁ V)
            ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl) D.psi p xi) := by
  intro V D xi
  have h := flatBaseChangeResolutionBeta_openMap_sections f g I J t p V D xi
  have hm := ConcreteCategory.congr_hom
    (flatBaseChangeRestrictedLift_homology f g I J t ht p V D) xi
  exact h.trans (congrArg (fun x ↦ D.targetClass p x) hm)

end AlgebraicGeometry.Scheme.Modules
