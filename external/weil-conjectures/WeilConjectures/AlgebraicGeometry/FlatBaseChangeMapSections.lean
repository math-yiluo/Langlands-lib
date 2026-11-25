/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSectionsLift
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeResolutionIndependence
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoicesExist
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeResolutionSections

/-! # FlatBaseChangeMapSections

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

/-- The base-change map constructed from resolutions is independent of the resolutions
and augmented lifts. Its adjoint sends the canonical image of a class on f⁻¹V to the
canonical image of its pullback along g' restricted to g'⁻¹(f⁻¹V).
The local pullback is written as the recorded cohomology h-map of the restricted unit;
the unit square identifies its target with the restriction of g'^*F.
Source: Stacks, Tags 02N7, 01E4, 01FB
(blueprint: lem-weil-pbc-flat-base-change-map-sections).

Proof: (1) Injective resolutions exist by lem-weil-pbc-scheme-modules-enough-injectives.
Flat pushforward preserves injectives by
lem-weil-pbc-flat-module-pullback-exact-pushforward-injective, so
lem-weil-pbc-lift-along-injective-quasi-iso supplies t with the prescribed augmentation.
Two such t are homotopic by lem-weil-pbc-lift-to-injective-unique-up-to-homotopy.
The pushforward square is the sectionwise comparison; termwise adjunction preserves
homotopies by lem-weil-pbc-termwise-adjunction-homotopy. Comparison lifts between
resolutions and their homotopy inverses prove the first equality for every choice.
(2) Restrict I and J to U = f⁻¹V and W = g'⁻¹U. Restriction preserves resolutions by
lem-weil-pbc-module-open-restriction-injectives. Restrict the unit sectionwise;
on each open it is m ↦ 1 ⊗ m. The restricted unit square gives psi and the canonical
identification h^*(F|U) ≅ F'|W. These resolutions and the section identifications give
FlatBaseChangeOpenChoices for every V.
(3) Restrict t to U. In def-weil-pbc-module-cohomology-fmap choose a resolution lambda
of h_*(J|W) and comparison lambda times the restricted t.
By lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso, H(Γlambda) is invertible.
Thus H(Γlambda) inverse times H(Γlambda times q_V) is H(q_V), so this is the
recorded cohomology pullback. A cocycle s maps to t(s).
(4) Restrictions commute with t, hence with H(q_V). The canonical theta maps of
lem-weil-pbc-higher-direct-image-presheaf turn these into a presheaf map to
 g_*R^p f'_*F'. Sheafification gives its unique extension.
(5) q = g_*c times the unit. Exactness of g^* identifies the homology of the pulled-back
complex with g^* of its homology. Locally represent a cohomology-sheaf section by a
cocycle s: the adjoint of H(c) takes [s] to [c(unit(s))] = [q(s)]. Therefore it is
that unique extension. Substituting step (3) proves the displayed section formula. -/
theorem flatBaseChangeMap_sections {X S S' : Scheme.{uBC}} (f : X ⟶ S) (g : S' ⟶ S)
    [Flat g] [Flat (pullback.snd g f)] (F : X.Modules) (p : ℕ) :
    ∃ beta : (tensorPullback g).obj (((pushforward f).rightDerived p).obj F) ⟶
        ((pushforward (pullback.fst g f)).rightDerived p).obj
          ((tensorPullback (pullback.snd g f)).obj F),
      (∀ (I : InjectiveResolution F)
        (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
        (t : I.cocomplex ⟶ ((pushforward (pullback.snd g f)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj J.cocomplex),
        I.ι.f 0 ≫ t.f 0 =
          (Classical.choose (exists_tensorPullbackAdjunction (pullback.snd g f))).unit.app F ≫
            (pushforward (pullback.snd g f)).map (J.ι.f 0) →
        flatBaseChangeResolutionBeta f g I J t p = beta) ∧
      (∀ (I : InjectiveResolution F)
        (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F)) (V : S.Opens),
        Nonempty (FlatBaseChangeOpenChoices f g F I J V)) ∧
      (∀ (I : InjectiveResolution F)
        (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F)) (V : S.Opens)
        (D : FlatBaseChangeOpenChoices f g F I J V)
        (xi : (forget₂ _ AddCommGrpCat.{uBC}).obj
          ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj
            ((restrictFunctor (f ⁻¹ᵁ V).ι).obj F))),
        Hom.app ((Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv _ _ beta) V
          (D.sourceClass p xi) =
        D.targetClass p
          (moduleCohomologyFMap ((pullback.snd g f).resLE (f ⁻¹ᵁ V)
            ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl) D.psi p xi)) := by
  let I := injectiveResolution F
  let J := injectiveResolution ((tensorPullback (pullback.snd g f)).obj F)
  refine (flatBaseChangeResolutionLift f g (F := F) I J).elim fun t ht ↦ ?_
  refine ⟨flatBaseChangeResolutionBeta f g I J t p, ?_, ?_, ?_⟩
  · intro I₁ J₁ t₁ ht₁
    exact flatBaseChangeResolutionBeta_independent f g I₁ J₁ t₁ ht₁ I J t ht p
  · exact flatBaseChangeMap_sections_choices f g F
  · intro I₁ J₁ V D xi
    refine (flatBaseChangeResolutionLift f g (F := F) I₁ J₁).elim fun t₁ ht₁ ↦ ?_
    rw [← flatBaseChangeResolutionBeta_independent f g I₁ J₁ t₁ ht₁ I J t ht p]
    exact flatBaseChangeResolutionBeta_sections f g I₁ J₁ t₁ ht₁ p V D xi

end AlgebraicGeometry.Scheme.Modules
