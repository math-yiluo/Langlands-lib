/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism

/-! # Cohomology along an affine morphism

Source: Stacks Project, Cohomology of Schemes, Lemma 089W and Lemma 01XC;
Cohomology, Lemma 01F4 and Equation 01FA
(blueprint: lem-weil-pbc-affine-morphism-cohomology-edge).
-/

@[expose] public section

universe v

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- For a direct-image-acyclic module, the horizontal comparison in any system of
edge-map resolution choices is a quasi-isomorphism. Source: Stacks Project, Tags
01XC and 01FB, with Leray's acyclicity lemma (015E). -/
private theorem beta_quasiIso {X S : Scheme.{v}} (h : X ⟶ S)
    [HasInjectiveResolutions X.Modules] (F : X.Modules)
    (hF : (pushforward h).rightAcyclic F)
    (D : ModuleCohomologyFMapData h ((pushforward h).obj F) F (𝟙 _)) :
    QuasiIso D.β := by
  have : PreservesFiniteLimits (pushforward h) :=
    have := (pullbackPushforwardAdjunction h).rightAdjoint_preservesLimits.{0, 0}
    inferInstance
  have hs (n : ℕ) : (pushforward h).rightAcyclic
      (((CochainComplex.single₀ X.Modules).obj F).X n) := by
    cases n with
    | zero => exact hF
    | succ n =>
      exact (pushforward h).rightAcyclic.prop_of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega))
  have := (pushforward h).quasiIso_map_of_rightAcyclic_nat D.I.ι hs
    (fun n ↦ Functor.rightAcyclic_of_injective (F := pushforward h) (D.I.cocomplex.X n))
  let α := (HomologicalComplex.singleMapHomologicalComplex (pushforward h)
    (ComplexShape.up ℕ) 0).inv.app F ≫
      ((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).map D.I.ι
  have : QuasiIso α := inferInstance
  have := D.quasiIso
  have heq : D.J.ι ≫ D.β = α ≫ D.lambda := by
    apply (CochainComplex.fromSingle₀Equiv _ _).injective
    apply Subtype.ext
    simpa [α] using D.compatible
  have : QuasiIso (D.J.ι ≫ D.β) := by
    rw [heq]
    infer_instance
  exact (quasiIso_iff_comp_left D.J.ι D.β).mp this

/-- For an affine morphism, higher direct images of a quasi-coherent module vanish and
cohomology is carried isomorphically by the edge map.
Source: Stacks Project, Cohomology of Schemes, Lemma 089W and Lemma 01XC;
Cohomology, Lemma 01F4 and Equation 01FA
(blueprint: lem-weil-pbc-affine-morphism-cohomology-edge).

Proof:
1. By lem-pc-affine-morphism-hi (Stacks 01XC), higher direct images vanish: on
an affine open V of S, its inverse image is affine, so positive quasi-coherent
cohomology vanishes; affine opens form a basis.
2. Choose an injective resolution F → I. By pqf-def-cohomology and step 1,
h_*F → h_*I is exact. Its terms are Γ(S,-)-acyclic by
lem-weil-pbc-module-pushforward-injective-acyclic.
3. Choose an injective resolution s : h_*F → J. By
lem-weil-pbc-lift-along-injective-quasi-iso, lift s to γ : h_*I → J over h_*F.
It is a quasi-isomorphism. By lemma-weil-pbc-leray-acyclicity, Γ(S,γ) induces
an isomorphism in every nonnegative degree.
4. In def-weil-pbc-module-cohomology-fmap take the h-map id, the resolutions
I and J, the third resolution J, λ = γ and β = id. By
lem-weil-pbc-module-cohomology-fmap-functorial the choices do not affect the map.
The edge map is H(Γ(S,γ)) inverse, using Γ(S,h_*I) = Γ(X,I), so is invertible.
All maps are O_S(S)-linear; the action on H(X,F) is through h.appTop.
-/
theorem affine_morphism_cohomology_edge
    {X S : Scheme.{v}} (h : X ⟶ S) [IsAffineHom h]
    (F : X.Modules) [F.IsQuasicoherent] :
    (∀ (p : ℕ), 0 < p →
      IsZero (((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).rightDerived p).obj F)) ∧
      (∀ (p : ℕ), IsIso (moduleCohomologyEdgeMap h F p) ∧
        ∀ (r : Γ(S, ⊤))
          (x : (RingedSpace.moduleCohomology S.toRingedSpace p).obj
            ((pushforward h).obj F)),
          moduleCohomologyEdgeMap h F p (r • x) =
            h.appTop r •
              @id ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F)
                (moduleCohomologyEdgeMap h F p x)) := by
  have := isGrothendieckAbelian X
  have := isGrothendieckAbelian S
  have : PreservesFiniteLimits (RingedSpace.globalSectionsFunctor S.toRingedSpace) :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.evaluation (moduleRings S.toRingedSpace) (op ⊤)))
  have hvan (p : ℕ) (hp : 0 < p) := isZero_higherDirectImage_of_isAffineHom h F hp
  constructor
  · intro p hp
    exact hvan p hp
  · intro p
    constructor
    · let D := Classical.choice (moduleCohomologyFMapData_nonempty h
        ((pushforward h).obj F) F (𝟙 _))
      have hF : (pushforward h).rightAcyclic F := fun q ↦ hvan (q + 1) (by omega)
      have : QuasiIso D.β := beta_quasiIso h F hF D
      have hJ (n : ℕ) : (RingedSpace.globalSectionsFunctor S.toRingedSpace ⋙
          forget₂ _ AddCommGrpCat.{v}).rightAcyclic (D.J.cocomplex.X n) :=
        Functor.rightAcyclic_of_injective _
      have hK (n : ℕ) : (RingedSpace.globalSectionsFunctor S.toRingedSpace ⋙
          forget₂ _ AddCommGrpCat.{v}).rightAcyclic (D.K.X n) := by
        have := D.injective n
        exact Functor.rightAcyclic_of_injective _
      have := (RingedSpace.globalSectionsFunctor S.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{v}).quasiIso_map_of_rightAcyclic_nat D.β hJ hK
      have : IsIso ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v}
          (ComplexShape.up ℕ) p).map
        (((RingedSpace.globalSectionsFunctor S.toRingedSpace ⋙
          forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℕ)).map
            D.β)) := by
        change IsIso (HomologicalComplex.homologyMap _ p)
        infer_instance
      change IsIso (D.map p)
      unfold ModuleCohomologyFMapData.map
      have := D.invertible p
      infer_instance
    · obtain ⟨L, hL⟩ := (moduleCohomologyFMap_basic_properties h
        (𝟙 ((pushforward h).obj F)) p).1
      intro r x
      rw [show moduleCohomologyEdgeMap h F p =
        (forget₂ _ AddCommGrpCat).map L from hL.symm]
      change L.hom (r • x) = r • L.hom x
      exact L.hom.map_smul r x

end AlgebraicGeometry.Scheme.Modules
