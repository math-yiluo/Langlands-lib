/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Acyclic resolution data for module cup products

Source: Stacks Project, Cohomology, section-cup-product and Tag 0FKV
(blueprint: def-sc-module-cup-resolution-data).
The characterization uses resolutions with a sectionwise bilinear chain pairing.
It determines the derived cup product; Godement resolutions supply such pairings.
-/

@[expose] public section

universe uM
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The class of a cocycle, using Mathlib's kernel description of the cycles.
Source: Stacks, section-cup-product (blueprint: def-sc-module-cup-resolution-data). -/
def cupCycleClass {R : Type uM} [Ring R] (K : CochainComplex (ModuleCat.{uM} R) ℕ)
    (n : ℕ) (z : (K.sc n).moduleCatLeftHomologyData.K) : K.homology n :=
  (K.sc n).homologyπ ((K.sc n).moduleCatCyclesIso.inv z)

/-- A resolution that computes module cohomology, with a comparison to an injective
resolution over the original coefficient sheaf. The global comparison must induce
isomorphisms; this holds, in particular, for flasque resolutions.
Source: Stacks, Tags 01DZ and 0FKV (blueprint: def-sc-module-cup-resolution-data). -/
structure CupAcyclicResolution {X : Scheme.{uM}} (F : X.Modules) where
  K : CochainComplex X.Modules ℕ
  augmentation : (CochainComplex.single₀ X.Modules).obj F ⟶ K
  quasiIso : QuasiIso augmentation
  I : InjectiveResolution F
  comparison : K ⟶ I.cocomplex
  over : augmentation ≫ comparison = I.ι
  computes : ∀ n : ℕ, IsIso (HomologicalComplex.homologyMap
    ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ) |>.map comparison) n)

/-- The cohomology class represented by a global cocycle in an acyclic resolution.
Source: Stacks, Tags 01DZ and 0FKV (blueprint: def-sc-module-cup-resolution-data). -/
def CupAcyclicResolution.class {X : Scheme.{uM}} {F : X.Modules}
    (D : CupAcyclicResolution F) (n : ℕ)
    (z : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.K).sc n).moduleCatLeftHomologyData.K) :
    (RingedSpace.moduleCohomology X.toRingedSpace n).obj F :=
  letI : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  letI := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  (D.I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) n).inv
    (HomologicalComplex.homologyMap
      (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ)).map D.comparison) n
      (cupCycleClass _ n z))

/-- A sectionwise O-linear chain pairing of three nonnegative acyclic resolutions,
restricting in degree zero to the ordinary tensor of coefficient sections.
The sign in Leibniz is the total tensor sign. No compatibility of cup products on
cohomology is assumed in this data.
Source: Stacks, section-cup-product and Tag 0FKV
(blueprint: def-sc-module-cup-resolution-data). -/
structure CupResolutionPairing {X : Scheme.{uM}} (F G : X.Modules) where
  left : CupAcyclicResolution F
  right : CupAcyclicResolution G
  target : CupAcyclicResolution (F ⊗ G)
  pair : ∀ (r s : ℕ) (V : X.Opens),
    Γ(left.K.X r, V) →ₗ[Γ(X, V)] Γ(right.K.X s, V) →ₗ[Γ(X, V)]
      Γ(target.K.X (r + s), V)
  restriction : ∀ (r s : ℕ) (V W : X.Opens) (h : W ≤ V)
    (a : Γ(left.K.X r, V)) (b : Γ(right.K.X s, V)),
    (target.K.X (r + s)).presheaf.map (homOfLE h).op (pair r s V a b) =
      pair r s W ((left.K.X r).presheaf.map (homOfLE h).op a)
        ((right.K.X s).presheaf.map (homOfLE h).op b)
  leibniz : ∀ (r s : ℕ) (V : X.Opens)
    (a : Γ(left.K.X r, V)) (b : Γ(right.K.X s, V)),
    (target.K.d (r + s) (r + s + 1)).val.app (op V) (pair r s V a b) =
      (eqToHom (congrArg (fun n ↦ target.K.X n)
          (by omega : r + 1 + s = r + s + 1))).val.app (op V)
        (pair (r + 1) s V ((left.K.d r (r + 1)).val.app (op V) a) b) +
      (-1 : ℤ) ^ r •
        (eqToHom (congrArg (fun n ↦ target.K.X n)
            (by omega : r + (s + 1) = r + s + 1))).val.app (op V)
          (pair r (s + 1) V a ((right.K.d s (s + 1)).val.app (op V) b))
  augmentation_pair : ∀ (V : X.Opens) (a : Γ(F, V)) (b : Γ(G, V)),
    pair 0 0 V ((left.augmentation.f 0).val.app (op V) a)
        ((right.augmentation.f 0).val.app (op V) b) =
      (target.augmentation.f 0).val.app (op V) (tmulSection a b)

end
end AlgebraicGeometry.Scheme.Modules
