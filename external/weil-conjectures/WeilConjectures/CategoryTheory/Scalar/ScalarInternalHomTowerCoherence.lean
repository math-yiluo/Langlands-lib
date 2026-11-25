/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
public import WeilConjectures.CategoryTheory.ClosedScalarHom.ClosedScalarHomComparison
public import WeilConjectures.CategoryTheory.Scalar.ScalarHomCanonicalIso
import WeilConjectures.CategoryTheory.ClosedScalarHom.ClosedScalarHomComposition
import WeilConjectures.CategoryTheory.ClosedScalarHom.ClosedScalarHomTransport
import WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence

/-! # Canonical scalar tensor comparisons and coefficient towers

Source: Stacks 07A4, 07A6 and 0D6D. The internal-Hom map occurring in the
coherence equations is the explicitly constructed map of the five Hom bijections.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open WeilConjectures SheafOfModules
namespace CategoryTheory
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ R : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J R)]
  (M : ScalarHomModels.{c, v, r, w} J) {R S : Sheaf J CommRingCat.{max c v r}}

/-- The normalized closed-Hom comparisons respect coefficient towers and identities.
Source: Stacks Project, Cohomology on Sites, Tags 0D6D, 07A4 and 07A6.
(blueprint: lem-sfb-scalar-internal-hom-tower-coherence).

Proof: on a K-flat representative, the unit-normalized left-adjoint composition
comparison is t tensor (s tensor x) mapped to t b(s) tensor x. It intertwines the
tensor comparisons: both paths send t tensor (s tensor (x tensor y)) to
(t b(s) tensor x) tensor (1 tensor y). The inverse inserts 1. Naturality and the
scalar-unit equation identify this with the canonical leftAdjointUniq comparison.
The equality of tensor maps descends through the fully faithful restriction to
K-flat pairs. The five Hom equivalences for the composite adjunction are the
successive five equivalences, using this tensor equality and the normalized units.
Evaluate at the source identity to obtain the tower equation. For an identity map,
scalar multiplication identifies extension with the identity; the same calculation
makes the five Hom equivalences the identity after the specified transports.
All computations include zero rings and require no flatness of a coefficient map. -/
theorem scalarInternalHomTowerCoherence
    (μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
      ScalarHomTensorComparison M a) :
  (∀ {R S T : Sheaf J CommRingCat.{max c v r}}
    (a : R ⟶ S) (b : S ⟶ T)
    (K : DerivedCategory (scalarModules J R)) (N : DerivedCategory (scalarModules J T)),
    (scalarHomCanonicalIso M (a ≫ b) (μ (a ≫ b))).hom.app (op K, N) ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom (𝟙 (op K)) ((scalarHomRestrictionComp.{c, v, r, w} a b).hom.app N)) =
      (scalarHomRestrictionComp.{c, v, r, w} a b).hom.app
          ((derivedInternalHomOfUniverses.{c, v, r, w} J T).obj
            (op ((M.scalar (a ≫ b)).derived.obj K), N)) ≫
        (scalarDerivedRestriction a).map ((scalarDerivedRestriction b).map
          ((derivedInternalHomOfUniverses.{c, v, r, w} J T).map
            (Prod.mkHom ((scalarHomExtensionComp M a b).hom.app K).op (𝟙 N)))) ≫
          (scalarDerivedRestriction a).map
            ((scalarHomCanonicalIso M b (μ b)).hom.app (op ((M.scalar a).derived.obj K), N)) ≫
              (scalarHomCanonicalIso M a (μ a)).hom.app
                (op K, (scalarDerivedRestriction b).obj N)) ∧
(∀ (R : Sheaf J CommRingCat.{max c v r})
    (K N : DerivedCategory (scalarModules J R)),
    (scalarHomCanonicalIso M (𝟙 R) (μ (𝟙 R))).hom.app (op K, N) ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom (𝟙 (op K)) ((scalarHomRestrictionId.{c, v, r, w} R).hom.app N)) =
      (scalarHomRestrictionId.{c, v, r, w} R).hom.app
          ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
            (op ((M.scalar (𝟙 R)).derived.obj K), N)) ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom ((scalarHomExtensionId M R).inv.app K).op (𝟙 N)))  := by
  obtain ⟨hcomp, hid⟩ := scalarHomTensorCoherence M μ
  constructor
  · intro R S T a b K N
    let adj := (M.scalar a).adjunction.comp (M.scalar b).adjunction
    let d := scalarHomRestrictionComp.{c, v, r, w} a b
    let cc := scalarHomExtensionComp M a b
    let μ₀ : (M.closed R).tensor ⋙ ((M.scalar a).derived ⋙ (M.scalar b).derived) ≅
        (((M.scalar a).derived ⋙ (M.scalar b).derived).prod
          ((M.scalar a).derived ⋙ (M.scalar b).derived)) ⋙ (M.closed T).tensor :=
      (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (μ a).iso (M.scalar b).derived ≪≫
        Functor.associator _ _ _ ≪≫
        isoWhiskerLeft ((M.scalar a).derived.prod (M.scalar a).derived) (μ b).iso
    have hμ₀ (X Y : DerivedCategory (scalarModules J R)) :
        μ₀.hom.app (X, Y) =
          (M.scalar b).derived.map ((μ a).iso.hom.app (X, Y)) ≫
            (μ b).iso.hom.app ((M.scalar a).derived.obj X, (M.scalar a).derived.obj Y) := by
      simp [μ₀]
    have hc := ClosedScalarHom.adjunction_compatibility
      adj (M.scalar (a ≫ b)).adjunction d
    have ht := ClosedScalarHom.transport (M.closed R) (M.closed T)
      adj (M.scalar (a ≫ b)).adjunction d cc hc μ₀ (μ (a ≫ b)).iso
      (by intro X Y; rw [hμ₀]; simpa only [Category.assoc] using hcomp a b X Y) K N
    have hg := ClosedScalarHom.composition (M.closed R) (M.closed S) (M.closed T)
      (M.scalar a).adjunction (M.scalar b).adjunction (μ a).iso (μ b).iso μ₀ hμ₀ K N
    rw [hg] at ht
    simpa only [scalarHomCanonicalIso, Functor.comp_map, Category.assoc] using ht
  · intro R K N
    let d := scalarHomRestrictionId.{c, v, r, w} R
    let cc := (scalarHomExtensionId M R).symm
    have hc (X Y : DerivedCategory (scalarModules J R))
        (f : (M.scalar (𝟙 R)).derived.obj X ⟶ Y) :
        Adjunction.id.homEquiv X Y (cc.hom.app X ≫ f) =
          (M.scalar (𝟙 R)).adjunction.homEquiv X Y f ≫ d.hom.app Y := by
      simpa only [cc, scalarHomExtensionId, Iso.symm_hom,
        Adjunction.leftAdjointUniq_inv_app] using
        ClosedScalarHom.adjunction_compatibility Adjunction.id
          (M.scalar (𝟙 R)).adjunction d X Y f
    exact ClosedScalarHom.transport_identity (M.closed R)
      (M.scalar (𝟙 R)).adjunction d cc hc (μ (𝟙 R)).iso (hid R) K N

end CategoryTheory
