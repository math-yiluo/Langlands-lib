/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
public import WeilConjectures.CategoryTheory.ClosedScalarHom.ClosedScalarHomComparison
public import WeilConjectures.CategoryTheory.Scalar.ScalarHomCanonicalIso
import WeilConjectures.CategoryTheory.ScalarHomTensor.ScalarHomTensorComparison
import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomTowerCoherence

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
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures SheafOfModules
namespace CategoryTheory
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ R : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J R)]
  (M : ScalarHomModels.{c, v, r, w} J) {R S : Sheaf J CommRingCat.{max c v r}}

/-- Scalar extension preserves K-flatness and has the normalized strong tensor
comparison, coherent along coefficient towers and at identity maps.
Source: Stacks 07A4, 07A6 and 0D6D
(blueprint: lem-sfb-scalar-tensor-tower-comparison).
Proof: scalar extension is the identity-topos pullback. The sectionwise tensor
map sends s tensor (x tensor y) to (s tensor x) tensor (1 tensor y), with inverse
(s tensor x) tensor (t tensor y) mapped to st tensor (x tensor y). Extend through
sheafification and the direct sums defining total complexes; all scalars have
degree zero, so the formulas commute with the signed differential. For an
acyclic S-complex Z, restriction identifies Z tensor_S (S tensor_R P) with
UZ tensor_R P. Restriction is exact and conservative, so a K-flat P has K-flat
extension. The universal left-derived comparison and two-variable K-flat
descent give the unique derived tensor comparison with the displayed
representative normalization. For a tower, the chain comparison sends
t tensor (s tensor x) to t b(s) tensor x. Its inverse inserts 1, and its
unit normalization identifies it with scalarHomExtensionComp. The two tensor
routes agree on pure-tensor generators; descent makes them equal in the
derived category. Composing the five Hom bijections then gives the stated
tower equation, since the scalar transposes compose with the normalized
unit. The same calculation with the identity ring map gives the identity
equation. These arguments include zero rings and arbitrary nonflat maps. -/
theorem scalarTensorTowerComparison_exists :
    ∃ μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
      ScalarHomTensorComparison M a,
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
          (Prod.mkHom ((scalarHomExtensionId M R).inv.app K).op (𝟙 N))) := by
  classical
  have hμ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) :
      Nonempty (ScalarHomTensorComparison M a) :=
    ScalarHomTensor.scalarHomTensorComparison_exists.{c, v, r, w} M a
  let μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
      ScalarHomTensorComparison M a := fun a ↦ (hμ a).some
  obtain ⟨hc, hi⟩ := scalarInternalHomTowerCoherence.{c, v, r, w} M μ
  exact ⟨μ, hc, hi⟩

end CategoryTheory
