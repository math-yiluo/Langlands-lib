/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldShriekSystem.FieldShriekSystemEvaluation
public import WeilConjectures.AlgebraicGeometry.FieldShriekSystem.FieldShriekSupportEvaluation
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
import WeilConjectures.Algebra.Homology.Ringed.RingedSliceTensorGenerators
import WeilConjectures.Algebra.Homology.Ringed.RingedOpenTotalTensorKFlat
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Coefficient-system comparison laws

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension,
sk-lem-sp-field-extension-towers.proof.md (2), proper/open system comparison
(blueprint: def-sp-field-shriek-system-coherence).

All arrows below live in the ordinary derived category of the ringed sequence site.
The recorded section-preserving equivalence identifies this with the original strict
tower category. Index n denotes positive exponent n+1. The structures package the
specified constructions and their laws as conclusions, rather than assuming the
comparison or choosing a lift of its finite evaluations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.FieldShriekSystem

variable (P : PurityFiniteSetting.{u})

attribute [local irreducible] coefficientMap HasDerivedCategory.standard
attribute [local irreducible] restrictionEvaluation supportEvaluation comparison

/-- Associativity of scalar extension on the sequence site, fixed by restriction
composition and the normalized adjunctions, hence by balanced tensor multiplication.
Source: blueprint (2), alpha_T (blueprint: def-sp-field-shriek-system-coherence). -/
def scalarAssoc (D : Models P) {E F L : Index P} (h : E ≤ F) (k : F ≤ L)
    (T : Scheme.{u})
    (hc : coefficientMap P (D.coefficients E L (h.trans k)) T =
      coefficientMap P (D.coefficients E F h) T ≫ coefficientMap P (D.coefficients F L k) T) :
    (D.scalars E F h T).T ⋙ (D.scalars F L k T).T ≅ (D.scalars E L (h.trans k) T).T :=
  Adjunction.leftAdjointUniq
    (((D.scalars E F h T).adjunction.comp (D.scalars F L k T).adjunction).ofNatIsoRight
      (Functor.exactDerivedRestrictionComposition _ _ _
        (SheafOfModules.systemScalarRestrictionComposition.{u + 1, u, u + 1}
          (coefficientMap P (D.coefficients E F h) T)
          (coefficientMap P (D.coefficients F L k) T)
          (coefficientMap P (D.coefficients E L (h.trans k)) T) hc)))
    (D.scalars E L (h.trans k) T).adjunction

/-- Identity scalar extension with its tensor unitor normalization.
Source: blueprint (2), identity coefficients
(blueprint: def-sp-field-shriek-system-coherence). -/
def scalarUnit (D : Models P) (E : Index P) (T : Scheme.{u})
    (hc : coefficientMap P (D.coefficients E E le_rfl) T = 𝟙 _) :
    (D.scalars E E le_rfl T).T ≅ 𝟭 _ :=
  Adjunction.leftAdjointUniq
    ((D.scalars E E le_rfl T).adjunction.ofNatIsoRight
      (Functor.exactDerivedRestrictionUnit _
        (SheafOfModules.systemScalarRestrictionUnit.{u + 1, u, u + 1}
          (coefficientMap P (D.coefficients E E le_rfl) T) hc))) Adjunction.id

attribute [local irreducible] scalarAssoc scalarUnit

/-- Composition and identity in the ordinary derived category of whole systems.
Source: blueprint (2), balanced coefficient cocycle
(blueprint: def-sp-field-shriek-system-coherence). -/
structure CoherenceLaw (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) where
  coefficientComposition : ∀ (E F L : Index P) (h : E ≤ F) (k : F ≤ L) (T : Scheme.{u}),
    coefficientMap P (D.coefficients E L (h.trans k)) T =
      coefficientMap P (D.coefficients E F h) T ≫ coefficientMap P (D.coefficients F L k) T
  composition : ∀ (E F L : Index P) (h : E ≤ F) (k : F ≤ L)
    (M : SpTowerShriek.D P.coefficients.l E.val X), normalized P D E X M →
    (D.scalars F L k Y).T.map ((comparison P D h c).app M) ≫
        (comparison P D k c).app ((D.scalars E F h X).T.obj M) ≫
        (SpTowerShriek.F P.coefficients.l L.val (D.base L) (D.operations L) c).map
          ((scalarAssoc P D h k X (coefficientComposition E F L h k X)).hom.app M) =
      (scalarAssoc P D h k Y (coefficientComposition E F L h k Y)).hom.app
          ((SpTowerShriek.F P.coefficients.l E.val (D.base E) (D.operations E) c).obj M) ≫
        (comparison P D (h.trans k) c).app M
  coefficientIdentity : ∀ (E : Index P) (T : Scheme.{u}),
    coefficientMap P (D.coefficients E E le_rfl) T = 𝟙 _
  identity : ∀ (E : Index P) (M : SpTowerShriek.D P.coefficients.l E.val X),
    normalized P D E X M →
    (comparison P D (E := E) (F := E) le_rfl c).app M ≫
        (SpTowerShriek.F P.coefficients.l E.val (D.base E) (D.operations E) c).map
          ((scalarUnit P D E X (coefficientIdentity E X)).hom.app M) =
      (scalarUnit P D E Y (coefficientIdentity E Y)).hom.app
        ((SpTowerShriek.F P.coefficients.l E.val (D.base E) (D.operations E) c).obj M)



end AlgebraicGeometry.ProEtale.FieldShriekSystem
