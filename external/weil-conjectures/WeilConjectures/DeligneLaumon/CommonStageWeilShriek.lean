/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.WeilCompactSupportCohomology
public import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientAction
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.SmoothPurity.Sf.SfCommonStageDirectImage
import WeilConjectures.SmoothPurity.Sf.SfRationalDirectImageAdjunction
import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientAction
import WeilConjectures.DeligneLaumon.WeilIndSheafCategory
import WeilConjectures.SmoothPurity.Supporting.DirectImagesConstructible
import WeilConjectures.CategoryTheory.StageSystem.Functor
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.DeligneLaumon.ZlFrobeniusCompactSupportComparison
import WeilConjectures.DeligneLaumon.ZlOpenUnit.ZlOpenWeilUnitEmptyFibre
import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
import WeilConjectures.SmoothPurity.Common.CommonStagePullbackIdentity
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Compact support with canonical Frobenius comparison

Source: blueprint main-20261015, proposition-composition-base-change-rf-shriek--1 and
prose-10-20; SGA 4, XVII, §5--6
(blueprint: def-zl-common-stage-weil-shriek).

Open extension and proper image are adjoints of the existing common-stage pullback.
Their Frobenius comparisons are specified mates of its normalized Frobenius square.
Their composite is identified naturally with the recorded compact-support action.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Endofunctor AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

-- The inverse-square argument also used by the private Frobenius helper in
-- SfCommonStageDirectImage; no separatedness hypothesis is needed.
section Proper
variable {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  (p₀ : X₀ ⟶ Y₀) [IsProper p₀.left]

end Proper

section Open
variable {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  (j₀ : X₀ ⟶ Y₀) [IsOpenImmersion j₀.left]

end Open

section CompactSupport
variable {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left)

end CompactSupport

end WeilConjectures
