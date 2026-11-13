import Langlands.Sheaf.Renard.VectorSheafModuleEquivalence
import Langlands.Sheaf.Renard.ModuleBasisChange

/-!
# Complex vector sheaves and sheaves of `𝒞^∞_X`-modules on a basis

Renard (9 July 2026), II.2.5 Remark, printed p.39 / PDF p.45: the notions of sheaf of complex
vector spaces and of sheaf of `𝒞^∞_X`-modules are equivalent, and "by the last paragraph of
II.2.1 this remains true for sheaves of base `T`". This file composes the published all-open
equivalence `VectorSheafModuleEquivalence.equivalence` with the inverse of the published
module-sheaf basis change `ModuleBasisChange.scalarEquivalence`, for any basis and for
Renard's base `T_c` of compact opens of a t.d. space.
-/

noncomputable section

namespace Langlands.Sheaf.Renard.CompactVectorSheafModuleEquivalence

open CategoryTheory TopologicalSpace Opposite
open VectorSheafScalars (VectorSheaf)
open ModuleBasisChange (ScalarModuleSheaf)

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The all-open category `ModuleSheaf X` of the II.2.5 Remark unit is the category
`ScalarModuleSheaf (allOpenBasis X)` of the basis-change unit. -/
theorem moduleSheaf_eq :
    VectorSheafModuleEquivalence.ModuleSheaf X = ScalarModuleSheaf (allOpenBasis X) :=
  rfl

/-- Renard II.2.5 Remark for sheaves of base `B`: complex vector sheaves on `X` and sheaves of
`𝒞^∞_X`-modules on the basis `B` are equivalent. The functor gives a vector sheaf its
locally constant action and restricts it to `B`; the inverse extends a module sheaf from `B`
to all opens by compatible families and forgets to complex scalars. -/
def basisEquivalence (B : OpenBasis X) : VectorSheaf X ≌ ScalarModuleSheaf B :=
  (VectorSheafModuleEquivalence.equivalence X).trans
    (ModuleBasisChange.scalarEquivalence B).symm

/-- Renard II.2.5 Remark for the base `T_c` of compact opens of a t.d. space: complex vector
sheaves on `X` and sheaves of `𝒞^∞_X`-modules on `T_c` are equivalent. -/
def compactEquivalence (hX : Langlands.Topology.IsLocallyProfinite X) :
    VectorSheaf X ≌ ScalarModuleSheaf (ProjectorBasisSheaf.compactOpenBasis hX) :=
  (VectorSheafModuleEquivalence.equivalence X).trans
    (ModuleBasisChange.compactScalarEquivalence hX).symm

theorem compactEquivalence_eq (hX : Langlands.Topology.IsLocallyProfinite X) :
    compactEquivalence hX = basisEquivalence (ProjectorBasisSheaf.compactOpenBasis hX) :=
  rfl

theorem basisEquivalence_functor (B : OpenBasis X) :
    (basisEquivalence B).functor =
      VectorSheafModuleEquivalence.toModule X ⋙
        ModuleBasisChange.restriction B (LocallyConstantScalar.ringPresheaf X ℂ) :=
  rfl

theorem basisEquivalence_inverse (B : OpenBasis X) :
    (basisEquivalence B).inverse =
      ModuleBasisChange.extension B (LocallyConstantScalar.ringPresheaf X ℂ) ⋙
        VectorSheafModuleEquivalence.toVector X :=
  rfl

/-- The sections over a basis member `U` of the module sheaf attached to `F` are the sections
of `F` over `U`. -/
theorem basisEquivalence_sections (B : OpenBasis X) (F : VectorSheaf X) (U : BasisOpen B) :
    (BasisModuleSheaf.sections ((basisEquivalence B).functor.obj F) U : Type u) =
      F.presheaf.obj (op U.obj) :=
  rfl

/-- A locally constant function on a basis member `U`, read as a scalar of the ring
`𝒞^∞(U)` of the basis ring presheaf (the identity map; it only fixes the type). -/
abbrev basisScalar {B : OpenBasis X} {U : BasisOpen B} (f : LocallyConstant U.obj ℂ) :
    (LocallyConstantScalar.basisRingPresheaf B ℂ).obj (op U) :=
  f

/-- On sections over a basis member, the `𝒞^∞(U)`-action is the published locally constant
action `VectorSheafScalars.smul`, with germs `f(x) s(x)`. -/
theorem basisEquivalence_smul (B : OpenBasis X) (F : VectorSheaf X) (U : BasisOpen B)
    (f : LocallyConstant U.obj ℂ)
    (s : BasisModuleSheaf.sections ((basisEquivalence B).functor.obj F) U) :
    basisScalar f • s = VectorSheafScalars.smul F f s :=
  rfl

/-- Morphisms keep their components over basis members. -/
theorem basisEquivalence_map_app (B : OpenBasis X) {F G : VectorSheaf X} (φ : F ⟶ G)
    (U : BasisOpen B) (s : F.presheaf.obj (op U.obj)) :
    BasisModuleSheaf.app ((basisEquivalence B).functor.map φ) U s = φ.hom.app (op U.obj) s :=
  rfl

end Langlands.Sheaf.Renard.CompactVectorSheafModuleEquivalence
