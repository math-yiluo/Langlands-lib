/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedScalarShiftCoordinates
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.SmoothPurity.Completed.CompletedScalarChainShift
import WeilConjectures.SmoothPurity.Completed.CompletedScalarShiftDescent
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory

set_option linter.privateModule false

/-!
# Completed scalar extension and cochain shifts

Source: the blueprint of the Weil conjectures, `lemma-perfect-complexes-geometric-point`,
final equivalence display (blueprint: lem-weil-point-completed-scalar-shift).
The representative sign calculation uses Stacks Project Tags 011G, 014E and 08TC.
The coordinates below are mapping-cocone coordinates: the first is detected by
`mappingCocone.fst` and the second by `mappingCocone.snd`.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 1024

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures

variable {l : ℕ} [Fact l.Prime] {E : Type u} [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {L : Type u} [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (Y : AlgebraicGeometry.Scheme.{t})

attribute [-instance] SheafOfModules.instPreadditive in
attribute [local irreducible] completedScalarChangeData
  completedIntegralCoefficientSheafUnrestricted

attribute [-instance] SheafOfModules.instPreadditive in
attribute [local irreducible] completedDerivedScalarExtension
  completedOrdinaryScalarExtension
  completedScalarChainComparison completedScalarComparison
  integralScalarExtensionOfUniverses integralScalarExtensionComparisonOfUniverses

attribute [-instance] SheafOfModules.instPreadditive in
private theorem goodRepresentative_exists
    (K : DerivedCategory (integralTowerModules l E Y)) :
    ∃ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
      Nonempty (DerivedCategory.Q.obj P.obj ≅ K) := by
  obtain ⟨A, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (DerivedCategory.Q : CochainComplex (integralTowerModules l E Y) ℤ ⥤ _) K
  obtain ⟨P, p, hk, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) A
  let := SheafOfModules.isMonoidal_W_independentCoefficients
    (completedIntegralCommRingSheafUnrestricted l E Y)
  let := SheafOfModules.monoidalCategory
    (completedIntegralCommRingSheafUnrestricted l E Y)
  have hp : integralOperationsGoodComplex l E Y P :=
    ⟨hk, fun n ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso
        (completedIntegralCommRingSheafUnrestricted l E Y) (P.X n)).symm (hf n)⟩
  have := hq
  exact ⟨⟨P, hp⟩, ⟨asIso (DerivedCategory.Q.map p) ≪≫ e⟩⟩

end WeilConjectures
