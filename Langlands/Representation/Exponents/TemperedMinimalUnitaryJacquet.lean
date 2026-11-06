import Langlands.Representation.Exponents.TemperedIdentityUnitaryJacquet
import Langlands.GroupScheme.Absolute.BorelExistenceCoordinates
import Langlands.GroupScheme.Absolute.ParabolicTransport
import Mathlib.Order.Minimal

/-! # Minimal actual parabolics with nonzero unitary Jacquet part -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance minimalUnitaryAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- Actual parabolic, Levi, radical and split-component data for which the
unitary Jacquet part of the fixed representation is nonzero. -/
structure UnitaryJacquetSupportData (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) where
  P : GroupScheme (Spec (CommRingCat.of k))
  M : GroupScheme (Spec (CommRingCat.of k))
  U : GroupScheme (Spec (CommRingCat.of k))
  p : P ⟶ G
  l : M ⟶ P
  r : U ⟶ P
  hp : IsParabolicSubgroup p
  hl : IsRationalLeviSubgroup l
  hr : LeviSubgroup.IsGeometricUnipotentRadical r
  hmul : IsIso (subgroupMultiplication l r)
  A : CommGroupScheme (Spec (CommRingCat.of k))
  a : A.toGrp ⟶ M
  ha : IsSplitComponent a
  nontrivial_unitaryPart : Nontrivial
    (SmoothRep.subrepresentation ((jacquetFunctor p l r hp hr hl hmul).obj π)
      (unitaryJacquetPart p l r hp hl hr hmul ha π))

namespace UnitaryJacquetSupportData

variable {π : SmoothRep.{0, u, v} ℂ (rationalPoints G)}

/-- Minimality is inclusion-minimality of the actual subgroup functor among all
parabolics admitting the stored nonzero unitary Jacquet data. -/
def IsMinimal (D : UnitaryJacquetSupportData π) : Prop :=
  ∀ E : UnitaryJacquetSupportData π,
    SubgroupFunctor.range E.p ≤ SubgroupFunctor.range D.p →
      SubgroupFunctor.range E.p = SubgroupFunctor.range D.p

/-- Maximality of the defining coordinate ideal implies actual minimality of
the supported parabolic. -/
theorem isMinimal_of_maximal_coordinateKernel (D : UnitaryJacquetSupportData π)
    (hmax : ∀ E : UnitaryJacquetSupportData π,
      BorelExistence.coordinateKernel D.p ≤ BorelExistence.coordinateKernel E.p →
        BorelExistence.coordinateKernel E.p ≤ BorelExistence.coordinateKernel D.p) :
    D.IsMinimal := by
  intro E hle
  have : IsClosedImmersion D.p.hom.hom.left := D.hp.isClosedSubgroup
  have : IsClosedImmersion E.p.hom.hom.left := E.hp.isClosedSubgroup
  have : Mono D.p.hom.hom := Over.mono_of_mono_left _
  have : Mono E.p.hom.hom := Over.mono_of_mono_left _
  let f := SubgroupFunctor.factorOfRangeLE hle
  have hf : f ≫ D.p = E.p := SubgroupFunctor.factorOfRangeLE_comp hle
  have hker := BorelExistence.coordinateKernel_le E.p D.p f hf
  have : IsIso f := BorelExistence.isIso_of_coordinateKernel_eq E.p D.p f
    E.hp.isClosedSubgroup D.hp.isClosedSubgroup hf (le_antisymm (hmax E hker) hker)
  apply le_antisymm hle
  exact SubgroupFunctor.range_le_of_factor (inv f)
    (by rw [← hf, IsIso.inv_hom_id_assoc])

/-- Every nonempty support family contains an actual minimal supported
parabolic. The affine finite-type coordinate ring is noetherian. -/
theorem exists_minimal [LocallyOfFiniteType G.X.hom]
    (hne : Nonempty (UnitaryJacquetSupportData π)) :
    ∃ D : UnitaryJacquetSupportData π, D.IsMinimal := by
  have := BorelExistence.isNoetherianRing_globalSections G
  obtain ⟨D, hmax⟩ := exists_maximalFor_of_wellFoundedGT
    (fun _ : UnitaryJacquetSupportData π => True)
    (fun D => BorelExistence.coordinateKernel D.p) (hne.elim fun D => ⟨D, trivial⟩)
  exact ⟨D, D.isMinimal_of_maximal_coordinateKernel
    (fun E hle => hmax.le_of_le trivial hle)⟩

end UnitaryJacquetSupportData

variable {hG : IsConnectedReductive G} {π : SmoothRep.{0, u, v} ℂ (rationalPoints G)}

/-- The whole-group identity parabolic supplies a member of the actual
unitary Jacquet support family for a nonzero tempered representation. -/
theorem IsNormalizedExponentTempered.nonempty_unitaryJacquetSupportData
    (hπ : IsNormalizedExponentTempered hG π) [Nontrivial π] :
    Nonempty (UnitaryJacquetSupportData π) := by
  obtain ⟨A, a, ha, hne⟩ := hπ.exists_nontrivial_unitaryJacquetPart
  exact ⟨{
    P := G
    M := G
    U := Grp.trivial (Over (Spec (CommRingCat.of k)))
    p := 𝟙 G
    l := 𝟙 G
    r := kernelUnit G
    hp := hG.isParabolicSubgroup_id
    hl := hG.isRationalLeviSubgroup_id
    hr := hG.isGeometricUnipotentRadical_kernelUnit
    hmul := isIso_subgroupMultiplication_id_kernelUnit
    A := A
    a := a
    ha := ha
    nontrivial_unitaryPart := hne }⟩

/-- A nonzero normalized-exponent tempered representation admits an actual
parabolic minimal among all those with nonzero unitary Jacquet part. -/
theorem IsNormalizedExponentTempered.exists_minimal_nontrivial_unitaryJacquetPart
    (hπ : IsNormalizedExponentTempered hG π) [Nontrivial π] :
    ∃ D : UnitaryJacquetSupportData π, D.IsMinimal := by
  have : Smooth G.X.hom := hG.smooth
  exact UnitaryJacquetSupportData.exists_minimal hπ.nonempty_unitaryJacquetSupportData

/-- A chosen actual minimal parabolic with its nonzero unitary Jacquet data. -/
def minimalUnitaryJacquetSupport
    (hπ : IsNormalizedExponentTempered hG π) [Nontrivial π] :
    UnitaryJacquetSupportData π :=
  Classical.choose hπ.exists_minimal_nontrivial_unitaryJacquetPart

/-- The chosen support is minimal for inclusion of actual subgroup functors. -/
theorem minimalUnitaryJacquetSupport_isMinimal
    (hπ : IsNormalizedExponentTempered hG π) [Nontrivial π] :
    (minimalUnitaryJacquetSupport hπ).IsMinimal :=
  Classical.choose_spec hπ.exists_minimal_nontrivial_unitaryJacquetPart

end Langlands.Aubert.General.RepresentedParabolic
