import Langlands.Representation.Aubert.General.RationalJacquetCommonTerm
import Langlands.Representation.Aubert.General.RationalJacquetSurvivorTerm
import Langlands.Representation.Aubert.General.GeometricTermReduction
import Langlands.Representation.Aubert.General.RationalHaarModulus

/-! # Collapsing the source of rational standard geometric terms -/

noncomputable section

open Classical

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

private theorem compose_stages
    {A B C D E : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup D] [AddCommGroup E]
    [Module ℤ A] [Module ℤ B] [Module ℤ C] [Module ℤ D] [Module ℤ E]
    (f : D →ₗ[ℤ] E) (c : C →ₗ[ℤ] D)
    (r : B →ₗ[ℤ] C) (s : A →ₗ[ℤ] B) (t : A →ₗ[ℤ] C)
    (h : r.comp s = t) :
    (f.comp (c.comp r)).comp s = f.comp (c.comp t) := by
  rw [LinearMap.comp_assoc, LinearMap.comp_assoc, h]

variable {k : Type u} [Field k] [TopologicalSpace k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hStandard : StandardCocharacterStatement.{u})

local instance rationalTermStagesPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))
  (hM : ∀ A, IsClosed (levi i ν A : Set (RationalPoint k G.X)))
  (hfl : ∀ A, ParabolicFiniteLength.{u, max (u + 1) v}
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν A) (hU A))
  (hLfl : ∀ J, letI := (hM J).locallyCompactSpace
    ∀ I : Finset J, ParabolicFiniteLength.{u, max (u + 1) v}
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
      ((hU (leviIndex J I)).preimage continuous_subtype_val))
  (J I : Finset (SimpleRoot i ν)) (S : Finset I) (K : Finset J)
  (g : RationalPoint k G.X)
  (hFine : ∀ x : RationalPoint k G.X,
    x ∈ levi i ν (leviIndex J K) ↔
      g⁻¹ * x * g ∈ levi i ν (leviIndex I S))

/-- The literal restricted term, written with actual ambient fine Levis. -/
def rationalRestrictedJacquetTerm :
    FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (levi i ν I) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (levi i ν J) :=
  (standardLeviInductionK0.{u, v} i ν hInter hG hi hν hU hM hLfl J K).comp
    ((conjugationK0.{u, max (u + 1) v} g hFine).comp
      (standardLeviJacquetK0.{u, v} i ν hInter hG hi hν hU hM hLfl I S))

/-- The wrappers retain exactly the generic standard intersection term. -/
theorem rationalRestrictedJacquetTerm_eq_standard :
    rationalRestrictedJacquetTerm.{u, v}
        i ν hInter hG hi hν hU hM hLfl J I S K g hFine =
      standardIntersectionTermK0.{u, u, max (u + 1) v}
        (parabolic i ν) (levi i ν) (unipotent i ν) hM hU
        J I (leviIndex I S) (leviIndex J K) g
        (levi_le_of_subset i ν hInter hG hi hν _ I (leviIndex_subset I S))
        (levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J K))
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I S)
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J K)
        hFine
        ⟨(hLfl I S).2.2.1, (hLfl I S).2.2.2⟩
        ⟨(hLfl J K).1, (hLfl J K).2.1⟩ := rfl

section LocalField

variable [ValuativeRel k] [IsNonarchimedeanLocalField k]
  (hproj : ∀ A, Continuous
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν A).projection)
  (hLUc : ∀ (A : Finset (SimpleRoot i ν)) (B : Finset A),
    Jacquet.Localization.IsLimitOfCompactSubgroups
      ((unipotent i ν (leviIndex A B)).subgroupOf (levi i ν A)))

include hproj hLUc in
/-- Actual Jacquet restriction in stages collapses the source of a restricted
term. The positive Haar factorization is derived from the standard projections. -/
theorem rationalRestrictedJacquetTerm_comp_ambient :
    (rationalRestrictedJacquetTerm.{u, v}
        i ν hInter hG hi hν hU hM hLfl J I S K g hFine).comp
        (standardAmbientJacquetK0.{u, v}
          i ν hG hi hν hStandard hU hfl I) =
      standardConjugatedJacquetTerm.{u, v}
        i ν hInter hG hi hν hStandard hU hM hfl hLfl
        J K (leviIndex I S) g hFine := by
  exact compose_stages
    (standardLeviInductionK0.{u, v} i ν hInter hG hi hν hU hM hLfl J K)
    (conjugationK0.{u, max (u + 1) v} g hFine)
    (standardLeviJacquetK0.{u, v} i ν hInter hG hi hν hU hM hLfl I S)
    (standardAmbientJacquetK0.{u, v} i ν hG hi hν hStandard hU hfl I)
    (standardAmbientJacquetK0.{u, v}
      i ν hG hi hν hStandard hU hfl (leviIndex I S))
    (standardLeviJacquetK0_comp_ambient.{u, v}
      i ν hInter hG hi hν hStandard hU hM hfl hLfl I S (hLUc I S)
      (standardJacquetModulus_stages
        i ν hInter hG hi hν hStandard hproj I S hU (hM I)))

end LocalField

end Langlands.Aubert.General.RationalPointFamily
