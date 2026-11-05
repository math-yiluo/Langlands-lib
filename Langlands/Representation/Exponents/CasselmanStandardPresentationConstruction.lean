import Langlands.Representation.Exponents.CasselmanSufficiencyAssembly
import Langlands.GroupScheme.Rational.StandardRepresentability
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.GroupScheme.Rational.StandardLeviSplitContainment
import Langlands.GroupScheme.Rational.MinimalStandardDynamicComparison

/-! # Fixed-torus Casselman presentations from actual geometric witnesses -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- Construct the exact fixed-torus standard presentation used by sufficiency,
from supplied geometric properties of the canonical standard representatives.
Split-component existence and the factor through the prescribed torus are
constructed using the published general theorems. -/
def standardCasselmanPresentationOfGeometry
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (hStandard : StandardCocharacterStatement.{u})
    (hminimal : IsMinimalParabolicFunctor (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)))
    (I : Finset (RationalPointFamily.SimpleRoot i ν))
    (hp : IsParabolicSubgroup
      (Standard.parabolicHom i ν (RationalPointFamily.rootSet i ν I)))
    (hl : IsRationalLeviSubgroup
      (Standard.leviToParabolic i ν (RationalPointFamily.rootSet i ν I)))
    (hr : LeviSubgroup.IsGeometricUnipotentRadical
      (Standard.unipotentToParabolic i ν (RationalPointFamily.rootSet i ν I)))
    (hmul : IsIso (subgroupMultiplication
      (Standard.leviToParabolic i ν (RationalPointFamily.rootSet i ν I))
      (Standard.unipotentToParabolic i ν (RationalPointFamily.rootSet i ν I)))) :
    StandardCasselmanPresentation i ν I := by
  classical
  apply Classical.choice
  let J := RationalPointFamily.rootSet i ν I
  obtain ⟨A, a, ha⟩ :=
    (splitComponentStatement k (Standard.leviScheme i ν J) hl.isConnectedReductive).1
  have hj : (standardLevi i ν J).IsRepresentedBy
      (Standard.leviToParabolic i ν J ≫ Standard.parabolicHom i ν J) := by
    rw [Standard.leviToParabolic_comp]
    exact Standard.isRepresentedBy_leviHom i ν J
  have hjc : IsClosedSubgroup
      (Standard.leviToParabolic i ν J ≫ Standard.parabolicHom i ν J) := by
    rw [Standard.leviToParabolic_comp]
    exact Standard.isClosedSubgroup_leviHom i ν J
  obtain ⟨f, hf, _, _⟩ := ha.exists_commFactor_standardLevi hi ν J hjc hj
  obtain ⟨⟨ζ, hζ⟩, hcomparison⟩ :=
    hStandard k G hG T i hi ν hν J (RationalPointFamily.rootSet_subset i ν I)
  have hc := hcomparison ζ hζ
  have hle : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
      standardParabolic i ν J := by
    rw [hc.1]
    apply ((relativeRootSignInclusions k G hG T i hi ν ζ).1).mpr
    intro α hα hnonneg
    apply hζ.pairing_nonneg_of_positive i ν
    refine ⟨hα, ?_⟩
    have hne := hν α hα
    omega
  refine ⟨?_⟩
  refine
    { P := Standard.parabolicScheme i ν J
      M := Standard.leviScheme i ν J
      U := Standard.unipotentScheme i ν J
      A := A
      p := Standard.parabolicHom i ν J
      l := Standard.leviToParabolic i ν J
      r := Standard.unipotentToParabolic i ν J
      a := a
      f := f
      compatible :=
        { parabolic := hp
          levi := hl
          splitComponent := ha
          maximalSplit := hi
          generic := hν
          subset_simpleRoots := RationalPointFamily.rootSet_subset i ν I
          parabolic_eq := (Standard.isRepresentedBy_parabolicHom i ν J).2
          levi_eq := hj.2
          factor_comp := hf
          minimal := hminimal
          minimal_le := ?_
          realization := ?_ }
      radical := hr
      multiplication := hmul
      radical_points_eq := ?_ }
  · rw [(Standard.isRepresentedBy_parabolicHom i ν J).2]
    exact hle
  · exact ⟨ζ, hζ, (Standard.isRepresentedBy_parabolicHom i ν J).2.trans hc.1,
      hj.2.trans hc.2.1⟩
  · rw [Standard.unipotentToParabolic_comp]
    exact congrArg (fun F : SubgroupFunctor G => F.carrier (Over.mk (𝟙 _)))
      (Standard.isRepresentedBy_unipotentHom i ν J).2

end Langlands.Aubert.General.RepresentedParabolic
