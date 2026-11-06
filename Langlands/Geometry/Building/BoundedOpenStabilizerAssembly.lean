import Langlands.Geometry.Building.SharpFixerBoundednessAssembly
import Langlands.Geometry.Building.ValuationBuildingAxioms
import Langlands.Geometry.Building.ChamberIwahoriCompactOpenReduction
import Mathlib.Topology.Algebra.Group.Basic

/-! # Assembling KP bounded open stabilizers on the actual quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Plancherel
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

namespace ValuationBuildingData

variable (B : ValuationBuildingData G)

private instance assemblyAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

private instance assemblyTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

/-- The norm-one stabilizer of an actual apartment point is the product of its
sharp fixer and its norm-one normalizer stabilizer. -/
theorem compactStabilizer_apartmentMap_eq_mul
    (hB : B.apartment.IsTopologyCompatible) (x : B.Apartment) :
    (B.compactStabilizer (B.apartmentMap x) : Set (rationalPoints G)) =
      (B.sharpFixer {x} : Set (rationalPoints G)) *
        (B.normOneNormalizerStabilizer x : Set (rationalPoints G)) := by
  ext g
  constructor
  · intro hg
    obtain ⟨hgK, hgfix⟩ := B.mem_compactStabilizer.mp hg
    have hg' : g ∈ MulAction.stabilizer (rationalPoints G) (B.apartmentMap x) := hgfix
    obtain ⟨n, hnx, p, hp, hgp⟩ :=
      (ApartmentQuotient.mem_stabilizer_apartment_iff B.apartment.sharpFixerFamily x g).mp hg'
    have hpK := B.sharpFixer_le_rationalCommonNormKernel hB (Set.mem_singleton x) hp
    have hnK : (n : rationalPoints G) ∈ rationalCommonNormKernel G := by
      have h := (rationalCommonNormKernel G).mul_mem (inv_mem hpK) hgK
      simpa only [hgp, inv_mul_cancel_left] using h
    exact ⟨p, hp, n, B.mem_normOneNormalizerStabilizer.mpr ⟨hnK, n, rfl, hnx⟩,
      hgp.symm⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    obtain ⟨hqK, n, rfl, hnx⟩ := B.mem_normOneNormalizerStabilizer.mp hq
    have hp' := B.mem_compactStabilizer.mp
      (B.sharpFixer_le_compactStabilizer hB (Set.mem_singleton x) hp)
    apply B.mem_compactStabilizer.mpr
    refine ⟨mul_mem hp'.1 hqK, ?_⟩
    rw [mul_smul, B.normalizer_smul_apartmentMap n x, hnx, hp'.2]

/-- Bounded sharp fixers and the actual centralizer norm kernel bound every
norm-one fixer at an original apartment point. -/
theorem isAlgebraicallyBounded_compactStabilizer_apartmentMap
    (hB : B.apartment.IsTopologyCompatible)
    (hsharp : ∀ x : B.Apartment,
      IsAlgebraicallyBounded F G.X (B.sharpFixer {x} : Set (rationalPoints G)))
    (hZ : IsAlgebraicallyBounded F G.X (rationalPoints.map B.centralizer.j ''
      (rationalCommonNormKernel B.centralizer.Z : Set (rationalPoints B.centralizer.Z))))
    (x : B.Apartment) :
    IsAlgebraicallyBounded F G.X
      (B.compactStabilizer (B.apartmentMap x) : Set (rationalPoints G)) := by
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  rw [B.compactStabilizer_apartmentMap_eq_mul hB x]
  exact (hsharp x).mul (B.isAlgebraicallyBounded_normOneNormalizerStabilizer hZ x)

/-- On the existing action, norm-one point fixers transform by actual group conjugation. -/
theorem coe_compactStabilizer_smul (g : rationalPoints G) (y : B.ReducedBuilding) :
    (B.compactStabilizer (g • y) : Set (rationalPoints G)) =
      (fun h => g * h * g⁻¹) '' (B.compactStabilizer y : Set (rationalPoints G)) := by
  ext q
  constructor
  · intro hq
    obtain ⟨hqK, hqfix⟩ := B.mem_compactStabilizer.mp hq
    refine ⟨g⁻¹ * q * g, B.mem_compactStabilizer.mpr ⟨?_, ?_⟩, by simp [mul_assoc]⟩
    · simpa only [inv_inv] using
        (inferInstance : (rationalCommonNormKernel G).Normal).conj_mem q hqK g⁻¹
    · rw [mul_smul, mul_smul, hqfix, inv_smul_smul]
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨hqK, hqfix⟩ := B.mem_compactStabilizer.mp hq
    refine B.mem_compactStabilizer.mpr
      ⟨(inferInstance : (rationalCommonNormKernel G).Normal).conj_mem q hqK g, ?_⟩
    rw [mul_smul, mul_smul, inv_smul_smul, hqfix]

/-- It suffices to prove the exact bounded-open condition at all original
apartment points, since every quotient point has an actual group representative. -/
theorem hasBoundedOpenStabilizers_of_apartment
    (hA : ∀ x : B.Apartment,
      IsOpen (B.compactStabilizer (B.apartmentMap x) : Set (rationalPoints G)) ∧
      IsAlgebraicallyBounded F G.X
        (B.compactStabilizer (B.apartmentMap x) : Set (rationalPoints G))) :
    B.HasBoundedOpenStabilizers := by
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  intro y
  obtain ⟨g, x, rfl⟩ := B.exists_smul_apartmentMap y
  rw [B.coe_compactStabilizer_smul]
  obtain ⟨ho, hb⟩ := hA x
  constructor
  · exact ((Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)).isOpenMap _ ho
  · refine ((hb.smul_set g).mul_singleton g⁻¹).mono ?_
    rintro _ ⟨q, hq, rfl⟩
    exact Set.mul_mem_mul ⟨q, hq, rfl⟩ (Set.mem_singleton _)

end ValuationBuildingData

namespace ParahoricBuildingData

variable (P : ParahoricBuildingData G)

private instance assemblyCentralizerAffine : IsAffine P.centralizer.Z.X.left := by
  have : IsClosedImmersion P.centralizer.j.hom.hom.left := P.centralizer.isClosedSubgroup
  exact isAffine_of_isAffineHom P.centralizer.j.hom.hom.left

private instance assemblyCentralizerTopology : TopologicalSpace (rationalPoints P.centralizer.Z) :=
  rationalPointTopology F P.centralizer.Z.X

private instance assemblyAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

private instance assemblyTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

/-- Bounded singleton sharp fixers, a bounded centralizer norm kernel and open
point parahorics give the complete unchanged KP Axiom 4.1.2 at every quotient point. -/
theorem hasBoundedOpenStabilizers_of_pointParahorics
    (hB : P.apartment.IsTopologyCompatible)
    (hsharp : ∀ x : P.Apartment,
      IsAlgebraicallyBounded F G.X (P.sharpFixer {x} : Set (rationalPoints G)))
    (hZ : IsAlgebraicallyBounded F G.X (rationalPoints.map P.centralizer.j ''
      (rationalCommonNormKernel P.centralizer.Z : Set (rationalPoints P.centralizer.Z))))
    (hopen : ∀ x : P.Apartment,
      IsOpen (P.parahoricAt x : Set (rationalPoints G))) :
    P.HasBoundedOpenStabilizers := by
  have : Smooth G.X.hom := P.isConnectedReductive.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  apply P.toValuationBuildingData.hasBoundedOpenStabilizers_of_apartment
  intro x
  exact ⟨Subgroup.isOpen_mono (P.parahoricAt_le_compactStabilizer hB x) (hopen x),
    P.toValuationBuildingData.isAlgebraicallyBounded_compactStabilizer_apartmentMap
      hB hsharp hZ x⟩

/-- Assemble the exact bounded-open predicate from the existing sharp-fixer,
centralizer and open-root-generation prerequisites, with none silently discharged. -/
theorem hasBoundedOpenStabilizers_of_prerequisites
    (hD : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hsharp : P.toValuationBuildingData.SharpFixerBoundednessStatement)
    (hZ : IsAlgebraicallyBounded F G.X (rationalPoints.map P.centralizer.j ''
      (rationalCommonNormKernel P.centralizer.Z : Set (rationalPoints P.centralizer.Z))))
    (hgen : RelativeRoot.OpenRootCentralizerGenerationStatement.{u})
    (hZo : IsOpen (P.centralizerZero : Set (rationalPoints P.centralizer.Z))) :
    P.HasBoundedOpenStabilizers :=
  P.hasBoundedOpenStabilizers_of_pointParahorics hD.topologyCompatible (hsharp hD) hZ
    (P.isOpen_parahoricAt_of_openRootGeneration hD.topologyCompatible hgen hZo)

/-- Actual bounded open norm-one stabilizers on the original quotient, under the
explicit structural inputs of the assembly theorem. -/
def boundedOpenStabilizerData
    (hD : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hsharp : P.toValuationBuildingData.SharpFixerBoundednessStatement)
    (hZ : IsAlgebraicallyBounded F G.X (rationalPoints.map P.centralizer.j ''
      (rationalCommonNormKernel P.centralizer.Z : Set (rationalPoints P.centralizer.Z))))
    (hgen : RelativeRoot.OpenRootCentralizerGenerationStatement.{u})
    (hZo : IsOpen (P.centralizerZero : Set (rationalPoints P.centralizer.Z)))
    (y : P.ReducedBuilding) :
    {K : OpenSubgroup (rationalPoints G) // K.toSubgroup = P.compactStabilizer y ∧
      IsAlgebraicallyBounded F G.X (K : Set (rationalPoints G))} := by
  have h := P.hasBoundedOpenStabilizers_of_prerequisites hD hsharp hZ hgen hZo y
  exact ⟨⟨P.compactStabilizer y, h.1⟩, rfl, h.2⟩

end ParahoricBuildingData

end Langlands.Geometry.Building
