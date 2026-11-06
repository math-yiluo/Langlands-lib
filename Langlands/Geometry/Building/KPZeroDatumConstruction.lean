import Langlands.Geometry.Building.KPParahoric
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicConjugacyAssembly
import Langlands.GroupScheme.Rational.MaximalTorusFiniteType
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof

/-! # Actual zero-subgroup data from simply connected derived covers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

section Field

variable {k : Type u} [Field k]

/-- Extending an actual maximal split torus to a maximal torus constructs a
maximally split maximal torus. No reductivity hypothesis is needed here. -/
theorem exists_isMaximallySplitMaximalTorus
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom] :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ H),
      IsMaximallySplitMaximalTorus i := by
  obtain ⟨A, a, ha⟩ := exists_maximalSplitTorus H
  obtain ⟨T, i, hi, f, hf⟩ :=
    exists_maximalTorus_extension_of_finiteType H a ha.1.1.isTorus ha.1.2
  exact ⟨T, i, hi, A, a, f, ha, hf⟩

/-- A finite Galois splitting field for a torus can be chosen inside any
specified separably closed extension of its ground field. -/
theorem exists_finiteGaloisSplittingField_inside
    (Ω : Type u) [Field Ω] [Algebra k Ω] [IsSepClosed Ω]
    (T : GroupScheme (Spec (CommRingCat.of k))) (hT : IsTorus T) :
    ∃ L : IntermediateField k Ω, FiniteDimensional k L ∧ IsGalois k L ∧
      IsSplitTorus (GaloisPointComparison.baseChanged k L T) := by
  obtain ⟨E, hE, hA, hfin, hgal, hsplit⟩ := torusFiniteGaloisSplitting k T hT
  let φ : E →ₐ[k] Ω := IsSepClosed.lift
  let L := φ.fieldRange
  let e : E ≃ₐ[k] L := φ.equivFieldRange
  have : FiniteDimensional k L := Module.Finite.equiv e.toLinearEquiv
  have : IsGalois k L := IsGalois.of_algEquiv e
  refine ⟨L, inferInstance, inferInstance, ?_⟩
  obtain ⟨I, hI, ⟨s⟩⟩ := hsplit
  exact ⟨I, hI, TorusExistence.nonempty_splitIso_extension e.toRingHom
    (RingHom.ext e.commutes) T I s⟩

end Field

section Local

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

namespace UnramifiedZeroDatum

/-- Construct all torus and embedded splitting-field choices from an actual
simply connected derived cover. The supplied covering maps are retained. -/
def ofDerivedCover
    {H D C : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
    (d : D ⟶ H) (π : C ⟶ D) (hcover : IsSimplyConnectedDerivedCover d π) :
    UnramifiedZeroDatum F H := by
  classical
  let : IsAffineHom H.X.hom := hcover.isConnectedReductive.isAffineHom
  let : Smooth H.X.hom := hcover.isConnectedReductive.smooth
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let hexists := exists_isMaximallySplitMaximalTorus H
  let T := hexists.choose
  let i := hexists.choose_spec.choose
  have hi : IsMaximallySplitMaximalTorus i := hexists.choose_spec.choose_spec
  let : IsClosedImmersion i.hom.hom.left := hi.1.2.1
  let : IsAffine T.X.left := isAffine_of_isAffineHom i.hom.hom.left
  let hsplit :=
    exists_finiteGaloisSplittingField_inside (SeparableClosure F) T.toGrp hi.1.1
  let L := hsplit.choose
  exact {
    T := T
    isAffine := inferInstance
    i := i
    isMaximallySplitMaximalTorus := hi
    L := L
    finiteDimensional := hsplit.choose_spec.1
    isGalois := hsplit.choose_spec.2.1
    isSplitTorus := hsplit.choose_spec.2.2
    D := D
    C := C
    d := d
    π := π
    isSimplyConnectedDerivedCover := hcover }

end UnramifiedZeroDatum

namespace ZeroSubgroupDatum

/-- Construct zero-subgroup data at the prescribed torus and centralizer from
actual derived covers of the ambient group and of the unramified centralizer. -/
def ofDerivedCovers
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G Z D C : GroupScheme (Spec (CommRingCat.of F))}
    (i : S.toGrp ⟶ G) (j : Z ⟶ G)
    (hi : IsMaximalSplitTorus i) (hj : (torusCentralizer i).IsRepresentedBy j)
    (d : D ⟶ G) (π : C ⟶ D) (hcover : IsSimplyConnectedDerivedCover d π)
    {DZ CZ : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
    (dZ : DZ ⟶ GaloisPointComparison.baseChanged F (UnramifiedClosure F) Z)
    (πZ : CZ ⟶ DZ) (hcoverZ : IsSimplyConnectedDerivedCover dZ πZ) :
    ZeroSubgroupDatum i j where
  isMaximalSplitTorus := hi
  isRepresentedBy := hj
  centralizerDatum := UnramifiedZeroDatum.ofDerivedCover dZ πZ hcoverZ
  D := D
  C := C
  d := d
  π := π
  isSimplyConnectedDerivedCover := hcover

end ZeroSubgroupDatum

namespace ParahoricBuildingData

/-- Add actual zero data to supplied valuation building data, preserving the
entire underlying valuation quotient and its rational-point action. -/
def ofDerivedCovers
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)
    {D C : GroupScheme (Spec (CommRingCat.of F))}
    (d : D ⟶ G) (π : C ⟶ D) (hcover : IsSimplyConnectedDerivedCover d π)
    {DZ CZ : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
    (dZ : DZ ⟶ GaloisPointComparison.baseChanged F (UnramifiedClosure F) B.centralizer.Z)
    (πZ : CZ ⟶ DZ) (hcoverZ : IsSimplyConnectedDerivedCover dZ πZ) :
    ParahoricBuildingData G where
  toValuationBuildingData := B
  zeroDatum := ZeroSubgroupDatum.ofDerivedCovers B.i B.centralizer.j
    B.isMaximalSplitTorus B.centralizer.isRepresentedBy d π hcover dZ πZ hcoverZ

end ParahoricBuildingData

end Local

end Langlands.Geometry.Building
