import Langlands.GroupScheme.Reductive.SplitIsogenyTargetCoverage
import Langlands.LinearAlgebra.RootDatumIsogenyChambers

/-! # Intrinsic chamber correspondence and reductive local-isogeny graphs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra

namespace Langlands.GroupScheme.RootDatumIsogenyRealization

variable {k : Type u} [Field k]
    {G G' : GroupScheme (Spec (CommRingCat.of k))}
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom G'.X.hom]
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'}
    {J J' : Type u} [Finite J] [Finite J']
    [Module.Finite ℤ (characterLattice T)] [Module.Finite ℤ (cocharacterLattice T)]
    [Module.Finite ℤ (characterLattice T')] [Module.Finite ℤ (cocharacterLattice T')]
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    {P' : RootDatum J' (characterLattice T') (cocharacterLattice T')}
    [P.IsReduced] [P'.IsReduced]

/-- A generic source chamber and its actual coweight pushforward have
exactly corresponding intrinsic simple roots. -/
theorem simple_root_coweightMap_iff_of_chambers
    (hP : IsRootDatumOf i P) (hP' : IsRootDatumOf i' P')
    (f : RootDatumIsogeny (ringExpChar k) P' P) {ν : cocharacterLattice T}
    (hν : IsGenericCocharacter i ν) (j : J') :
    P'.root j ∈ simpleRelativeRoots i' (f.coweightMap ν) ↔
      P.root (f.indexEquiv j) ∈ simpleRelativeRoots i ν := by
  classical
  let : Fintype J := Fintype.ofFinite J
  let : Fintype J' := Fintype.ofFinite J'
  have hreg (a : J) : P.root' a ν ≠ 0 := by
    change P.toLinearMap (P.root a) ν ≠ 0
    rw [hP.1]
    exact hν _ (by rw [relativeRoots_eq_roots, ← hP.2.1]; exact Set.mem_range_self a)
  obtain ⟨b, hb⟩ := RootDatumCoweightFace.exists_base_support P ν hreg
  have hbpos (a : J) (ha : a ∈ b.support) :
      0 < latticePairing T (P.root a) ν := by
    have ha' : a ∈ IsAddIndecomposable.baseOf P.root
        ((P.flip.toLinearMap ν) : characterLattice T →+ ℤ) := by
      rw [← hb]
      exact ha
    have hpos := ha'.1
    change 0 < P.toLinearMap (P.root a) ν at hpos
    simpa only [hP.1] using hpos
  have hsign := base_isPos_iff_of_positive_support hP b hν hbpos
  have hν' := generic_coweightMap hP hP' f hν
  have hreg' (a : J') : P'.root' a (f.coweightMap ν) ≠ 0 := by
    change P'.toLinearMap (P'.root a) (f.coweightMap ν) ≠ 0
    rw [hP'.1]
    exact hν' _ (by rw [relativeRoots_eq_roots, ← hP'.2.1]; exact Set.mem_range_self a)
  obtain ⟨b', hb'⟩ := RootDatumCoweightFace.exists_base_support P' (f.coweightMap ν) hreg'
  have hbpos' (a : J') (ha : a ∈ b'.support) :
      0 < latticePairing T' (P'.root a) (f.coweightMap ν) := by
    have ha' : a ∈ IsAddIndecomposable.baseOf P'.root
        ((P'.flip.toLinearMap (f.coweightMap ν)) : characterLattice T' →+ ℤ) := by
      rw [← hb']
      exact ha
    have hpos := ha'.1
    change 0 < P'.toLinearMap (P'.root a) (f.coweightMap ν) at hpos
    simpa only [hP'.1] using hpos
  have hsign' := base_isPos_iff_of_positive_support hP' b' hν' hbpos'
  have hsupport := f.mem_support_iff_of_coweight_signs ν b' b
    (fun a => by simpa only [hP'.1] using hsign' a)
    (fun a => by simpa only [hP.1] using hsign a) j
  rw [← mem_base_support_iff_simple_of_isPos hP' b' _ hsign',
    ← mem_base_support_iff_simple_of_isPos hP b ν hsign]
  exact hsupport

namespace SimpleIsogenyGraph

variable {t : T ⟶ T'} (D : SimpleIsogenyGraph i i' t)

/-- The pushed source directions cover every simple root of the target
chamber using intrinsic chamber correspondence. -/
theorem target_coverage
    (hP : IsRootDatumOf i P) (hP' : IsRootDatumOf i' P')
    (f : RootDatumIsogeny (ringExpChar k) P' P)
    (hw : ∀ χ : characterLattice T', f.weightMap χ = t ≫ χ) :
    ∀ α ∈ simpleRelativeRoots i' (f.coweightMap D.directions.chamber),
      ∃ a : D.SimpleIndex, latticePairing T' α (D.targetDirection a) = 0 := by
  intro α hα
  have hroot := hα.1.1
  rw [relativeRoots_eq_roots, ← hP'.2.1] at hroot
  obtain ⟨j, rfl⟩ := hroot
  have hsimple := (simple_root_coweightMap_iff_of_chambers hP hP' f
    D.directions.generic j).mp hα
  let a : D.SimpleIndex := ⟨P.root (f.indexEquiv j), hsimple⟩
  refine ⟨a, ?_⟩
  have hdir : D.targetDirection a = f.coweightMap (D.directions.direction a) :=
    (D.targetDirectionComp a).symm.trans
      (coweightMap_apply_of_weightMap hP.1 hP'.1 f t hw _).symm
  rw [hdir, root_pairing_coweightMap hP hP' f]
  have hz := D.directions.annihilates a
  change latticePairing T (P.root (f.indexEquiv j)) (D.directions.direction a) = 0 at hz
  rw [hz, mul_zero]

/-- The target projection has faithfully flat, finitely presented geometry
using the prescribed root-datum isogeny and its chamber comparison. -/
theorem second_geometry
    (hG' : IsConnectedReductive G') (hT' : IsSplitTorus T'.toGrp)
    (hi' : IsMaximalTorus i') (ht : IsIsogeny (CommGroupScheme.groupHom t))
    (hP : IsRootDatumOf i P) (hP' : IsRootDatumOf i' P')
    (f : RootDatumIsogeny (ringExpChar k) P' P)
    (hw : ∀ χ : characterLattice T', f.weightMap χ = t ≫ χ) :
    Flat D.envelope.second.hom.hom.left ∧ Surjective D.envelope.second.hom.hom.left ∧
      LocallyOfFinitePresentation D.envelope.second.hom.hom.left ∧
        QuasiCompact D.envelope.second.hom.hom.left := by
  let : Smooth G'.X.hom := hG'.smooth
  let : ConnectedSpace G'.X.left := hG'.connectedSpace
  have hgeneric := generic_coweightMap hP hP' f D.directions.generic
  exact D.envelope.second_geometry hT' hi'.2.1 ht P' hP'
    (f.coweightMap D.directions.chamber) hgeneric
    (D.target_coverage hP hP' f hw)
    (LocalIsogenyGraphEnvelope.chamber_centralizer_eq_range hG' hT' hi' _ hgeneric)

/-- Record both projection geometries, deriving source coverage from the
graph and target coverage from intrinsic chamber comparison. -/
def faithfullyFlatGraph
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (hT' : IsSplitTorus T'.toGrp) (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    (ht : IsIsogeny (CommGroupScheme.groupHom t))
    (hP : IsRootDatumOf i P) (hP' : IsRootDatumOf i' P')
    (f : RootDatumIsogeny (ringExpChar k) P' P)
    (hw : ∀ χ : characterLattice T', f.weightMap χ = t ≫ χ) :
    FaithfullyFlatLocalIsogenyGraphEnvelope D.comparisons := by
  let : Smooth G.X.hom := hG.smooth
  exact ⟨D.envelope, D.first_geometry hG hi P hP,
    D.second_geometry hG' hT' hi' ht hP hP' f hw⟩

/-- Certify the actual graph as connected reductive, retaining both
faithfully flat projections, using the intrinsic chamber comparison. -/
def reductiveGraph
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (hT' : IsSplitTorus T'.toGrp) (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    (ht : IsIsogeny (CommGroupScheme.groupHom t))
    (hP : IsRootDatumOf i P) (hP' : IsRootDatumOf i' P')
    (f : RootDatumIsogeny (ringExpChar k) P' P)
    (hw : ∀ χ : characterLattice T', f.weightMap χ = t ≫ χ) :
    ReductiveLocalIsogenyGraphEnvelope D.comparisons :=
  reductiveLocalIsogenyGraphEnvelope
    (D.faithfullyFlatGraph hG hG' hT' hi hi' ht hP hP' f hw)
    hG hG'

end SimpleIsogenyGraph

end Langlands.GroupScheme.RootDatumIsogenyRealization
