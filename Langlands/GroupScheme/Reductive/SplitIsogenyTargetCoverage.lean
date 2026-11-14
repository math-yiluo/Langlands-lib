import Langlands.GroupScheme.Reductive.SplitIsogenySimpleGraph
import Langlands.GroupScheme.Reductive.SplitIsogenyGraphProjections
import Langlands.LinearAlgebra.RootDatumIsogenyBaseStatement
import Langlands.LinearAlgebra.RootDatumCoweightFace
import Langlands.LinearAlgebra.RootDatumZeroFace

/-! # Target simple-root coverage for local-isogeny graphs -/

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

/-- The actual target root pairing is the source pairing multiplied by its
positive characteristic-power factor. -/
theorem root_pairing_coweightMap
    (hP : IsRootDatumOf i P) (hP' : IsRootDatumOf i' P')
    (f : RootDatumIsogeny (ringExpChar k) P' P) (ν : cocharacterLattice T) (j : J') :
    latticePairing T' (P'.root j) (f.coweightMap ν) =
      (f.rootFactor j : ℤ) * latticePairing T (P.root (f.indexEquiv j)) ν := by
  rw [← hP'.1, ← f.pairing_apply, f.root_weightMap, hP.1]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]

/-- Positive target roots have precisely the signs of their corresponding
source roots, even when their root factors differ. -/
theorem root_pos_coweightMap_iff
    (hP : IsRootDatumOf i P) (hP' : IsRootDatumOf i' P')
    (f : RootDatumIsogeny (ringExpChar k) P' P) (ν : cocharacterLattice T) (j : J') :
    0 < latticePairing T' (P'.root j) (f.coweightMap ν) ↔
      0 < latticePairing T (P.root (f.indexEquiv j)) ν := by
  rw [root_pairing_coweightMap hP hP' f ν j]
  exact mul_pos_iff_of_pos_left (by exact_mod_cast f.rootFactor_pos j)

/-- Pushforward of a generic source chamber is generic for the target. -/
theorem generic_coweightMap
    (hP : IsRootDatumOf i P) (hP' : IsRootDatumOf i' P')
    (f : RootDatumIsogeny (ringExpChar k) P' P) {ν : cocharacterLattice T}
    (hν : IsGenericCocharacter i ν) : IsGenericCocharacter i' (f.coweightMap ν) := by
  intro α hα
  rw [relativeRoots_eq_roots, ← hP'.2.1] at hα
  obtain ⟨j, rfl⟩ := hα
  rw [root_pairing_coweightMap hP hP' f ν j]
  exact mul_ne_zero (by exact_mod_cast (f.rootFactor_pos j).ne')
    (hν _ (by rw [relativeRoots_eq_roots, ← hP.2.1]; exact Set.mem_range_self _))

section BaseComparison

variable {J : Type u} [Finite J]
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}

omit [Module.Finite ℤ (characterLattice T)] [Module.Finite ℤ (cocharacterLattice T)]
  [Finite J] in
/-- A base whose simple roots are positive on a generic chamber has that
chamber's full positive system. -/
theorem base_isPos_iff_of_positive_support
    (hP : IsRootDatumOf i P) (b : P.Base) {ν : cocharacterLattice T}
    (hν : IsGenericCocharacter i ν)
    (hb : ∀ j ∈ b.support, 0 < latticePairing T (P.root j) ν) (j : J) :
    b.IsPos j ↔ 0 < latticePairing T (P.root j) ν := by
  have hnonneg (x : characterLattice T)
      (hx : x ∈ AddSubmonoid.closure (P.root '' (b.support : Set J))) :
      0 ≤ latticePairing T x ν := by
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      exact (hb j hj).le
    | zero => simp
    | add x y _ _ hx hy =>
      simpa only [map_add, LinearMap.add_apply] using add_nonneg hx hy
  constructor
  · intro hj
    have hn := hnonneg _ ((RootDatumZeroFace.isPos_iff_mem_closure b j).mp hj)
    have hz := hν (P.root j) (by rw [relativeRoots_eq_roots, ← hP.2.1]; exact Set.mem_range_self j)
    exact lt_of_le_of_ne hn hz.symm
  · intro hj
    by_contra h
    have hn := hnonneg _ ((RootDatumZeroFace.neg_mem_closure_iff_not_isPos b j).mpr h)
    simp only [map_neg, LinearMap.neg_apply] at hn
    omega

omit [Module.Finite ℤ (characterLattice T)] [Module.Finite ℤ (cocharacterLattice T)] in
/-- An integral base with the chamber's positive system has exactly the
intrinsic simple-root characters of that chamber. -/
theorem mem_base_support_iff_simple_of_isPos
    (hP : IsRootDatumOf i P) (b : P.Base) (ν : cocharacterLattice T)
    (hb : ∀ j, b.IsPos j ↔ 0 < latticePairing T (P.root j) ν) (j : J) :
    j ∈ b.support ↔ P.root j ∈ simpleRelativeRoots i ν := by
  rw [b.mem_support_iff_positive_indecomposable P j, hb]
  constructor
  · rintro ⟨hj, hindecomp⟩
    refine ⟨⟨?_, hj⟩, ?_⟩
    · rw [relativeRoots_eq_roots, ← hP.2.1]
      exact Set.mem_range_self j
    · rintro ⟨a, ha, c, hc, heq⟩
      have ha' := ha.1
      have hc' := hc.1
      rw [relativeRoots_eq_roots, ← hP.2.1] at ha' hc'
      obtain ⟨a, rfl⟩ := ha'
      obtain ⟨c, rfl⟩ := hc'
      exact hindecomp a c ((hb a).mpr ha.2) ((hb c).mpr hc.2) heq
  · intro hj
    refine ⟨hj.1.2, ?_⟩
    intro a c ha hc heq
    apply hj.2
    exact ⟨P.root a, ⟨by rw [relativeRoots_eq_roots, ← hP.2.1]; exact Set.mem_range_self a, (hb a).mp ha⟩,
      P.root c, ⟨by rw [relativeRoots_eq_roots, ← hP.2.1]; exact Set.mem_range_self c, (hb c).mp hc⟩, heq⟩

end BaseComparison

/-- Base transport identifies the intrinsic simple systems for a source
chamber and its actual coweight pushforward. The base-transport theorem is
retained as an explicit input. -/
theorem simple_root_coweightMap_iff
    (hbase : RootDatumIsogenyBaseStatement.{u, u, u, u, u, u})
    (hP : IsRootDatumOf i P) (hP' : IsRootDatumOf i' P')
    (f : RootDatumIsogeny (ringExpChar k) P' P) {ν : cocharacterLattice T}
    (hν : IsGenericCocharacter i ν) (j : J') :
    P'.root j ∈ simpleRelativeRoots i' (f.coweightMap ν) ↔
      P.root (f.indexEquiv j) ∈ simpleRelativeRoots i ν := by
  classical
  let : Fintype J := Fintype.ofFinite J
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
  obtain ⟨b', hsupport, hpositive⟩ := hbase (ringExpChar k) P' P f b
  have hsign' (a : J') : b'.IsPos a ↔
      0 < latticePairing T' (P'.root a) (f.coweightMap ν) :=
    (hpositive a).trans ((hsign (f.indexEquiv a)).trans
      (root_pos_coweightMap_iff hP hP' f ν a).symm)
  rw [← mem_base_support_iff_simple_of_isPos hP' b' _ hsign',
    hsupport, mem_base_support_iff_simple_of_isPos hP b ν hsign]

namespace SimpleIsogenyGraph

variable {t : T ⟶ T'} (D : SimpleIsogenyGraph i i' t)

/-- The pushed source directions cover every simple root of the target
chamber once bases are transported through the root-datum isogeny. -/
theorem target_coverage_of_base_transport
    (hbase : RootDatumIsogenyBaseStatement.{u, u, u, u, u, u})
    (hP : IsRootDatumOf i P) (hP' : IsRootDatumOf i' P')
    (f : RootDatumIsogeny (ringExpChar k) P' P)
    (hw : ∀ χ : characterLattice T', f.weightMap χ = t ≫ χ) :
    ∀ α ∈ simpleRelativeRoots i' (f.coweightMap D.directions.chamber),
      ∃ a : D.SimpleIndex, latticePairing T' α (D.targetDirection a) = 0 := by
  intro α hα
  have hroot := hα.1.1
  rw [relativeRoots_eq_roots, ← hP'.2.1] at hroot
  obtain ⟨j, rfl⟩ := hroot
  have hsimple := (simple_root_coweightMap_iff hbase hP hP' f
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
once bases are transported through the prescribed root-datum isogeny. -/
theorem second_geometry_of_base_transport
    (hbase : RootDatumIsogenyBaseStatement.{u, u, u, u, u, u})
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
    (D.target_coverage_of_base_transport hbase hP hP' f hw)
    (LocalIsogenyGraphEnvelope.chamber_centralizer_eq_range hG' hT' hi' _ hgeneric)

/-- Record both projection geometries, deriving source coverage from the
graph and target coverage from base transport. -/
def faithfullyFlatGraph_of_base_transport
    (hbase : RootDatumIsogenyBaseStatement.{u, u, u, u, u, u})
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (hT' : IsSplitTorus T'.toGrp) (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    (ht : IsIsogeny (CommGroupScheme.groupHom t))
    (hP : IsRootDatumOf i P) (hP' : IsRootDatumOf i' P')
    (f : RootDatumIsogeny (ringExpChar k) P' P)
    (hw : ∀ χ : characterLattice T', f.weightMap χ = t ≫ χ) :
    FaithfullyFlatLocalIsogenyGraphEnvelope D.comparisons := by
  let : Smooth G.X.hom := hG.smooth
  exact ⟨D.envelope, D.first_geometry hG hi P hP,
    D.second_geometry_of_base_transport hbase hG' hT' hi' ht hP hP' f hw⟩

/-- Certify the actual graph as connected reductive, retaining both
faithfully flat projections and the explicit base-transport input. -/
def reductiveGraph_of_base_transport
    (hbase : RootDatumIsogenyBaseStatement.{u, u, u, u, u, u})
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (hT' : IsSplitTorus T'.toGrp) (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    (ht : IsIsogeny (CommGroupScheme.groupHom t))
    (hP : IsRootDatumOf i P) (hP' : IsRootDatumOf i' P')
    (f : RootDatumIsogeny (ringExpChar k) P' P)
    (hw : ∀ χ : characterLattice T', f.weightMap χ = t ≫ χ) :
    ReductiveLocalIsogenyGraphEnvelope D.comparisons :=
  reductiveLocalIsogenyGraphEnvelope
    (D.faithfullyFlatGraph_of_base_transport hbase hG hG' hT' hi hi' ht hP hP' f hw)
    hG hG'

end SimpleIsogenyGraph

end Langlands.GroupScheme.RootDatumIsogenyRealization
