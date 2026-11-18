import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitPositiveConstantTerm
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCentralProjection

/-! # Central invariance of the actual Levi Xi weight

The compatible split component acts through the actual minimal Levi. Its translation leaves
`rationalLeviXi` unchanged, as used in the proof of Waldspurger VI.2.3, printed p.301.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  {A : CommGroupScheme (Spec (CommRingCat.of F))} (q : A.toGrp ⟶ S.toGrp)

/-- The specified torus map sends `A(F)` to the actual minimal Levi `M₀(F)`. -/
def rationalMinimalComponentHom : rationalPoints A.toGrp →* standardLeviPoints i ν ∅ :=
  { toFun := fun x => ⟨rationalPoints.map (q ≫ i) x, map_mem_standardLeviPoints_empty q x⟩
    map_one' := Subtype.ext (map_one _)
    map_mul' := fun x y => Subtype.ext (map_mul _ x y) }

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
@[simp] theorem coe_rationalMinimalComponentHom (x : rationalPoints A.toGrp) :
    ((rationalMinimalComponentHom (i := i) (ν := ν) q x : standardLeviPoints i ν ∅) :
      rationalPoints G) = rationalPoints.map (q ≫ i) x := rfl

variable {q} (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) {J : Set (characterLattice S)}
  (hA : IsCompatibleStandardSplitComponent i ν J A q)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The inclusion of the minimal Levi agrees with the specified component map to `M_J(F)`. -/
@[simp] theorem minimalLeviInclusion_rationalMinimalComponentHom (x : rationalPoints A.toGrp) :
    minimalLeviInclusion hG hi hν J (rationalMinimalComponentHom q x) =
      standardComponentHom hA x := Subtype.ext rfl

omit [LocallyOfFiniteType G.X.hom] in
/-- The target module's component valuation is `H₀` of this actual point. -/
theorem rationalComponentH0_eq_minimalComponentHom (x : rationalPoints A.toGrp) :
    rationalComponentH0 hG hi hν (qA := q) x =
      rationalMinimalH0 hG hi hν (rationalMinimalComponentHom q x) := rfl

variable {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
  (hKc : IsCompact (K : Set (rationalPoints G))) (hJ : J ⊆ simpleRelativeRoots i ν)
  (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
    (K.subgroupOf (standardLeviPoints i ν J)))

include hG hi hν hKo hJ in
/-- A central point of `M_J(F)` lying in `P₀(F)` leaves `Ξ^{M_J}` unchanged. -/
theorem rationalLeviXi_mul_left_of_mem_center {z : standardLeviPoints i ν J}
    (hzP : (z : rationalPoints G) ∈ standardParabolicPoints i ν ∅)
    (hz : z ∈ Subgroup.center (standardLeviPoints i ν J)) (m : standardLeviPoints i ν J) :
    rationalLeviXi hKc hM (z * m) = rationalLeviXi hKc hM m := by
  have := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := J) hKc
  have hz1 : standardLeviMinimalModulusOf i ν J ⟨z, hzP⟩ = 1 := by
    rw [standardLeviMinimalModulusOf_apply]
    apply standardLeviMinimalModulus_eq_one_of_commute
    intro n hn
    exact congrArg (fun x : standardLeviPoints i ν J => (x : rationalPoints G))
      (Subgroup.mem_center_iff.mp hz ⟨n, hn⟩).symm
  exact xi_mul_left_of_eq_one
    (fun p hp => standardLeviMinimalModulusOf_eq_one hKo hKc hG hi hν hJ p hp)
    hzP hz1 (fun k _ => Subgroup.mem_center_iff.mp hz k) m

include hG hi hν hKo hJ in
/-- Right translation by a point of the compatible split component preserves the actual Levi Xi
function, with the actual compact subgroup and Iwasawa pair. -/
theorem rationalLeviXi_mul_standardComponentHom (m : standardLeviPoints i ν J)
    (x : rationalPoints A.toGrp) :
    rationalLeviXi hKc hM (m * standardComponentHom hA x) = rationalLeviXi hKc hM m := by
  rw [← standardComponentHom_commute hA x m]
  apply rationalLeviXi_mul_left_of_mem_center hG hi hν hKo hKc hJ hM
  · exact standardLevi_le_standardParabolic i ν ∅ _ (map_mem_standardLeviPoints_empty q x)
  · exact Subgroup.mem_center_iff.mpr fun n => (standardComponentHom_commute hA x n).symm

include hA hKo hJ in
/-- The Xi weight on the actual minimal Levi used in the positive-decay target is invariant under
translation by every point of the compatible split component. -/
theorem rationalLeviXi_minimal_mul_component (m : standardLeviPoints i ν ∅)
    (x : rationalPoints A.toGrp) :
    rationalLeviXi hKc hM
        (minimalLeviInclusion hG hi hν J (m * rationalMinimalComponentHom q x)) =
      rationalLeviXi hKc hM (minimalLeviInclusion hG hi hν J m) := by
  rw [map_mul, minimalLeviInclusion_rationalMinimalComponentHom hG hi hν hA]
  exact rationalLeviXi_mul_standardComponentHom hG hi hν hA hKo hKc hJ hM _ x

end Langlands.HarishChandraSchwartz
