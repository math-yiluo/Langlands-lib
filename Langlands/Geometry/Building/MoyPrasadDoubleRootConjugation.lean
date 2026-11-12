import Langlands.Geometry.Building.KPMoyPrasadDoubleRootStatement
import Langlands.Geometry.Building.MoyPrasadMixedConjugation
import Langlands.Geometry.Building.MoyPrasadCovarianceReduction

/-! # Mixed conjugation from double-root commutator friendliness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData.CentralizerFiltration

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {P : ParahoricBuildingData G} (Zf : P.CentralizerFiltration)

/-- The actual central coordinate of an ordinary/doubled-opposite exchange
has the full doubled input depth under double-root friendliness. -/
theorem double_opposite_central_mem_of_doubleRootCommutatorFriendly
    (hZ2 : Zf.IsDoubleRootCommutatorFriendly)
    (x : P.Apartment) {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i)
    (h2a : 2 • a ∈ relativeRoots P.i) (r : NNReal) (hr : 0 < r)
    {u v : rationalPoints G}
    (hu : u ∈ P.filtration x a 0) (hv : v ∈ P.filtration x (-(2 • a)) r)
    (v' : rationalPoints G) (hv' : v' ∈ rootGroupPoints P.i (-a))
    (z : rationalPoints P.centralizer.Z) (u' : rationalPoints G)
    (hu' : u' ∈ rootGroupPoints P.i a)
    (heq : v' * rationalPoints.map P.centralizer.j z * u' = u * v) :
    z ∈ Zf.filtration r := by
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  have hna : -a ∈ relativeRoots P.i :=
    KPApartmentData.neg_mem_relativeRoots_of_rankOne
      P.isMaximalSplitTorus.isSplitSubtorus.1
      (rootRankOneFactorization F G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus)
      x ha
  have h2na : 2 • (-a) ∈ relativeRoots P.i := by
    have hn := KPApartmentData.neg_mem_relativeRoots_of_rankOne
      P.isMaximalSplitTorus.isSplitSubtorus.1
      (rootRankOneFactorization F G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus)
      x h2a
    simpa only [smul_neg] using hn
  have hvHalf : v ∈ P.filtration x (-a) ((r : ℝ) / 2) :=
    P.apartment.filtration_double_le_half x hna h2na r
      (by simpa only [smul_neg] using hv)
  have hjinj : Function.Injective (rationalPoints.map P.centralizer.j) := by
    intro z w h
    have : Mono P.centralizer.j.hom.hom := P.centralizer.isRepresentedBy.1
    exact (cancel_mono P.centralizer.j.hom.hom).mp h
  by_cases hu1 : u = 1
  · have huniq := P.oppositeRootTripleProduct_injective ha
      (a₁ := (⟨v', hv'⟩,
        ⟨rationalPoints.map P.centralizer.j z,
          map_mem_centralizerPoints P.centralizer.isRepresentedBy z⟩, ⟨u', hu'⟩))
      (a₂ := (⟨v, hvHalf.1⟩, 1, 1)) (by simpa [hu1] using heq)
    have hzG : rationalPoints.map P.centralizer.j z = 1 :=
      congrArg (fun p : rootGroupPoints P.i (-a) × centralizerPoints P.i ×
        rootGroupPoints P.i a => (p.2.1 : rationalPoints G)) huniq
    have hz1 : z = 1 := hjinj (by simpa using hzG)
    simpa only [hz1] using (Zf.filtration r).one_mem
  by_cases hv1 : v = 1
  · have huniq := P.oppositeRootTripleProduct_injective ha
      (a₁ := (⟨v', hv'⟩,
        ⟨rationalPoints.map P.centralizer.j z,
          map_mem_centralizerPoints P.centralizer.isRepresentedBy z⟩, ⟨u', hu'⟩))
      (a₂ := (1, 1, ⟨u, hu.1⟩)) (by simpa [hv1] using heq)
    have hzG : rationalPoints.map P.centralizer.j z = 1 :=
      congrArg (fun p : rootGroupPoints P.i (-a) × centralizerPoints P.i ×
        rootGroupPoints P.i a => (p.2.1 : rationalPoints G)) huniq
    have hz1 : z = 1 := hjinj (by simpa using hzG)
    simpa only [hz1] using (Zf.filtration r).one_mem
  obtain ⟨t, ht⟩ := KPApartmentData.exists_val_eq_coe x ha hu.1 hu1
  obtain ⟨s, hs⟩ := KPApartmentData.exists_val_eq_coe x hna hvHalf.1 hv1
  have ht0 : 0 ≤ t := by
    have h := hu.2
    rwa [ht, WithTop.coe_le_coe] at h
  have hsr : (r : ℝ) / 2 ≤ s := by
    have h := hvHalf.2
    rwa [hs, WithTop.coe_le_coe] at h
  have hsum : 0 < t + s := by
    have hr' : 0 < (r : ℝ) := hr
    linarith
  let d : NNReal := ⟨t + s, hsum.le⟩
  have hd : 0 < d := hsum
  have hvalue : (((d : ℝ) : WithTop ℝ)) = x.val a u + x.val (-a) v := by
    rw [ht, hs, ← WithTop.coe_add]
    rfl
  have hvDouble : v ∈ P.doubleRootGroup (-a) := by
    change v ∈ doubleRootGroupPoints P.i (-a)
    simp only [doubleRootGroupPoints, h2na, ↓reduceIte]
    simpa only [smul_neg] using hv.1
  have hcomm : v⁻¹ * u * v * u⁻¹ =
      (v⁻¹ * v') * rationalPoints.map P.centralizer.j z * (u' * u⁻¹) := by
    calc v⁻¹ * u * v * u⁻¹ = v⁻¹ * (u * v) * u⁻¹ := by group
      _ = v⁻¹ * (v' * rationalPoints.map P.centralizer.j z * u') * u⁻¹ := by rw [heq]
      _ = (v⁻¹ * v') * rationalPoints.map P.centralizer.j z * (u' * u⁻¹) := by group
  have hzdepth : z ∈ Zf.filtration (2 * d) :=
    hZ2 x ⟨a, ha⟩ u v hu.1 hu1 hvHalf.1 hv1 (Or.inr hvDouble)
      d hd hvalue (v⁻¹ * v') (u' * u⁻¹) z
      ((rootGroupPoints P.i (-a)).mul_mem
        ((rootGroupPoints P.i (-a)).inv_mem hvHalf.1) hv')
      ((rootGroupPoints P.i a).mul_mem hu' ((rootGroupPoints P.i a).inv_mem hu.1))
      hcomm
  apply Zf.antitone (show r ≤ 2 * d from ?_) hzdepth
  apply NNReal.coe_le_coe.mp
  change (r : ℝ) ≤ 2 * (t + s)
  linarith

/-- Double-root friendliness discharges the last middle-coordinate input
for mixed doubled-opposite conjugation in the original subgroup. -/
theorem conjugate_double_opposite_mem_moyPrasad_of_doubleRootCommutatorFriendly
    (hP : P.SatisfiesApartmentAxioms) (hZ : Zf.IsCommutatorFriendly)
    (hZ2 : Zf.IsDoubleRootCommutatorFriendly)
    (x : P.Apartment) {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i)
    (h2a : 2 • a ∈ relativeRoots P.i) (r : NNReal) (hr : 0 < r)
    {u v : rationalPoints G}
    (hu : u ∈ P.filtration x a 0) (hv : v ∈ P.filtration x (-(2 • a)) r) :
    u * v * u⁻¹ ∈ Zf.moyPrasad x r :=
  Zf.conjugate_double_opposite_mem_moyPrasad_of_central_bound hP hZ x ha h2a r hr hu hv
    (Zf.double_opposite_central_mem_of_doubleRootCommutatorFriendly
      hZ2 x ha h2a r hr hu hv)

/-- Every original sharp fixer normalizes the original Moy–Prasad group
for a supplied double-root-friendly filtration. -/
theorem sharpFixer_le_normalizer_moyPrasad_of_doubleRootCommutatorFriendly
    (hP : P.SatisfiesApartmentAxioms) (hZ : Zf.IsCommutatorFriendly)
    (hZr : Zf.IsRootCompatible) (hZ2 : Zf.IsDoubleRootCommutatorFriendly)
    (x : P.Apartment) (r : NNReal) :
    P.sharpFixer {x} ≤ Subgroup.normalizer (Zf.moyPrasad x r : Set (rationalPoints G)) :=
  Zf.sharpFixer_le_normalizer_moyPrasad_of_double_opposite_bound hP hZ hZr
    (fun x r hr _a ha h2a _ _ hu hv =>
      Zf.conjugate_double_opposite_mem_moyPrasad_of_doubleRootCommutatorFriendly
        hP hZ hZ2 x ha h2a r hr hu hv) x r

/-- The actual reduced-building presentation is unique under the original
filtration axioms and the supplied double-root predicate. -/
theorem isMoyPrasadAt_unique_of_doubleRootCommutatorFriendly
    (hP : P.SatisfiesApartmentAxioms) (hZ : Zf.SatisfiesFiltrationAxioms)
    (hZ2 : Zf.IsDoubleRootCommutatorFriendly)
    (y : P.ReducedBuilding) (r : NNReal) (Q Q' : Subgroup (rationalPoints G))
    (hQ : Zf.IsMoyPrasadAt y r Q) (hQ' : Zf.IsMoyPrasadAt y r Q') : Q = Q' :=
  Zf.isMoyPrasadAt_unique_of_sharp_normalization hZ.2.1
    (Zf.sharpFixer_le_normalizer_moyPrasad_of_doubleRootCommutatorFriendly
      hP hZ.1 hZ.2.2.2 hZ2) y r Q Q' hQ hQ'

/-- The original reduced-building Moy–Prasad subgroup, with its presentation
and uniqueness certificate, for a supplied double-root-friendly filtration. -/
def moyPrasadAtUniqueOfDoubleRootCommutatorFriendly
    (hP : P.SatisfiesApartmentAxioms) (hZ : Zf.SatisfiesFiltrationAxioms)
    (hZ2 : Zf.IsDoubleRootCommutatorFriendly) (y : P.ReducedBuilding) (r : NNReal) :
    {Q : Subgroup (rationalPoints G) //
      Zf.IsMoyPrasadAt y r Q ∧
        ∀ Q', Zf.IsMoyPrasadAt y r Q' → Q' = Q} :=
  Zf.moyPrasadAtUniqueOfSharpNormalization hZ.2.1
    (Zf.sharpFixer_le_normalizer_moyPrasad_of_doubleRootCommutatorFriendly
      hP hZ.1 hZ.2.2.2 hZ2) y r

end Langlands.Geometry.Building.ParahoricBuildingData.CentralizerFiltration
