import Langlands.GroupScheme.Rational.RankOneParabolicMinimality
import Langlands.GroupScheme.Rational.RankOneWeylImage
import Langlands.GroupScheme.Reductive.RankOneRootReducednessAssembly

/-! # Dynamic parabolics for cocharacters on a dependent root line -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Dependent characters annihilate the integral cross difference of any
two cocharacters. No primitive generator of their common line is needed. -/
theorem latticePairing_cross_difference_eq_zero_of_dependent
    (a b : characterLattice T) (hdep : ¬ LinearIndependent ℤ ![a, b])
    (ν eta : cocharacterLattice T) :
    latticePairing T b
      ((latticePairing T a ν) • eta - (latticePairing T a eta) • ν) = 0 := by
  simp only [map_sub, map_zsmul, smul_eq_mul]
  by_contra hcross
  apply hdep
  rw [LinearIndependent.pair_iff]
  intro m n hmn
  have hν : m * latticePairing T a ν + n * latticePairing T b ν = 0 := by
    simpa using congrArg (fun χ => latticePairing T χ ν) hmn
  have heta : m * latticePairing T a eta + n * latticePairing T b eta = 0 := by
    simpa using congrArg (fun χ => latticePairing T χ eta) hmn
  constructor
  · have hm : m * (latticePairing T a ν * latticePairing T b eta -
        latticePairing T a eta * latticePairing T b ν) = 0 := by
      linear_combination (latticePairing T b eta) * hν -
        (latticePairing T b ν) * heta
    exact (mul_eq_zero.mp hm).resolve_right hcross
  · have hn : n * (latticePairing T a ν * latticePairing T b eta -
        latticePairing T a eta * latticePairing T b ν) = 0 := by
      linear_combination (latticePairing T a ν) * heta -
        (latticePairing T a eta) * hν
    exact (mul_eq_zero.mp hn).resolve_right hcross

variable [IsAffineHom G.X.hom]

/-- The precise dependence hypothesis with an actual root forces
semisimple rank exactly one, measured by the rational root span. -/
theorem IsSplitTorus.finrank_relativeRootSpan_eq_one_of_rankOne
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hdep : ∀ a ∈ roots i, ∀ b ∈ roots i, ¬ LinearIndependent ℤ ![a, b])
    {a : characterLattice T} (ha : a ∈ roots i) :
    Module.finrank ℚ (relativeRootSpan i) = 1 := by
  have hneq : toRat a ≠ 0 := by
    intro h
    exact ha.1 (hT.character_toRat_injective (by simpa using h))
  rw [hT.relativeRootSpan_eq_span_singleton_of_rankOne i hdep ha,
    finrank_span_singleton hneq]

/-- Under pairwise root dependence, nonorthogonality to one root
is already regularity on the whole actual root set. -/
theorem IsSplitTorus.isRegularCocharacter_of_rankOne
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hdep : ∀ a ∈ roots i, ∀ b ∈ roots i, ¬ LinearIndependent ℤ ![a, b])
    {a : characterLattice T} (ha : a ∈ roots i) {ν : cocharacterLattice T}
    (hν : latticePairing T a ν ≠ 0) : IsRegularCocharacter i ν := by
  intro b hb
  exact hT.latticePairing_ne_zero_of_not_linearIndependent hb.1
    (hdep a ha b hb) hν

variable [Smooth G.X.hom] [ConnectedSpace G.X.left]

namespace RelativeRoot

/-- Integral cross differences are central on every test scheme when
every actual root is dependent with the chosen character. -/
theorem isCentral_cross_difference_of_dependent_relativeRoots
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (a : characterLattice T)
    (hdep : ∀ b ∈ relativeRoots i, ¬ LinearIndependent ℤ ![a, b])
    (ν eta : cocharacterLattice T) :
    IsCentral (CommGroupScheme.groupHom
      ((latticePairing T a ν) • eta - (latticePairing T a eta) • ν) ≫ i) := by
  apply rootAnnihilatorCentrality k G T hT i
  intro b hb
  exact latticePairing_cross_difference_eq_zero_of_dependent a b (hdep b hb) ν eta

/-- Positive pairings with a dependent root direction determine the same
dynamic parabolic, as an actual subgroup functor on every test scheme. -/
theorem parabolic_eq_of_dependent_pairings_pos
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (a : characterLattice T)
    (hdep : ∀ b ∈ relativeRoots i, ¬ LinearIndependent ℤ ![a, b])
    (ν eta : cocharacterLattice T)
    (hν : 0 < latticePairing T a ν) (heta : 0 < latticePairing T a eta) :
    Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) =
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hcentral :=
    isCentral_cross_difference_of_dependent_relativeRoots hT i a hdep ν eta
  have hshift := Dynamic.parabolic_add_of_isCentral i
    ((latticePairing T a eta) • ν)
    ((latticePairing T a ν) • eta - (latticePairing T a eta) • ν) hcentral
  have hadd : (latticePairing T a eta) • ν +
      ((latticePairing T a ν) • eta - (latticePairing T a eta) • ν) =
        (latticePairing T a ν) • eta := by abel
  rw [hadd, Dynamic.parabolic_zsmul T i eta hν,
    Dynamic.parabolic_zsmul T i ν heta] at hshift
  exact hshift

/-- The same comparison holds for two negative pairings. -/
theorem parabolic_eq_of_dependent_pairings_neg
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (a : characterLattice T)
    (hdep : ∀ b ∈ relativeRoots i, ¬ LinearIndependent ℤ ![a, b])
    (ν eta : cocharacterLattice T)
    (hν : latticePairing T a ν < 0) (heta : latticePairing T a eta < 0) :
    Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) =
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) := by
  apply parabolic_eq_of_dependent_pairings_pos hT i (-a)
    (fun b hb => by simpa only [LinearIndependent.pair_neg_left_iff] using hdep b hb)
    ν eta
  · simpa only [map_neg, LinearMap.neg_apply, neg_pos] using hν
  · simpa only [map_neg, LinearMap.neg_apply, neg_pos] using heta

/-- For arbitrary nonorthogonal cocharacters, the two signed dynamic
parabolics agree as an ordered pair or after interchanging the pair. -/
theorem parabolic_pair_eq_or_swap_of_dependent_pairings_ne_zero
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (a : characterLattice T)
    (hdep : ∀ b ∈ relativeRoots i, ¬ LinearIndependent ℤ ![a, b])
    (ν eta : cocharacterLattice T)
    (hν : latticePairing T a ν ≠ 0) (heta : latticePairing T a eta ≠ 0) :
    (Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) =
        Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ∧
      Dynamic.parabolic (CommGroupScheme.groupHom (-eta) ≫ i) =
        Dynamic.parabolic (CommGroupScheme.groupHom (-ν) ≫ i)) ∨
    (Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) =
        Dynamic.parabolic (CommGroupScheme.groupHom (-ν) ≫ i) ∧
      Dynamic.parabolic (CommGroupScheme.groupHom (-eta) ≫ i) =
        Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)) := by
  have hneg (μ : cocharacterLattice T) :
      latticePairing T a (-μ) = -latticePairing T a μ := map_neg _ _
  rcases lt_or_gt_of_ne hν with hν | hν <;>
    rcases lt_or_gt_of_ne heta with heta | heta
  · exact Or.inl
      ⟨parabolic_eq_of_dependent_pairings_neg hT i a hdep ν eta hν heta,
        parabolic_eq_of_dependent_pairings_pos hT i a hdep (-ν) (-eta)
          (by rw [hneg]; exact neg_pos.mpr hν)
          (by rw [hneg]; exact neg_pos.mpr heta)⟩
  · exact Or.inr
      ⟨parabolic_eq_of_dependent_pairings_pos hT i a hdep (-ν) eta
          (by rw [hneg]; exact neg_pos.mpr hν) heta,
        parabolic_eq_of_dependent_pairings_neg hT i a hdep ν (-eta) hν
          (by rw [hneg]; exact neg_neg_of_pos heta)⟩
  · exact Or.inr
      ⟨parabolic_eq_of_dependent_pairings_neg hT i a hdep (-ν) eta
          (by rw [hneg]; exact neg_neg_of_pos hν) heta,
        parabolic_eq_of_dependent_pairings_pos hT i a hdep ν (-eta) hν
          (by rw [hneg]; exact neg_pos.mpr heta)⟩
  · exact Or.inl
      ⟨parabolic_eq_of_dependent_pairings_pos hT i a hdep ν eta hν heta,
        parabolic_eq_of_dependent_pairings_neg hT i a hdep (-ν) (-eta)
          (by rw [hneg]; exact neg_neg_of_pos hν)
          (by rw [hneg]; exact neg_neg_of_pos heta)⟩

/-- Choose whether the signed dynamic parabolics agree in the same order
or after interchange, retaining the two actual subgroup-functor equalities. -/
def signedParabolicPairIdentification
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (a : characterLattice T)
    (hdep : ∀ b ∈ relativeRoots i, ¬ LinearIndependent ℤ ![a, b])
    (ν eta : cocharacterLattice T)
    (hν : latticePairing T a ν ≠ 0) (heta : latticePairing T a eta ≠ 0) :
    { swap : Bool //
      Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) =
          Dynamic.parabolic (CommGroupScheme.groupHom (if swap then -ν else ν) ≫ i) ∧
        Dynamic.parabolic (CommGroupScheme.groupHom (-eta) ≫ i) =
          Dynamic.parabolic (CommGroupScheme.groupHom (if swap then ν else -ν) ≫ i) } := by
  classical
  have h := parabolic_pair_eq_or_swap_of_dependent_pairings_ne_zero
    hT i a hdep ν eta hν heta
  exact if hsame :
      Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) =
          Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ∧
        Dynamic.parabolic (CommGroupScheme.groupHom (-eta) ≫ i) =
          Dynamic.parabolic (CommGroupScheme.groupHom (-ν) ≫ i)
    then ⟨false, by simpa using hsame⟩
    else ⟨true, by simpa using h.resolve_left hsame⟩

end RelativeRoot
end Langlands.GroupScheme
