import Langlands.Global.AdelicConstantTermSplitComponent
import Langlands.Global.AdelicPositiveTorusSplitComponentStatement
import Langlands.Global.AdelicLocalFinitenessChamberCoordinates
import Langlands.Global.AdelicLocalFinitenessComponentShifts
import Langlands.Global.AdelicLeadingCuspidalPairing

/-! # The translations of `Ξ_main` as shifts of the chamber coordinates

The translations `a_α = i(t_α)` and `z_j = i(z_j)` of the system `Ξ_main` move the chamber
coordinates of the minimal-parabolic height by the unit vectors, commute with the Levi and
normalize the unipotent radical of every standard parabolic whose index omits `α` (for `a_α`),
respectively of every standard parabolic (for `z_j`).
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Opposite Set
open scoped CategoryTheory.MonObj

namespace Langlands.Global

/-- The point `b` moves the coordinate map `c` by the vector `v`: `c(b g) = c(g) + v` for all
`g`. -/
def IsCoordinateShift {X V : Type*} [Mul X] [Add V] (c : X → V) (b : X) (v : V) : Prop :=
  ∀ g, c (b * g) = c g + v

namespace AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

private instance : IsClosedImmersion (Standard.parabolicHom i ν ∅).hom.hom.left :=
  Standard.isClosedSubgroup_parabolicHom i ν ∅

private instance : IsAffine (Standard.parabolicScheme i ν ∅).X.left :=
  isAffine_of_isAffineHom (Standard.parabolicHom i ν ∅).hom.hom.left

/-- Left translation by the image of a torus point `q` moves the coordinates `e ∘ H₀` of the
minimal-parabolic height by `e` of the logarithm of `q` in the minimal parabolic. -/
theorem isCoordinateShift_torus {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K) {V : Type*} [AddCommGroup V]
    [Module ℝ V] (e : RealCharacterDual F (Standard.parabolicScheme i ν ∅) →ₗ[ℝ] V)
    (q : AdelicGroupPoints F T.toGrp) :
    IsCoordinateShift (fun g => e (hK.height g)) (map F T.toGrp G i q)
      (e (characterLog F _ (map F T.toGrp _ (torusToStandardParabolic F G T i ν) q))) := by
  intro g
  have hq : map F T.toGrp G i q = map F _ G (Standard.parabolicHom i ν ∅)
      (map F T.toGrp _ (torusToStandardParabolic F G T i ν) q) := by
    conv_lhs => rw [← torusToStandardParabolic_comp F G T i ν]
    simp only [map_apply, GroupScheme.affinePointsTarget_apply, Grp.comp_hom_hom, Category.assoc]
  simp only
  rw [hq, hK.height_map_mul, map_add, add_comm]

end AdelicSiegelFactors

namespace StandardParabolicFamily

open Langlands.GroupScheme AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

/-- The image of a point of the positive split component of `P` commutes with every adelic point
of the standard Levi of an index `J ⊆ P`. -/
theorem commute_positiveSplitComponent_standardLevi {P : StandardIndex F G 𝓕.i 𝓕.ν}
    (a : 𝓕.positiveSplitComponent P) {J : Set (characterLattice 𝓕.T)}
    (hJ : J ⊆ simpleRelativeRoots 𝓕.i 𝓕.ν) (hJP : J ⊆ P.1) {x : AdelicGroupPoints F G}
    (hx : x ∈ AdelicSubgroupPoints.adelicPoints F G (standardLevi 𝓕.i 𝓕.ν J)) :
    Commute (map F (𝓕.P P) G (𝓕.p P) a) x := by
  have hle := (((standardParabolicOrder F G 𝓕.connectedReductive 𝓕.T 𝓕.i 𝓕.maximalSplit
    𝓕.ν 𝓕.generic).1 J P.1 hJ P.2).2 hJP).1
  have hxM : x ∈ (SubgroupFunctor.range (𝓕.l P ≫ 𝓕.p P)).carrier _ := by
    rw [(𝓕.isCompatible P).levi_eq]
    exact hle _ hx
  obtain ⟨m, hm⟩ := SubgroupFunctor.mem_range.mp hxM
  have hxm : x = map F (𝓕.M P) G (𝓕.l P ≫ 𝓕.p P) m := by
    rw [← hm]
    simp only [map_apply, GroupScheme.affinePointsTarget_apply, Grp.comp_hom_hom]
  rw [hxm]
  exact 𝓕.commute_positiveSplitComponent_levi P a m

/-- The image of a torus point normalizes `U_J(𝔸)` in both directions; if it also commutes with
`L_J(𝔸)`, it is a Levi-normalizing point for `J`. -/
theorem isLeviNormalizingPoint_torus (t : AdelicGroupPoints F 𝓕.T.toGrp)
    {J : Set (characterLattice 𝓕.T)}
    (hcomm : ∀ x ∈ AdelicSubgroupPoints.adelicPoints F G (standardLevi 𝓕.i 𝓕.ν J),
      map F 𝓕.T.toGrp G 𝓕.i t * x = x * map F 𝓕.T.toGrp G 𝓕.i t) :
    𝓕.IsLeviNormalizingPoint J (map F 𝓕.T.toGrp G 𝓕.i t) := by
  have hP : map F 𝓕.T.toGrp G 𝓕.i t ∈ (standardParabolic 𝓕.i 𝓕.ν J).carrier _ := by
    apply standardLevi_le_standardParabolic
    apply torusCentralizer_le_standardLevi
    apply range_le_torusCentralizer
    exact SubgroupFunctor.mem_range.mpr ⟨t, rfl⟩
  refine ⟨hcomm, fun w hw => ?_, fun w hw => ?_⟩
  · exact StandardLeviIntersection.conj_mem_standardUnipotent 𝓕.i 𝓕.ν hP hw
  · have hP' := (standardParabolic 𝓕.i 𝓕.ν J).carrier _ |>.inv_mem hP
    have := StandardLeviIntersection.conj_mem_standardUnipotent 𝓕.i 𝓕.ν hP' hw
    rw [inv_inv] at this
    exact this

/-- **The translations of `Ξ_main` are Levi-normalizing points.** Assume
`PositiveTorusSplitComponentStatement`. For group data of `Ξ_main` for `𝓕`, the image
`i(t_β)` commutes with `L_J(𝔸)` and normalizes `U_J(𝔸)` for every `J ⊆ Δ` not containing `β`,
and every image `i(z_j)` does so for every `J ⊆ Δ`. -/
theorem isLeviNormalizingPoint_of_groupData (hsplit : PositiveTorusSplitComponentStatement.{u})
    {Ua : simpleRelativeRoots 𝓕.i 𝓕.ν → GroupScheme (Spec (CommRingCat.of F))}
    {u : ∀ α, Ua α ⟶ G} {t : simpleRelativeRoots 𝓕.i 𝓕.ν → AdelicGroupPoints F 𝓕.T.toGrp}
    {r : ℕ} {z : Fin r → AdelicGroupPoints F 𝓕.T.toGrp}
    (hdata : IsLocalFinitenessGroupData 𝓕.i 𝓕.ν u t z) :
    (∀ (β : simpleRelativeRoots 𝓕.i 𝓕.ν) (J : Set (characterLattice 𝓕.T)),
      J ⊆ simpleRelativeRoots 𝓕.i 𝓕.ν → β.val ∉ J →
        𝓕.IsLeviNormalizingPoint J (map F 𝓕.T.toGrp G 𝓕.i (t β))) ∧
    (∀ (j : Fin r) (J : Set (characterLattice 𝓕.T)), J ⊆ simpleRelativeRoots 𝓕.i 𝓕.ν →
      𝓕.IsLeviNormalizingPoint J (map F 𝓕.T.toGrp G 𝓕.i (z j))) := by
  refine ⟨fun β J hJ hβ => ?_, fun j J hJ => ?_⟩
  · let P : StandardIndex F G 𝓕.i 𝓕.ν :=
      ⟨simpleRelativeRoots 𝓕.i 𝓕.ν \ {β.val}, sdiff_subset⟩
    obtain ⟨a, ha, hmap⟩ := hsplit F G 𝓕 P (t β) (hdata.2.1 β) fun c0 hc0 =>
      hdata.2.2.1 β ⟨c0, hc0.1⟩ fun h => hc0.2 (by rw [← h]; rfl)
    have hJP : J ⊆ P.1 := fun x hxJ =>
      ⟨hJ hxJ, fun h => hβ (by rw [mem_singleton_iff] at h; rw [← h]; exact hxJ)⟩
    refine 𝓕.isLeviNormalizingPoint_torus (t β) fun x hx => ?_
    rw [← hmap]
    exact (𝓕.commute_positiveSplitComponent_standardLevi ⟨a, ha⟩ hJ hJP hx).eq
  · obtain ⟨a, ha, hmap⟩ := hsplit F G 𝓕 𝓕.top (z j) (hdata.2.2.2.2.2.1 j) fun c0 hc0 =>
      hdata.2.2.2.2.2.2.1 j ⟨c0, hc0⟩
    refine 𝓕.isLeviNormalizingPoint_torus (z j) fun x hx => ?_
    rw [← hmap]
    exact (𝓕.commute_positiveSplitComponent_standardLevi ⟨a, ha⟩ hJ hJ hx).eq

end StandardParabolicFamily

end Langlands.Global
