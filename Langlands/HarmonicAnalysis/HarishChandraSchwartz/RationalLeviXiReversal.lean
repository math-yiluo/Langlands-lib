import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiChangeMinimal
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalStructuralChamberReversal

/-! # Reversing the minimal parabolic inside the actual standard Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

section Transport

variable {H H' : Type*} [Group H] [Group H']

/-- Transport an Iwasawa product through a group equivalence matching its
parabolic and compact subgroups. -/
theorem IsIwasawaPair.transport {P K : Subgroup H} {Q L : Subgroup H'}
    (hPK : IsIwasawaPair P K) (e : H ≃* H')
    (hP : ∀ p : H, p ∈ P ↔ e p ∈ Q)
    (hK : ∀ k : H, k ∈ K ↔ e k ∈ L) : IsIwasawaPair Q L := by
  intro g
  obtain ⟨p, hp, k, hk, hg⟩ := hPK (e.symm g)
  refine ⟨e p, (hP p).mp hp, e k, (hK k).mp hk, ?_⟩
  simpa only [map_mul, e.apply_symm_apply] using congrArg e hg

end Transport

section Scheme

variable {F : Type u} [Field F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} {ν ξ : cocharacterLattice S} {J : Set (characterLattice S)}

/-- Every ambient generic cocharacter remains generic for the fixed standard
Levi scheme, including the reversed cocharacter. -/
theorem isGenericCocharacter_leviTorusHom_of_generic (hξ : IsGenericCocharacter i ξ) :
    haveI := leviScheme_isAffineHom i ν J
    IsGenericCocharacter (Standard.leviTorusHom i ν J) ξ := by
  have := leviScheme_isAffineHom i ν J
  exact fun α hα => hξ α (relativeRoots_subset_of_factor (Standard.isRepresentedBy_leviHom i ν J)
    _ (Standard.leviTorusHom_comp i ν J) hα)

/-- The intrinsic minimal parabolic of any ambient generic chamber is the
preimage of that chamber's ambient minimal parabolic in the fixed Levi. -/
theorem standardParabolic_leviTorusHom_empty_of_generic (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) (hξ : IsGenericCocharacter i ξ) :
    haveI := leviScheme_isAffineHom i ν J
    standardParabolic (Standard.leviTorusHom i ν J) ξ ∅ =
      (standardParabolic i ξ ∅).comap (Standard.leviHom i ν J) := by
  have := leviScheme_isAffineHom i ν J
  have hiL := Standard.isMaximalSplitTorus_leviTorusHom i ν J hi
  have hGL := standardLevi_isConnectedReductive hG i hi ν hν J hJ
  rw [standardParabolic_empty_eq_dynamic_of_generic _ ξ hGL hiL
      (isGenericCocharacter_leviTorusHom_of_generic hξ),
    standardParabolic_empty_eq_dynamic_of_generic i ξ hG hi hξ]
  simpa only [Category.assoc, Standard.leviTorusHom_comp] using
    Dynamic.parabolic_eq_comap_of_isClosedSubgroup
      (CommGroupScheme.groupHom ξ ≫ Standard.leviTorusHom i ν J)
      (Standard.leviHom i ν J) (Standard.isClosedSubgroup_leviHom i ν J)

end Scheme

section Actual

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

local instance reversalLeviAffine (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (J : Set (characterLattice S)) : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J

local instance reversalLeviFiniteType (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (J : Set (characterLattice S)) : LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J

variable {i : S.toGrp ⟶ G} {ν ξ : cocharacterLattice S} {J : Set (characterLattice S)}

/-- The actual minimal Levi modulus is the modular character of its actual
minimal parabolic, with the subspace topology. -/
theorem standardLeviMinimalModulusOf_eq_modularCharacter (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν)
    [LocallyCompactSpace ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))]
    (p : (standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J)) :
    (standardLeviMinimalModulusOf i ν J p : ℝ≥0) = Measure.modularCharacter p := by
  have := leviScheme_isAffineHom i ν J
  have := leviScheme_locallyOfFiniteType i ν J
  have hGL := standardLevi_isConnectedReductive hG i hi ν hν J hJ
  have hiL := Standard.isMaximalSplitTorus_leviTorusHom i ν J hi
  have hνL := isGenericCocharacter_leviTorusHom hν (J := J)
  have : LocallyCompactSpace (standardParabolicPoints (Standard.leviTorusHom i ν J) ν ∅) :=
    (isClosed_standardParabolicPoints_empty hGL hiL hνL).locallyCompactSpace
  have hP : ∀ x : rationalPoints (Standard.leviScheme i ν J),
      x ∈ standardParabolicPoints (Standard.leviTorusHom i ν J) ν ∅ ↔
        leviSchemePointsEquiv i ν J x ∈
          (standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J) := by
    intro x
    exact mem_standardParabolicPoints_leviTorusHom_iff hG hi hν hJ x
  let eP := subgroupContinuousMulEquiv (leviSchemePointsEquiv i ν J) hP
  let q := eP.symm p
  have hq : rationalPoints.map (Standard.leviHom i ν J) q =
      ((p : standardLeviPoints i ν J) : rationalPoints G) :=
    congrArg (fun y : (standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J) =>
      ((y : standardLeviPoints i ν J) : rationalPoints G)) (eP.apply_symm_apply p)
  have hmod := standardLeviMinimalModulus_leviHom hG hi hν hJ q
  have hδ : standardLeviMinimalModulusOf i ν J p =
      rationalMinimalModulus (Standard.leviTorusHom i ν J) ν q := by
    simpa only [hq, standardLeviMinimalModulusOf_apply] using hmod
  rw [hδ, rationalMinimalModulus_eq_modularCharacter hGL hiL hνL]
  simpa only [q, eP.apply_symm_apply] using
    (Aubert.General.modularCharacter_continuousMulEquiv eP q).symm

/-- The original intrinsic Levi scheme, read as points of the same actual
Levi subgroup with its reversed standard presentation. -/
def leviSchemePointsReversedEquiv (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    rationalPoints (Standard.leviScheme i ν J) ≃ₜ*
      standardLeviPoints i (-ν) (Neg.neg '' J) :=
  (leviSchemePointsEquiv i ν J).trans
    (subgroupContinuousMulEquiv (ContinuousMulEquiv.refl (rationalPoints G)) (fun x => by
      change x ∈ standardLeviPoints i ν J ↔ x ∈ standardLeviPoints i (-ν) (Neg.neg '' J)
      rw [standardLeviPoints_reversed hG hi hν hJ]))

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
@[simp] theorem leviSchemePointsReversedEquiv_apply_coe (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) (x : rationalPoints (Standard.leviScheme i ν J)) :
    ((leviSchemePointsReversedEquiv hG hi hν hJ x :
      standardLeviPoints i (-ν) (Neg.neg '' J)) : rationalPoints G) =
        rationalPoints.map (Standard.leviHom i ν J) x := rfl

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The reversed intrinsic and ambient minimal parabolics match under the
actual reversed-Levi point equivalence. -/
theorem mem_reversedParabolic_leviScheme_iff (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) (x : rationalPoints (Standard.leviScheme i ν J)) :
    x ∈ standardParabolicPoints (Standard.leviTorusHom i ν J) (-ν) ∅ ↔
      leviSchemePointsReversedEquiv hG hi hν hJ x ∈
        (standardParabolicPoints i (-ν) ∅).subgroupOf
          (standardLeviPoints i (-ν) (Neg.neg '' J)) := by
  change x ∈ (standardParabolic (Standard.leviTorusHom i ν J) (-ν) ∅).carrier _ ↔ _
  rw [standardParabolic_leviTorusHom_empty_of_generic hG hi hν hJ (hν.neg i ν)]
  exact SubgroupFunctor.mem_comap

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/-- Reversing the minimal parabolic preserves the supplied exact compact
Levi Iwasawa factor. -/
theorem IsIwasawaPair.reversedLevi (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) {K : Subgroup (rationalPoints G)}
    (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
      (K.subgroupOf (standardLeviPoints i ν J))) :
    IsIwasawaPair ((standardParabolicPoints i (-ν) ∅).subgroupOf
      (standardLeviPoints i (-ν) (Neg.neg '' J)))
      (K.subgroupOf (standardLeviPoints i (-ν) (Neg.neg '' J))) := by
  have := leviScheme_isAffineHom i ν J
  have := leviScheme_locallyOfFiniteType i ν J
  have hGL := standardLevi_isConnectedReductive hG i hi ν hν J hJ
  have hiL := Standard.isMaximalSplitTorus_leviTorusHom i ν J hi
  have hνL := isGenericCocharacter_leviTorusHom hν (J := J)
  have hPK := isIwasawaPair_leviSchemeCompact hG hi hν hJ hM
  have hQK := IsIwasawaPair.rationalChangeMinimal hGL hiL hνL
    (hνL.neg (Standard.leviTorusHom i ν J) ν) hPK
  exact hQK.transport (leviSchemePointsReversedEquiv hG hi hν hJ).toMulEquiv
    (mem_reversedParabolic_leviScheme_iff hG hi hν hJ) (fun _ => Iff.rfl)

/-- The reversed intrinsic spherical integral is exactly the actual
reversed Levi integral, with the same compact and normalized Haar measure. -/
theorem rationalXi_leviScheme_reversed (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν)
    {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
    (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints (Standard.leviTorusHom i ν J) (-ν) ∅)
      (leviSchemeCompact K i ν J))
    (hM : IsIwasawaPair ((standardParabolicPoints i (-ν) ∅).subgroupOf
      (standardLeviPoints i (-ν) (Neg.neg '' J)))
      (K.subgroupOf (standardLeviPoints i (-ν) (Neg.neg '' J))))
    (x : rationalPoints (Standard.leviScheme i ν J)) :
    rationalXi (isCompact_leviSchemeCompact hKc) hPK x =
      rationalLeviXi hKc hM (leviSchemePointsReversedEquiv hG hi hν hJ x) := by
  have := leviScheme_isAffineHom i ν J
  have := leviScheme_locallyOfFiniteType i ν J
  have hGL := standardLevi_isConnectedReductive hG i hi ν hν J hJ
  have hiL := Standard.isMaximalSplitTorus_leviTorusHom i ν J hi
  have hνL := isGenericCocharacter_leviTorusHom hν (J := J)
  have hneg : IsGenericCocharacter i (-ν) := hν.neg i ν
  have hnegL := hνL.neg (Standard.leviTorusHom i ν J) ν
  have hJneg : Neg.neg '' J ⊆ simpleRelativeRoots i (-ν) := by
    rintro _ ⟨α, hα, rfl⟩
    exact neg_mem_simpleRelativeRoots i ν (relativeRootNegation F G hG S i hi) (hJ hα)
  have : LocallyCompactSpace
      (standardParabolicPoints (Standard.leviTorusHom i ν J) (-ν) ∅) :=
    (isClosed_standardParabolicPoints_empty hGL hiL hnegL).locallyCompactSpace
  have : LocallyCompactSpace (standardLeviPoints i (-ν) (Neg.neg '' J)) :=
    (isClosed_standardLeviPoints i (-ν) (Neg.neg '' J)).locallyCompactSpace
  have : LocallyCompactSpace ((standardParabolicPoints i (-ν) ∅).subgroupOf
      (standardLeviPoints i (-ν) (Neg.neg '' J))) :=
    ((isClosed_standardParabolicPoints_empty hG hi hneg).preimage
      (continuous_subtype_val : Continuous
        (Subtype.val : standardLeviPoints i (-ν) (Neg.neg '' J) → rationalPoints G))).locallyCompactSpace
  have := compactSpace_leviSchemeCompact (i := i) (ν := ν) (J := J) hKc
  have := compactSpace_subgroupOf_standardLevi
    (i := i) (ν := -ν) (J := Neg.neg '' J) hKc
  let e := leviSchemePointsReversedEquiv hG hi hν hJ
  have hP := mem_reversedParabolic_leviScheme_iff hG hi hν hJ
  let eP := subgroupContinuousMulEquiv e hP
  have hchar : ∀ p : standardParabolicPoints (Standard.leviTorusHom i ν J) (-ν) ∅,
      standardLeviMinimalModulusOf i (-ν) (Neg.neg '' J) ⟨e p, (hP p).mp p.2⟩ =
        rationalMinimalModulus (Standard.leviTorusHom i ν J) (-ν) p := by
    intro p
    apply Units.ext
    rw [standardLeviMinimalModulusOf_eq_modularCharacter hG hi hneg hJneg,
      rationalMinimalModulus_eq_modularCharacter hGL hiL hnegL]
    exact Aubert.General.modularCharacter_continuousMulEquiv eP p
  unfold rationalXi rationalLeviXi
  exact (xi_map (hPK := hPK) (hPK' := hM) e
    (fun p hp => standardLeviMinimalModulusOf_eq_one hKo hKc hG hi hneg hJneg p hp)
    (fun p hp => (hP p).mp hp) (fun _ => Iff.rfl) hchar x).symm

/-- Reversal leaves the actual Levi spherical function unchanged at the
same ambient point. Both presentations use the exact same compact subgroup. -/
theorem rationalLeviXi_reversed (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν)
    {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
    (hKc : IsCompact (K : Set (rationalPoints G)))
    (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
      (K.subgroupOf (standardLeviPoints i ν J)))
    (hMr : IsIwasawaPair ((standardParabolicPoints i (-ν) ∅).subgroupOf
      (standardLeviPoints i (-ν) (Neg.neg '' J)))
      (K.subgroupOf (standardLeviPoints i (-ν) (Neg.neg '' J))))
    (m : standardLeviPoints i ν J) (n : standardLeviPoints i (-ν) (Neg.neg '' J))
    (hmn : (m : rationalPoints G) = n) :
    rationalLeviXi hKc hMr n = rationalLeviXi hKc hM m := by
  have := leviScheme_isAffineHom i ν J
  have := leviScheme_locallyOfFiniteType i ν J
  have hGL := standardLevi_isConnectedReductive hG i hi ν hν J hJ
  have hiL := Standard.isMaximalSplitTorus_leviTorusHom i ν J hi
  have hνL := isGenericCocharacter_leviTorusHom hν (J := J)
  have hPK := isIwasawaPair_leviSchemeCompact hG hi hν hJ hM
  have hQK := IsIwasawaPair.rationalChangeMinimal hGL hiL hνL
    (hνL.neg (Standard.leviTorusHom i ν J) ν) hPK
  let x := (leviSchemePointsEquiv i ν J).symm m
  have hxn : leviSchemePointsReversedEquiv hG hi hν hJ x = n := by
    apply Subtype.ext
    change rationalPoints.map (Standard.leviHom i ν J) x = (n : rationalPoints G)
    simpa only [x, map_leviSchemePointsEquiv_symm] using hmn
  have hchange := rationalXi_changeMinimal hGL hiL hνL
    (hνL.neg (Standard.leviTorusHom i ν J) ν)
    (isOpen_leviSchemeCompact hKo) (isCompact_leviSchemeCompact hKc) hPK hQK x
  rw [rationalXi_leviScheme_reversed hG hi hν hJ hKo hKc hQK hMr, hxn,
    rationalXi_leviScheme hG hi hν hJ hKo hKc hM,
    ContinuousMulEquiv.apply_symm_apply] at hchange
  exact hchange

end Actual

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

/-- The supplied actual Levi Iwasawa compact and its spherical function are
preserved under simultaneous chamber and face reversal. -/
def RationalLeviXiReversalStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ J : Set (characterLattice S), J ⊆ simpleRelativeRoots i ν →
    ∀ K : Subgroup (rationalPoints G), IsOpen (K : Set (rationalPoints G)) →
    ∀ (hKc : IsCompact (K : Set (rationalPoints G)))
      (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
        (K.subgroupOf (standardLeviPoints i ν J))),
    ∃ hMr : IsIwasawaPair ((standardParabolicPoints i (-ν) ∅).subgroupOf
        (standardLeviPoints i (-ν) (Neg.neg '' J)))
        (K.subgroupOf (standardLeviPoints i (-ν) (Neg.neg '' J))),
      ∀ (m : standardLeviPoints i ν J) (n : standardLeviPoints i (-ν) (Neg.neg '' J)),
        (m : rationalPoints G) = n → rationalLeviXi hKc hMr n = rationalLeviXi hKc hM m

/-- Exact spherical-function and Iwasawa reversal inside the actual Levi. -/
theorem rationalLeviXiReversal : RationalLeviXiReversalStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν J hJ K hKo hKc hM
  refine ⟨IsIwasawaPair.reversedLevi hG hi hν hJ hM, ?_⟩
  exact rationalLeviXi_reversed hG hi hν hJ hKo hKc hM _

end Langlands.HarishChandraSchwartz
