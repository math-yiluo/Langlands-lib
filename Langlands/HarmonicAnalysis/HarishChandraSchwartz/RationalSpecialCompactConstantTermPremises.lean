import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConstantTerm
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviScheme
import Langlands.Representation.Aubert.General.RationalPositiveCartanCoverProof
import Langlands.Representation.Aubert.General.RationalCartanLatticeModel
import Langlands.BruhatTits.SpecialCompact.JointBasisStatement

/-! # Structural premises of Proposition II.4.5 at the joint special compact subgroup

The published `RationalConstantTermEstimateStatement` (Waldspurger II.4.5 on actual points)
takes a compact open `K0` with Renard's simultaneous basis, the finite Cartan covering of `G(F)`
and the finite Cartan covering of every standard Levi `M_J(F)`, and a compact open `K` with the
Iwasawa decompositions `G(F) = P₀(F) K` and `M_J(F) = (P₀(F) ∩ M_J(F))(K ∩ M_J(F))`. This module
derives all of these premises, with `K = K0`, from the conjuncts of the published
`JointSpecialCompactBasisExistenceStatement`:

* `standardLeviCartanCovering_of_compatibility`: the standard-Levi compatibility of the
  special compact subgroup gives `StandardLeviCartanCovering` for every `J ⊆ Δ`;
* `isIwasawaPair_standardLevi_of_leviProducts`: the actual parabolic product family of the
  Levi scheme at `K0 ∩ M_J` gives the Levi Iwasawa factorization;
* `exists_constantTermPremises_of_joint`: one compact open `K0` with all premises.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.Cartan
open Langlands.Plancherel.RenardCartan Langlands.BruhatTits.SpecialCompact
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

section LeviCover

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G Z : GroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (D : KPApartmentData i (localFieldOrder F)) (x : D.Apartment)
  (ν : cocharacterLattice S) {j : Z ⟶ G} {s : S.toGrp ⟶ Z}
  {h : Function.Bijective (restrictionEvaluation s)}

/-- **Finite Cartan covering of a standard Levi at the special compact subgroup.** If the
torus centralizer is represented by `j` with `s ≫ j = i`, the standard-Levi compatibility of
`K₀ = D.specialCompactSubgroup x` gives, for every `J ⊆ Δ`, a finite set `F₀` of centralizer
points with `M_J(F) = ⋃_{f ∈ F₀} (K₀ ∩ M_J(F)) f C_A^+(J) (K₀ ∩ M_J(F))`. -/
theorem standardLeviCartanCovering_of_compatibility
    (hrep : (torusCentralizer i).IsRepresentedBy j) (hsj : s ≫ j = i)
    (hcompat : SpecialCompactStandardLeviCompatibility D x ν s h j)
    {J : Set (characterLattice S)} (hJ : J ⊆ simpleRelativeRoots i ν) :
    StandardLeviCartanCovering F i ν J (D.specialCompactSubgroup x) := by
  classical
  have : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
    (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
  obtain ⟨jM, -, -, hjM, -, -, hc, hlat⟩ := hcompat J hJ
  let emb : rationalPoints Z → centralizerPoints i := fun z =>
    ⟨rationalPoints.map j z, by
      rw [← torusCentralizer_carrier_base]
      exact (hrep.pointsEquiv (Over.mk (𝟙 _)) z).property⟩
  obtain ⟨Fcover, hFcover⟩ := hlat.2.2.2.2.2.1
  refine ⟨hFcover.1.toFinset.image emb, fun m hm => ?_⟩
  obtain ⟨m', hm'⟩ := (Standard.leviPointsEquiv i ν J).surjective ⟨m, hm⟩
  have hm'v : rationalPoints.map (Standard.leviHom i ν J) m' = m := congrArg Subtype.val hm'
  obtain ⟨z, hz⟩ := hc.1 m'
  obtain ⟨t, ht, htz⟩ := hFcover.2.2.2
    (show (Langlands.Plancherel.rationalCharacterValuation Z).rangeRestrict z.val ∈
      (Langlands.Plancherel.rationalCharacterValuation Z).rangeRestrict ''
        dominantCentralizer (Standard.leviTorusHom i ν J) ν s h from ⟨z.val, z.property, rfl⟩)
  have htdom := hFcover.2.2.1 ht
  have hvalue : DoubleCoset.mk (D.specialCompactLeviSubgroup ν J x)
      (D.specialCompactLeviSubgroup ν J x) (rationalPoints.map jM t) =
        DoubleCoset.mk (D.specialCompactLeviSubgroup ν J x)
          (D.specialCompactLeviSubgroup ν J x) (rationalPoints.map jM z.val) := by
    rw [hc.2 ⟨t, htdom⟩ z, ← Langlands.Plancherel.rationalCharacterValuation_ker,
      ← div_eq_mul_inv, MonoidHom.div_mem_ker_iff, eq_comm]
    exact congrArg Subtype.val htz
  obtain ⟨k₁, hk₁, k₂, hk₂, hg⟩ := DoubleCoset.eq.mp (hvalue.trans hz)
  obtain ⟨c, hcC, f, hf, rfl⟩ := ht
  obtain ⟨cchar, hcchar, rfl⟩ :=
    (mem_C0Plus S s (positiveRelativeRoots (Standard.leviTorusHom i ν J) ν) c).mp hcC
  let a := uniformizerSection S (Multiplicative.ofAdd cchar)
  have ha : a ∈ CocharacterUniformizer.CAplus F S J := by
    refine ⟨⟨Multiplicative.ofAdd cchar, rfl⟩, fun α hα => ?_⟩
    change CocharacterUniformizer.characterNorm F S α
      (CocharacterUniformizer.latticeSection F S (Multiplicative.ofAdd cchar)) ≤ 1
    rw [CocharacterUniformizer.characterNorm_latticeSection]
    have hq : (1 : ℝ) < LocalField.residueCardinality F := by
      exact_mod_cast LocalField.residueCardinality_gt_one F
    exact (zpow_le_one_iff_right₀ hq).mpr
      (neg_nonpos.mpr (hcchar α
        (Langlands.Aubert.General.mem_positiveRelativeRoots_leviTorusHom i ν hJ hα)))
  have hcomm : Commute (rationalPoints.map j f) (rationalPoints.map i a) := by
    have hfcentral := (hrep.pointsEquiv (Over.mk (𝟙 _)) f).property
    have hcm := hfcentral (Over.mk (𝟙 _)) (𝟙 _) a
    simpa only [SubgroupFunctor.IsRepresentedBy.pointsEquiv_apply_coe, Category.id_comp,
      rationalPoints.map_apply] using hcm
  have hmapj : ∀ y : rationalPoints Z,
      rationalPoints.map (Standard.leviHom i ν J) (rationalPoints.map jM y) =
        rationalPoints.map j y := by
    intro y
    rw [← hjM, Aubert.General.RationalPointFamily.rationalPoints_map_comp_apply]
  have hmap : rationalPoints.map j (rationalPoints.map s a) = rationalPoints.map i a := by
    rw [← Aubert.General.RationalPointFamily.rationalPoints_map_comp_apply, hsj]
  refine ⟨rationalPoints.map (Standard.leviHom i ν J) k₁,
    rationalPoints.map (Standard.leviHom i ν J) k₂, emb f, a,
    ⟨hk₁, (Standard.leviPointsEquiv i ν J k₁).property⟩,
    ⟨hk₂, (Standard.leviPointsEquiv i ν J k₂).property⟩,
    Finset.mem_image.mpr ⟨f, hFcover.1.mem_toFinset.mpr hf, rfl⟩, ha, ?_⟩
  change m = rationalPoints.map (Standard.leviHom i ν J) k₁ * rationalPoints.map j f *
    rationalPoints.map i a * rationalPoints.map (Standard.leviHom i ν J) k₂
  calc
    m = rationalPoints.map (Standard.leviHom i ν J) m' := hm'v.symm
    _ = rationalPoints.map (Standard.leviHom i ν J) k₁ *
        (rationalPoints.map j (rationalPoints.map s a) * rationalPoints.map j f) *
          rationalPoints.map (Standard.leviHom i ν J) k₂ := by
      rw [hg]
      simp only [map_mul, hmapj]
      rfl
    _ = rationalPoints.map (Standard.leviHom i ν J) k₁ *
        (rationalPoints.map i a * rationalPoints.map j f) *
          rationalPoints.map (Standard.leviHom i ν J) k₂ := by rw [hmap]
    _ = rationalPoints.map (Standard.leviHom i ν J) k₁ * rationalPoints.map j f *
        rationalPoints.map i a * rationalPoints.map (Standard.leviHom i ν J) k₂ := by
      rw [← hcomm.eq]
      simp only [mul_assoc]

end LeviCover

section LeviIwasawa

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {J : Set (characterLattice S)}

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- **Levi Iwasawa factorization from the Levi parabolic products.** If the actual parabolic
product family of the Levi scheme `L = M_J` holds at `j⁻¹(K)`, then
`M_J(F) = (P₀(F) ∩ M_J(F))(K ∩ M_J(F))`. -/
theorem isIwasawaPair_standardLevi_of_leviProducts (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) {K : Subgroup (rationalPoints G)}
    (hP : haveI : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
        (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
      BruhatTits.Iwasawa.ParabolicPointProductFamily (Standard.leviTorusHom i ν J) ν
        (leviSchemeCompact K i ν J)) :
    IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
      (K.subgroupOf (standardLeviPoints i ν J)) := by
  have : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
    (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
  have hL : IsIwasawaPair (standardParabolicPoints (Standard.leviTorusHom i ν J) ν ∅)
      (leviSchemeCompact K i ν J) :=
    isIwasawaPair_of_pointProductEqualities (hP.2.2.1 ∅ (Set.empty_subset _))
  intro m
  obtain ⟨p, hp, k, hk, hx⟩ := hL ((leviSchemePointsEquiv i ν J).symm m)
  refine ⟨leviSchemePointsEquiv i ν J p, ?_, leviSchemePointsEquiv i ν J k, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf, leviSchemePointsEquiv_coe]
    exact (mem_standardParabolicPoints_leviTorusHom_iff hG hi hν hJ p).1 hp
  · exact (mem_leviSchemeCompact_iff k).1 hk
  · rw [← map_mul, ← hx, ContinuousMulEquiv.apply_symm_apply]

end LeviIwasawa

section Package

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

/-- **All structural premises of Proposition II.4.5 at one compact open subgroup.** Under
`JointSpecialCompactBasisExistenceStatement`, there is a compact open `K0` with
`G(F) = P₀(F) K0`, Renard's simultaneous basis, the finite Cartan covering of `G(F)`, and for
every `J ⊆ Δ` the finite Cartan covering of `M_J(F)` and
`M_J(F) = (P₀(F) ∩ M_J(F))(K0 ∩ M_J(F))`. -/
theorem exists_constantTermPremises_of_joint
    (hJoint : JointSpecialCompactBasisExistenceStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν) :
    ∃ K0 : Subgroup (rationalPoints G), IsOpen (K0 : Set (rationalPoints G)) ∧
      IsCompact (K0 : Set (rationalPoints G)) ∧
      IsIwasawaPair (standardParabolicPoints i ν ∅) K0 ∧
      SimultaneousStandardBasisAt i ν K0 ∧
      Aubert.General.RationalPointFamily.FiniteCartanCovering F i ν K0 ∧
      ∀ J : Set (characterLattice S), J ⊆ simpleRelativeRoots i ν →
        StandardLeviCartanCovering F i ν J K0 ∧
          IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
            (K0.subgroupOf (standardLeviPoints i ν J)) := by
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  obtain ⟨D, x, Z, j, s, -, hrep, hsj, h, -, hsc, -, hP, hcomp, hLeviP, hcompat, hbasis⟩ :=
    hJoint F G hG S i hi ν hν
  refine ⟨D.specialCompactSubgroup x, hsc.2.1.2.1, hsc.2.1.1,
    isIwasawaPair_of_pointProductEqualities (hP.2.2.1 ∅ (Set.empty_subset _)), hbasis,
    Aubert.General.RationalPointFamily.rationalPositiveCartanCover F G S i ν D x Z j s h
      hrep hsj hcomp,
    fun J hJ => ⟨standardLeviCartanCovering_of_compatibility D x ν hrep hsj hcompat hJ,
      isIwasawaPair_standardLevi_of_leviProducts hG hi hν hJ (hLeviP J hJ)⟩⟩

end Package

end Langlands.HarishChandraSchwartz
