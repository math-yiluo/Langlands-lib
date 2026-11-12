import Langlands.Representation.Exponents.ArbitraryParabolicCasselmanStatement
import Langlands.BruhatTits.Unipotent.CocharacterContraction
import Langlands.Representation.CuspidalSupport.RationalNormKernelPositiveGenerators
import Langlands.Representation.Exponents.CasselmanStandardPresentationConstruction
import Langlands.Representation.Exponents.CasselmanStandardTorusTests
import Langlands.Representation.Aubert.General.RationalSquareIntegrabilityReductionProof
import Langlands.Representation.Aubert.General.RepresentedStandardCuspidality
import Langlands.Representation.Aubert.General.StandardFamilyStructure
import Langlands.Representation.Plancherel.SplitTorusCompactKernel
import Langlands.GroupScheme.Rational.GenericMinimalParabolicProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.CocharacterCentralizerPointDetection
import Langlands.Geometry.Building.CocharacterUniformizerProof

/-! # Sufficiency in Casselman's criterion from the strict-chamber statement

The selected simple roots have valuation one on every torus point that is central
in the standard Levi. With this law, the sufficiency half of Casselman's criterion
for represented parabolics follows from the published strict Jacquet
square-integrability statement, hence from the joint special-compact basis
statement.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Filter Topology
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.DynamicUnipotentContainment

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [IsAffineHom G.X.hom] in
/-- The image of a cocharacter point of the torus is the cocharacter point of the
composite cocharacter. -/
theorem map_cocharacterPoints (i : T.toGrp ⟶ G) (c : cocharacterLattice T) (t : kˣ) :
    rationalPoints.map i (CocharacterUniformizer.cocharacterPoints k T c t) =
      cocharPoint (CommGroupScheme.groupHom c ≫ i) t := by
  rw [cocharPoint_eq]
  simp only [CocharacterUniformizer.cocharacterPoints, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]

/-- A torus point commuting with a nonidentity point of the root subgroup of `α`
cannot differ from the uniformizer point of a cocharacter `c` with `⟨α, c⟩ > 0`
by an element of the norm kernel. -/
theorem latticePairing_nonpos_of_commute_rootPoint [Smooth G.X.hom]
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (α : characterLattice T)
    (x : rationalPoints G) (hx : x ∈ (RelativeRoot.subgroup i α).carrier (Over.mk (𝟙 _)))
    (hx1 : x ≠ 1) (t : rationalPoints T.toGrp)
    (htx : Commute (rationalPoints.map i t) x) (c : cocharacterLattice T)
    (hc : t * (CocharacterUniformizer.latticeSection k T (Multiplicative.ofAdd c))⁻¹ ∈
      Plancherel.rationalCommonNormKernel T.toGrp) :
    latticePairing T α c ≤ 0 := by
  by_contra hpos
  push Not at hpos
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  have : IsAffine T.X.left := isAffine_of_isAffineHom T.X.hom
  have : Smooth T.X.hom := hT.smooth
  have hk2 : T2Space k := Langlands.HarmonicAnalysis.GeneralLocalField.t2Space k
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology k G.X
  let : TopologicalSpace (rationalPoints T.toGrp) := rationalPointTopology k T.X
  have : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup k G
  have : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  let K0 := Plancherel.rationalCommonNormKernel T.toGrp
  have hK0 : IsCompact (K0 : Set (rationalPoints T.toGrp)) :=
    Plancherel.SplitTorus.isCompact_commonNormKernel hT
  let f : rationalPoints T.toGrp → rationalPoints G := fun s =>
    rationalPoints.map i s * x * (rationalPoints.map i s)⁻¹
  have hmapc : Continuous (fun s : rationalPoints T.toGrp => rationalPoints.map i s) :=
    (continuous_rationalPointMap k (X := T.X) (Y := G.X) i.hom.hom).congr
      (fun s => (rationalPoints.map_apply i s).symm)
  have hf : Continuous f := (hmapc.mul continuous_const).mul hmapc.inv
  let C : Set (rationalPoints G) := f '' (K0 : Set (rationalPoints T.toGrp))
  have hC : IsClosed C := (hK0.image hf).isClosed
  have h1C : (1 : rationalPoints G) ∉ C := by
    rintro ⟨s, -, hs⟩
    apply hx1
    have e : x = (rationalPoints.map i s)⁻¹ * f s * rationalPoints.map i s := by
      dsimp only [f]
      group
    rw [e, hs]
    group
  -- the root point lies in the radical of the cocharacter
  let ϖ := SplitTorusValuation.uniformizerUnit k
  let χc := CommGroupScheme.groupHom c ≫ i
  have hxU : x ∈ unipotentPoints χc :=
    RelativeRoot.subgroup_le_dynamicUnipotent i c hpos _ hx
  obtain ⟨n, hn⟩ := (eventually_cocharPoint_pow_conj_mem_ambient χc ϖ
    (SplitTorusValuation.tendsto_uniformizerUnit_pow_zero k) {x} isCompact_singleton
    (Set.singleton_subset_iff.mpr hxU) Cᶜ (hC.isOpen_compl.mem_nhds h1C)).exists
  apply hn x rfl
  -- the conjugate by the cocharacter power is a conjugate by a norm-kernel point
  let L := CocharacterUniformizer.latticeSection k T (Multiplicative.ofAdd c)
  let s0 := t * L⁻¹
  have hL : L = s0⁻¹ * t := by
    dsimp only [s0]
    group
  have hb : cocharPoint χc ϖ = rationalPoints.map i L := (map_cocharacterPoints i c ϖ).symm
  refine ⟨s0⁻¹ ^ n, K0.pow_mem (K0.inv_mem hc) n, ?_⟩
  have htn : Commute (rationalPoints.map i t ^ n) x := htx.pow_left n
  have hpow : cocharPoint χc ϖ ^ n =
      rationalPoints.map i (s0⁻¹ ^ n) * rationalPoints.map i t ^ n := by
    rw [hb, hL, ← map_pow, ← map_pow, ← map_mul, mul_pow]
  rw [hpow]
  change rationalPoints.map i (s0⁻¹ ^ n) * x * (rationalPoints.map i (s0⁻¹ ^ n))⁻¹ = _
  rw [mul_assoc (rationalPoints.map i (s0⁻¹ ^ n)) _ x, htn.eq]
  group

/-- **Selected-root valuation law.** At a torus point central in a standard Levi,
the values of the Levi's simple roots have valuation one. -/
theorem simpleRootPointValue_valuation_eq_one_of_leviCenter
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (I : Finset (SimpleRoot i ν)) (t : rationalPoints T.toGrp)
    (z : Subgroup.center (levi i ν I))
    (hz : ((z : levi i ν I) : rationalPoints G) = rationalPoints.map i t)
    (α : SimpleRoot i ν) (hα : α ∈ I) :
    ValuativeRel.valuation k (simpleRootPointValue i ν α t : k) = 1 := by
  have := hG.smooth
  have hT : IsSplitTorus T.toGrp := hi.isSplitSubtorus.1
  have hαroot : (α : characterLattice T) ∈ relativeRoots i := α.property.1.1
  obtain ⟨x, hx, hx1⟩ := RelativeRoot.exists_rootPoint_actual hT i hαroot
  -- the root point lies in the standard Levi
  have hxL : x ∈ levi i ν I := by
    rw [mem_levi_iff]
    intro zeta hzeta
    exact RelativeRoot.subgroup_le_dynamicCentralizer_of_pairing_eq_zero i α zeta
      (hzeta.2.1 α ⟨α, hα, rfl⟩) _ hx
  have htx : Commute (rationalPoints.map i t) x := by
    have h := Subgroup.mem_center_iff.mp z.property ⟨x, hxL⟩
    have h' := congrArg Subtype.val h
    rw [← hz]
    exact h'.symm
  obtain ⟨c, hc, -⟩ := (CocharacterUniformizer.isUniformizerLatticeSection k T hT).2.2 t
  have h1 := latticePairing_nonpos_of_commute_rootPoint hT i α x hx hx1 t htx c.toAdd
    (by simpa only [ofAdd_toAdd] using hc)
  have h2 : latticePairing T α (-c.toAdd) ≤ 0 := by
    apply latticePairing_nonpos_of_commute_rootPoint hT i α x hx hx1 t⁻¹
      (by rw [map_inv]; exact htx.inv_left) (-c.toAdd)
    have e : t⁻¹ * (CocharacterUniformizer.latticeSection k T
        (Multiplicative.ofAdd (-c.toAdd)))⁻¹ =
        (t * (CocharacterUniformizer.latticeSection k T c)⁻¹)⁻¹ := by
      rw [ofAdd_neg, ofAdd_toAdd, map_inv, inv_inv, mul_inv_rev, inv_inv]
      exact mul_comm _ _
    rw [e]
    exact (Plancherel.rationalCommonNormKernel T.toGrp).inv_mem hc
  rw [map_neg] at h2
  have hzero : latticePairing T α c.toAdd = 0 := by
    have := LinearMap.neg_apply (latticePairing T α) c.toAdd
    omega
  -- the integer order of the root value vanishes
  let αc := (rationalCharacters.equivCharacterLattice T).symm α.val
  have hord : (Plancherel.rationalCharacterValuation T.toGrp t).toAdd αc = 0 := by
    have hK := (Plancherel.mem_rationalCommonNormKernel_iff_valuation (G := T.toGrp) _).mp hc αc
    have hsec := (CocharacterUniformizer.isUniformizerLatticeSection k T hT).2.1 c.toAdd α.val
    rw [ofAdd_toAdd] at hsec
    have e : t = (t * (CocharacterUniformizer.latticeSection k T c)⁻¹) *
        CocharacterUniformizer.latticeSection k T c := by group
    rw [e, map_mul, toAdd_mul, AddMonoidHom.add_apply, hK, hsec, hzero, add_zero]
  have hn := (Plancherel.rationalCharacterValuation_nonneg_iff t αc).mp hord.ge
  have hp : ¬ ValuativeRel.valuation k (rationalCharacterEval αc t : k) < 1 := by
    rw [← Plancherel.rationalCharacterValuation_pos_iff, hord]
    exact lt_irrefl 0
  exact le_antisymm hn (not_lt.mp hp)

/-- The selected-root valuation law used by the sufficiency assembly: at every torus
point whose image is central in a standard Levi `M_I`, every simple root in `I`
takes a value of valuation one. -/
def HasSelectedRootValuationLaw (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) : Prop :=
  ∀ (I : Finset (SimpleRoot i ν)) (t : rationalPoints T.toGrp)
    (z : Subgroup.center (levi i ν I)),
    ((z : levi i ν I) : rationalPoints G) = rationalPoints.map i t →
      ∀ α ∈ I, ValuativeRel.valuation k (simpleRootPointValue i ν α t : k) = 1

/-- The selected-root valuation law holds for every maximal split torus of a
connected reductive group. -/
theorem hasSelectedRootValuationLaw (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) :
    HasSelectedRootValuationLaw i ν :=
  fun I t z hz α hα =>
    simpleRootPointValue_valuation_eq_one_of_leviCenter hG i hi ν I t z hz α hα

end Langlands.Aubert.General.RationalPointFamily

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- The sufficiency half of Renard VII.1.2 for represented parabolics: an admissible
representation with a unitary central character whose normalized Jacquet exponents
at every represented parabolic with a compatible root presentation have normalized
real part in the strictly positive root cone is square integrable modulo the center. -/
def ArbitraryParabolicCasselmanSufficiencyStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI := hG.smooth
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      [MeasurableSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
      [BorelSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
      (haar : MeasureTheory.Measure (rationalPoints G ⧸ Subgroup.center (rationalPoints G)))
      [haar.IsHaarMeasure] (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
      π.IsAdmissible → Nonempty (UnitaryCentralCharacter π.representation) →
        (∀ (P M U : GroupScheme (Spec (CommRingCat.of k)))
            (A : CommGroupScheme (Spec (CommRingCat.of k)))
            (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (a : A.toGrp ⟶ M)
            (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
            (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
            (hmul : IsIso (subgroupMultiplication l r)) (ha : IsSplitComponent a)
            (pres : ParabolicRootPresentation p l a) (χ : rationalPoints A.toGrp →* ℂˣ),
            IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ →
              Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ∈
                pres.positiveCone) →
          IsSquareIntegrableModCenter π.representation haar

/-- **Sufficiency from the strict-chamber statement.** The published strict Jacquet
square-integrability statement implies the sufficiency half of the criterion. -/
theorem arbitraryParabolicCasselmanSufficiency_of_strictJacquet
    (hsq : RationalPointFamily.RationalStrictJacquetSquareIntegrabilityStatement.{u, v}) :
    ArbitraryParabolicCasselmanSufficiencyStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ _ _ haar _ π hπ hc hcone
  obtain ⟨T, i, ν, hi, hν⟩ :=
    RationalPointFamily.exists_maximalSplitTorus_genericCocharacter hG
  have hgeom := fun I =>
    standard_representatives_geometric_of_standardCocharacter i ν standardCocharacter
      hG hi hν I
  let D : ∀ I, StandardCasselmanPresentation i ν I := fun I =>
    standardCasselmanPresentationOfGeometry hG i hi ν hν standardCocharacter
      (genericMinimalParabolic k G hG T i hi ν hν) I (hgeom I).1 (hgeom I).2.1
      (hgeom I).2.2.1 (hgeom I).2.2.2
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact squareIntegrableModCenter_of_positiveRepresented hG hsq i hi ν hν
    standardCocharacter
    (fun I => RationalPointFamily.isClosed_unipotent_of_isNonarchimedeanLocalField i ν I)
    D (RationalPointFamily.hasSelectedRootValuationLaw hG i hi ν)
    π hπ hc hcone haar

/-- **Sufficiency from the joint special-compact basis statement.** -/
theorem arbitraryParabolicCasselmanSufficiency_of_jointSpecialCompactBasis
    (hjoint : BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{u}) :
    ArbitraryParabolicCasselmanSufficiencyStatement.{u, v} :=
  arbitraryParabolicCasselmanSufficiency_of_strictJacquet
    (RationalPointFamily.rationalStrictJacquetSquareIntegrabilityReduction hjoint)

end Langlands.Aubert.General.RepresentedParabolic
