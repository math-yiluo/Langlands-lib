import Langlands.Global.AdelicStandardBruhatRepresentatives
import Langlands.Global.AdelicStandardBruhatPiece
import Langlands.Global.AdelicEisensteinConstantTermProof
import Langlands.GroupScheme.Rational.RelativeWeylCoxeterProof
import Langlands.GroupScheme.Rational.SimpleReflectionConjugacy
import Langlands.Group.RelativeWeylCoatomSurvivors

/-! # The full constant-term formula with its standard Weyl indices -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions
  Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G fam.i fam.ν
local notation "Roots" => SimpleRoot fam.i fam.ν
local notation "Weyl" => relativeWeylGroup fam.i
local notation "Fun" => (AdelicGroupPoints F G → ℂ)

/-- A relative Coxeter realization and rational representatives for the minimal Weyl
elements of the given two standard parabolics. -/
structure StandardBruhatConstantTermData (I J : Idx) where
  matrix : CoxeterMatrix Roots
  system : CoxeterSystem matrix Weyl
  realizes : IsRelativeWeylCoxeterRealization fam.i fam.ν system
  lift : {w : Weyl // IsMinimal system (fam.simpleRootsOfIndex J) (fam.simpleRootsOfIndex I) w} →
    normalizerPoints fam.i
  lift_spec : ∀ w, (QuotientGroup.mk (lift w) : Weyl) = w.val

omit [NumberField F] in
/-- Standard Bruhat data exist for every pair of standard parabolics. -/
theorem nonempty_standardBruhatConstantTermData (I J : Idx) :
    Nonempty (StandardBruhatConstantTermData fam I J) := by
  obtain ⟨_, _, M, cs, hcs⟩ := relativeWeylCoxeter F G fam.connectedReductive fam.T fam.i
    fam.maximalSplit fam.ν fam.generic
  exact ⟨⟨M, cs, hcs, fun w => (QuotientGroup.mk_surjective w.val).choose,
    fun w => (QuotientGroup.mk_surjective w.val).choose_spec⟩⟩

namespace StandardBruhatConstantTermData

variable {fam}
variable {I J : StandardIndex F G fam.i fam.ν} (b : StandardBruhatConstantTermData fam I J)

/-- The minimal representatives of the standard Weyl double cosets. -/
abbrev Index :=
  {w : Weyl // IsMinimal b.system (fam.simpleRootsOfIndex J) (fam.simpleRootsOfIndex I) w}

instance : Fintype b.Index := by
  have h := relativeWeylCoxeter F G fam.connectedReductive fam.T fam.i fam.maximalSplit fam.ν fam.generic
  let : Finite Weyl := h.1
  exact Fintype.ofFinite _

/-- The source intersection index of a Bruhat piece. -/
def sourceIndex (w : b.Index) : Idx :=
  fam.indexOfSimpleRoots
    (intersectionSubset b.system (fam.simpleRootsOfIndex J) (fam.simpleRootsOfIndex I) w.val)

/-- The target intersection index of a Bruhat piece. -/
def targetIndex (w : b.Index) : Idx :=
  fam.indexOfSimpleRoots
    (intersectionSubset b.system (fam.simpleRootsOfIndex I) (fam.simpleRootsOfIndex J) w.val⁻¹)

omit [NumberField F] in
theorem sourceIndex_le (w : b.Index) : b.sourceIndex w ≤ I := by
  have h := (fam.indexOfSimpleRoots_le _ _).mpr
    (intersectionSubset_subset b.system (fam.simpleRootsOfIndex J) (fam.simpleRootsOfIndex I) w.val)
  rwa [fam.indexOfSimpleRoots_simpleRootsOfIndex] at h

omit [NumberField F] in
theorem targetIndex_le (w : b.Index) : b.targetIndex w ≤ J := by
  have h := (fam.indexOfSimpleRoots_le _ _).mpr
    (intersectionSubset_subset b.system (fam.simpleRootsOfIndex I) (fam.simpleRootsOfIndex J) w.val⁻¹)
  rwa [fam.indexOfSimpleRoots_simpleRootsOfIndex] at h

/-- The indices of the relative terms whose source intersection is the whole inducing
parabolic. -/
abbrev FullSourceIndex := {w : b.Index // b.sourceIndex w = I}

instance : Fintype b.FullSourceIndex := Fintype.ofFinite _

omit [NumberField F] in
/-- The full source condition on a minimal Weyl element says that the source Levi simple
roots map into the target Levi simple roots. -/
theorem sourceIndex_eq_iff (w : b.Index) :
    b.sourceIndex w = I ↔ ∀ α ∈ I.val, schemeWeylCharacterAction fam.i w.val α ∈ J.val := by
  have hW := relativeWeylCoxeter F G fam.connectedReductive fam.T fam.i fam.maximalSplit fam.ν fam.generic
  let : Finite Weyl := hW.1
  let : Finite Roots := hW.2.1
  let : Fintype Roots := Fintype.ofFinite _
  let P := fam.simpleRootsOfIndex I
  let Q := fam.simpleRootsOfIndex J
  have hP : rootSet fam.i fam.ν P = I.val :=
    congrArg Subtype.val (fam.indexOfSimpleRoots_simpleRootsOfIndex I)
  have hQ : rootSet fam.i fam.ν Q = J.val :=
    congrArg Subtype.val (fam.indexOfSimpleRoots_simpleRootsOfIndex J)
  have hIndices : b.sourceIndex w = I ↔ intersectionSubset b.system Q P w.val = P := by
    change fam.indexOfSimpleRoots (intersectionSubset b.system Q P w.val) = I ↔ _
    have hIP : fam.indexOfSimpleRoots P = I := fam.indexOfSimpleRoots_simpleRootsOfIndex I
    constructor
    · intro h
      have he := h.trans hIP.symm
      exact Finset.Subset.antisymm ((fam.indexOfSimpleRoots_le _ _).mp he.le)
        ((fam.indexOfSimpleRoots_le _ _).mp he.ge)
    · intro h
      exact (congrArg fam.indexOfSimpleRoots h).trans hIP
  rw [hIndices, intersectionSubset_eq_source_iff_mapsIntoSimple b.system w.property, ← hP, ← hQ]
  constructor
  · intro h α hα
    obtain ⟨a, ha, rfl⟩ := hα
    obtain ⟨c, hc, he⟩ := h a ha
    have hpos := (b.realizes.2.2.1 w.val a).mp
      (((minimalityLengthCriterion_proof b.system) Q P w.val).mp w.property |>.2 a ha)
    exact ⟨c, hc, (b.realizes.root_eq_of_conj_simple w.val a c hpos he).symm⟩
  · intro h a ha
    obtain ⟨c, hc, he⟩ := h a.val ((val_mem_rootSet fam.i fam.ν P a).mpr ha)
    have hpos : schemeWeylCharacterAction fam.i w.val a.val ∈ positiveRelativeRoots fam.i fam.ν :=
      he ▸ c.property.1
    exact ⟨c, hc, (b.realizes.conj_simple_iff fam.maximalSplit.isSplitSubtorus.1 w.val a c hpos).mpr
      he.symm⟩

/-- Each Weyl index gives the two actual smaller parabolics and their Levi conjugation. -/
def piece (w : b.Index) :
    StandardBruhatPiece fam I J (b.sourceIndex w) (b.targetIndex w) (b.lift w) := by
  have hmin : IsMinimal b.system (fam.simpleRootsOfIndex J) (fam.simpleRootsOfIndex I)
      (QuotientGroup.mk (b.lift w)) := by
    rw [b.lift_spec]
    exact w.property
  have h := fam.standardBruhatPiece (b.lift w) b.system (fam.simpleRootsOfIndex I)
    (fam.simpleRootsOfIndex J) b.realizes hmin
  rw [fam.indexOfSimpleRoots_simpleRootsOfIndex I, fam.indexOfSimpleRoots_simpleRootsOfIndex J,
    b.lift_spec] at h
  exact h.some

theorem isDoubleCosetRepresentatives :
    IsDoubleCosetRepresentatives F (fam.p J) (fam.p I) (fun w => (b.lift w).val) := by
  apply fam.standardBruhatRepresentatives b.system (fam.simpleRootsOfIndex I) (fam.simpleRootsOfIndex J)
    I J b.realizes _ _ b.lift b.lift_spec
  · exact congrArg Subtype.val (fam.indexOfSimpleRoots_simpleRootsOfIndex I)
  · exact congrArg Subtype.val (fam.indexOfSimpleRoots_simpleRootsOfIndex J)

instance closedSource (w : b.Index) :
    IsClosedImmersion ((b.piece w).source.inclusion ≫ fam.p I).hom.hom.left := by
  rw [(b.piece w).source.inclusion_comp]
  exact fam.isClosedImmersion_p (b.sourceIndex w)

instance closedSourceRadical (w : b.Index) :
    IsClosedImmersion (fam.iU (b.sourceIndex w) ≫
      (b.piece w).source.inclusion ≫ fam.p I).hom.hom.left := by
  rw [(b.piece w).source.inclusion_comp]
  exact fam.closedU (b.sourceIndex w)

instance closedTargetRadical (w : b.Index) :
    IsClosedImmersion (fam.iU (b.targetIndex w) ≫
      (b.piece w).target.inclusion ≫ fam.p J).hom.hom.left := by
  rw [(b.piece w).target.inclusion_comp]
  exact fam.closedU (b.targetIndex w)

variable {K : Subgroup (AdelicGroupPoints F G)}
  (hKmin : IsIwasawaCompact (fam.p (fam.indexOfSimpleRoots ∅)) K)

include hKmin in
/-- The Iwasawa compact used for the source of the particular Bruhat piece. -/
theorem sourceIwasawa (w : b.Index) :
    IsIwasawaCompact ((b.piece w).source.inclusion ≫ fam.p I) K :=
  ((b.piece w).iwasawa K hKmin).1

/-- The intertwining integral of the inducing form's constant term in one Bruhat piece. -/
def intertwiningValue (w : b.Index) (φ : Fun) (lam : ComplexCharacterParameter F (fam.P I)) : Fun :=
  (b.sourceIwasawa hKmin w).intertwiningIntegral (fam.iU (b.sourceIndex w))
    (fam.iU (b.targetIndex w) ≫ (b.piece w).target.inclusion ≫ fam.p J) (b.lift w).val
    (subgroupConstantTerm F (fam.iU (b.sourceIndex w) ≫ (b.piece w).source.inclusion ≫ fam.p I) φ)
    (parameterRestrict (b.piece w).source.inclusion lam)

/-- The cosets of one piece in the target rational parabolic. -/
abbrev Cosets (w : b.Index) :=
  RelativeRationalCosets F ((b.piece w).target.inclusion ≫ fam.p J) (fam.p J)

/-- The relative Eisenstein summand, as the sum over the actual target parabolic cosets. -/
def summand (w : b.Index) (φ : Fun) (lam : ComplexCharacterParameter F (fam.P I)) : Fun :=
  fun g => ∑' c : b.Cosets w, b.intertwiningValue hKmin w φ lam
    (((Quotient.out c : rationalImage F (fam.p J)) : AdelicGroupPoints F G) * g)

/-- The individual intertwining integrand is integrable at the given ambient point. -/
def IntegrableIntertwining (w : b.Index) (φ : Fun) (lam : ComplexCharacterParameter F (fam.P I))
    (g : AdelicGroupPoints F G) : Prop :=
  Integrable
    ((b.sourceIwasawa hKmin w).intertwiningIntegrand (fam.iU (b.sourceIndex w))
      (fam.iU (b.targetIndex w) ≫ (b.piece w).target.inclusion ≫ fam.p J) (b.lift w).val
      (subgroupConstantTerm F (fam.iU (b.sourceIndex w) ≫ (b.piece w).source.inclusion ≫ fam.p I) φ)
      (parameterRestrict (b.piece w).source.inclusion lam) g)
    (intertwiningMeasure F ((b.piece w).source.inclusion ≫ fam.p I) (fam.iU (b.sourceIndex w))
      (fam.iU (b.targetIndex w) ≫ (b.piece w).target.inclusion ≫ fam.p J)
      (innerAdelicPoint F G (b.lift w).val))

end StandardBruhatConstantTermData

variable {fam}
variable {I J : StandardIndex F G fam.i fam.ν} [IsClosedImmersion (fam.p I).hom.hom.left]
  (b : StandardBruhatConstantTermData fam I J)
  {K : Subgroup (AdelicGroupPoints F G)}
  (hKI : IsIwasawaCompact (fam.p I) K)
  (hKmin : IsIwasawaCompact (fam.p (fam.indexOfSimpleRoots ∅)) K)
  (r : ParabolicRootPresentation (fam.p I) (fam.l I) (fam.a I))
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus (fam.A I).toGrp) (hT : IsSplitTorus r.data.T.toGrp)

/-- The standard Weyl-indexed expansion, including the absolute convergence of its
individual sums and the absolute integrability of each intertwining integral. -/
def StandardBruhatConstantTermStatement (φ : Fun) : Prop :=
  ∃ R : ℝ, ∀ lam : ComplexCharacterParameter F (fam.P I), r.IsRegularParameter hA hT R lam →
    (∀ (w : b.Index) (g : AdelicGroupPoints F G), b.IntegrableIntertwining hKmin w φ lam g) ∧
    (∀ (w : b.Index) (g : AdelicGroupPoints F G),
      Summable (fun c : b.Cosets w => b.intertwiningValue hKmin w φ lam
        (((Quotient.out c : rationalImage F (fam.p J)) : AdelicGroupPoints F G) * g))) ∧
    fam.constantTerm J (hKI.eisensteinSeries φ lam) = ∑ w : b.Index, b.summand hKmin w φ lam

set_option maxHeartbeats 1400000 in
/-- Apply the full constant-term formula with the canonical intersection parabolics
for the chosen minimal Weyl elements. -/
theorem standardBruhatConstantTerm
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hKmax : IsMaximalCompactSubgroup F G K) (hrho : IsClosedSubgroup rho) (φ : Fun)
    (hφ : fam.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho I φ) :
    StandardBruhatConstantTermStatement b hKI hKmin r hA hT φ := by
  have hP (w : b.Index) : IsParabolicSubgroup ((b.piece w).source.inclusion ≫ fam.p I) := by
    rw [(b.piece w).source.inclusion_comp]
    exact (fam.isCompatible (b.sourceIndex w)).parabolic
  have hQ (w : b.Index) : IsParabolicSubgroup ((b.piece w).target.inclusion ≫ fam.p J) := by
    rw [(b.piece w).target.inclusion_comp]
    exact (fam.isCompatible (b.targetIndex w)).parabolic
  have hexp := eisensteinConstantTerm F G (fam.P I) (fam.M I) (fam.U I) (fam.P J) (fam.U J)
    (fam.A I) (fam.p I) (fam.iU I) (fam.l I) (fam.a I) r hA hT (fam.p J) (fam.iU J)
    b.Index (fun w => (b.lift w).val)
    (fun w => fam.P (b.sourceIndex w)) (fun w => fam.U (b.sourceIndex w))
    (fun w => fam.P (b.targetIndex w)) (fun w => fam.U (b.targetIndex w))
    (fun w => (b.piece w).source.inclusion) (fun w => fam.iU (b.sourceIndex w))
    (fun w => (b.piece w).target.inclusion) (fun w => fam.iU (b.targetIndex w))
    fam.connectedReductive (fam.isUnipotentRadical I) (fam.isCompatible J).parabolic
    (fam.isUnipotentRadical J) b.isDoubleCosetRepresentatives
    hP (fun w => fam.isUnipotentRadical (b.sourceIndex w))
    hQ (fun w => fam.isUnipotentRadical (b.targetIndex w)) (fun w => (b.piece w).geometry)
    K hKI (b.sourceIwasawa hKmin) rho hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth) φ hKmax hrho
    (by simpa only [IsAutomorphicOn] using hφ)
  obtain ⟨R, hR⟩ := hexp
  refine ⟨R, fun lam hlam => ⟨fun w g => ?_, fun w g => (hR lam hlam g).2.1 w, ?_⟩⟩
  · let c : b.Cosets w := Quotient.mk _ 1
    let x : AdelicGroupPoints F G := ((Quotient.out c : rationalImage F (fam.p J)) : AdelicGroupPoints F G)
    have hi := (hR lam hlam (x⁻¹ * g)).1 w c
    have hx : x * (x⁻¹ * g) = g := mul_inv_cancel_left x g
    change b.IntegrableIntertwining hKmin w φ lam (x * (x⁻¹ * g)) at hi
    rwa [hx] at hi
  · funext g
    simpa only [constantTerm, StandardBruhatConstantTermData.summand,
      StandardBruhatConstantTermData.intertwiningValue, Finset.sum_apply] using (hR lam hlam g).2.2

end Langlands.Global.StandardParabolicFamily
