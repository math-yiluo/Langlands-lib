import Langlands.GroupScheme.Rational.SemistandardSpectralIndex
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalStandardSpectralFamily
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup

/-! # Actual semistandard rational-point orbit sections -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}

namespace RationalSemistandard

abbrev parabolic (p : SemistandardSpectralIndex i) : Subgroup (rationalPoints G) :=
  p.parabolic.rationalPointSubgroup
abbrev levi (p : SemistandardSpectralIndex i) : Subgroup (rationalPoints G) :=
  p.levi.rationalPointSubgroup
abbrev radical (p : SemistandardSpectralIndex i) : Subgroup (rationalPoints G) :=
  p.radical.rationalPointSubgroup

/-- All-test decomposition specializes to the literal point subgroups. -/
theorem decomposition (p : SemistandardSpectralIndex i) :
    IsSemidirectDecomposition (parabolic p) (levi p) (radical p) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ :=
    p.isParabolicWithLeviAndRadical
  obtain ⟨hU, hM, hN, hC, _⟩ := h (Over.mk (𝟙 _))
  exact ⟨hM, hU, (Subgroup.normal_subgroupOf_iff_le_normalizer hU).mp hN, hC.symm⟩

/-- A model of this exact all-test Levi. It is auxiliary data, never an index. -/
structure LeviModel (p : SemistandardSpectralIndex i) where
  scheme : GroupScheme (Spec (CommRingCat.of F))
  inclusion : scheme ⟶ G
  represents : p.levi.IsRepresentedBy inclusion
  closed : IsClosedSubgroup inclusion
  reductive : IsConnectedReductive scheme

/-- The intrinsic index already guarantees an actual reductive closed model. -/
theorem nonempty_leviModel (p : SemistandardSpectralIndex i) : Nonempty (LeviModel p) := by
  obtain ⟨P, M, U, j, l, r, hj, hP, hl, hM, hrM, hU, _, _⟩ :=
    p.isParabolicWithLeviAndRadical
  have hc := hl.comp hP.isClosedSubgroup
  have : IsClosedImmersion (l ≫ j).hom.hom.left := hc
  exact ⟨⟨M, l ≫ j, ⟨Over.mono_of_mono_left _, hrM⟩, hc, hM⟩⟩

/-- An available model, with no choice added to the intrinsic index. -/
def chosenLeviModel (p : SemistandardSpectralIndex i) : LeviModel p :=
  Classical.choice (nonempty_leviModel p)

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

local instance modelAffine (p : SemistandardSpectralIndex i) (m : LeviModel p) :
    IsAffine m.scheme.X.left := by
  have := m.reductive.isAffineHom
  exact isAffine_of_isAffineHom m.scheme.X.hom
local instance modelTopology (p : SemistandardSpectralIndex i) (m : LeviModel p) :
    TopologicalSpace (rationalPoints m.scheme) := rationalPointTopology F m.scheme.X

/-- The canonical identification through the actual inclusion into G. -/
def LeviModel.pointHomeomorph {p : SemistandardSpectralIndex i} (m : LeviModel p) :
    rationalPoints m.scheme ≃ₜ* levi p :=
  rationalPointSubgroupHomeomorph F p.levi m.inclusion m.represents m.closed

@[simp] theorem LeviModel.pointHomeomorph_coe {p : SemistandardSpectralIndex i}
    (m : LeviModel p) (x : rationalPoints m.scheme) :
    (m.pointHomeomorph x : rationalPoints G) = rationalPoints.map m.inclusion x := rfl

/-- Every actual algebraic rational-character norm, on the literal Levi. -/
def LeviModel.normCharacters {p : SemistandardSpectralIndex i} (m : LeviModel p) :
    rationalCharacters m.scheme → (levi p →* ℝ≥0ˣ) :=
  fun chi => (rationalNormCharacters m.scheme chi).toMul.comp
    m.pointHomeomorph.symm.toMulEquiv.toMonoidHom

theorem LeviModel.continuous_normCharacters {p : SemistandardSpectralIndex i}
    (m : LeviModel p) (chi : rationalCharacters m.scheme) :
    Continuous (m.normCharacters chi) :=
  (rationalNormContinuousCharacter m.scheme chi).continuous.comp
    m.pointHomeomorph.symm.continuous

/-- The published finite circle coordinates, transported through the inclusion. -/
def LeviModel.unitaryCoordinates {p : SemistandardSpectralIndex i} (m : LeviModel p) :
    unitaryUnramifiedCharacters m.normCharacters ≃ₜ*
      (Fin (rationalImageRank m.scheme) → Circle) :=
  (unitaryUnramifiedCharactersHomeomorph m.pointHomeomorph
    (fun chi => (rationalNormCharacters m.scheme chi).toMul)).symm.trans
      (rationalCanonicalUnitaryUnramifiedCharacterCoordinates m.scheme m.reductive)

theorem LeviModel.unitaryCoordinates_hasLaurent {p : SemistandardSpectralIndex i}
    (m : LeviModel p) :
    HasLaurentUnitaryCoordinates m.normCharacters m.unitaryCoordinates.toMulEquiv :=
  hasLaurentUnitaryCoordinates_transport m.pointHomeomorph _ _
    (rationalCanonicalUnitaryUnramifiedCharacterCoordinates_hasLaurent m.scheme m.reductive)

/-- The split component's actual point image in the literal Levi. -/
def LeviModel.splitCenter {p : SemistandardSpectralIndex i} (m : LeviModel p)
    {A : CommGroupScheme (Spec (CommRingCat.of F))} (a : A.toGrp ⟶ m.scheme) :
    Subgroup (levi p) :=
  (rationalPoints.map a).range.map m.pointHomeomorph.toMulEquiv.toMonoidHom

theorem LeviModel.splitCenter_le_center {p : SemistandardSpectralIndex i}
    (m : LeviModel p) {A : CommGroupScheme (Spec (CommRingCat.of F))}
    (a : A.toGrp ⟶ m.scheme) (ha : IsSplitComponent a) :
    m.splitCenter a ≤ Subgroup.center (levi p) := by
  rintro _ ⟨y, hy, rfl⟩
  exact (centerHomOfEquiv m.pointHomeomorph
    ⟨y, ha.isCentralSplitTorus.isCentral.range_le_center hy⟩).property

theorem isClosed_parabolic (p : SemistandardSpectralIndex i) :
    IsClosed (parabolic p : Set (rationalPoints G)) := by
  obtain ⟨P, M, U, j, l, r, hj, hP, _⟩ := p.isParabolicWithLeviAndRadical
  exact isClosed_rationalPoint_subgroup F p.parabolic j hj hP.isClosedSubgroup

theorem isClosed_radical (p : SemistandardSpectralIndex i) :
    IsClosed (radical p : Set (rationalPoints G)) := by
  obtain ⟨P, M, U, j, l, r, _, hP, _, _, _, hU, hr, _⟩ :=
    p.isParabolicWithLeviAndRadical
  have hc := hU.1.comp hP.isClosedSubgroup
  have : IsClosedImmersion (r ≫ j).hom.hom.left := hc
  exact isClosed_rationalPoint_subgroup F p.radical (r ≫ j)
    ⟨Over.mono_of_mono_left _, hr⟩ hc

/-- Continuity of the uniquely determined literal Levi projection, in the
source's local-field, connected-reductive and maximal-split-torus setting. -/
def ProjectionContinuityStatement : Prop :=
  IsNonarchimedeanLocalField F → IsConnectedReductive G → IsMaximalSplitTorus i →
    ∀ p : SemistandardSpectralIndex i, Continuous (decomposition p).projection

/-- Compact-picture input for this index. The projection continuity and
Iwasawa factorization are visible structural obligations. -/
structure CompactData (p : SemistandardSpectralIndex i) where
  compact : OpenSubgroup (rationalPoints G)
  isCompact : IsCompact (compact : Set (rationalPoints G))
  projection_continuous : Continuous (decomposition p).projection
  factorization : ∀ g : rationalPoints G, ∃ x : parabolic p, ∃ k : compact,
    g = (x : rationalPoints G) * (k : rationalPoints G)

/-- Compact-picture existence in the source's local-field, connected-reductive
and maximal-split-torus setting. The premises are explicit because `CompactData`
itself does not retain those source restrictions. -/
def CompactDataExistenceStatement : Prop :=
  IsNonarchimedeanLocalField F → IsConnectedReductive G → IsMaximalSplitTorus i →
    ∀ p : SemistandardSpectralIndex i, Nonempty (CompactData p)

/-- The actual normalized product-induced coefficient fibers at every
irreducible admissible representative in the unitary twist orbit. -/
abbrev OrbitSections {p : SemistandardSpectralIndex i} (m : LeviModel p)
    (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)) :=
  ProductInducedOrbitSections m.normCharacters pi (decomposition p) (isClosed_radical p)

/-- Waldspurger's coherent smooth C∞(O,P), including covariance under
all actual inducing equivalences and self-twists. -/
def smoothOrbitSections {p : SemistandardSpectralIndex i} (m : LeviModel p)
    (d : CompactData p)
    (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)) :
    Submodule ℂ (OrbitSections m pi) :=
  have := (isClosed_parabolic p).locallyCompactSpace
  productInducedSmoothOrbitSections m.normCharacters pi m.unitaryCoordinates.toMulEquiv
    (decomposition p) (isClosed_radical p) d.compact (isClosed_parabolic p) d.isCompact
    m.continuous_normCharacters d.projection_continuous d.factorization



namespace LeviModel

variable {p : SemistandardSpectralIndex i} (m n l : LeviModel p)

/-- The unique scheme comparison compatible with the two actual inclusions. -/
def schemeIso : m.scheme ≅ n.scheme := m.represents.isoOfIsRepresentedBy n.represents

theorem schemeIso_hom_comp : (m.schemeIso n).hom ≫ n.inclusion = m.inclusion :=
  m.represents.isoOfIsRepresentedBy_hom_comp n.represents

/-- The model comparison fixes every element of the actual Levi subgroup. -/
def pointChange : rationalPoints m.scheme ≃ₜ* rationalPoints n.scheme :=
  m.pointHomeomorph.trans n.pointHomeomorph.symm

@[simp] theorem pointChange_inclusion (x : rationalPoints m.scheme) :
    n.pointHomeomorph (m.pointChange n x) = m.pointHomeomorph x :=
  n.pointHomeomorph.apply_symm_apply _

@[simp] theorem pointChange_refl (x : rationalPoints m.scheme) :
    m.pointChange m x = x := m.pointHomeomorph.symm_apply_apply x

@[simp] theorem pointChange_trans (x : rationalPoints m.scheme) :
    n.pointChange l (m.pointChange n x) = m.pointChange l x := by
  simp only [pointChange, ContinuousMulEquiv.trans_apply,
    ContinuousMulEquiv.apply_symm_apply]

/-- The topological comparison is the point map of the actual scheme isomorphism. -/
theorem pointChange_eq_map (x : rationalPoints m.scheme) :
    m.pointChange n x = rationalPoints.map (m.schemeIso n).hom x := by
  apply n.pointHomeomorph.injective
  rw [pointChange_inclusion]
  apply Subtype.ext
  change x ≫ m.inclusion.hom.hom =
    (x ≫ (m.schemeIso n).hom.hom.hom) ≫ n.inclusion.hom.hom
  rw [Category.assoc]
  have h := congrArg (fun f => f.hom.hom) (m.schemeIso_hom_comp n)
  exact congrArg (x ≫ ·) h.symm

/-- Restriction along the actual model isomorphism, on all rational characters. -/
def characterEquiv : rationalCharacters n.scheme ≃+ rationalCharacters m.scheme where
  toFun := characterRestrict (m.schemeIso n).hom
  invFun := characterRestrict (m.schemeIso n).inv
  left_inv chi := by
    change ((characterRestrict (m.schemeIso n).inv).comp
      (characterRestrict (m.schemeIso n).hom)) chi = chi
    rw [← characterRestrict_comp, Iso.inv_hom_id, characterRestrict_id]
    rfl
  right_inv chi := by
    change ((characterRestrict (m.schemeIso n).hom).comp
      (characterRestrict (m.schemeIso n).inv)) chi = chi
    rw [← characterRestrict_comp, Iso.hom_inv_id, characterRestrict_id]
    rfl
  map_add' := (characterRestrict (m.schemeIso n).hom).map_add

/-- Algebraic norm transport is equality of actual characters on the literal Levi. -/
theorem normCharacters_characterEquiv (chi : rationalCharacters n.scheme) :
    m.normCharacters (m.characterEquiv n chi) = n.normCharacters chi := by
  apply MonoidHom.ext
  intro x
  change (rationalNormCharacters m.scheme
    (characterRestrict (m.schemeIso n).hom chi)).toMul (m.pointHomeomorph.symm x) =
    (rationalNormCharacters n.scheme chi).toMul (n.pointHomeomorph.symm x)
  rw [rationalNormCharacters_characterRestrict, ← pointChange_eq_map]
  congr 1
  exact congrArg n.pointHomeomorph.symm (m.pointHomeomorph.apply_symm_apply x)

/-- The actual norm-one subgroup is independent of the representing model. -/
theorem commonNormKernel_eq : commonNormKernel m.normCharacters =
    commonNormKernel n.normCharacters := by
  ext x
  simp only [mem_commonNormKernel]
  constructor
  · intro h chi
    rw [← normCharacters_characterEquiv m n chi]
    exact h _
  · intro h chi
    obtain ⟨eta, rfl⟩ := (m.characterEquiv n).surjective chi
    rw [normCharacters_characterEquiv]
    exact h eta

/-- Thus models give exactly the same actual continuous unitary character subgroup. -/
theorem unitaryCharacters_eq : unitaryUnramifiedCharacters m.normCharacters =
    unitaryUnramifiedCharacters n.normCharacters := by
  ext chi
  change (commonNormKernel m.normCharacters ≤ chi.toMonoidHom.ker ∧ _) ↔
    (commonNormKernel n.normCharacters ≤ chi.toMonoidHom.ker ∧ _)
  rw [commonNormKernel_eq m n]

/-- No character values change under model comparison. -/
def unitaryCharactersEquiv : unitaryUnramifiedCharacters m.normCharacters ≃*
    unitaryUnramifiedCharacters n.normCharacters :=
  MulEquiv.subgroupCongr (m.unitaryCharacters_eq n)

@[simp] theorem unitaryCharactersEquiv_val
    (chi : unitaryUnramifiedCharacters m.normCharacters) :
    (m.unitaryCharactersEquiv n chi).val = chi.val := rfl

/-- Actual orbit objects are reindexed by identical inducing objects. -/
def representativeModelEquiv
    (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)) :
    UnitaryOrbitRepresentative m.normCharacters pi ≃
      UnitaryOrbitRepresentative n.normCharacters pi where
  toFun B := ⟨B.val, by
    obtain ⟨chi, hchi⟩ := B.property
    exact ⟨m.unitaryCharactersEquiv n chi, hchi⟩⟩
  invFun B := ⟨B.val, by
    obtain ⟨chi, hchi⟩ := B.property
    exact ⟨(m.unitaryCharactersEquiv n).symm chi, hchi⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

@[simp] theorem representativeModelEquiv_val
    (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
    (B : UnitaryOrbitRepresentative m.normCharacters pi) :
    (m.representativeModelEquiv n pi B).val = B.val := rfl

/-- Model change preserves all actual normalized coefficient values. -/
def orbitSectionsModelEquiv
    (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)) :
    OrbitSections m pi ≃ₗ[ℂ] OrbitSections n pi where
  toFun q B := q ((m.representativeModelEquiv n pi).symm B)
  invFun q B := q (m.representativeModelEquiv n pi B)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem orbitSectionsModelEquiv_apply
    (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
    (q : OrbitSections m pi) (B : UnitaryOrbitRepresentative m.normCharacters pi) :
    m.orbitSectionsModelEquiv n pi q (m.representativeModelEquiv n pi B) = q B := rfl

theorem orbitSectionsModelEquiv_coherent_iff
    (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
    (q : OrbitSections m pi) :
    m.orbitSectionsModelEquiv n pi q ∈ coherentProductInducedOrbitSections
      n.normCharacters pi (decomposition p) (isClosed_radical p) ↔
    q ∈ coherentProductInducedOrbitSections
      m.normCharacters pi (decomposition p) (isClosed_radical p) := by
  constructor
  · intro h B C a
    exact h (m.representativeModelEquiv n pi B) (m.representativeModelEquiv n pi C) a
  · intro h B C a
    exact h ((m.representativeModelEquiv n pi).symm B)
      ((m.representativeModelEquiv n pi).symm C) a


/-- The model change also fixes discrete-series classes; only their orbit
relation is reindexed by the equal actual character subgroups. -/
def orbitClassModelEquiv (C : Subgroup (levi p)) [C.Normal]
    (hC : C ≤ Subgroup.center (levi p)) [MeasurableSpace (levi p ⧸ C)]
    (mu : Measure (levi p ⧸ C)) [mu.IsHaarMeasure] :
    DiscreteSeriesOrbitClass.{u, u, uV} C hC mu m.normCharacters ≃
      DiscreteSeriesOrbitClass.{u, u, uV} C hC mu n.normCharacters :=
  Quotient.congrRight (by
    intro x y
    constructor
    · rintro ⟨chi, hchi⟩
      exact ⟨m.unitaryCharactersEquiv n chi, hchi⟩
    · rintro ⟨chi, hchi⟩
      exact ⟨(m.unitaryCharactersEquiv n).symm chi, hchi⟩)

@[simp] theorem orbitClassModelEquiv_mk (C : Subgroup (levi p)) [C.Normal]
    (hC : C ≤ Subgroup.center (levi p)) [MeasurableSpace (levi p ⧸ C)]
    (mu : Measure (levi p ⧸ C)) [mu.IsHaarMeasure]
    (x : DiscreteSeriesClass.{u, uV} C hC mu) :
    m.orbitClassModelEquiv n C hC mu (Quotient.mk _ x) = Quotient.mk _ x := rfl

@[simp] theorem orbitSectionsModelEquiv_refl
    (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
    (q : OrbitSections m pi) : m.orbitSectionsModelEquiv m pi q = q := rfl

@[simp] theorem orbitSectionsModelEquiv_trans
    (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
    (q : OrbitSections m pi) :
    n.orbitSectionsModelEquiv l pi (m.orbitSectionsModelEquiv n pi q) =
      m.orbitSectionsModelEquiv l pi q := rfl

end LeviModel

/-- The remaining smoothness comparison uses the specified actual model map,
including the coordinate systems and compact-picture choices of both sides. -/
def ModelSmoothComparisonStatement : Prop :=
  ∀ (p : SemistandardSpectralIndex i) (m n : LeviModel p) (d e : CompactData p)
    (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
    (q : OrbitSections m pi),
    m.orbitSectionsModelEquiv n pi q ∈ smoothOrbitSections n e pi ↔
      q ∈ smoothOrbitSections m d pi

section OrbitClasses

variable {p : SemistandardSpectralIndex i} (m : LeviModel p)
  {A : CommGroupScheme (Spec (CommRingCat.of F))} (a : A.toGrp ⟶ m.scheme)
  (ha : IsSplitComponent a) [(m.splitCenter a).Normal]
  [MeasurableSpace (levi p ⧸ m.splitCenter a)]
  (mu : Measure (levi p ⧸ m.splitCenter a)) [mu.IsHaarMeasure]

/-- Unitary unramified orbits of actual discrete series modulo the split center. -/
abbrev OrbitClass : Type _ :=
  DiscreteSeriesOrbitClass.{u, u, uV} (m.splitCenter a)
    (m.splitCenter_le_center a ha) mu m.normCharacters

/-- Choose an actual irreducible admissible object in the given orbit. -/
def orbitRepresentative (O : OrbitClass m a ha mu) :
    IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p) :=
  O.out.val.out

theorem orbitRepresentative_isSquareIntegrable (O : OrbitClass m a ha mu) :
    IsSquareIntegrableModCentralSubgroup (m.splitCenter a)
      (m.splitCenter_le_center a ha) (orbitRepresentative m a ha mu O).obj.representation
      mu := by
  have h := O.out.property
  rw [← Quotient.out_eq O.out.val] at h
  exact h

theorem mk_discreteSeriesClass_orbitRepresentative (O : OrbitClass m a ha mu) :
    (Quotient.mk _ (discreteSeriesClass (m.splitCenter a) (m.splitCenter_le_center a ha)
      mu (orbitRepresentative m a ha mu O)
      (orbitRepresentative_isSquareIntegrable m a ha mu O)) : OrbitClass m a ha mu) = O := by
  have h : discreteSeriesClass (m.splitCenter a) (m.splitCenter_le_center a ha) mu
      (orbitRepresentative m a ha mu O)
      (orbitRepresentative_isSquareIntegrable m a ha mu O) = O.out :=
    Subtype.ext (Quotient.out_eq _)
  rw [h]
  exact Quotient.out_eq O

/-- Membership in the very same actual unitary twist orbit. -/
def orbitRepresentativeMember (O : OrbitClass m a ha mu)
    (pi' : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
    (hsq : IsSquareIntegrableModCentralSubgroup (m.splitCenter a)
      (m.splitCenter_le_center a ha) pi'.obj.representation mu)
    (hO : (Quotient.mk _ (discreteSeriesClass (m.splitCenter a)
      (m.splitCenter_le_center a ha) mu pi' hsq) : OrbitClass m a ha mu) = O) :
    UnitaryOrbitRepresentative m.normCharacters (orbitRepresentative m a ha mu O) :=
  ⟨pi', by
    obtain ⟨chi, hchi⟩ := Quotient.exact
      (hO.trans (mk_discreteSeriesClass_orbitRepresentative m a ha mu O).symm)
    exact ⟨chi, congrArg Subtype.val hchi⟩⟩

@[simp] theorem orbitRepresentativeMember_val (O : OrbitClass m a ha mu)
    (pi' : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
    (hsq : IsSquareIntegrableModCentralSubgroup (m.splitCenter a)
      (m.splitCenter_le_center a ha) pi'.obj.representation mu)
    (hO : (Quotient.mk _ (discreteSeriesClass (m.splitCenter a)
      (m.splitCenter_le_center a ha) mu pi' hsq) : OrbitClass m a ha mu) = O) :
    (orbitRepresentativeMember m a ha mu O pi' hsq hO).val = pi' := rfl

/-- Actual representative change retains all inducing objects and coefficient values. -/
def orbitSectionsBaseEquiv (O : OrbitClass m a ha mu)
    (pi' : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
    (hsq : IsSquareIntegrableModCentralSubgroup (m.splitCenter a)
      (m.splitCenter_le_center a ha) pi'.obj.representation mu)
    (hO : (Quotient.mk _ (discreteSeriesClass (m.splitCenter a)
      (m.splitCenter_le_center a ha) mu pi' hsq) : OrbitClass m a ha mu) = O) :
    OrbitSections m (orbitRepresentative m a ha mu O) ≃ₗ[ℂ] OrbitSections m pi' :=
  productInducedOrbitBaseEquiv m.normCharacters (orbitRepresentative m a ha mu O)
    (orbitRepresentativeMember m a ha mu O pi' hsq hO) (decomposition p) (isClosed_radical p)

/-- Smooth representative change is the published compact-picture base change. -/
def orbitSmoothSectionsBaseEquiv (d : CompactData p) (O : OrbitClass m a ha mu)
    (pi' : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
    (hsq : IsSquareIntegrableModCentralSubgroup (m.splitCenter a)
      (m.splitCenter_le_center a ha) pi'.obj.representation mu)
    (hO : (Quotient.mk _ (discreteSeriesClass (m.splitCenter a)
      (m.splitCenter_le_center a ha) mu pi' hsq) : OrbitClass m a ha mu) = O) :
    smoothOrbitSections m d (orbitRepresentative m a ha mu O) ≃ₗ[ℂ]
      smoothOrbitSections m d pi' :=
  have := (isClosed_parabolic p).locallyCompactSpace
  productInducedSmoothOrbitBaseEquiv m.normCharacters (orbitRepresentative m a ha mu O)
    (orbitRepresentativeMember m a ha mu O pi' hsq hO) (decomposition p) (isClosed_radical p)
    m.unitaryCoordinates.toMulEquiv d.compact (isClosed_parabolic p) d.isCompact
    m.continuous_normCharacters d.projection_continuous d.factorization

@[simp] theorem orbitSmoothSectionsBaseEquiv_val (d : CompactData p)
    (O : OrbitClass m a ha mu)
    (pi' : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
    (hsq : IsSquareIntegrableModCentralSubgroup (m.splitCenter a)
      (m.splitCenter_le_center a ha) pi'.obj.representation mu)
    (hO : (Quotient.mk _ (discreteSeriesClass (m.splitCenter a)
      (m.splitCenter_le_center a ha) mu pi' hsq) : OrbitClass m a ha mu) = O)
    (q : smoothOrbitSections m d (orbitRepresentative m a ha mu O)) :
    (orbitSmoothSectionsBaseEquiv m a ha mu d O pi' hsq hO q).val =
      orbitSectionsBaseEquiv m a ha mu O pi' hsq hO q.val := rfl

end OrbitClasses

/-- Equality of the actual split-center point images for all scheme presentations.
This is a geometric choice-independence target, not a model-field assumption. -/
def SplitCenterChoiceIndependenceStatement : Prop :=
  ∀ (p : SemistandardSpectralIndex i) (m n : LeviModel p)
    (A B : CommGroupScheme (Spec (CommRingCat.of F)))
    (a : A.toGrp ⟶ m.scheme) (b : B.toGrp ⟶ n.scheme),
    IsSplitComponent a → IsSplitComponent b → m.splitCenter a = n.splitCenter b

section Standard

variable {nu : cocharacterLattice S} (hG : IsConnectedReductive G)
  (hi : IsMaximalSplitTorus i) (hnu : IsGenericCocharacter i nu)
  (I : Finset (RationalPointFamily.SimpleRoot i nu))

/-- The already published standard triple is an intrinsic semistandard index. -/
abbrev standardIndex : SemistandardSpectralIndex i :=
  SemistandardSpectralIndex.ofStandard hG hi nu hnu
    (RationalPointFamily.rootSet i nu I) (RationalPointFamily.rootSet_subset i nu I)

/-- The existing standard Levi scheme, with its exact all-test inclusion. -/
def standardLeviModel : LeviModel (standardIndex hG hi hnu I) where
  scheme := Standard.leviScheme i nu (RationalPointFamily.rootSet i nu I)
  inclusion := Standard.leviHom i nu (RationalPointFamily.rootSet i nu I)
  represents := Standard.isRepresentedBy_leviHom i nu (RationalPointFamily.rootSet i nu I)
  closed := Standard.isClosedSubgroup_leviHom i nu (RationalPointFamily.rootSet i nu I)
  reductive := isConnectedReductive_leviScheme_rootSet hG hi hnu I

@[simp] theorem standardLeviModel_normCharacters :
    (standardLeviModel hG hi hnu I).normCharacters =
      RationalPointFamily.leviRationalNormCharacters i nu I := rfl

@[simp] theorem standardLeviModel_unitaryCoordinates :
    (standardLeviModel hG hi hnu I).unitaryCoordinates =
      leviRationalUnitaryCoordinates hG hi hnu I := rfl

@[simp] theorem standardLeviModel_splitCenter
    {A : CommGroupScheme (Spec (CommRingCat.of F))}
    (a : A.toGrp ⟶ (standardLeviModel hG hi hnu I).scheme) :
    (standardLeviModel hG hi hnu I).splitCenter a = rationalLeviSplitCenter I a := rfl

/-- Continuity of the projection and Iwasawa factorization specialize to the
published standard inputs, for the chosen actual compact open subgroup. -/
def standardCompactData {K : OpenSubgroup (rationalPoints G)}
    (hK : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G))) :
    CompactData (standardIndex hG hi hnu I) where
  compact := K
  isCompact := hK
  projection_continuous :=
    continuous_projection_standard hG hi hnu (RationalPointFamily.rootSet_subset i nu I) _
  factorization :=
    factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hnu I hPK)

/-- Standard specialization agrees with the existing normalized smooth section space. -/
theorem smoothOrbitSections_standard {K : OpenSubgroup (rationalPoints G)}
    (hK : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
    (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ)
      (G := levi (standardIndex hG hi hnu I))) :
    smoothOrbitSections (standardLeviModel hG hi hnu I)
      (standardCompactData hG hi hnu I hK hPK) pi =
      rationalInducedSmoothOrbitSections hG hi hnu I hK hPK pi := rfl

section StandardOrbitClasses

set_option maxHeartbeats 800000

variable
  {T : Finset (RationalPointFamily.SimpleRoot i nu) →
    CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ I, (T I).toGrp ⟶ Standard.leviScheme i nu (RationalPointFamily.rootSet i nu I))
  (ha : ∀ I, IsSplitComponent (a I))
  [hNormal : ∀ I, (rationalLeviSplitCenter I (a I)).Normal]
  [hMeas : ∀ I, MeasurableSpace
    (standardLeviPoints i nu (RationalPointFamily.rootSet i nu I) ⧸
      rationalLeviSplitCenter I (a I))]
  (mu : ∀ I, Measure
    (standardLeviPoints i nu (RationalPointFamily.rootSet i nu I) ⧸
      rationalLeviSplitCenter I (a I)))
  [hHaar : ∀ I, (mu I).IsHaarMeasure]

/-- The standard orbit quotient is exactly the published standard quotient. -/
theorem OrbitClass_standard :
    @OrbitClass.{u, uV} F _ S G i _ _ _ _ _ (standardIndex hG hi hnu I)
        (standardLeviModel hG hi hnu I) (T I) (a I) (ha I)
        (hNormal I) (hMeas I) (mu I) (hHaar I) =
      RationalLeviOrbitClass.{u, uV} a ha mu I := rfl

/-- Both constructions choose the same actual object from the same quotient. -/
theorem orbitRepresentative_standard (O : RationalLeviOrbitClass a ha mu I) :
    @orbitRepresentative.{u, uV} F _ S G i _ _ _ _ _ (standardIndex hG hi hnu I)
        (standardLeviModel hG hi hnu I) (T I) (a I) (ha I)
        (hNormal I) (hMeas I) (mu I) (hHaar I) O =
      rationalOrbitRepresentative a ha mu I O := rfl

variable (O : RationalLeviOrbitClass a ha mu I)
  (pi' : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ)
    (G := standardLeviPoints i nu (RationalPointFamily.rootSet i nu I)))
  (hsq : IsSquareIntegrableModCentralSubgroup (rationalLeviSplitCenter I (a I))
    (rationalLeviSplitCenter_le_center I (a I) (ha I)) pi'.obj.representation (mu I))
  (hO : (Quotient.mk _ (discreteSeriesClass (rationalLeviSplitCenter I (a I))
    (rationalLeviSplitCenter_le_center I (a I) (ha I)) (mu I) pi' hsq) :
      RationalLeviOrbitClass a ha mu I) = O)

/-- Standard orbit membership uses the existing actual representative. -/
theorem orbitRepresentativeMember_standard :
    @orbitRepresentativeMember.{u, uV} F _ S G i _ _ _ _ _ (standardIndex hG hi hnu I)
        (standardLeviModel hG hi hnu I) (T I) (a I) (ha I)
        (hNormal I) (hMeas I) (mu I) (hHaar I) O pi' hsq hO =
      rationalOrbitRepresentativeMember a ha mu I O pi' hsq hO := rfl

/-- The standard specialization uses exactly the published raw base change. -/
theorem orbitSectionsBaseEquiv_standard :
    @orbitSectionsBaseEquiv.{u, uV} F _ S G i _ _ _ _ _ (standardIndex hG hi hnu I)
        (standardLeviModel hG hi hnu I) (T I) (a I) (ha I)
        (hNormal I) (hMeas I) (mu I) (hHaar I) O pi' hsq hO =
      rationalOrbitSectionsBaseEquiv hG hi hnu a ha mu I O pi' hsq hO := rfl

/-- After the proved equality of the smooth submodules, standard smooth base
change has exactly the same underlying actual coefficient values. -/
theorem orbitSmoothSectionsBaseEquiv_standard_val {K : OpenSubgroup (rationalPoints G)}
    (hK : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
    (q : smoothOrbitSections (standardLeviModel hG hi hnu I)
      (standardCompactData hG hi hnu I hK hPK) (rationalOrbitRepresentative a ha mu I O)) :
    (@orbitSmoothSectionsBaseEquiv.{u, uV} F _ S G i _ _ _ _ _ (standardIndex hG hi hnu I)
        (standardLeviModel hG hi hnu I) (T I) (a I) (ha I)
        (hNormal I) (hMeas I) (mu I) (hHaar I) (standardCompactData hG hi hnu I hK hPK)
        O pi' hsq hO q).val =
      (rationalOrbitSmoothSectionsBaseEquiv hG hi hnu hK hPK a ha mu I O pi' hsq hO
        ⟨q.val, q.property⟩).val := rfl

end StandardOrbitClasses

end Standard

end RationalSemistandard
end Langlands.HarishChandraSchwartz
