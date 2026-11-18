import Langlands.HarmonicAnalysis.HarishChandraSchwartz.GroupTransport
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedConstantTermFourier
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalSemistandardComparison
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardOrbitSections

/-! # The Schwartz function on a semistandard Levi in VIII.2.1 -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable

open RationalSemistandard

local instance leviConstantTermAffine (p : SemistandardSpectralIndex i) (m : LeviModel p) :
    IsAffineHom m.scheme.X.hom := m.reductive.isAffineHom

local instance leviConstantTermFiniteType (p : SemistandardSpectralIndex i) (m : LeviModel p) :
    LocallyOfFiniteType m.scheme.X.hom := by
  let := m.reductive.smooth
  infer_instance

local instance leviConstantTermCompactOpen : Nonempty (CompactOpenSubgroup (rationalPoints G)) :=
  ⟨Langlands.BruhatTits.rationalPointCompactOpenSubgroup F G⟩

variable {nu : cocharacterLattice S}
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
  (p : SemistandardSpectralIndex i) (m : LeviModel p)
  {SM : CommGroupScheme (Spec (CommRingCat.of F))} {iM : SM.toGrp ⟶ m.scheme}
  {nuM : cocharacterLattice SM} {KM : OpenSubgroup (rationalPoints m.scheme)}
  (hKMc : IsCompact (KM : Set (rationalPoints m.scheme)))
  (hPMK : IsIwasawaPair (standardParabolicPoints iM nuM ∅) (KM : Subgroup (rationalPoints m.scheme)))
  {XiM sigmaM : levi p → ℝ}
  (hXiM : ∀ x, rationalXi hKMc hPMK x = XiM (m.pointHomeomorph x))
  (hSigmaM : ∀ x, rationalHeight (F := F) (rho.restrict m.inclusion) x = sigmaM (m.pointHomeomorph x))
  (muU : Measure (radical p))
  (hD : ConstantTermData muU (semistandardUnipotentModulus p))
  (hE : ConstantTermEstimate muU (semistandardUnipotentModulus p)
    (rationalXi hKc hPK) (rationalHeight (F := F) rho) XiM sigmaM)
  (htM : TranslationWeights XiM sigmaM)

/-- The actual `f^M` in VIII.2.1, as a Schwartz function on the Levi scheme.
The normalized term on the literal subgroup is pulled back along the point
homeomorphism induced by the actual Levi inclusion. -/
def rationalSemistandardLeviConstantTerm
    (f : RationalSchwartzSpace hKc hPK rho) (g : rationalPoints G × rationalPoints G) :
    RationalSchwartzSpace hKMc hPMK (rho.restrict m.inclusion) :=
  Space.comapLinear m.pointHomeomorph hXiM hSigmaM
    (Space.constantTermInd hD hE (rationalTranslationWeights K.isOpen hKc hPK rho) htM f g)

@[simp] theorem rationalSemistandardLeviConstantTerm_apply
    (f : RationalSchwartzSpace hKc hPK rho) (g : rationalPoints G × rationalPoints G)
    (x : rationalPoints m.scheme) :
    rationalSemistandardLeviConstantTerm hKc hPK rho p m hKMc hPMK hXiM hSigmaM
        muU hD hE htM f g x =
      constantTermInd muU (semistandardUnipotentModulus p) f g (m.pointHomeomorph x) := rfl

omit [LocallyOfFiniteType G.X.hom] in
/-- For the restricted matrix model, the height comparison follows from the
height on `G` when the literal Levi weight is its restriction. -/
theorem rationalHeight_restrict_semistandardLevi (x : rationalPoints m.scheme) :
    rationalHeight (F := F) (rho.restrict m.inclusion) x =
      rationalHeight (F := F) rho (m.pointHomeomorph x : rationalPoints G) := by
  unfold rationalHeight MatrixRepresentation.rationalMatrixNorm
  rw [MatrixRepresentation.rationalMatrix_restrict]
  rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Nonempty (Fin N)] in
theorem isClosedSubgroup_restrict_semistandardLevi (hrho : IsClosedSubgroup rho) :
    IsClosedSubgroup (rho.restrict m.inclusion) :=
  m.closed.comp hrho

/-- Vanishing after the actual Levi model comparison detects vanishing of
the underlying normalized term on the literal Levi. -/
theorem rationalSemistandardLeviConstantTerm_eq_zero_iff
    (f : RationalSchwartzSpace hKc hPK rho) (g : rationalPoints G × rationalPoints G) :
    rationalSemistandardLeviConstantTerm hKc hPK rho p m hKMc hPMK hXiM hSigmaM
        muU hD hE htM f g = 0 ↔
      constantTermInd muU (semistandardUnipotentModulus p) f g = 0 := by
  constructor
  · intro h
    funext x
    have hx := congrArg (fun y : RationalSchwartzSpace hKMc hPMK (rho.restrict m.inclusion) =>
      y (m.pointHomeomorph.symm x)) h
    simpa only [rationalSemistandardLeviConstantTerm_apply, ContinuousMulEquiv.apply_symm_apply,
      Space.coe_zero, Pi.zero_apply] using hx
  · intro h
    apply Space.ext
    intro x
    exact congrFun h (m.pointHomeomorph x)

section III6

variable (q : SemistandardSpectralIndex iM) (r : SemistandardSpectralIndex i)
  (muQ : Measure (radical q)) (muI : Measure ((radical r).subgroupOf (levi p)))
  (deltaI : (levi r).subgroupOf (levi p) →* ℝ≥0ˣ)
  (eL : levi q ≃ₜ* (levi r).subgroupOf (levi p))
  (eU : radical q ≃ₜ* (radical r).subgroupOf (levi p))

/-- The pointwise group and measure comparisons for the intermediate
parabolic `q` in the Levi model and the lifted parabolic `r` in `G`. -/
structure RationalSemistandardConstantTermModelComparison : Prop where
  levi_apply : ∀ l : levi q, (eL l : levi p) = m.pointHomeomorph l
  radical_apply : ∀ v : radical q, (eU v : levi p) = m.pointHomeomorph v
  radical_measure : Measure.map eU muQ = muI
  modulus_apply : ∀ l : levi q, semistandardUnipotentModulus q l = deltaI (eL l)

variable (hmodel : RationalSemistandardConstantTermModelComparison p m q r muQ muI deltaI eL eU)

include hmodel in
/-- The same inner normalized integral in the Levi scheme and literal
Levi presentations. -/
theorem rationalSemistandardLeviConstantTerm_induced_model
    (f : RationalSchwartzSpace hKc hPK rho) (g : rationalPoints G × rationalPoints G)
    (x₁ x₂ : rationalPoints m.scheme) (l : levi q) :
    constantTermInd muQ (semistandardUnipotentModulus q)
        (rationalSemistandardLeviConstantTerm hKc hPK rho p m hKMc hPMK hXiM hSigmaM
          muU hD hE htM f g) (x₁, x₂) l =
      constantTermInd muI deltaI (constantTermInd muU (semistandardUnipotentModulus p) f g)
        (m.pointHomeomorph x₁, m.pointHomeomorph x₂) (eL l) := by
  have heU : MeasurePreserving eU muQ muI :=
    ⟨eU.continuous.measurable, hmodel.radical_measure⟩
  simp only [constantTermInd, constantTerm, hmodel.modulus_apply]
  congr 1
  rw [← heU.integral_comp eU.toHomeomorph.measurableEmbedding]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    simp only [translate_apply, rationalSemistandardLeviConstantTerm_apply, map_mul, map_inv,
      hmodel.levi_apply, hmodel.radical_apply, constantTermInd]

variable (muR : Measure (radical r)) [SFinite muI] [SFinite muU]
  (htrans : TransitivityData muR (semistandardUnipotentModulus r)
    muU (semistandardUnipotentModulus p) muI deltaI)
  (hconj : IsConjModulus (semistandardLeviPoints_le_normalizer_radicalPoints p)
    muU (semistandardUnipotentModulus p))

include hmodel htrans hconj in
/-- The III.6 diagram on the actual Schwartz function `f^M` on the Levi
model. Both half-modulus factors use the outer parabolic `p`. -/
theorem rationalSemistandardLeviConstantTerm_induced_transitivity
    (f : RationalSchwartzSpace hKc hPK rho) (g : rationalPoints G × rationalPoints G)
    (x₁ x₂ : rationalPoints m.scheme) (l : levi q)
    (hint : Integrable (fun u : radical r =>
      translate ((m.pointHomeomorph x₁ : rationalPoints G) * g.1)
        ((m.pointHomeomorph x₂ : rationalPoints G) * g.2) f
        (((eL l : levi p) : rationalPoints G) * u)) muR) :
    constantTermInd muQ (semistandardUnipotentModulus q)
        (rationalSemistandardLeviConstantTerm hKc hPK rho p m hKMc hPMK hXiM hSigmaM
          muU hD hE htM f g) (x₁, x₂) l =
      (((NNReal.sqrt (semistandardUnipotentModulus p (m.pointHomeomorph x₁)) : ℝ) : ℂ) *
        ((NNReal.sqrt (semistandardUnipotentModulus p (m.pointHomeomorph x₂)) : ℝ) : ℂ))⁻¹ *
      constantTermInd muR (semistandardUnipotentModulus r) f
        ((m.pointHomeomorph x₁ : rationalPoints G) * g.1, (m.pointHomeomorph x₂ : rationalPoints G) * g.2)
        ⟨((eL l : levi p) : rationalPoints G), (eL l).property⟩ := by
  rw [rationalSemistandardLeviConstantTerm_induced_model hKc hPK rho p m hKMc hPMK
    hXiM hSigmaM muU hD hE htM q r muQ muI deltaI eL eU hmodel]
  exact htrans.constantTermInd_constantTermInd hconj f g.1 g.2
    (m.pointHomeomorph x₁) (m.pointHomeomorph x₂) (eL l) hint

end III6

end Langlands.HarishChandraSchwartz
