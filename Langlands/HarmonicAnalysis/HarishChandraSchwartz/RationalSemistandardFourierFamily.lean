import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardFourierTransform
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardStandardComparison
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalFourierOrbitContinuity

/-! # The actual Fourier family in the full semistandard product -/

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ComplexConjugate
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

open RationalSemistandard

variable {nu : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hnu : IsGenericCocharacter i nu)
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
  {muG : Measure (rationalPoints G)} [muG.IsMulLeftInvariant] [muG.IsMulRightInvariant]
  (hsw : SquareIntegrableWeight muG (rationalXi hKc hPK) (rationalHeight (F := F) rho))

local instance familyAmbientCompactOpen : Nonempty (CompactOpenSubgroup (rationalPoints G)) :=
  ⟨Langlands.BruhatTits.rationalPointCompactOpenSubgroup F G⟩
local instance familyParabolicLC (p : SemistandardSpectralIndex i) : LocallyCompactSpace (parabolic p) :=
  (isClosed_parabolic p).locallyCompactSpace

section Orbit

variable (p : SemistandardSpectralIndex i) (m : LeviModel p) (d : CompactData p)
  (hdelta : ModularNormalization p)
  (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
  (C : Subgroup (levi p)) [C.Normal] (hC : C ≤ Subgroup.center (levi p))
  [MeasurableSpace (levi p ⧸ C)] [BorelSpace (levi p ⧸ C)]
  (muM : Measure (levi p ⧸ C)) [muM.IsHaarMeasure] [muM.IsInvInvariant]
  (hsqPi : IsSquareIntegrableModCentralSubgroup C hC pi.obj.representation muM)
  (hT : ∀ A : UnitaryOrbitRepresentative m.normCharacters pi,
    HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) rho)
      ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj A.val.obj).representation)

/-- The actual raw section, defined before any smoothness assertion. -/
def rationalSemistandardFourierOrbit :
    RationalSchwartzSpace hKc hPK rho →ₗ[ℂ] OrbitSections m pi where
  toFun f A := rationalSemistandardInducedFourierTransform hG hi hnu hKc hPK rho hsw
    p d hdelta A.val.obj C hC muM
    (unitaryOrbitRepresentative_isDiscreteSeries m.normCharacters pi C hC muM hsqPi A)
    A.val.property.1 (hT A) f
  map_add' f g := funext fun A => map_add _ f g
  map_smul' c f := funext fun A => map_smul _ c f

@[simp] theorem rationalSemistandardFourierOrbit_apply
    (f : RationalSchwartzSpace hKc hPK rho) (A : UnitaryOrbitRepresentative m.normCharacters pi) :
    rationalSemistandardFourierOrbit hG hi hnu hKc hPK rho hsw
      p m d hdelta pi C hC muM hsqPi hT f A =
    rationalSemistandardInducedFourierTransform hG hi hnu hKc hPK rho hsw
      p d hdelta A.val.obj C hC muM
      (unitaryOrbitRepresentative_isDiscreteSeries m.normCharacters pi C hC muM hsqPi A)
      A.val.property.1 (hT A) f := rfl

/-- This raw section uses exactly the already published generic actual construction. -/
theorem rationalSemistandardFourierOrbit_eq (f : RationalSchwartzSpace hKc hPK rho) :
    rationalSemistandardFourierOrbit hG hi hnu hKc hPK rho hsw
      p m d hdelta pi C hC muM hsqPi hT f =
    fourierOrbitSection (decomposition p) (isClosed_radical p) (isClosed_parabolic p)
      d.projection_continuous d.compact d.isCompact d.factorization_mem
      (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
      hdelta m.normCharacters pi (compactOpenCofinal p d) C hC muM
      (unitaryOrbitRepresentative_isDiscreteSeries m.normCharacters pi C hC muM hsqPi)
      (rationalL2Weights K.isOpen hKc hPK rho hsw) hT
      (rationalXi_inv hG hi hnu K.isOpen hKc hPK) (rationalHeight_inv rho) f := rfl

/-- Coherence holds for every inducing equivalence, including every self-twist. -/
theorem rationalSemistandardFourierOrbit_coherent [muG.IsInvInvariant]
    (f : RationalSchwartzSpace hKc hPK rho) :
    rationalSemistandardFourierOrbit hG hi hnu hKc hPK rho hsw
      p m d hdelta pi C hC muM hsqPi hT f ∈
      coherentProductInducedOrbitSections m.normCharacters pi (decomposition p) (isClosed_radical p) := by
  intro A B e
  exact (rationalSemistandardFourier_transport hG hi hnu hKc hPK rho hsw
    p d hdelta A.val.obj C hC muM
    (unitaryOrbitRepresentative_isDiscreteSeries m.normCharacters pi C hC muM hsqPi A)
    A.val.property.1 (hT A) B.val.obj
    (unitaryOrbitRepresentative_isDiscreteSeries m.normCharacters pi C hC muM hsqPi B)
    B.val.property.1 (hT B) e f).symm

/-- Recentering the orbit keeps every actual inducing object and Fourier value. -/
theorem rationalSemistandardFourierOrbit_baseChange
    (A : UnitaryOrbitRepresentative m.normCharacters pi)
    (hTA : ∀ B : UnitaryOrbitRepresentative m.normCharacters A.val,
      HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) rho)
        ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj B.val.obj).representation)
    (f : RationalSchwartzSpace hKc hPK rho) :
    productInducedOrbitBaseEquiv m.normCharacters pi A (decomposition p) (isClosed_radical p)
        (rationalSemistandardFourierOrbit hG hi hnu hKc hPK rho hsw
          p m d hdelta pi C hC muM hsqPi hT f) =
      rationalSemistandardFourierOrbit hG hi hnu hKc hPK rho hsw
        p m d hdelta A.val C hC muM
        (unitaryOrbitRepresentative_isDiscreteSeries m.normCharacters pi C hC muM hsqPi A) hTA f := rfl

/-- The prescribed model comparison preserves every literal Fourier tensor. -/
theorem rationalSemistandardFourierOrbit_modelChange (n : LeviModel p)
    (hTn : ∀ A : UnitaryOrbitRepresentative n.normCharacters pi,
      HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) rho)
        ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj A.val.obj).representation)
    (f : RationalSchwartzSpace hKc hPK rho) :
    m.orbitSectionsModelEquiv n pi
        (rationalSemistandardFourierOrbit hG hi hnu hKc hPK rho hsw
          p m d hdelta pi C hC muM hsqPi hT f) =
      rationalSemistandardFourierOrbit hG hi hnu hKc hPK rho hsw
        p n d hdelta pi C hC muM hsqPi hTn f := rfl

/-- The full group acts on the raw orbit section by the actual normalized fibers. -/
theorem rationalSemistandardFourierOrbit_translate (g1 g2 : rationalPoints G)
    (f : RationalSchwartzSpace hKc hPK rho) :
    rationalSemistandardFourierOrbit hG hi hnu hKc hPK rho hsw
      p m d hdelta pi C hC muM hsqPi hT
        (Space.translate (rationalTranslationWeights K.isOpen hKc hPK rho) g1 g2 f) =
    productInducedOrbitRepresentation (decomposition p) (isClosed_radical p) m.normCharacters pi
      (g1, g2) (rationalSemistandardFourierOrbit hG hi hnu hKc hPK rho hsw
        p m d hdelta pi C hC muM hsqPi hT f) := by
  funext A
  exact rationalSemistandardFourier_translate hG hi hnu hKc hPK rho hsw
    p d hdelta A.val.obj C hC muM
    (unitaryOrbitRepresentative_isDiscreteSeries m.normCharacters pi C hC muM hsqPi A)
    A.val.property.1 (hT A) g1 g2 f

section Analysis

variable (muL : Measure (levi p)) (muU : Measure (radical p))
  (XiM sigmaM : levi p → ℝ)

/-- Exact preceding inputs of the published Laurent-smoothness and continuity
interfaces, on the actual semistandard groups. No Fourier regularity is a field. -/
structure RationalSemistandardFourierAnalyticInputs : Prop where
  ambient_inv : muG.IsInvInvariant
  ambient_sigmaFinite : SigmaFinite muG
  ambient_compact_volume : muG (d.compact : Set (rationalPoints G)) = 1
  radical_unimodular : IsUnimodularModulus (radical p) (isClosed_radical p)
  levi_left : muL.IsMulLeftInvariant
  levi_right : muL.IsMulRightInvariant
  levi_inv : muL.IsInvInvariant
  levi_sfinite : SFinite muL
  levi_weights : L2Weights muL XiM sigmaM
  levi_tempered : HasTemperedCoefficients XiM sigmaM pi.obj.representation
  orbit_tempered : ∀ A : UnitaryOrbitRepresentative m.normCharacters pi,
    HasTemperedCoefficients XiM sigmaM A.val.obj.representation
  levi_xi_inv : ∀ x, XiM x⁻¹ = XiM x
  levi_height_inv : ∀ x, sigmaM x⁻¹ = sigmaM x
  radical_left : muU.IsMulLeftInvariant
  radical_right : muU.IsMulRightInvariant
  radical_sfinite : SFinite muU
  constant_term : ConstantTermData muU
    (HaarModulus.closedRestrictCharacter (radical p) (isClosed_radical p) (levi p)
      (decomposition p).levi_le_normalizer)
  conjugation_modulus : IsConjModulus (decomposition p).levi_le_normalizer muU
    (HaarModulus.closedRestrictCharacter (radical p) (isClosed_radical p) (levi p)
      (decomposition p).levi_le_normalizer)
  constant_term_estimate : ConstantTermEstimate muU
    (HaarModulus.closedRestrictCharacter (radical p) (isClosed_radical p) (levi p)
      (decomposition p).levi_le_normalizer)
    (rationalXi hKc hPK) (rationalHeight (F := F) rho) XiM sigmaM
  levi_translations : TranslationWeights XiM sigmaM
  compact_factorization : ∀ (x : levi p) (u : radical p),
    (x : rationalPoints G) * u ∈ d.compact ↔
      (x : rationalPoints G) ∈ d.compact ∧ (u : rationalPoints G) ∈ d.compact
  levi_compact_volume : muL {x : levi p | (x : rationalPoints G) ∈ d.compact} = 1
  radical_compact_volume : muU {x : radical p | (x : rationalPoints G) ∈ d.compact} = 1
  laurent_height : ∃ Cn : ℝ, ∀ x : levi p,
    ‖laurentExponent m.normCharacters m.unitaryCoordinates.toMulEquiv
      m.unitaryCoordinates_hasLaurent x‖ ≤ Cn * (1 + sigmaM x)
  double_integrability : ∀ (f : RationalSchwartzSpace hKc hPK rho)
    (A : UnitaryOrbitRepresentative m.normCharacters pi)
    (psi : productInducedCoefficientObject (decomposition p) (isClosed_radical p) A.val.obj),
    Integrable (fun x : rationalPoints G × d.compact =>
      conj (CompactInduction.integrand (decomposition p) (isClosed_radical p) A.val.obj
        d.compact x.1 psi x.2) * f x.1)
      (muG.prod (CompactInduction.measure d.compact d.isCompact))

/-- VII.1.3: the new raw section is coherently smooth, from precisely the
preceding analytic inputs. This target does not assume its own membership. -/
def RationalSemistandardFourierSmoothnessStatement : Prop :=
  RationalSemistandardFourierAnalyticInputs (muG := muG) hKc hPK rho p m d pi muL muU XiM sigmaM →
    ∀ f : RationalSchwartzSpace hKc hPK rho,
      rationalSemistandardFourierOrbit hG hi hnu hKc hPK rho hsw
        p m d hdelta pi C hC muM hsqPi hT f ∈ smoothOrbitSections m d pi

/-- The published VI.3 orbit topology on the new actual component. -/
abbrev rationalSemistandardFourierOrbitSpace :=
  OrbitSectionSpace m.normCharacters pi m.unitaryCoordinates.toMulEquiv
    (decomposition p) (isClosed_radical p) d.compact (isClosed_parabolic p) d.isCompact
    m.continuous_normCharacters d.projection_continuous d.factorization

/-- Conditional typed lift: its raw values are already defined, and this lift
explicitly consumes the preceding smoothness result. -/
def rationalSemistandardFourierOrbitSmooth
    (hsm : ∀ f : RationalSchwartzSpace hKc hPK rho,
      rationalSemistandardFourierOrbit hG hi hnu hKc hPK rho hsw
        p m d hdelta pi C hC muM hsqPi hT f ∈ smoothOrbitSections m d pi) :
    RationalSchwartzSpace hKc hPK rho →ₗ[ℂ] rationalSemistandardFourierOrbitSpace p m d pi where
  toFun f := ⟨rationalSemistandardFourierOrbit hG hi hnu hKc hPK rho hsw
    p m d hdelta pi C hC muM hsqPi hT f, hsm f⟩
  map_add' f g := Subtype.ext (map_add _ f g)
  map_smul' c f := Subtype.ext (map_smul _ c f)

/-- VII.1.3 continuity, for the existing Schwartz and VI.3 section topologies.
The output is a continuous complex-linear map with the prescribed raw values. -/
def RationalSemistandardFourierContinuityStatement : Prop :=
  RationalSemistandardFourierAnalyticInputs (muG := muG) hKc hPK rho p m d pi muL muU XiM sigmaM →
    ∃ L : RationalSchwartzSpace hKc hPK rho →L[ℂ] rationalSemistandardFourierOrbitSpace p m d pi,
      ∀ f, (OrbitSectionSpace.toSections m.normCharacters pi m.unitaryCoordinates.toMulEquiv
        (decomposition p) (isClosed_radical p) d.compact (isClosed_parabolic p) d.isCompact
        m.continuous_normCharacters d.projection_continuous d.factorization (L f)).val =
          rationalSemistandardFourierOrbit hG hi hnu hKc hPK rho hsw
            p m d hdelta pi C hC muM hsqPi hT f

/-- A common finite compact-picture range at every compact level, membership in
the exact VI.3 level, and compatibility with every smaller open level. Finiteness
here concerns the compact-picture vectors, not the full Fourier support. -/
def RationalSemistandardFourierCompactLevelStatement : Prop :=
  RationalSemistandardFourierAnalyticInputs (muG := muG) hKc hPK rho p m d pi muL muU XiM sigmaM →
    ∀ H : OpenSubgroup (rationalPoints G), H ≤ d.compact →
      ∃ W : Submodule ℂ (ProductInducedCompactPicture (decomposition p) d.compact pi.obj),
        FiniteDimensional ℂ W ∧ ∀ f : RationalSchwartzSpace hKc hPK rho,
          IsBiInvariant (H : Subgroup (rationalPoints G)) f →
          (rationalSemistandardFourierOrbit hG hi hnu hKc hPK rho hsw
            p m d hdelta pi C hC muM hsqPi hT f ∈
              orbitSectionLevelSubmodule m.normCharacters pi m.unitaryCoordinates.toMulEquiv
                (decomposition p) (isClosed_radical p) d.compact (isClosed_parabolic p) d.isCompact
                m.continuous_normCharacters d.projection_continuous d.factorization H) ∧
          (∀ H' : OpenSubgroup (rationalPoints G), H' ≤ H →
            rationalSemistandardFourierOrbit hG hi hnu hKc hPK rho hsw
              p m d hdelta pi C hC muM hsqPi hT f ∈
                orbitSectionLevelSubmodule m.normCharacters pi m.unitaryCoordinates.toMulEquiv
                  (decomposition p) (isClosed_radical p) d.compact (isClosed_parabolic p) d.isCompact
                  m.continuous_normCharacters d.projection_continuous d.factorization H') ∧
          ∀ z : Fin (rationalImageRank m.scheme) → Circle,
            productInducedFamilyRestriction m.normCharacters m.unitaryCoordinates.toMulEquiv
              (decomposition p) d.compact (isClosed_parabolic p) d.isCompact
              m.continuous_normCharacters d.projection_continuous (isClosed_radical p)
              d.factorization pi.obj
              (productInducedOrbitPullback m.normCharacters pi m.unitaryCoordinates.toMulEquiv
                (decomposition p) (isClosed_radical p)
                (rationalSemistandardFourierOrbit hG hi hnu hKc hPK rho hsw
                  p m d hdelta pi C hC muM hsqPi hT f)) z ∈ W

end Analysis

end Orbit

section FullProduct

variable {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ p, (T p).toGrp ⟶ (chosenLeviModel p).scheme)
  (ha : ∀ p, IsSplitComponent (a p))
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (muM : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
  [∀ p, (muM p).IsHaarMeasure] [∀ p, (muM p).IsInvInvariant]
  (d : ∀ p : SemistandardSpectralIndex i, CompactData p)
  (hdelta : ∀ p : SemistandardSpectralIndex i, ModularNormalization p)
  (hT : ∀ (p : SemistandardSpectralIndex i)
    (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)),
    IsSquareIntegrableModCentralSubgroup ((chosenLeviModel p).splitCenter (a p))
      ((chosenLeviModel p).splitCenter_le_center (a p) (ha p)) A.obj.representation (muM p) →
    HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) rho)
      ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj A.obj).representation)

/-- The actual family over full intrinsic Theta, in its dependent product.
No smoothness or finite-support witness is used by this definition. -/
def rationalSemistandardFourierFamily :
    RationalSchwartzSpace hKc hPK rho →ₗ[ℂ] RationalSemistandardThetaSections.{u, uV} a ha muM where
  toFun f t := rationalSemistandardFourierOrbit hG hi hnu hKc hPK rho hsw
    t.1 (chosenLeviModel t.1) (d t.1) (hdelta t.1)
    (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2)
    ((chosenLeviModel t.1).splitCenter (a t.1))
    ((chosenLeviModel t.1).splitCenter_le_center (a t.1) (ha t.1)) (muM t.1)
    (orbitRepresentative_isSquareIntegrable (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2)
    (fun A => hT t.1 A.val
      (unitaryOrbitRepresentative_isDiscreteSeries _ _ _ _ _
        (orbitRepresentative_isSquareIntegrable (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2) A)) f
  map_add' f g := funext fun t => map_add _ f g
  map_smul' c f := funext fun t => map_smul _ c f

/-- Evaluation of the full family is the actual tensor at this inducing object. -/
@[simp] theorem rationalSemistandardFourierFamily_apply
    (f : RationalSchwartzSpace hKc hPK rho) (t : RationalSemistandardTheta.{u, uV} a ha muM)
    (A : UnitaryOrbitRepresentative (chosenLeviModel t.1).normCharacters
      (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2)) :
    rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f t A =
      rationalSemistandardInducedFourierTransform hG hi hnu hKc hPK rho hsw
        t.1 (d t.1) (hdelta t.1) A.val.obj ((chosenLeviModel t.1).splitCenter (a t.1))
        ((chosenLeviModel t.1).splitCenter_le_center (a t.1) (ha t.1)) (muM t.1)
        (unitaryOrbitRepresentative_isDiscreteSeries _ _ _ _ _
          (orbitRepresentative_isSquareIntegrable (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2) A)
        A.val.property.1 (hT t.1 A.val
          (unitaryOrbitRepresentative_isDiscreteSeries _ _ _ _ _
            (orbitRepresentative_isSquareIntegrable (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2) A)) f := rfl

/-- The canonical representative-base change of the full Fourier component is
the actual section based at any other representative of the same orbit. -/
theorem rationalSemistandardFourierFamily_baseChange
    (t : RationalSemistandardTheta.{u, uV} a ha muM)
    (pi' : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi t.1))
    (hsq' : IsSquareIntegrableModCentralSubgroup ((chosenLeviModel t.1).splitCenter (a t.1))
      ((chosenLeviModel t.1).splitCenter_le_center (a t.1) (ha t.1)) pi'.obj.representation (muM t.1))
    (hO : (Quotient.mk _ (discreteSeriesClass ((chosenLeviModel t.1).splitCenter (a t.1))
      ((chosenLeviModel t.1).splitCenter_le_center (a t.1) (ha t.1)) (muM t.1) pi' hsq') :
      OrbitClass (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1)) = t.2)
    (f : RationalSchwartzSpace hKc hPK rho) :
    orbitSectionsBaseEquiv (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2 pi' hsq' hO
      (rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f t) =
    rationalSemistandardFourierOrbit hG hi hnu hKc hPK rho hsw
      t.1 (chosenLeviModel t.1) (d t.1) (hdelta t.1) pi'
      ((chosenLeviModel t.1).splitCenter (a t.1))
      ((chosenLeviModel t.1).splitCenter_le_center (a t.1) (ha t.1)) (muM t.1) hsq'
      (fun A => hT t.1 A.val (unitaryOrbitRepresentative_isDiscreteSeries _ pi' _ _ _ hsq' A)) f := rfl

/-- The actual pointwise G x G action on the full dependent product. -/
def rationalSemistandardFourierProductRepresentation :
    Representation ℂ (rationalPoints G × rationalPoints G)
      (RationalSemistandardThetaSections.{u, uV} a ha muM) where
  toFun x :=
    { toFun := fun q t => productInducedOrbitRepresentation (decomposition t.1) (isClosed_radical t.1)
        (chosenLeviModel t.1).normCharacters
        (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2) x (q t)
      map_add' := fun q r => funext fun t => map_add _ _ _
      map_smul' := fun c q => funext fun t => map_smul _ c _ }
  map_one' := by
    ext q t A
    exact congrArg (fun L => L (q t A))
      (productInducedCoefficientObject (decomposition t.1) (isClosed_radical t.1) A.val.obj).representation.map_one
  map_mul' x y := by
    ext q t A
    exact congrArg (fun L => L (q t A))
      ((productInducedCoefficientObject (decomposition t.1) (isClosed_radical t.1) A.val.obj).representation.map_mul x y)

/-- VII.1.1(i) on the whole product, without any Fourier-support conclusion. -/
theorem rationalSemistandardFourierFamily_translate (g1 g2 : rationalPoints G)
    (f : RationalSchwartzSpace hKc hPK rho) :
    rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT
      (Space.translate (rationalTranslationWeights K.isOpen hKc hPK rho) g1 g2 f) =
    rationalSemistandardFourierProductRepresentation a ha muM (g1, g2)
      (rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f) := by
  funext t
  exact rationalSemistandardFourierOrbit_translate hG hi hnu hKc hPK rho hsw
    t.1 (chosenLeviModel t.1) (d t.1) (hdelta t.1) _ _ _ _
      (orbitRepresentative_isSquareIntegrable (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2) _ g1 g2 f

/-- Every component retains all representative and self-twist coherence. -/
theorem rationalSemistandardFourierFamily_coherent [muG.IsInvInvariant]
    (f : RationalSchwartzSpace hKc hPK rho) (t : RationalSemistandardTheta.{u, uV} a ha muM) :
    rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f t ∈
      coherentProductInducedOrbitSections (chosenLeviModel t.1).normCharacters
        (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2)
        (decomposition t.1) (isClosed_radical t.1) :=
  rationalSemistandardFourierOrbit_coherent hG hi hnu hKc hPK rho hsw
    t.1 (chosenLeviModel t.1) (d t.1) (hdelta t.1) _ _ _ _
      (orbitRepresentative_isSquareIntegrable (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2) _ f

/-- Conditional lift to a product of coherent smooth components. This target
carrier imposes no support condition. -/
def rationalSemistandardFourierSmoothFamily
    (hsm : ∀ (f : RationalSchwartzSpace hKc hPK rho) (t : RationalSemistandardTheta.{u, uV} a ha muM),
      rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f t ∈
        rationalSemistandardThetaComponentSpace a ha muM d t) :
    RationalSchwartzSpace hKc hPK rho →ₗ[ℂ]
      ∀ t : RationalSemistandardTheta.{u, uV} a ha muM, rationalSemistandardThetaComponentSpace a ha muM d t where
  toFun f t := ⟨rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f t,
    hsm f t⟩
  map_add' f g := funext fun t => Subtype.ext (congrFun (map_add
    (rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT) f g) t)
  map_smul' c f := funext fun t => Subtype.ext (congrFun (map_smul
    (rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT) c f) t)

/-- Full product version of the component smoothness target. The hypotheses
are the preceding analytic inputs at the requested actual component. -/
def RationalSemistandardFourierFamilySmoothnessStatement : Prop :=
  ∀ (t : RationalSemistandardTheta.{u, uV} a ha muM)
    (muL : Measure (levi t.1)) (muU : Measure (radical t.1)) (XiM sigmaM : levi t.1 → ℝ),
    RationalSemistandardFourierAnalyticInputs (muG := muG) hKc hPK rho
      t.1 (chosenLeviModel t.1) (d t.1)
      (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2)
      muL muU XiM sigmaM → ∀ f : RationalSchwartzSpace hKc hPK rho,
        rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f t ∈
          rationalSemistandardThetaComponentSpace a ha muM d t

/-- At the published standard compact picture, the component topology is the
existing rational standard orbit topology. -/
theorem rationalSemistandardFourierOrbitSpace_standard
    (I : Finset (RationalPointFamily.SimpleRoot i nu))
    (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi (standardIndex hG hi hnu I))) :
    rationalSemistandardFourierOrbitSpace (standardIndex hG hi hnu I)
      (standardLeviModel hG hi hnu I) (standardCompactData hG hi hnu I hKc hPK) pi =
    rationalInducedOrbitSectionSpace hG hi hnu I hKc hPK pi := rfl

section Standard

variable {B : Finset (RationalPointFamily.SimpleRoot i nu) → CommGroupScheme (Spec (CommRingCat.of F))}
  (b : ∀ I, (B I).toGrp ⟶ (standardLeviModel hG hi hnu I).scheme)
  (hb : ∀ I, IsSplitComponent (b I))
  [hStdNormal : ∀ I, (rationalLeviSplitCenter I (b I)).Normal]
  [hStdMeas : ∀ I, MeasurableSpace
    (levi (standardIndex hG hi hnu I) ⧸ rationalLeviSplitCenter I (b I))]
  [hStdBorel : ∀ I, BorelSpace
    (levi (standardIndex hG hi hnu I) ⧸ rationalLeviSplitCenter I (b I))]
  (eta : ∀ I, Measure (levi (standardIndex hG hi hnu I) ⧸ rationalLeviSplitCenter I (b I)))
  [hStdHaar : ∀ I, (eta I).IsHaarMeasure] [hStdInv : ∀ I, (eta I).IsInvInvariant]
  (hds : RationalSemistandardStandardDiscreteSeriesComparison.{u, uV}
    a ha muM hG hi hnu b hb eta)

/-- The exact compact and formal-degree normalization needed for equality with
the independently supplied standard-family data. This is not Fourier covariance. -/
def RationalSemistandardStandardFourierNormalization : Prop :=
  (∀ I, d (standardIndex hG hi hnu I) = standardCompactData hG hi hnu I hKc hPK) ∧
  ∀ (I : Finset (RationalPointFamily.SimpleRoot i nu))
    (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi (standardIndex hG hi hnu I)))
    (hfull : IsSquareIntegrableModCentralSubgroup
      ((chosenLeviModel (standardIndex hG hi hnu I)).splitCenter (a (standardIndex hG hi hnu I)))
      ((chosenLeviModel (standardIndex hG hi hnu I)).splitCenter_le_center
        (a (standardIndex hG hi hnu I)) (ha (standardIndex hG hi hnu I)))
      A.obj.representation (muM (standardIndex hG hi hnu I)))
    (hstd : IsSquareIntegrableModCentralSubgroup (rationalLeviSplitCenter I (b I))
      (rationalLeviSplitCenter_le_center I (b I) (hb I)) A.obj.representation (eta I)),
    representationFormalDegree
      ((chosenLeviModel (standardIndex hG hi hnu I)).splitCenter (a (standardIndex hG hi hnu I)))
      ((chosenLeviModel (standardIndex hG hi hnu I)).splitCenter_le_center
        (a (standardIndex hG hi hnu I)) (ha (standardIndex hG hi hnu I)))
      (muM (standardIndex hG hi hnu I))
      (compactOpenCofinal (standardIndex hG hi hnu I) (d (standardIndex hG hi hnu I))) hfull A.property.1 =
    representationFormalDegree (rationalLeviSplitCenter I (b I))
      (rationalLeviSplitCenter_le_center I (b I) (hb I)) (eta I)
      (by exact compactOpenCofinal_standardLevi I hKc) hstd A.property.1

variable (hrho : IsClosedSubgroup rho)
  (hKrho : (K : Subgroup (rationalPoints G)) ≤ rationalHeightSubgroup (F := F) rho)
  (hM : ∀ I : Finset (RationalPointFamily.SimpleRoot i nu), IsIwasawaPair
    ((standardParabolicPoints i nu ∅).subgroupOf (standardLeviPoints i nu (RationalPointFamily.rootSet i nu I)))
    ((K : Subgroup (rationalPoints G)).subgroupOf (standardLeviPoints i nu (RationalPointFamily.rootSet i nu I))))
  (hTA : ∀ (I : Finset (RationalPointFamily.SimpleRoot i nu))
    (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ)
      (G := standardLeviPoints i nu (RationalPointFamily.rootSet i nu I))),
    IsSquareIntegrableModCentralSubgroup (rationalLeviSplitCenter I (b I))
      (rationalLeviSplitCenter_le_center I (b I) (hb I)) pi.obj.representation (eta I) →
    ∀ A : UnitaryOrbitRepresentative (RationalPointFamily.leviRationalNormCharacters i nu I) pi,
      IsRationalLeviTempered hKc rho (hM I) A.val.obj)

/-- Exact comparison with the published actual standard product. Restriction
uses its prescribed orbit, representative and model maps. Normalizations are
preceding explicit conditions, not arbitrary comparison maps. -/
def RationalSemistandardFourierStandardComparisonStatement : Prop :=
  RationalSemistandardStandardFourierNormalization.{u, uV} hG hi hnu hKc hPK a ha muM d b hb eta →
    ∀ f : RationalSchwartzSpace hKc hPK rho,
      rationalStandardFullRestrict a ha muM hG hi hnu b hb eta hds
        (rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f) =
      rationalFourierThetaFamily hG hi hnu hKc hPK b hb eta rho hrho hKrho hM hsw hTA f

end Standard

end FullProduct

end Langlands.HarishChandraSchwartz
