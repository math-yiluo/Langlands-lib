import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardOrbitSections
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedFourierCoherence

/-! # The actual Fourier tensor for every semistandard parabolic -/

noncomputable section

set_option maxRecDepth 2048

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

namespace RationalSemistandard

local instance parabolicLC (p : SemistandardSpectralIndex i) :
    LocallyCompactSpace (parabolic p) := (isClosed_parabolic p).locallyCompactSpace

/-- Closedness of the literal Levi, from an actual representing closed model. -/
private theorem isClosed_fourierLevi (p : SemistandardSpectralIndex i) :
    IsClosed (levi p : Set (rationalPoints G)) :=
  isClosed_rationalPoint_subgroup F p.levi (chosenLeviModel p).inclusion
    (chosenLeviModel p).represents (chosenLeviModel p).closed

/-- Compact open subgroups of the literal Levi are cofinal. -/
theorem compactOpenCofinal (p : SemistandardSpectralIndex i) (d : CompactData p) :
    CompactOpenCofinal (levi p) := by
  have hc : IsCompact
      ((d.compact.comap (levi p).subtype continuous_subtype_val) : Set (levi p)) :=
    (isClosed_fourierLevi p).isClosedEmbedding_subtypeVal.isCompact_preimage d.isCompact
  have : Nonempty (CompactOpenSubgroup (levi p)) :=
    ⟨⟨d.compact.comap (levi p).subtype continuous_subtype_val, hc⟩⟩
  exact CompactOpenSubgroup.cofinal

/-- The compact factorization in the exact form used by normalized induction. -/
theorem CompactData.factorization_mem {p : SemistandardSpectralIndex i} (d : CompactData p) :
    ∀ g : rationalPoints G, ∃ q ∈ parabolic p, ∃ k ∈ d.compact, g = q * k := by
  intro g
  obtain ⟨q, k, h⟩ := d.factorization g
  exact ⟨q, q.property, k, k.property, h⟩

/-- The actual parabolic modular character equals its radical's Haar modulus. -/
def ModularNormalization (p : SemistandardSpectralIndex i) : Prop :=
  ∀ q : parabolic p, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter (radical p) (isClosed_radical p)
      (parabolic p) (decomposition p).le_normalizer q : ℝ≥0)

end RationalSemistandard

/-- The remaining semistandard modular comparison, in the reductive source setting. -/
def RationalSemistandardModularNormalizationStatement : Prop :=
  IsConnectedReductive G → IsMaximalSplitTorus i →
    ∀ p : SemistandardSpectralIndex i, RationalSemistandard.ModularNormalization p

open RationalSemistandard

variable {nu : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hnu : IsGenericCocharacter i nu)
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
  {mu : Measure (rationalPoints G)} [mu.IsMulLeftInvariant] [mu.IsMulRightInvariant]
  (hsw : SquareIntegrableWeight mu (rationalXi hKc hPK) (rationalHeight (F := F) rho))
  (p : SemistandardSpectralIndex i) (d : CompactData p)
  (hdelta : ModularNormalization p)

local instance parabolicLC : LocallyCompactSpace (parabolic p) :=
  (isClosed_parabolic p).locallyCompactSpace
local instance ambientCompactOpen : Nonempty (CompactOpenSubgroup (rationalPoints G)) :=
  ⟨Langlands.BruhatTits.rationalPointCompactOpenSubgroup F G⟩

variable (A : SmoothRep.{0, u, uV} ℂ (levi p))
  (C : Subgroup (levi p)) [C.Normal] (hC : C ≤ Subgroup.center (levi p))
  [MeasurableSpace (levi p ⧸ C)] [BorelSpace (levi p ⧸ C)]
  (muM : Measure (levi p ⧸ C)) [muM.IsHaarMeasure] [muM.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation muM)
  (hirr : A.representation.IsIrreducible)
  (hT : HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) rho)
    ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj A).representation)

/-- VII.1: the inverse actual coefficient-tensor map applied to
`d(A) (I_P^G A)(check f)`. The induced temperedness and modular comparison
are explicit preceding inputs. -/
def rationalSemistandardInducedFourierTransform :
    RationalSchwartzSpace hKc hPK rho →ₗ[ℂ]
      productInducedCoefficientObject (decomposition p) (isClosed_radical p) A :=
  inducedFourierTransform (decomposition p) (isClosed_radical p)
    (isClosed_parabolic p) d.projection_continuous d.compact d.isCompact d.factorization_mem
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    hdelta A (compactOpenCofinal p d) C hC muM hsq hirr
    (rationalL2Weights K.isOpen hKc hPK rho hsw) hT
    (rationalXi_inv hG hi hnu K.isOpen hKc hPK) (rationalHeight_inv rho)

/-- The construction is literally the published generic actual transform. -/
theorem rationalSemistandardInducedFourierTransform_eq_inducedFourierTransform :
    rationalSemistandardInducedFourierTransform hG hi hnu hKc hPK rho hsw
      p d hdelta A C hC muM hsq hirr hT =
    inducedFourierTransform (decomposition p) (isClosed_radical p)
      (isClosed_parabolic p) d.projection_continuous d.compact d.isCompact d.factorization_mem
      (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
      hdelta A (compactOpenCofinal p d) C hC muM hsq hirr
      (rationalL2Weights K.isOpen hKc hPK rho hsw) hT
      (rationalXi_inv hG hi hnu K.isOpen hKc hPK) (rationalHeight_inv rho) := rfl

/-- The exact embedding of the dependency's actual fiber into tensors. -/
abbrev rationalSemistandardFourierTensorEquiv :=
  CompactInduction.coefficientTensorEquiv (decomposition p) (isClosed_radical p) A
    d.compact d.isCompact (isClosed_parabolic p) d.projection_continuous d.factorization_mem
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    hdelta hsq.1

/-- The actual normalized coefficient map, with the same compact Haar probability. -/
abbrev rationalSemistandardFourierCoefficientMap :=
  CompactInduction.coefficientMap (decomposition p) (isClosed_radical p) A
    d.compact d.isCompact (isClosed_parabolic p) d.projection_continuous d.factorization_mem
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    hdelta hsq.1

/-- The V.2 product, normalized by the actual inducing formal degree. -/
abbrev rationalSemistandardFourierProductForm :=
  CompactInduction.formalDegreeProductForm (decomposition p) (isClosed_radical p)
    (isClosed_parabolic p) d.compact d.isCompact d.factorization_mem
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    hdelta A (compactOpenCofinal p d) C hC muM hsq hirr

/-- Admissibility of the actual normalized induction, deduced from discrete-series
admissibility and the supplied compact picture. -/
abbrev rationalSemistandardFourierAdmissible :=
  CompactInduction.induced_isAdmissible (decomposition p) (isClosed_radical p)
    d.compact d.isCompact d.factorization_mem A d.projection_continuous hsq.1

/-- Under the dependency's tensor equivalence the transform is precisely
`d(A)` times the tensor of the actual induced operator at `check f`. -/
theorem rationalSemistandardFourierTensorEquiv_transform
    (f : RationalSchwartzSpace hKc hPK rho) :
    rationalSemistandardFourierTensorEquiv hG p d hdelta A C hC muM hsq
        (rationalSemistandardInducedFourierTransform hG hi hnu hKc hPK rho hsw
      p d hdelta A C hC muM hsq hirr hT f) =
      coefficientFourierTransform ((normalizedInductionFunctor (decomposition p)
        (isClosed_radical p)).obj A) (rationalL2Weights K.isOpen hKc hPK rho hsw)
        (CompactInduction.induced_isAdmissible (decomposition p) (isClosed_radical p)
    d.compact d.isCompact d.factorization_mem A d.projection_continuous hsq.1) hT
        (rationalXi_inv hG hi hnu K.isOpen hKc hPK) (rationalHeight_inv rho)
        (representationFormalDegree C hC muM (compactOpenCofinal p d) hsq hirr) f :=
  coefficientTensorEquiv_inducedFourierTransform (decomposition p) (isClosed_radical p)
    (isClosed_parabolic p) d.projection_continuous d.compact d.isCompact d.factorization_mem
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    hdelta A (compactOpenCofinal p d) C hC muM hsq hirr
    (rationalL2Weights K.isOpen hKc hPK rho hsw) hT
    (rationalXi_inv hG hi hnu K.isOpen hKc hPK) (rationalHeight_inv rho) f

/-- VII.1 (1): the actual endomorphism of this tensor is
`d(A) (I_P^G A)(check f)`. -/
theorem rationalSemistandardFourier_operator
    (f : RationalSchwartzSpace hKc hPK rho) :
    coefficientTensorToEnd ((normalizedInductionFunctor (decomposition p)
        (isClosed_radical p)).obj A)
      (rationalSemistandardFourierTensorEquiv hG p d hdelta A C hC muM hsq
        (rationalSemistandardInducedFourierTransform hG hi hnu hKc hPK rho hsw
      p d hdelta A C hC muM hsq hirr hT f)) =
      (representationFormalDegree C hC muM (compactOpenCofinal p d) hsq hirr : ℂ) •
        schwartzAction (rationalL2Weights K.isOpen hKc hPK rho hsw)
          (CompactInduction.induced_isAdmissible (decomposition p) (isClosed_radical p)
    d.compact d.isCompact d.factorization_mem A d.projection_continuous hsq.1) hT
          (Space.check (rationalXi_inv hG hi hnu K.isOpen hKc hPK)
            (rationalHeight_inv rho) f) := by
  rw [rationalSemistandardFourierTensorEquiv_transform]
  exact coefficientTensorToEnd_coefficientFourierTransform _ _ _ _ _ _ _ f

/-- The operator in VII.1 has finite rank, by the actual tensor embedding. -/
theorem rationalSemistandardFourier_operator_finiteRank
    (f : RationalSchwartzSpace hKc hPK rho) :
    coefficientTensorToEnd ((normalizedInductionFunctor (decomposition p)
        (isClosed_radical p)).obj A)
      (rationalSemistandardFourierTensorEquiv hG p d hdelta A C hC muM hsq
        (rationalSemistandardInducedFourierTransform hG hi hnu hKc hPK rho hsw
      p d hdelta A C hC muM hsq hirr hT f)) ∈
      finiteRankEnd ((normalizedInductionFunctor (decomposition p)
        (isClosed_radical p)).obj A) :=
  coefficientTensorToEnd_mem_finiteRankEnd _ _

/-- VII.1.1(i), with `translate g1 g2 f(x) = f(g2⁻¹ * x * g1)`. -/
theorem rationalSemistandardFourier_translate (g1 g2 : rationalPoints G)
    (f : RationalSchwartzSpace hKc hPK rho) :
    rationalSemistandardInducedFourierTransform hG hi hnu hKc hPK rho hsw
      p d hdelta A C hC muM hsq hirr hT
        (Space.translate (rationalTranslationWeights K.isOpen hKc hPK rho) g1 g2 f) =
      (productInducedCoefficientObject (decomposition p) (isClosed_radical p) A).representation
        (g1, g2) (rationalSemistandardInducedFourierTransform hG hi hnu hKc hPK rho hsw
      p d hdelta A C hC muM hsq hirr hT f) :=
  inducedFourierTransform_translate (decomposition p) (isClosed_radical p)
    (isClosed_parabolic p) d.projection_continuous d.compact d.isCompact d.factorization_mem
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    hdelta A (compactOpenCofinal p d) C hC muM hsq hirr
    (rationalL2Weights K.isOpen hKc hPK rho hsw) hT
    (rationalXi_inv hG hi hnu K.isOpen hKc hPK) (rationalHeight_inv rho)
    (rationalTranslationWeights K.isOpen hKc hPK rho) g1 g2 f

include hsw hT in
/-- The coefficient pairing in VII.1.1(ii) is an absolutely convergent integral. -/
theorem rationalSemistandardFourier_pairing_integrable
    (psi : productInducedCoefficientObject (decomposition p) (isClosed_radical p) A)
    (f : RationalSchwartzSpace hKc hPK rho) :
    Integrable (fun g => conj (rationalSemistandardFourierCoefficientMap hG p d hdelta A C hC muM hsq psi g) * f g) mu :=
  integrable_conj_coefficientTensorMap_mul _ (rationalL2Weights K.isOpen hKc hPK rho hsw)
    (CompactInduction.induced_isAdmissible (decomposition p) (isClosed_radical p)
    d.compact d.isCompact d.factorization_mem A d.projection_continuous hsq.1) hT
    (rationalSemistandardFourierTensorEquiv hG p d hdelta A C hC muM hsq psi) f

/-- VII.1.1(ii) for the actual quotient Haar measure, formal degree and V.2 product. -/
theorem rationalSemistandardFourier_pairing [mu.IsInvInvariant]
    (psi : productInducedCoefficientObject (decomposition p) (isClosed_radical p) A)
    (f : RationalSchwartzSpace hKc hPK rho) :
    ∫ g, conj (rationalSemistandardFourierCoefficientMap hG p d hdelta A C hC muM hsq psi g) * f g ∂mu =
      (rationalSemistandardFourierProductForm hG p d hdelta A C hC muM hsq hirr).inner psi
        (rationalSemistandardInducedFourierTransform hG hi hnu hKc hPK rho hsw
      p d hdelta A C hC muM hsq hirr hT f) :=
  integral_conj_coefficientMap_mul_eq_inner (decomposition p) (isClosed_radical p)
    (isClosed_parabolic p) d.projection_continuous d.compact d.isCompact d.factorization_mem
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    hdelta A (compactOpenCofinal p d) C hC muM hsq hirr
    (rationalL2Weights K.isOpen hKc hPK rho hsw) hT
    (rationalXi_inv hG hi hnu K.isOpen hKc hPK) (rationalHeight_inv rho) psi f

/-- VII.1.1(iii). Here the source's `lambda(g)` is `translate 1 g`,
so `lambda(g) check f(x) = check f(g⁻¹ * x)`. The trace is that of the
actual finite-rank normalized induced operator. -/
theorem rationalSemistandardFourier_trace
    (f : RationalSchwartzSpace hKc hPK rho) (g : rationalPoints G) :
    rationalSemistandardFourierCoefficientMap hG p d hdelta A C hC muM hsq
        (rationalSemistandardInducedFourierTransform hG hi hnu hKc hPK rho hsw
      p d hdelta A C hC muM hsq hirr hT f) g =
      representationFormalDegree C hC muM (compactOpenCofinal p d) hsq hirr *
        FiniteRankEnd.trace (finiteRankSchwartzAction
          (rationalL2Weights K.isOpen hKc hPK rho hsw)
          (CompactInduction.induced_isAdmissible (decomposition p) (isClosed_radical p)
    d.compact d.isCompact d.factorization_mem A d.projection_continuous hsq.1) hT
          (Space.translate (rationalTranslationWeights K.isOpen hKc hPK rho) 1 g
            (Space.check (rationalXi_inv hG hi hnu K.isOpen hKc hPK)
              (rationalHeight_inv rho) f))) :=
  coefficientMap_inducedFourierTransform (decomposition p) (isClosed_radical p)
    (isClosed_parabolic p) d.projection_continuous d.compact d.isCompact d.factorization_mem
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    hdelta A (compactOpenCofinal p d) C hC muM hsq hirr
    (rationalL2Weights K.isOpen hKc hPK rho hsw) hT
    (rationalXi_inv hG hi hnu K.isOpen hKc hPK) (rationalHeight_inv rho)
    (rationalTranslationWeights K.isOpen hKc hPK rho) f g

/-- The coefficient pairing characterizes the actual transform uniquely. -/
theorem rationalSemistandardFourier_eq_of_pairings [mu.IsInvInvariant]
    (f : RationalSchwartzSpace hKc hPK rho)
    (phi : productInducedCoefficientObject (decomposition p) (isClosed_radical p) A)
    (hphi : ∀ psi, ∫ g, conj (rationalSemistandardFourierCoefficientMap hG p d hdelta A C hC muM hsq psi g) * f g ∂mu =
      (rationalSemistandardFourierProductForm hG p d hdelta A C hC muM hsq hirr).inner psi phi) :
    rationalSemistandardInducedFourierTransform hG hi hnu hKc hPK rho hsw
      p d hdelta A C hC muM hsq hirr hT f = phi :=
  inducedFourierTransform_eq_of_forall_integral (decomposition p) (isClosed_radical p)
    (isClosed_parabolic p) d.projection_continuous d.compact d.isCompact d.factorization_mem
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    hdelta A (compactOpenCofinal p d) C hC muM hsq hirr
    (rationalL2Weights K.isOpen hKc hPK rho hsw) hT
    (rationalXi_inv hG hi hnu K.isOpen hKc hPK) (rationalHeight_inv rho) f phi hphi

/-- Every inducing equivalence, including every self-twist, transports the
actual Fourier tensor to the tensor at the target inducing representation. -/
theorem rationalSemistandardFourier_transport [mu.IsInvInvariant]
    (B : SmoothRep.{0, u, uV} ℂ (levi p))
    (hsqB : IsSquareIntegrableModCentralSubgroup C hC B.representation muM)
    (hirrB : B.representation.IsIrreducible)
    (hTB : HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) rho)
      ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj B).representation)
    (e : A.representation.Equiv B.representation) (f : RationalSchwartzSpace hKc hPK rho) :
    productInducedCoefficientTransport (decomposition p) (isClosed_radical p) e
        (rationalSemistandardInducedFourierTransform hG hi hnu hKc hPK rho hsw
      p d hdelta A C hC muM hsq hirr hT f) =
      rationalSemistandardInducedFourierTransform hG hi hnu hKc hPK rho hsw
        p d hdelta B C hC muM hsqB hirrB hTB f :=
  productInducedCoefficientTransport_inducedFourierTransform
    (decomposition p) (isClosed_radical p) (isClosed_parabolic p)
    d.projection_continuous d.compact d.isCompact d.factorization_mem
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    hdelta (compactOpenCofinal p d) C hC muM hsq hirr hsqB hirrB
    (rationalL2Weights K.isOpen hKc hPK rho hsw) hT hTB
    (rationalXi_inv hG hi hnu K.isOpen hKc hPK) (rationalHeight_inv rho) e f

@[simp] theorem rationalSemistandardFourier_add
    (f g : RationalSchwartzSpace hKc hPK rho) :
    rationalSemistandardInducedFourierTransform hG hi hnu hKc hPK rho hsw
      p d hdelta A C hC muM hsq hirr hT (f + g) =
      rationalSemistandardInducedFourierTransform hG hi hnu hKc hPK rho hsw
      p d hdelta A C hC muM hsq hirr hT f +
        rationalSemistandardInducedFourierTransform hG hi hnu hKc hPK rho hsw
      p d hdelta A C hC muM hsq hirr hT g :=
  map_add _ f g

@[simp] theorem rationalSemistandardFourier_smul
    (c : ℂ) (f : RationalSchwartzSpace hKc hPK rho) :
    rationalSemistandardInducedFourierTransform hG hi hnu hKc hPK rho hsw
      p d hdelta A C hC muM hsq hirr hT (c • f) =
      c • rationalSemistandardInducedFourierTransform hG hi hnu hKc hPK rho hsw
      p d hdelta A C hC muM hsq hirr hT f :=
  map_smul _ c f

/-- The prescribed comparison between two compact pictures is induced by their
actual coefficient-tensor equivalences. It is not a freely supplied map. -/
def rationalSemistandardFourierCompactTransport (e : CompactData p) :=
  (rationalSemistandardFourierTensorEquiv hG p d hdelta A C hC muM hsq).trans
    (rationalSemistandardFourierTensorEquiv hG p e hdelta A C hC muM hsq).symm

/-- The actual operator definition commutes with the specified change of compact
picture. No assertion that the raw identity preserves all compact normalizations
is needed. -/
theorem rationalSemistandardFourier_compactTransport (e : CompactData p)
    (f : RationalSchwartzSpace hKc hPK rho) :
    rationalSemistandardFourierCompactTransport hG p d hdelta A C hC muM hsq e
        (rationalSemistandardInducedFourierTransform hG hi hnu hKc hPK rho hsw
      p d hdelta A C hC muM hsq hirr hT f) =
      rationalSemistandardInducedFourierTransform hG hi hnu hKc hPK rho hsw
        p e hdelta A C hC muM hsq hirr hT f := by
  let t := coefficientFourierTransform ((normalizedInductionFunctor (decomposition p)
    (isClosed_radical p)).obj A) (rationalL2Weights K.isOpen hKc hPK rho hsw)
    (rationalSemistandardFourierAdmissible p d A C hC muM hsq) hT
    (rationalXi_inv hG hi hnu K.isOpen hKc hPK) (rationalHeight_inv rho)
    (representationFormalDegree C hC muM (compactOpenCofinal p d) hsq hirr) f
  change (rationalSemistandardFourierTensorEquiv hG p e hdelta A C hC muM hsq).symm
      ((rationalSemistandardFourierTensorEquiv hG p d hdelta A C hC muM hsq)
        ((rationalSemistandardFourierTensorEquiv hG p d hdelta A C hC muM hsq).symm t)) =
    (rationalSemistandardFourierTensorEquiv hG p e hdelta A C hC muM hsq).symm t
  rw [Representation.Equiv.apply_symm_apply]

/-- Changes of actual central quotient data preserve the transform when their
actual formal degrees agree. This premise records the Haar normalization;
square-integrability alone would not identify two differently scaled measures. -/
theorem rationalSemistandardFourier_normalization
    (D : Subgroup (levi p)) [D.Normal] (hD : D ≤ Subgroup.center (levi p))
    [MeasurableSpace (levi p ⧸ D)] [BorelSpace (levi p ⧸ D)]
    (eta : Measure (levi p ⧸ D)) [eta.IsHaarMeasure] [eta.IsInvInvariant]
    (hsqD : IsSquareIntegrableModCentralSubgroup D hD A.representation eta)
    (hdegree : representationFormalDegree C hC muM (compactOpenCofinal p d) hsq hirr =
      representationFormalDegree D hD eta (compactOpenCofinal p d) hsqD hirr) :
    rationalSemistandardInducedFourierTransform hG hi hnu hKc hPK rho hsw
      p d hdelta A C hC muM hsq hirr hT =
    rationalSemistandardInducedFourierTransform hG hi hnu hKc hPK rho hsw
      p d hdelta A D hD eta hsqD hirr hT := by
  unfold rationalSemistandardInducedFourierTransform inducedFourierTransform
  rw [hdegree]

section StandardComparison

variable (I : Finset (RationalPointFamily.SimpleRoot i nu))
  (A0 : SmoothRep.{0, u, uV} ℂ (levi (standardIndex hG hi hnu I)))
  (C0 : Subgroup (levi (standardIndex hG hi hnu I))) [hNormal0 : C0.Normal]
  (hC0 : C0 ≤ Subgroup.center (levi (standardIndex hG hi hnu I)))
  [hMeas0 : MeasurableSpace (levi (standardIndex hG hi hnu I) ⧸ C0)]
  [hBorel0 : BorelSpace (levi (standardIndex hG hi hnu I) ⧸ C0)]
  (mu0 : Measure (levi (standardIndex hG hi hnu I) ⧸ C0))
  [hHaar0 : mu0.IsHaarMeasure] [hInv0 : mu0.IsInvInvariant]
  (hsq0 : IsSquareIntegrableModCentralSubgroup C0 hC0 A0.representation mu0)
  (hirr0 : A0.representation.IsIrreducible)
  (hrho : IsClosedSubgroup rho)
  (hKrho : (K : Subgroup (rationalPoints G)) ≤ rationalHeightSubgroup (F := F) rho)
  (hM : IsIwasawaPair
    ((standardParabolicPoints i nu ∅).subgroupOf (levi (standardIndex hG hi hnu I)))
    ((K : Subgroup (rationalPoints G)).subgroupOf (levi (standardIndex hG hi hnu I))))
  (hTA0 : IsRationalLeviTempered hKc rho hM A0)

/-- At a standard index the modular comparison is the published theorem. -/
theorem rationalSemistandardModularNormalization_standard :
    ModularNormalization (standardIndex hG hi hnu I) := by
  haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hnu I
  exact modularCharacter_standardParabolicPoints hG hi hnu I rfl
    (RationalPointFamily.rootSet_subset i nu I)

/-- With the published standard compact picture and induced-temperedness proof,
the semistandard transform is exactly `rationalInducedFourierTransform`.
Only proof-irrelevant witnesses differ. -/
theorem rationalSemistandardFourier_standard :
    rationalSemistandardInducedFourierTransform hG hi hnu hKc hPK rho hsw
      (standardIndex hG hi hnu I) (standardCompactData hG hi hnu I hKc hPK)
      (rationalSemistandardModularNormalization_standard hG hi hnu I)
      A0 C0 hC0 mu0 hsq0 hirr0
      (rationalHasTemperedCoefficients_normalizedInduction rho hG hi hnu
        (RationalPointFamily.rootSet_subset i nu I) I rfl K hKc hPK (by exact hM) hrho hKrho A0
        hsq0.1 hTA0) =
    @rationalInducedFourierTransform F _ _ _ _ S G _ _ i nu hG hi hnu I K hKc hPK N _
      rho hrho hKrho (by exact hM) A0 C0 hNormal0 hC0 hMeas0 hBorel0 mu0 hHaar0 hInv0
      hsq0 hirr0 hTA0 mu _ _ hsw := rfl

end StandardComparison

end Langlands.HarishChandraSchwartz
