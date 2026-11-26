import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardFourierFamily
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardInvariance
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardComparisonHaar

/-! # VII.1.4: Weyl covariance of the actual full Fourier family

Waldspurger (2003), Lemma VII.1.4, for `rationalSemistandardFourierFamily` and the
actual normalized comparison of `WeylSectionComparisonData`. The covariance and the
V.3.1 transport in the Fourier fibers are Prop-valued targets. The module proves
that the second implies the first (Waldspurger's proof), that the first is the
relation `IsWeylInvariant` for every family, and the elementary linearity and
translation laws. No Fourier support condition is used or concluded. -/

noncomputable section

set_option maxRecDepth 4096
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
open RationalSemistandard.InvariantComparison (Representatives)
open RationalSemistandard.WeylOrbits (weylElement)
open RationalSemistandard.WeylSections (orbitFiber)

local instance covarianceAmbientCompactOpen : Nonempty (CompactOpenSubgroup (rationalPoints G)) :=
  ⟨Langlands.BruhatTits.rationalPointCompactOpenSubgroup F G⟩
local instance covarianceParabolicLC (p : SemistandardSpectralIndex i) :
    LocallyCompactSpace (parabolic p) :=
  (isClosed_parabolic p).locallyCompactSpace

variable {nu : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hnu : IsGenericCocharacter i nu)
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
  {muG : Measure (rationalPoints G)} [muG.IsMulLeftInvariant] [muG.IsMulRightInvariant]
  (hsw : SquareIntegrableWeight muG (rationalXi hKc hPK) (rationalHeight (F := F) rho))

variable {Z : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ p, (Z p).toGrp ⟶ (chosenLeviModel p).scheme)
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

set_option hygiene false in
set_option quotPrecheck false in
local notation "Θ" => RationalSemistandardTheta.{u, uV} a ha muM

set_option hygiene false in
set_option quotPrecheck false in
local notation "fam" => rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT

section Fibers

omit [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  [∀ p, (muM p).IsInvInvariant] in
/-- Every actual inducing object of the orbit of a full index is square
integrable modulo the actual split center, for the measure of that index. -/
theorem rationalSemistandardFourierRepresentative_isSquareIntegrable (t : Θ) (A : Representatives a ha muM t) :
    IsSquareIntegrableModCentralSubgroup ((chosenLeviModel t.1).splitCenter (a t.1))
      ((chosenLeviModel t.1).splitCenter_le_center (a t.1) (ha t.1))
      A.val.obj.representation (muM t.1) :=
  unitaryOrbitRepresentative_isDiscreteSeries _ _ _ _ _
    (orbitRepresentative_isSquareIntegrable (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2) A

/-- The normalized coefficient map `E_P^G` on the fiber of the full Fourier family
at an actual inducing object: the map used in VII.1.1(ii) for that fiber. -/
abbrev rationalSemistandardFourierFiberCoefficient (t : Θ) (A : Representatives a ha muM t) :=
  rationalSemistandardFourierCoefficientMap hG t.1 (d t.1) (hdelta t.1) A.val.obj
    ((chosenLeviModel t.1).splitCenter (a t.1))
    ((chosenLeviModel t.1).splitCenter_le_center (a t.1) (ha t.1)) (muM t.1)
    (rationalSemistandardFourierRepresentative_isSquareIntegrable a ha muM t A)

/-- The inverse-formal-degree V.2 product on the same fiber: the form used in
VII.1.1(ii) for that fiber. -/
abbrev rationalSemistandardFourierFiberForm (t : Θ) (A : Representatives a ha muM t) :=
  rationalSemistandardFourierProductForm hG t.1 (d t.1) (hdelta t.1) A.val.obj
    ((chosenLeviModel t.1).splitCenter (a t.1))
    ((chosenLeviModel t.1).splitCenter_le_center (a t.1) (ha t.1)) (muM t.1)
    (rationalSemistandardFourierRepresentative_isSquareIntegrable a ha muM t A) A.val.property.1

/-- VII.1.1(ii) for one component of the full family: the coefficient pairing
against `f` is the inverse-degree product with the family's tensor. -/
theorem rationalSemistandardFourierFamily_pairing [muG.IsInvInvariant]
    (f : RationalSchwartzSpace hKc hPK rho) (t : Θ) (A : Representatives a ha muM t)
    (psi : orbitFiber A.val) :
    ∫ g, conj (rationalSemistandardFourierFiberCoefficient hG a ha muM d hdelta t A psi g) * f g ∂muG =
      (rationalSemistandardFourierFiberForm hG a ha muM d hdelta t A).inner psi (fam f t A) :=
  rationalSemistandardFourier_pairing hG hi hnu hKc hPK rho hsw t.1 (d t.1) (hdelta t.1) A.val.obj
    _ _ (muM t.1) (rationalSemistandardFourierRepresentative_isSquareIntegrable a ha muM t A) A.val.property.1 _ psi f

/-- The pairings of VII.1.1(ii) determine each component of the full family. -/
theorem rationalSemistandardFourierFamily_eq_of_pairings [muG.IsInvInvariant]
    (f : RationalSchwartzSpace hKc hPK rho) (t : Θ) (A : Representatives a ha muM t)
    (phi : orbitFiber A.val)
    (hphi : ∀ psi : orbitFiber A.val,
      ∫ g, conj (rationalSemistandardFourierFiberCoefficient hG a ha muM d hdelta t A psi g) * f g ∂muG =
        (rationalSemistandardFourierFiberForm hG a ha muM d hdelta t A).inner psi phi) :
    fam f t A = phi :=
  rationalSemistandardFourier_eq_of_pairings hG hi hnu hKc hPK rho hsw t.1 (d t.1) (hdelta t.1)
    A.val.obj _ _ (muM t.1) (rationalSemistandardFourierRepresentative_isSquareIntegrable a ha muM t A)
    A.val.property.1 _ f phi hphi

end Fibers

variable {hG} (C : WeylSectionComparisonData.{u, uV} a ha muM d hG)

/-- **Lemma VII.1.4** (Waldspurger 2003) for the actual full Fourier family.
For every `f`, every full index `t = (O, P)`, every relative Weyl element `w` (the source's `s`),
every semistandard parabolic `q = P'` whose Levi is the `w`-conjugate of the
Levi of `P`, every lift `n` of `w` in the common source compact and every
actual inducing object `A = ω` of `O`, the component at the transported index
`(sO, P')` evaluated at the conjugate object `sω` is the actual normalized
comparison `°c_{P'|P}(s, ω)` applied to the component at `(O, P)`.
The equality is in the coefficient fiber of the conjugate object `sω`.
The quotient Haar measures are normalized by their compact traces, as in I.1. -/
def RationalSemistandardFourierCovarianceStatement : Prop :=
  SourceMeasure.IntrinsicQuotientNormalization a muM d →
  ∀ (f : RationalSchwartzSpace hKc hPK rho) (t : Θ) (w : relativeWeylGroup i)
    (q : SemistandardSpectralIndex i),
    relativeWeylConjugateSubgroupFunctor i t.1.levi (C.centralizer_le t.1) w = q.levi →
    ∀ n : C.Lift t q, (weylElement (C.centralizer_le t.1) (d t.1).compact n).val = w →
    ∀ A : Representatives a ha muM t,
      fam f (C.target t q n) (C.representative t q n A) = C.fiberComparison t q n A (fam f t A)

/-- VII.1.4 is exactly the pointwise invariance relation `IsWeylInvariant` of the
invariant carrier, imposed on the full Fourier family of every `f`. No support
condition enters on either side. -/
theorem rationalSemistandardFourierCovarianceStatement_iff :
    RationalSemistandardFourierCovarianceStatement hi hnu hKc hPK rho hsw a ha muM d hdelta hT C ↔
      (SourceMeasure.IntrinsicQuotientNormalization a muM d →
        ∀ f : RationalSchwartzSpace hKc hPK rho, IsWeylInvariant C (fam f)) := by
  constructor
  · intro h hn f
    exact (isWeylInvariant_iff C (fam f)).mpr (h hn f)
  · intro h hn f
    exact (isWeylInvariant_iff C (fam f)).mp (h hn f)

/-- **Lemma V.3.1** (Waldspurger 2003) in the fibers of the Fourier family:
at every unitary point, the actual normalized comparison `°c_{P'|P}(s, ω)`
preserves the coefficient map `E_P^G` and the inverse-formal-degree product
used by VII.1.1(ii). The degree factor makes this depend on the I.1 normalization
of the quotient Haar measures, which is the displayed premise. -/
def RationalSemistandardFourierFiberTransportStatement : Prop :=
  SourceMeasure.IntrinsicQuotientNormalization a muM d →
  ∀ (t : Θ) (q : SemistandardSpectralIndex i) (n : C.Lift t q) (A : Representatives a ha muM t),
    (∀ v : orbitFiber A.val,
      rationalSemistandardFourierFiberCoefficient hG a ha muM d hdelta (C.target t q n)
          (C.representative t q n A) (C.fiberComparison t q n A v) =
        rationalSemistandardFourierFiberCoefficient hG a ha muM d hdelta t A v) ∧
    ∀ v w : orbitFiber A.val,
      (rationalSemistandardFourierFiberForm hG a ha muM d hdelta (C.target t q n)
          (C.representative t q n A)).inner (C.fiberComparison t q n A v) (C.fiberComparison t q n A w) =
        (rationalSemistandardFourierFiberForm hG a ha muM d hdelta t A).inner v w

/-- Waldspurger's proof of VII.1.4: VII.1.1(ii) twice, V.3.1 and the
bijectivity of the actual comparison, followed by uniqueness from pairings. -/
theorem rationalSemistandardFourierCovariance_of_fiberTransport [muG.IsInvInvariant]
    (h : RationalSemistandardFourierFiberTransportStatement a ha muM d hdelta C) :
    RationalSemistandardFourierCovarianceStatement hi hnu hKc hPK rho hsw a ha muM d hdelta hT C := by
  intro hn f t w q _ n _ A
  obtain ⟨hcoef, hform⟩ := h hn t q n A
  apply rationalSemistandardFourierFamily_eq_of_pairings hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT
  intro psi
  obtain ⟨v, rfl⟩ := (C.fiberComparison_bijective t q n A).2 psi
  rw [hcoef v, rationalSemistandardFourierFamily_pairing hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT,
    hform v]

section Elementary

/-- The set of Schwartz functions whose full Fourier family satisfies VII.1.4. -/
def rationalSemistandardFourierCovariantSubmodule : Submodule ℂ (RationalSchwartzSpace hKc hPK rho) where
  carrier := {f | IsWeylInvariant C (fam f)}
  zero_mem' := by
    intro t q n A
    change fam 0 (C.target t q n) (C.representative t q n A) = C.fiberComparison t q n A (fam 0 t A)
    rw [map_zero]
    exact (C.fiberComparison t q n A).map_zero.symm
  add_mem' := by
    intro f g hf hg t q n A
    change fam (f + g) (C.target t q n) (C.representative t q n A) =
      C.fiberComparison t q n A (fam (f + g) t A)
    rw [map_add]
    change fam f (C.target t q n) (C.representative t q n A) +
        fam g (C.target t q n) (C.representative t q n A) =
      C.fiberComparison t q n A (fam f t A + fam g t A)
    rw [hf t q n A, hg t q n A]
    exact ((C.fiberComparison t q n A).map_add _ _).symm
  smul_mem' := by
    intro c f hf t q n A
    change fam (c • f) (C.target t q n) (C.representative t q n A) =
      C.fiberComparison t q n A (fam (c • f) t A)
    rw [map_smul]
    change c • fam f (C.target t q n) (C.representative t q n A) =
      C.fiberComparison t q n A (c • fam f t A)
    rw [hf t q n A]
    exact ((C.fiberComparison t q n A).map_smul _ _).symm

@[simp] theorem mem_rationalSemistandardFourierCovariantSubmodule (f : RationalSchwartzSpace hKc hPK rho) :
    f ∈ rationalSemistandardFourierCovariantSubmodule hi hnu hKc hPK rho hsw a ha muM d hdelta hT C ↔
      IsWeylInvariant C (fam f) := Iff.rfl

omit [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  [∀ p, (muM p).IsInvInvariant] in
/-- The full product action of VII.1.1(i) is the action of the invariant carrier. -/
theorem rationalSemistandardFourierProductRepresentation_eq :
    rationalSemistandardFourierProductRepresentation a ha muM =
      rationalSemistandardThetaRepresentation.{u, uV} a ha muM := rfl

/-- Covariance is stable under the two-sided translations of `f`, by VII.1.1(i)
and the intertwining property of the actual comparison. -/
theorem translate_mem_rationalSemistandardFourierCovariantSubmodule (g1 g2 : rationalPoints G)
    {f : RationalSchwartzSpace hKc hPK rho}
    (hf : f ∈ rationalSemistandardFourierCovariantSubmodule hi hnu hKc hPK rho hsw a ha muM d hdelta hT C) :
    Space.translate (rationalTranslationWeights K.isOpen hKc hPK rho) g1 g2 f ∈
      rationalSemistandardFourierCovariantSubmodule hi hnu hKc hPK rho hsw a ha muM d hdelta hT C := by
  change IsWeylInvariant C (fam (Space.translate (rationalTranslationWeights K.isOpen hKc hPK rho) g1 g2 f))
  rw [rationalSemistandardFourierFamily_translate]
  exact IsWeylInvariant.action C (g1, g2) hf

/-- Under the I.1 normalization, VII.1.4 says that every Schwartz function is covariant. -/
theorem rationalSemistandardFourierCovarianceStatement_iff_submodule :
    RationalSemistandardFourierCovarianceStatement hi hnu hKc hPK rho hsw a ha muM d hdelta hT C ↔
      (SourceMeasure.IntrinsicQuotientNormalization a muM d →
        rationalSemistandardFourierCovariantSubmodule hi hnu hKc hPK rho hsw a ha muM d hdelta hT C = ⊤) := by
  rw [rationalSemistandardFourierCovarianceStatement_iff]
  constructor
  · intro h hn
    exact Submodule.eq_top_iff'.mpr fun f => h hn f
  · intro h hn f
    exact Submodule.eq_top_iff'.mp (h hn) f

/-- Comparison of carriers for one `f`. If a separately supplied witness places the
family of this `f` in the coherent smooth finite-support family, then VII.1.4 at `f`
is exactly membership of that element in the invariant carrier. This module supplies
no such witness: finite Fourier support is not asserted for general `f`. -/
theorem rationalSemistandardFourierFamily_mem_invariantSections_iff
    (f : RationalSchwartzSpace hKc hPK rho)
    (hfin : fam f ∈ rationalSemistandardThetaSmoothSections.{u, uV} a ha muM d) :
    (⟨fam f, hfin⟩ : rationalSemistandardThetaSmoothSections.{u, uV} a ha muM d) ∈
        rationalSemistandardThetaInvariantSections C ↔
      f ∈ rationalSemistandardFourierCovariantSubmodule hi hnu hKc hPK rho hsw a ha muM d hdelta hT C :=
  Iff.rfl

end Elementary

end Langlands.HarishChandraSchwartz
