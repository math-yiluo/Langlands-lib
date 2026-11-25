import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardFourierFamily
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardThetaFixedSupport

/-! # Support of the actual Fourier family in `Theta^H` (Waldspurger VIII.1.3) -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
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

local instance fourierSupportCompactOpen : Nonempty (CompactOpenSubgroup (rationalPoints G)) :=
  ⟨Langlands.BruhatTits.rationalPointCompactOpenSubgroup F G⟩
local instance fourierSupportParabolicLC (p : SemistandardSpectralIndex i) :
    LocallyCompactSpace (parabolic p) :=
  (isClosed_parabolic p).locallyCompactSpace

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

/-! ## The support inclusion -/

/-- `psi_f[O, P] = 0` when `(O, P) ∉ Theta^H` and `f` is right invariant under
`H`: every value of the component is the actual induced Fourier transform at a
member of the orbit, which vanishes by Lemma VII.1.1(i) as soon as the induced
representation has no nonzero `H`-fixed vector. -/
theorem rationalSemistandardFourierFamily_apply_eq_zero_of_not_mem_thetaFixed
    {H : Subgroup (rationalPoints G)} (f : RationalSchwartzSpace hKc hPK rho)
    (hf : ∀ k ∈ H, ∀ g, f (g * k) = f g) (t : RationalSemistandardTheta.{u, uV} a ha muM)
    (ht : t ∉ rationalSemistandardThetaFixed.{u, uV} a ha muM H) :
    rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f t = 0 := by
  funext A
  rw [rationalSemistandardFourierFamily_apply,
    rationalSemistandardInducedFourierTransform_eq_inducedFourierTransform]
  refine inducedFourierTransform_eq_zero_of_fixedVectors_eq_bot _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ (rationalTranslationWeights K.isOpen hKc hPK rho) ?_ f hf
  by_contra hA
  apply ht
  rw [mem_rationalSemistandardThetaFixed]
  have hmem := mk_mem_inducedDiscreteSeriesFixedOrbits_of_representative (decomposition t.1)
    (isClosed_radical t.1) ((chosenLeviModel t.1).splitCenter (a t.1))
    ((chosenLeviModel t.1).splitCenter_le_center (a t.1) (ha t.1)) (muM t.1)
    (chosenLeviModel t.1).normCharacters
    (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2)
    (orbitRepresentative_isSquareIntegrable (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2)
    A hA
  rwa [mk_discreteSeriesClass_orbitRepresentative] at hmem

/-- Waldspurger VIII.1.3, support inclusion, for right `H`-invariance: the
actual family `psi_f` is supported in `Theta^H`. -/
theorem rationalSemistandardFourierFamily_mem_thetaFixedSupported
    {H : Subgroup (rationalPoints G)} (f : RationalSchwartzSpace hKc hPK rho)
    (hf : ∀ k ∈ H, ∀ g, f (g * k) = f g) :
    rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f ∈
      rationalSemistandardThetaFixedSupported.{u, uV} a ha muM H := fun t ht =>
  by_contra fun hn => ht
    (rationalSemistandardFourierFamily_apply_eq_zero_of_not_mem_thetaFixed hG hi hnu hKc hPK rho
      hsw a ha muM d hdelta hT f hf t hn)

/-- The support inclusion of Waldspurger VIII.1.3, in its source form: for a
compact open subgroup `H` and `f` bi-invariant under `H`, every nonzero
component `psi_f[O, P]` has its index in `Theta^H`. -/
def RationalSemistandardFourierThetaFixedSupportStatement : Prop :=
  ∀ H : Subgroup (rationalPoints G), IsOpen (H : Set (rationalPoints G)) →
    IsCompact (H : Set (rationalPoints G)) → ∀ f : RationalSchwartzSpace hKc hPK rho,
      IsBiInvariant H f →
        rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f ∈
          rationalSemistandardThetaFixedSupported.{u, uV} a ha muM H

/-- The support inclusion holds: only right invariance is used. -/
theorem rationalSemistandardFourierThetaFixedSupportStatement_holds :
    RationalSemistandardFourierThetaFixedSupportStatement hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT := fun _ _ _ f hf =>
  rationalSemistandardFourierFamily_mem_thetaFixedSupported hG hi hnu hKc hPK rho hsw
    a ha muM d hdelta hT f fun k hk g => by
      have h := hf 1 (one_mem _) k hk g
      rwa [one_mul] at h

/-- The proper support inclusion: the proper part of the support lies in
`Theta^H`. -/
theorem rationalSemistandardFourierFamily_mem_thetaProperFixedSupported
    {H : Subgroup (rationalPoints G)} (f : RationalSchwartzSpace hKc hPK rho)
    (hf : ∀ k ∈ H, ∀ g, f (g * k) = f g) :
    rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f ∈
      rationalSemistandardThetaProperFixedSupported.{u, uV} a ha muM H :=
  rationalSemistandardThetaFixedSupported_le_proper a ha muM H
    (rationalSemistandardFourierFamily_mem_thetaFixedSupported hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT f hf)

/-! ## Conditional VIII.1.3(ii) for the actual family -/

/-- Full VIII.1.3(ii) for the actual family: `psi_f` has finite support for
every `f`. -/
def RationalSemistandardFourierFiniteSupportStatement : Prop :=
  ∀ f : RationalSchwartzSpace hKc hPK rho,
    (rationalSemistandardThetaSupport.{u, uV} a ha muM
      (rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f)).Finite

/-- Proper VIII.1.3(ii) for the actual family: only the components at `P ≠ G`
are required to be finitely many nonzero. -/
def RationalProperSemistandardFourierFiniteSupportStatement : Prop :=
  ∀ f : RationalSchwartzSpace hKc hPK rho,
    (rationalSemistandardThetaSupport.{u, uV} a ha muM
        (rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f) ∩
      rationalSemistandardThetaProper.{u, uV} a ha muM).Finite

/-- Full VIII.1.3(ii), conditionally on the support inclusion and the full
finite-index conclusion of VIII.1.3(i) at every compact open level. -/
theorem rationalSemistandardFourierFiniteSupport_of_support_of_fixedFinite
    (hsupp : RationalSemistandardFourierThetaFixedSupportStatement hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT)
    (hfin : ∀ H : Subgroup (rationalPoints G), IsOpen (H : Set (rationalPoints G)) →
      IsCompact (H : Set (rationalPoints G)) →
        (rationalSemistandardThetaFixed.{u, uV} a ha muM H).Finite) :
    RationalSemistandardFourierFiniteSupportStatement hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT := by
  intro f
  obtain ⟨H, hH⟩ := Space.exists_isBiInvariant f
  exact finite_rationalSemistandardThetaSupport_of_fixedSupported
    (hsupp H.toSubgroup H.1.isOpen H.2 f hH) (hfin H.toSubgroup H.1.isOpen H.2)

/-- Proper VIII.1.3(ii), conditionally on the support inclusion and the proper
finite-index conclusion of VIII.1.3(i) (finiteness of `Theta^H - Theta^H_G`). -/
theorem rationalProperSemistandardFourierFiniteSupport_of_support_of_fixedFinite
    (hsupp : RationalSemistandardFourierThetaFixedSupportStatement hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT)
    (hfin : ∀ H : Subgroup (rationalPoints G), IsOpen (H : Set (rationalPoints G)) →
      IsCompact (H : Set (rationalPoints G)) →
        (rationalSemistandardThetaFixed.{u, uV} a ha muM H ∩
          rationalSemistandardThetaProper.{u, uV} a ha muM).Finite) :
    RationalProperSemistandardFourierFiniteSupportStatement hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT := by
  intro f
  obtain ⟨H, hH⟩ := Space.exists_isBiInvariant f
  exact finite_rationalSemistandardThetaSupport_inter_proper_of_properFixedSupported
    (rationalSemistandardThetaFixedSupported_le_proper a ha muM H.toSubgroup
      (hsupp H.toSubgroup H.1.isOpen H.2 f hH)) (hfin H.toSubgroup H.1.isOpen H.2)

/-- Full VIII.1.3(ii) from the full finite-index conclusion alone, the support
inclusion being proved. -/
theorem rationalSemistandardFourierFiniteSupport_of_fixedFinite
    (hfin : ∀ H : Subgroup (rationalPoints G), IsOpen (H : Set (rationalPoints G)) →
      IsCompact (H : Set (rationalPoints G)) →
        (rationalSemistandardThetaFixed.{u, uV} a ha muM H).Finite) :
    RationalSemistandardFourierFiniteSupportStatement hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT :=
  rationalSemistandardFourierFiniteSupport_of_support_of_fixedFinite hG hi hnu hKc hPK rho hsw
    a ha muM d hdelta hT
    (rationalSemistandardFourierThetaFixedSupportStatement_holds hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT) hfin

/-- Proper VIII.1.3(ii) from the proper finite-index conclusion alone. -/
theorem rationalProperSemistandardFourierFiniteSupport_of_fixedFinite
    (hfin : ∀ H : Subgroup (rationalPoints G), IsOpen (H : Set (rationalPoints G)) →
      IsCompact (H : Set (rationalPoints G)) →
        (rationalSemistandardThetaFixed.{u, uV} a ha muM H ∩
          rationalSemistandardThetaProper.{u, uV} a ha muM).Finite) :
    RationalProperSemistandardFourierFiniteSupportStatement hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT :=
  rationalProperSemistandardFourierFiniteSupport_of_support_of_fixedFinite hG hi hnu hKc hPK rho
    hsw a ha muM d hdelta hT
    (rationalSemistandardFourierThetaFixedSupportStatement_holds hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT) hfin

/-- The full statement implies the proper one. -/
theorem RationalSemistandardFourierFiniteSupportStatement.proper
    (h : RationalSemistandardFourierFiniteSupportStatement hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT) :
    RationalProperSemistandardFourierFiniteSupportStatement hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT :=
  fun f => (h f).subset Set.inter_subset_left

/-! ## Componentwise smoothness from the full smoothness target -/

/-- The componentwise smoothness consumed below, obtained from the full smoothness target
`RationalSemistandardFourierFamilySmoothnessStatement` and its analytic inputs at every
component. -/
theorem rationalSemistandardFourierFamily_mem_componentSpace_of_smoothness
    (hS : RationalSemistandardFourierFamilySmoothnessStatement (muG := muG) hG hi hnu hKc hPK rho
      hsw a ha muM d hdelta hT)
    (hin : ∀ t : RationalSemistandardTheta.{u, uV} a ha muM,
      ∃ (muL : Measure (levi t.1)) (muU : Measure (radical t.1)) (XiM sigmaM : levi t.1 → ℝ),
        RationalSemistandardFourierAnalyticInputs (muG := muG) hKc hPK rho
          t.1 (chosenLeviModel t.1) (d t.1)
          (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2)
          muL muU XiM sigmaM)
    (f : RationalSchwartzSpace hKc hPK rho) (t : RationalSemistandardTheta.{u, uV} a ha muM) :
    rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f t ∈
      rationalSemistandardThetaComponentSpace.{u, uV} a ha muM d t := by
  obtain ⟨muL, muU, XiM, sigmaM, h⟩ := hin t
  exact hS t muL muU XiM sigmaM h f

/-! ## Finite-support and proper-supported restrictions -/

/-- The actual family as a linear map into the direct sum `C^infinity(Theta)`.
It is constructed only from componentwise smoothness and the full VIII.1.3(ii)
conclusion; the raw product family carries no support condition. -/
def rationalSemistandardFourierThetaSmoothFamily
    (hsm : ∀ (f : RationalSchwartzSpace hKc hPK rho) (t : RationalSemistandardTheta.{u, uV} a ha muM),
      rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f t ∈
        rationalSemistandardThetaComponentSpace.{u, uV} a ha muM d t)
    (hfs : RationalSemistandardFourierFiniteSupportStatement hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT) :
    RationalSchwartzSpace hKc hPK rho →ₗ[ℂ]
      rationalSemistandardThetaSmoothSections.{u, uV} a ha muM d where
  toFun f := rationalSemistandardThetaSmoothOfFinite.{u, uV} a ha muM d
    (rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f)
    (hsm f) (hfs f)
  map_add' f g := Subtype.ext
    (map_add (rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT) f g)
  map_smul' c f := Subtype.ext
    (map_smul (rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT) c f)

@[simp] theorem rationalSemistandardFourierThetaSmoothFamily_val
    (hsm : ∀ (f : RationalSchwartzSpace hKc hPK rho) (t : RationalSemistandardTheta.{u, uV} a ha muM),
      rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f t ∈
        rationalSemistandardThetaComponentSpace.{u, uV} a ha muM d t)
    (hfs : RationalSemistandardFourierFiniteSupportStatement hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT)
    (f : RationalSchwartzSpace hKc hPK rho) :
    (rationalSemistandardFourierThetaSmoothFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT
      hsm hfs f).val =
        rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f := rfl

/-- The proper-supported family (the shape of Waldspurger VIII.2's `psi`):
`psi_f` at `P ≠ G` and zero at `P = G`, as a linear map into
`C^infinity(Theta)`. Only smoothness at proper indices and the proper
VIII.1.3(ii) conclusion are used; no full support is required. -/
def rationalSemistandardFourierThetaProperSmoothFamily
    (hsm : ∀ (f : RationalSchwartzSpace hKc hPK rho),
      ∀ t ∈ rationalSemistandardThetaProper.{u, uV} a ha muM,
        rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f t ∈
          rationalSemistandardThetaComponentSpace.{u, uV} a ha muM d t)
    (hfs : RationalProperSemistandardFourierFiniteSupportStatement hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT) :
    RationalSchwartzSpace hKc hPK rho →ₗ[ℂ]
      rationalSemistandardThetaSmoothSections.{u, uV} a ha muM d where
  toFun f := rationalSemistandardThetaProperSmoothOfFinite.{u, uV} a ha muM d
    (rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f)
    (hsm f) (hfs f)
  map_add' f g := Subtype.ext (by
    change rationalSemistandardThetaProperPart.{u, uV} a ha muM _ =
      rationalSemistandardThetaProperPart.{u, uV} a ha muM _ +
        rationalSemistandardThetaProperPart.{u, uV} a ha muM _
    rw [map_add, map_add])
  map_smul' c f := Subtype.ext (by
    change rationalSemistandardThetaProperPart.{u, uV} a ha muM _ =
      c • rationalSemistandardThetaProperPart.{u, uV} a ha muM _
    rw [map_smul, map_smul])

@[simp] theorem rationalSemistandardFourierThetaProperSmoothFamily_val
    (hsm : ∀ (f : RationalSchwartzSpace hKc hPK rho),
      ∀ t ∈ rationalSemistandardThetaProper.{u, uV} a ha muM,
        rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f t ∈
          rationalSemistandardThetaComponentSpace.{u, uV} a ha muM d t)
    (hfs : RationalProperSemistandardFourierFiniteSupportStatement hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT)
    (f : RationalSchwartzSpace hKc hPK rho) :
    (rationalSemistandardFourierThetaProperSmoothFamily hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT hsm hfs f).val =
        rationalSemistandardThetaProperPart.{u, uV} a ha muM
          (rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f) :=
  rfl

/-- The proper-index form: `psi_f` restricted to `Theta - Theta_G`, as a
linear map into finitely supported smooth families on the proper index type. -/
def rationalSemistandardFourierProperSmoothFamily
    (hsm : ∀ (f : RationalSchwartzSpace hKc hPK rho),
      ∀ t ∈ rationalSemistandardThetaProper.{u, uV} a ha muM,
        rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f t ∈
          rationalSemistandardThetaComponentSpace.{u, uV} a ha muM d t)
    (hfs : RationalProperSemistandardFourierFiniteSupportStatement hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT) :
    RationalSchwartzSpace hKc hPK rho →ₗ[ℂ]
      FiniteSupportSections.submodule
        (fun t : RationalSemistandardProperTheta.{u, uV} a ha muM =>
          rationalSemistandardThetaComponentSpace.{u, uV} a ha muM d t.val) where
  toFun f := rationalSemistandardProperSmoothOfFinite.{u, uV} a ha muM d
    (rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f)
    (hsm f) (hfs f)
  map_add' f g := Subtype.ext (by
    change rationalSemistandardProperRestrict.{u, uV} a ha muM _ =
      rationalSemistandardProperRestrict.{u, uV} a ha muM _ +
        rationalSemistandardProperRestrict.{u, uV} a ha muM _
    rw [map_add, map_add])
  map_smul' c f := Subtype.ext (by
    change rationalSemistandardProperRestrict.{u, uV} a ha muM _ =
      c • rationalSemistandardProperRestrict.{u, uV} a ha muM _
    rw [map_smul, map_smul])

@[simp] theorem rationalSemistandardFourierProperSmoothFamily_val
    (hsm : ∀ (f : RationalSchwartzSpace hKc hPK rho),
      ∀ t ∈ rationalSemistandardThetaProper.{u, uV} a ha muM,
        rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f t ∈
          rationalSemistandardThetaComponentSpace.{u, uV} a ha muM d t)
    (hfs : RationalProperSemistandardFourierFiniteSupportStatement hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT)
    (f : RationalSchwartzSpace hKc hPK rho) :
    (rationalSemistandardFourierProperSmoothFamily hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT hsm hfs f).val =
        rationalSemistandardProperRestrict.{u, uV} a ha muM
          (rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f) :=
  rfl

/-- When the full statement holds, the proper part of the full map is the
proper-supported map. -/
theorem rationalSemistandardThetaSmoothProperPart_fourierThetaSmoothFamily
    (hsm : ∀ (f : RationalSchwartzSpace hKc hPK rho) (t : RationalSemistandardTheta.{u, uV} a ha muM),
      rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f t ∈
        rationalSemistandardThetaComponentSpace.{u, uV} a ha muM d t)
    (hfs : RationalSemistandardFourierFiniteSupportStatement hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT)
    (f : RationalSchwartzSpace hKc hPK rho) :
    rationalSemistandardThetaSmoothProperPart.{u, uV} a ha muM d
        (rationalSemistandardFourierThetaSmoothFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta
          hT hsm hfs f) =
      rationalSemistandardFourierThetaProperSmoothFamily hG hi hnu hKc hPK rho hsw a ha muM d
        hdelta hT (fun f t _ => hsm f t)
        (RationalSemistandardFourierFiniteSupportStatement.proper hG hi hnu hKc hPK rho hsw
          a ha muM d hdelta hT hfs) f := rfl

/-- Restricting the proper-supported family to the proper index type gives the
proper-index family. -/
theorem rationalSemistandardProperSmoothRestrict_fourierThetaProperSmoothFamily
    (hsm : ∀ (f : RationalSchwartzSpace hKc hPK rho),
      ∀ t ∈ rationalSemistandardThetaProper.{u, uV} a ha muM,
        rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f t ∈
          rationalSemistandardThetaComponentSpace.{u, uV} a ha muM d t)
    (hfs : RationalProperSemistandardFourierFiniteSupportStatement hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT)
    (f : RationalSchwartzSpace hKc hPK rho) :
    rationalSemistandardProperSmoothRestrict.{u, uV} a ha muM d
        (rationalSemistandardFourierThetaProperSmoothFamily hG hi hnu hKc hPK rho hsw
          a ha muM d hdelta hT hsm hfs f) =
      rationalSemistandardFourierProperSmoothFamily hG hi hnu hKc hPK rho hsw
        a ha muM d hdelta hT hsm hfs f :=
  rationalSemistandardProperSmoothRestrict_properSmoothOfFinite.{u, uV} a ha muM d _ (hsm f) (hfs f)

/-! ## The standard slice -/

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
  [hStdHaar : ∀ I, (eta I).IsHaarMeasure]
  (hds : RationalSemistandardStandardDiscreteSeriesComparison.{u, uV}
    a ha muM hG hi hnu b hb eta)

/-- On the existing standard product, the restriction of `psi_f` is supported in
the existing standard `Theta^H` when `f` is right invariant under `H`, using the
discrete-series comparison `hds` for the two Borel quotients. -/
theorem rationalStandardFullRestrict_fourierFamily_support_subset_rationalThetaFixed
    {H : Subgroup (rationalPoints G)} (f : RationalSchwartzSpace hKc hPK rho)
    (hf : ∀ k ∈ H, ∀ g, f (g * k) = f g) :
    {t : RationalStandardTheta.{u, uV} b hb eta |
      rationalStandardFullRestrict.{u, uV} a ha muM hG hi hnu b hb eta hds
        (rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f)
          t.1 t.2 ≠ 0} ⊆
      rationalThetaFixed.{u, uV} hG hi hnu b hb eta H :=
  rationalStandardFullRestrict_support_subset_rationalThetaFixed a ha muM hG hi hnu b hb eta hds
    (rationalSemistandardFourierFamily_mem_thetaFixedSupported hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT f hf)

variable [hStdInv : ∀ I, (eta I).IsInvInvariant]
  (hrho : IsClosedSubgroup rho)
  (hKrho : (K : Subgroup (rationalPoints G)) ≤ rationalHeightSubgroup (F := F) rho)
  (hM : ∀ I : Finset (RationalPointFamily.SimpleRoot i nu), IsIwasawaPair
    ((standardParabolicPoints i nu ∅).subgroupOf
      (standardLeviPoints i nu (RationalPointFamily.rootSet i nu I)))
    ((K : Subgroup (rationalPoints G)).subgroupOf
      (standardLeviPoints i nu (RationalPointFamily.rootSet i nu I))))
  (hTA : ∀ (I : Finset (RationalPointFamily.SimpleRoot i nu))
    (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ)
      (G := standardLeviPoints i nu (RationalPointFamily.rootSet i nu I))),
    IsSquareIntegrableModCentralSubgroup (rationalLeviSplitCenter I (b I))
      (rationalLeviSplitCenter_le_center I (b I) (hb I)) pi.obj.representation (eta I) →
    ∀ A : UnitaryOrbitRepresentative (RationalPointFamily.leviRationalNormCharacters i nu I) pi,
      IsRationalLeviTempered hKc rho (hM I) A.val.obj)
  (hsmc : ModelSmoothComparisonStatement.{u, uV} (F := F) (G := G) (i := i))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
/-- The standard restriction of the finite-support family is the existing
standard family `rationalFourierThetaFamily f`, under the standard comparison target
`RationalSemistandardFourierStandardComparisonStatement` and its normalization. -/
theorem rationalStandardFullSmoothRestrict_fourierThetaSmoothFamily_val
    (hcmp : RationalSemistandardFourierStandardComparisonStatement.{u, uV} hG hi hnu hKc hPK rho
      hsw a ha muM d hdelta hT b hb eta hds hrho hKrho hM hTA)
    (hnorm : RationalSemistandardStandardFourierNormalization.{u, uV} hG hi hnu hKc hPK
      a ha muM d b hb eta)
    (hsm : ∀ (f : RationalSchwartzSpace hKc hPK rho) (t : RationalSemistandardTheta.{u, uV} a ha muM),
      rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f t ∈
        rationalSemistandardThetaComponentSpace.{u, uV} a ha muM d t)
    (hfs : RationalSemistandardFourierFiniteSupportStatement hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT)
    (f : RationalSchwartzSpace hKc hPK rho) :
    (rationalStandardFullSmoothRestrict.{u, uV} a ha muM hG hi hnu b hb eta hds d hsmc hKc hPK
      (rationalSemistandardFourierThetaSmoothFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT
        hsm hfs f)).val =
      rationalFourierThetaFamily hG hi hnu hKc hPK b hb eta rho hrho hKrho hM hsw hTA f :=
  hcmp hnorm f

end Standard

end Langlands.HarishChandraSchwartz
