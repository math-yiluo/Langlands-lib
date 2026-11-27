import Langlands.Shimura.PEL.HarrisTaylorCMKottwitzRegularStatement
import Langlands.Shimura.Unitary.ClozelOnePlaceExistenceStatement
import Langlands.Automorphic.SupercuspidalComponent
import Langlands.Automorphic.RegularHighestWeight
import Langlands.Automorphic.ConjugateContragredient
import Langlands.Global.Arithmetic.HarrisSetup
import Langlands.Galois.CompatibleFamily

/-! # Clozel's transfer to the similitude group and the occurrence in the middle degree

Two inputs of the geometric endpoint of Harris's Theorem 1.2 with multiplicity, on the
division datum and the Harris charts of the Kottwitz statements: the finite part `π_f`
and the coefficient system `ρ` that Clozel's transfer attaches to a conjugate self-dual
cuspidal class of regular highest weight, with the unramified matching at the good
places (Clozel 1991, Proposition 4.11, Lemma 5.6, (5.17)–(5.18), §5.3), and the occurrence
of the same `π_f` in the middle degree of the cohomology at a small level (Kottwitz 1992,
printed pp. 655 and 658). Both are statements, not proved here. See
`HarrisClozelSimilitudeTransferStatement.md`.
-/

noncomputable section

universe wS wR

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

set_option autoImplicit false
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Shimura.Coefficients Langlands.Geometry
open Langlands.Global AdelicFunctoriality
open Langlands.Shimura.CompactOpenLevel Langlands.Shimura.RestrictedLevelColimit
open Langlands.Shimura.SmallLevelGaloisTower
open Langlands.Shimura.KottwitzUnramified (UnramifiedChart LocalPoints SqrtPrime)
open Langlands.Shimura.KottwitzDual (IsKottwitzPolynomial)
open Langlands.Shimura.FiniteUnitary (IsSplitPlace IsDivisionAbove IsQuasiSplitAt)
open Langlands.Automorphic Langlands.Unramified
open Langlands.GaloisRepresentation (residueCardinality)

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {r : ℕ} (D : CentralSimpleUnitaryData E F A (r + 1))
  {L : Type} [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  {τ₀ : L →+* ℂ}
  (C : HarrisSignatureCharts D.toSecondKindInvolution (r + 1)
    (harrisCMSection E (algebraMap L F) τ₀))
  [Module.Finite ℚ A]

set_option hygiene false in
/-- Harris's CM-type section `Φ`. -/
local notation "Φ" => harrisCMSection E (algebraMap L F) τ₀

set_option hygiene false in
local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀

/-- **The output of Clozel's transfer to the similitude group** at the small level `U`:
`π_f` (a representation of the finite adelic points of the similitude group over the
number field `K`) is admissible and irreducible over `K̄`; the coefficient system `ρ` is
irreducible over `K̄` and of regular highest weight; and there are a finite set `S₁` of
primes, an algebraic Hecke character `μ` of `F` and a spectrum `s` of the class `c` such
that, at every prime `p₀ ∉ S₁` at which `F` is unramified, for every unramified chart
whose level is the `p₀`-component of `U`, every local component `π_{p₀}` of `π_f` and
every place `w = v_θ` of `F` above `p₀` outside the exceptional set of `s`: `π_{p₀}` is
spherical, a Kottwitz polynomial `P(π_{p₀}, F_w)` exists, and every Kottwitz polynomial
`P` has, through `j`, the roots `q_w^{(n-1)/2} μ_w(ϖ_w) tᵢ`, with `tᵢ` the eigenvalues of
`s` at `w` and `ϖ_w` any uniformizer at `w` (`n = r + 1`). -/
def IsClozelSimilitudeTransfer [CompactSpace (AdeleQuotient F)]
    (c : CuspidalOperatorRealization.IsoClass F r)
    {K : Type} [Field K] [NumberField K] (j : K →+* ℂ)
    {V : Type} [AddCommGroup V] [Module K V]
    (πf : Representation K D.rationalInvolution.FiniteAdelicPoints V)
    {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
    (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
    (U : SmallCMLevel D) : Prop :=
  Langlands.IsAdmissible πf ∧
  Representation.IsIrreducible
    ((Module.End.baseChangeHom K (AlgebraicClosure K) V).toMonoidHom.comp πf) ∧
  Representation.IsIrreducible (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    (ρ.act (AlgebraicClosure K))) ∧
  Langlands.Shimura.AlgebraInvolution.IsRegularHighestWeight (r + 1) ρ ∧
  ∃ (S₁ : Finset ℕ) (μ : HeckeCharacter F) (s : SpectralSystem (Langlands.Global.FinitePlace F) (r + 1)),
    Harris.IsAlgebraic μ ∧ CuspidalOperatorRealization.IsoClass.HasSpectralSystem.{0, 0} c s ∧
    ∀ (p₀ : ℕ) [Fact p₀.Prime], p₀ ∉ S₁ →
      KottwitzUnramified.IsUnramifiedAt (rationalPrimePlace p₀) F →
      ∀ ch : UnramifiedChart D.toSecondKindInvolution (rationalPrimePlace p₀) (r + 1),
      (∃ Kaway : Subgroup (D.rationalInvolution.PrimeToPoints p₀),
        (inverseOpposite U.obj).subgroup.map
            (D.rationalInvolution.finiteAdelicPointsSplit p₀
              (Fact.out : p₀.Prime).ne_zero).toMulEquiv.toMonoidHom =
          (ch.level.comap (D.rationalInvolution.dividingLocalMap p₀
            ⟨rationalPrimePlace p₀, natCast_mem_rationalPrimePlace p₀⟩).toMonoidHom).prod
            Kaway) →
      ∀ πp : SmoothRep.{0, 0, 0} K
        (LocalPoints D.toSecondKindInvolution (rationalPrimePlace p₀)),
      (∃ πaway : Rep.{0} K (D.rationalInvolution.PrimeToPoints p₀),
        Nonempty (πf.Equiv (Representation.tprod
          (πp.representation.comp
            (D.rationalInvolution.finiteLocalMap (rationalPrimePlace p₀)).toMonoidHom)
          (πaway.ρ.comp ((MonoidHom.snd _ _).comp
            (D.rationalInvolution.finiteAdelicPointsSplit p₀
              (Fact.out : p₀.Prime).ne_zero).toMulEquiv.toMonoidHom))))) →
      ∀ (θ : ℂ →+* PadicAlgCl p₀)
        (hw : (harrisPlace p₀ θ (Φ C.distinguished)).1 ∉ s.exceptional),
        ch.IsSphericalIrreducible (AlgebraicClosure K) πp ∧
        (∃ (sq : SqrtPrime (rationalPrimePlace p₀) (AlgebraicClosure K)) (P : Polynomial K),
          IsKottwitzPolynomial ch θ hΦ C.hodgeFunction
            (KottwitzDual.harrisCharts_hodgeFunction_add_conjugate hΦ C) πp sq P) ∧
        ∀ (sq : SqrtPrime (rationalPrimePlace p₀) (AlgebraicClosure K)) (P : Polynomial K),
          IsKottwitzPolynomial ch θ hΦ C.hodgeFunction
            (KottwitzDual.harrisCharts_hodgeFunction_add_conjugate hΦ C) πp sq P →
          ∀ ϖ : (FiniteCompletion F (harrisPlace p₀ θ (Φ C.distinguished)).1)ˣ,
            Valued.v (ϖ : FiniteCompletion F
                (harrisPlace p₀ θ (Φ C.distinguished)).1) =
              WithZero.exp (-1 : ℤ) →
            (P.map j).roots =
              ((s.eigenvalues _ hw : Multiset ℂˣ).map fun t =>
                ((((residueCardinality
                    (harrisPlace p₀ θ (Φ C.distinguished)).1 : ℝ) ^
                  ((r : ℝ) / 2) : ℝ) : ℂ) *
                  (μ.finiteComponent _ ϖ : ℂ) * (t : ℂ)))

/-- **Clozel's transfer to the similitude group** (Clozel 1991, Proposition 4.11,
Lemma 5.6, (5.17)–(5.18) and §5.3), on the division datum `D` and the Harris charts
`C`, in the form of the output of the one-place existence statement: if `D` is a division
algebra, `3 ≤ n` or the totally real field has a real place other than the distinguished
one, `v₀` is a finite place of `E` split in `F` above which the algebra is divided and
`D` is quasi-split at the other finite places of `E`, then every conjugate self-dual
cuspidal class `c` of `GL_n` over `F` (`n = r + 1`) of regular highest weight with a
supercuspidal component at a place `w` of `F` above `v₀` has, at some small level `U`,
the output `IsClozelSimilitudeTransfer` of the transfer: a number field `K` with an
embedding `j : K → ℂ`, a finite part `π_f` over `K` and a coefficient system `ρ` over `K`
with the unramified matching. The statement is not proved here. -/
def ClozelSimilitudeTransferStatement : Prop :=
  ∀ [CompactSpace (AdeleQuotient F)],
  D.IsDivision →
  (3 ≤ r + 1 ∨ ∃ τ, τ ≠ C.distinguished) →
  ∀ v₀ : Langlands.Global.FinitePlace E, IsSplitPlace E F v₀ →
    IsDivisionAbove (K := F) (A := A) v₀ →
    (∀ v : Langlands.Global.FinitePlace E, v ≠ v₀ →
      IsQuasiSplitAt D.toSecondKindInvolution (r + 1) v) →
  ∀ (c : CuspidalOperatorRealization.IsoClass F r) (w : Langlands.Global.FinitePlace F),
    w.asIdeal.LiesOver v₀.asIdeal →
    c.HasRegularHighestWeight → c.IsConjugateSelfDual →
    CuspidalOperatorRealization.IsoClass.HasSupercuspidalComponent.{0, 0} c w →
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (j : K →+* ℂ)
      (V : Type) (_ : AddCommGroup V) (_ : Module K V)
      (πf : Representation K D.rationalInvolution.FiniteAdelicPoints V)
      (W : Type) (_ : AddCommGroup W) (_ : Module K W) (_ : Module.Finite K W)
      (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
      (U : SmallCMLevel D),
      IsClozelSimilitudeTransfer D C c j πf ρ U

variable
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

open Langlands.AlgebraicGeometry

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)
  (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : ∀ U : SmallCMLevel D, CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)

/-- **The occurrence in the middle degree** of `π_f` at the small level `U`, for the
coefficient system `ρ`: for every prime `ℓ`, every choice of the derived-category
instances and every coefficient place `λ` of `K` above `ℓ`, under the fixed-vector
comparison in degree `n - 1 = r`, the Hecke multiplicity space
`cmHarrisLambdaTowerHeckeMultiplicity` of `π_f ⊗_K K_λ` in degree `r` at `U` is
nonzero. -/
def CMHarrisMiddleDegreeOccurs
    {K : Type} [Field K] [NumberField K]
    {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
    (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
    {V : Type} [AddCommGroup V] [Module K V]
    (πf : Representation K D.rationalInvolution.FiniteAdelicPoints V)
    (U : SmallCMLevel D) : Prop :=
  ∀ (ℓ : Global.FinitePlace ℚ)
    [∀ U' : SmallCMLevel D, HasDerivedCategory.{wS}
      (EtaleDerivedSections.ModuleSheaf ((cmGeometricSchemeTower D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q).obj U')
        (HarrisCoefficientIntegers K ℓ))]
    [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K ℓ))]
    (lam : FinitePlacesAbove K ℓ),
    CMHarrisLambdaTowerFixedVectorComparison D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q ℓ ρ existence geometry hRigid lam r →
    Nontrivial (cmHarrisLambdaTowerHeckeMultiplicity D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q ℓ ρ existence geometry
      hRigid lam r (FiniteCompletion K lam.1)
      ((Module.End.baseChangeHom K (FiniteCompletion K lam.1) V).toMonoidHom.comp πf) U).V

/-- **Clozel's transfer with the occurrence in the middle degree** (Clozel 1991, (5.18)
and printed p. 143; Kottwitz 1992, printed pp. 655 and 658): under the hypotheses of
`ClozelSimilitudeTransferStatement`, the transfer can be chosen so that its finite part
`π_f` occurs, for the same coefficient system `ρ` and at the same small level `U`, in the
middle degree of the cohomology of the tower (`CMHarrisMiddleDegreeOccurs`). It
strengthens `ClozelSimilitudeTransferStatement`
(`clozelSimilitudeTransfer_of_middleDegreeOccurrence`). The statement is not proved
here. -/
def ClozelMiddleDegreeOccurrenceStatement : Prop :=
  ∀ [CompactSpace (AdeleQuotient F)],
  D.IsDivision →
  (3 ≤ r + 1 ∨ ∃ τ, τ ≠ C.distinguished) →
  ∀ v₀ : Langlands.Global.FinitePlace E, IsSplitPlace E F v₀ →
    IsDivisionAbove (K := F) (A := A) v₀ →
    (∀ v : Langlands.Global.FinitePlace E, v ≠ v₀ →
      IsQuasiSplitAt D.toSecondKindInvolution (r + 1) v) →
  ∀ (c : CuspidalOperatorRealization.IsoClass F r) (w : Langlands.Global.FinitePlace F),
    w.asIdeal.LiesOver v₀.asIdeal →
    c.HasRegularHighestWeight → c.IsConjugateSelfDual →
    CuspidalOperatorRealization.IsoClass.HasSupercuspidalComponent.{0, 0} c w →
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (j : K →+* ℂ)
      (V : Type) (_ : AddCommGroup V) (_ : Module K V)
      (πf : Representation K D.rationalInvolution.FiniteAdelicPoints V)
      (W : Type) (_ : AddCommGroup W) (_ : Module K W) (_ : Module.Finite K W)
      (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
      (U : SmallCMLevel D),
      IsClozelSimilitudeTransfer D C c j πf ρ U ∧
        CMHarrisMiddleDegreeOccurs.{wS, wR} D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q existence geometry hRigid ρ πf U

/-- The transfer with the occurrence gives the transfer: forget the occurrence. -/
theorem clozelSimilitudeTransfer_of_middleDegreeOccurrence
    (hocc : ClozelMiddleDegreeOccurrenceStatement.{wS, wR} D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q existence geometry
      hRigid) :
    ClozelSimilitudeTransferStatement D C := by
  intro _ hD hn v₀ hsplit hdiv hqs c w hw hreg hcsd hsc
  obtain ⟨K, _, _, j, V, _, _, πf, W, _, _, _, ρ, U, ht, -⟩ :=
    hocc hD hn v₀ hsplit hdiv hqs c w hw hreg hcsd hsc
  exact ⟨K, _, _, j, V, _, _, πf, W, _, _, _, ρ, U, ht⟩

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
