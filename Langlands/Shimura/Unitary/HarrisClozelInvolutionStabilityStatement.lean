import Langlands.Shimura.Unitary.HarrisClozelGlobalJLStatement
import Langlands.Global.NumberFieldAdeleTensorComparison
import Langlands.Automorphic.ConjugateContragredient

/-! # The actual Clozel involution on the Harris division group -/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField MeasureTheory
open Langlands.Global Langlands.Global.RestrictionSplitCentre
open Langlands.GroupScheme Langlands.Shimura Langlands.Automorphic
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Shimura.HarrisClozel

variable {E₀ E A : Type} [Field E₀] [NumberField E₀] [IsTotallyReal E₀]
  [Field E] [NumberField E] [IsTotallyComplex E]
  [Algebra E₀ E] [Algebra.IsQuadraticExtension E₀ E]
  [Ring A] [Algebra E₀ A] [Algebra E A] [IsScalarTower E₀ E A]
  [Algebra E₀ (Adeles E)] [IsScalarTower E₀ E (Adeles E)]
  {n : ℕ} (D : CentralSimpleUnitaryData E₀ E A n)

/-- The actual global scalar-extension comparison, using both balanced tensor
identifications and the canonical adelic base-change map. -/
private def tensorAdelesEquiv : Adeles E₀ ⊗[E₀] A ≃ₐ[E₀] Adeles E ⊗[E] A :=
  let e₁ := Algebra.TensorProduct.comm E₀ (Adeles E₀) A
  let e₂ := (Algebra.TensorProduct.rid E E A).restrictScalars E₀
  let e₃ : A ⊗[E₀] Adeles E₀ ≃ₐ[E₀] (A ⊗[E] E) ⊗[E₀] Adeles E₀ :=
    Algebra.TensorProduct.congr e₂.symm (AlgEquiv.refl : Adeles E₀ ≃ₐ[E₀] Adeles E₀)
  let e₄ := (Algebra.TensorProduct.assoc E₀ E E (A := A) E (Adeles E₀)).restrictScalars E₀
  let e₅ : A ⊗[E] (E ⊗[E₀] Adeles E₀) ≃ₐ[E] A ⊗[E] Adeles E :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[E] A) (numberFieldAdeleTensorEquiv E₀ E)
  e₁.trans (e₃.trans (e₄.trans ((e₅.trans
    (Algebra.TensorProduct.comm E A (Adeles E))).restrictScalars E₀)))

/-- Clozel's involutive automorphism on the actual division adelic group:
`x ↦ σ(x)⁻¹`, with `σ` scalar-extended over the real subfield. -/
def divisionAdelicInvolution [FiniteDimensional E A] :
    AdelicGroupPoints E (divisionGroup (E := E) (A := A)) ≃*
      AdelicGroupPoints E (divisionGroup (E := E) (A := A)) :=
  let e := (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis E A)
    (CommAlgCat.of E (Adeles E))).trans
      (Units.mapEquiv (tensorAdelesEquiv (E₀ := E₀) (E := E) (A := A)).symm.toRingEquiv.toMulEquiv)
  e.trans (((D.involution.baseChange (Adeles E₀)).inverseUnits).trans e.symm)

/-- Spectral stability is an equivariant identification with the pullback
along this automorphism. It need not fix a chosen realization pointwise. -/
def IsInvolutionStable [FiniteDimensional E A] {V : Type} [AddCommGroup V] [Module ℂ V]
    [PseudoMetricSpace V]
    (π : Representation ℂ (AdelicGroupPoints E (divisionGroup (E := E) (A := A))) V) : Prop :=
  ∃ e : Representation.Equiv (π.comp (divisionAdelicInvolution D).toMonoidHom) π,
    Isometry e

local notation "Gd" => divisionGroup (E := E) (A := A)

/-- An actual irreducible admissible component embedded in the restriction
of the specified whole adelic representation at a finite place. -/
def IsFiniteConstituent {F : Type} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (divisionRep : Representation ℂ (AdelicGroupPoints F G) V)
    (v : Langlands.Global.FinitePlace F) (X : ModuleCat ℂ)
    (π : Representation ℂ (PlaceGroupPoints F G (.inr v)) X) : Prop :=
  π.IsIrreducible ∧ IsAdmissible π ∧
    ∃ f : π.IntertwiningMap (divisionRep.comp (AdelicGroupPoints.ofPlace F G (.inr v))),
      Function.Injective f

local instance {m : ℕ} : AddCommGroup (RationalInvariantFunctions E m) := Submodule.addCommGroup _
local instance {m : ℕ} : AddCommGroup (ContinuousRationalFunctions E m) :=
  Submodule.addCommGroup _
local instance {m : ℕ} : AddCommGroup (FiniteSmoothRationalFunctions E m) :=
  Submodule.addCommGroup _
local instance {m : ℕ} : AddCommGroup (AutomorphicForms E m) := Submodule.addCommGroup _
local instance {m : ℕ} {p : Langlands.Global.FinitePlace E} (π : LocalRealization E m p) :
    AddCommGroup π.Space := Submodule.addCommGroup _

set_option maxRecDepth 2048 in
set_option maxHeartbeats 600000 in
/-- Clozel's Corollary 3.4 for the actual conjugate self-dual source: the same
closed irreducible summand of the division-group quotient `L²` whose almost
all local constituents match the source components in matrix charts is
isometrically isomorphic to its pullback along `x ↦ σ(x)⁻¹`. -/
def HarrisClozelInvolutionStabilityStatement : Prop :=
  ∀ (E₀ E A : Type) [Field E₀] [NumberField E₀] [IsTotallyReal E₀]
    [Field E] [NumberField E] [IsTotallyComplex E] [IsCMField E]
    [Algebra E₀ E] [Algebra.IsQuadraticExtension E₀ E] [CompactSpace (AdeleQuotient E)]
    [Ring A] [Algebra E₀ A] [Algebra E A] [IsScalarTower E₀ E A]
    [Algebra E₀ (Adeles E)] [IsScalarTower E₀ E (Adeles E)]
    (r : ℕ) (D : CentralSimpleUnitaryData E₀ E A (r + 1)),
    letI : FiniteDimensional E A := D.finite
    let G := divisionGroup (E := E) (A := A)
    ∀ (hCST : CentralSplitTorusCharacterStatement.{0}) (hG : IsConnectedReductive G)
      (S : CuspidalOperatorRealization E r) (P : CuspidalSpectralPresentation.{0, 0} S)
      (T : Subrepresentation (canonicalL2RightAction E G hCST hG)),
      D.IsDivision → S.isoClass.IsConjugateSelfDual → IsClosedIrreducible T →
      (∀ p : Langlands.Global.FinitePlace E,
        (P.localComponent p).IsIrreducible ∧ (P.localComponent p).IsAdmissible) →
      (∃ bad : Finset (Langlands.Global.FinitePlace E),
        ∀ (p : Langlands.Global.FinitePlace E), p ∉ bad →
          let πp := P.localComponent p
          ∃ (X : ModuleCat.{0} ℂ) (τ : Representation ℂ (PlaceGroupPoints E G (.inr p)) X),
            IsFiniteConstituent T.toRepresentation p X τ ∧
            IsSplitLocalTransfer (A := A) p (ModuleCat.of ℂ πp.Space) πp.representation X τ) →
      IsInvolutionStable D T.toRepresentation

end Langlands.Shimura.HarrisClozel
