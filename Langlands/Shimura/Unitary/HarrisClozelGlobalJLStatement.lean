import Langlands.Representation.Archimedean.StandardModule
import Langlands.Automorphic.CuspidalHilbertAdelicCompletion
import Langlands.Automorphic.SquareIntegrableComponent
import Langlands.Global.AdelicLocalInclusion
import Langlands.Global.AdelicRestrictionSplitCentreCanonical
import Langlands.Global.Arithmetic.HarrisSetup
import Langlands.Global.Factors.CuspidalPairPoleStatement
import Langlands.GroupScheme.FiniteAlgebraUnits
import Langlands.JacquetLanglands.HarrisTransfer
import Langlands.Shimura.Unitary.FiniteScalarExtension

/-! # Global Jacquet–Langlands for the division algebra in Harris's construction -/

noncomputable section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open Langlands.Automorphic Langlands.Global Langlands.Global.RestrictionSplitCentre
open Langlands.GroupScheme Langlands.Shimura.FiniteUnitary Langlands.JacquetLanglands
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Shimura.HarrisClozel

section AddGroups
variable {F : Type} [Field F] [NumberField F] {n : ℕ}

local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _
local instance {p : Langlands.Global.FinitePlace F} (π : LocalRealization F n p) :
    AddCommGroup π.Space := Submodule.addCommGroup _

/-- A nonzero closed invariant subspace with no proper nonzero closed invariant subspace. -/
def IsClosedIrreducible {G H : Type} [Group G] [AddCommGroup H] [Module ℂ H]
    [TopologicalSpace H] {ρ : Representation ℂ G H} (S : Subrepresentation ρ) : Prop :=
  S.toSubmodule ≠ ⊥ ∧ IsClosed (S.toSubmodule : Set H) ∧
    ∀ T : Subrepresentation ρ, T.toSubmodule ≤ S.toSubmodule →
      IsClosed (T.toSubmodule : Set H) → T.toSubmodule = ⊥ ∨ T.toSubmodule = S.toSubmodule

variable {E : Type} [Field E] [NumberField E] {A : Type} [Ring A] [Algebra E A]
  [FiniteDimensional E A]

/-- The group scheme of units of the actual central algebra over its center. -/
abbrev divisionGroup := FiniteAlgebraUnits.groupScheme (Module.finBasis E A)

/-- Coordinates on the actual local points, over the corresponding completion. -/
private def finiteUnitChart (v : Langlands.Global.FinitePlace E) :
    PlaceGroupPoints E (divisionGroup (E := E) (A := A)) (.inr v) ≃*
      (CompletedAlgebra E A v)ˣ :=
  FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis E A) (placeCompletion E (.inr v))

/-- Local Jacquet–Langlands on the actual transferred component over a division place. -/
def IsDivisionLocalTransfer {r : ℕ} (v : Langlands.Global.FinitePlace E)
    (X : ModuleCat ℂ) (π : Representation ℂ (FiniteLocalGL E (r + 1) v) X)
    (Y : ModuleCat ℂ)
    (τ : Representation ℂ (PlaceGroupPoints E (divisionGroup (E := E) (A := A)) (.inr v)) Y) :
    Prop :=
  ∃ (Δ : Type) (dr : DivisionRing Δ),
    letI : DivisionRing Δ := dr
    ∃ alg : Algebra (FiniteCompletion E v) Δ,
      letI : Algebra (FiniteCompletion E v) Δ := alg
      ∃ (hfd : FiniteDimensional (FiniteCompletion E v) Δ)
        (hcen : Algebra.IsCentral (FiniteCompletion E v) Δ),
        letI : FiniteDimensional (FiniteCompletion E v) Δ := hfd
        letI : Algebra.IsCentral (FiniteCompletion E v) Δ := hcen
        letI : TopologicalSpace Δ := moduleTopology (FiniteCompletion E v) Δ
        ∃ t : CompletedAlgebra E A v ≃ₐ[FiniteCompletion E v] Δ,
          let e := (finiteUnitChart (E := E) (A := A) v).trans
            (Units.mapEquiv t.toRingEquiv.toMulEquiv)
          completionJacquetLanglandsPair v (r + 1) Δ X Y π
            (τ.comp e.symm.toMonoidHom)

/-- At a split finite place the two actual constituents agree in the matrix chart. -/
def IsSplitLocalTransfer {r : ℕ} (v : Langlands.Global.FinitePlace E)
    (X : ModuleCat ℂ) (π : Representation ℂ (FiniteLocalGL E (r + 1) v) X)
    (Y : ModuleCat ℂ)
    (τ : Representation ℂ (PlaceGroupPoints E (divisionGroup (E := E) (A := A)) (.inr v)) Y) :
    Prop :=
  ∃ s : CompletedAlgebra E A v ≃ₐ[FiniteCompletion E v]
      Matrix (Fin (r + 1)) (Fin (r + 1)) (FiniteCompletion E v),
    let e := (finiteUnitChart (E := E) (A := A) v).trans
      (Units.mapEquiv s.toRingEquiv.toMulEquiv)
    Nonempty (Representation.Equiv (π.comp e.toMonoidHom) τ)

/-- Matching at infinity means that the two archimedean restrictions contain the same
irreducible Hilbert constituent, not that their multiplicity spaces have been identified. -/
def IsInfiniteTransfer {r : ℕ} {H V : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [AddCommGroup V] [Module ℂ V] [PseudoMetricSpace V]
    (π : AdelicGL E (r + 1) →* (H →L[ℂ] H))
    (τ : Representation ℂ (AdelicGroupPoints E (divisionGroup (E := E) (A := A))) V) : Prop :=
  ∃ s : (InfiniteAdeleRing E ⊗[E] A) ≃ₐ[InfiniteAdeleRing E]
      Matrix (Fin (r + 1)) (Fin (r + 1)) (InfiniteAdeleRing E),
    let e := (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis E A)
      (CommAlgCat.of E (InfiniteAdeleRing E))).trans (Units.mapEquiv s.toRingEquiv.toMulEquiv)
    let πinf := (Langlands.Archimedean.linearRepresentation π).comp (AdelicGL.ofInfinite E (r + 1)).toMonoidHom
    let incl := AdelicGroupPoints.ofInfinite E (divisionGroup (E := E) (A := A))
    let τinf := τ.comp (incl.toMonoidHom.comp e.symm.toMonoidHom)
    ∃ S : Subrepresentation πinf, IsClosedIrreducible S ∧
      ∃ f : S.toRepresentation.IntertwiningMap τinf, Isometry f

set_option maxRecDepth 2048 in
set_option maxHeartbeats 400000 in
/-- The even-degree Harris route uses the global transfer only for a division algebra
ramified at the two distinct CM-conjugate places and an actual cuspidal representation
having square-integrable components there. Stability under the unitary involution
and descent to its fixed group are subsequent comparisons. -/
def HarrisClozelGlobalJLStatement : Prop :=
  ∀ (E₀ E A : Type) [Field E₀] [NumberField E₀] [IsTotallyReal E₀]
    [Field E] [NumberField E] [IsTotallyComplex E] [IsCMField E]
    [Algebra E₀ E] [Algebra.IsQuadraticExtension E₀ E] [CompactSpace (AdeleQuotient E)]
    [Ring A] [Algebra E A] [Algebra E₀ A] [IsScalarTower E₀ E A]
    (r : ℕ) (D : CentralSimpleUnitaryData E₀ E A (r + 1))
    (S : CuspidalOperatorRealization E r) (P : CuspidalSpectralPresentation.{0, 0} S)
    (v : Langlands.Global.FinitePlace E)
    (χ : IdeleClassGroup (𝓞 E) E →ₜ* ℂˣ) (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1)
    (hSχ : S.realization.HasCentralCharacter χ) (b : S.realization.UnitaryForm)
    (hb : OperatorDeterminantSlice.ComputesBandInnerProduct S.realization b),
    letI : FiniteDimensional E A := D.finite
    let G := divisionGroup (E := E) (A := A)
    let w := Langlands.Global.Harris.conjPlace E v
    ∀ (hCST : CentralSplitTorusCharacterStatement.{0}) (hG : IsConnectedReductive G),
      CuspidalPairPoles.IsTrivialOnSplitCentre S →
      v ≠ w → D.IsDivision →
      IsDivisionAt E A v → IsDivisionAt E A w →
      (∀ p : Langlands.Global.FinitePlace E, p ≠ v → p ≠ w → IsSplitAt E A p (r + 1)) →
      (∀ p : Langlands.Global.FinitePlace E,
        (P.localComponent p).IsIrreducible ∧ (P.localComponent p).IsAdmissible) →
      (P.localComponent v).IsSquareIntegrable → (P.localComponent w).IsSquareIntegrable →
      ∃ T : Subrepresentation (canonicalL2RightAction E G hCST hG),
        IsClosedIrreducible T ∧
        (∀ p : Langlands.Global.FinitePlace E,
          let πp := P.localComponent p
          ∃ (Y : ModuleCat ℂ) (τp : Representation ℂ (PlaceGroupPoints E G (.inr p)) Y),
            τp.IsIrreducible ∧ IsAdmissible τp ∧
            (∃ f : τp.IntertwiningMap
                (T.toRepresentation.comp (AdelicGroupPoints.ofPlace E G (.inr p))),
              Function.Injective f) ∧
            ((p = v ∨ p = w) → IsDivisionLocalTransfer (A := A) p
              (ModuleCat.of ℂ πp.Space) πp.representation Y τp) ∧
            (p ≠ v → p ≠ w → IsSplitLocalTransfer (A := A) p
              (ModuleCat.of ℂ πp.Space) πp.representation Y τp)) ∧
        IsInfiniteTransfer (A := A)
          (OperatorDeterminantSlice.adelicCompletion S χ hχ hSχ b hb).action T.toRepresentation

end AddGroups

end Langlands.Shimura.HarrisClozel
