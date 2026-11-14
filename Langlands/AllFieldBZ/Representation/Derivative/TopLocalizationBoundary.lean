import Langlands.AllFieldBZ.Representation.Derivative.PartialDerivativeTensorStatement
import Langlands.Representation.Derivative.TopLocalizationBoundary

/-!
# All-field port of `Langlands.Representation.Derivative.TopLocalizationBoundary`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.TopLocalizationBoundary` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative.TopLocalization
open Langlands.Derivative.TopLocalization hiding topLocalizationZeroIso upperOneEquiv upperOneEquiv_mk
open Langlands.GeneralLinear
open Langlands.Jacquet.Localization
universe uF uV

private theorem _root_.Langlands.Derivative.TopLocalization.singleton_relations {G : Type uF} [Group G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (U : Subgroup G) (θ : U →* ℂˣ)
    (hu : ∀ u : U, u = 1) :
    relations ρ U θ = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨u, v⟩, rfl⟩
  simp [hu u]

private def _root_.Langlands.Derivative.TopLocalization.singletonQuotientEquiv {G : Type uF} [Group G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (U : Subgroup G) (θ : U →* ℂˣ)
    (hu : ∀ u : U, u = 1) :
    Coinvariants ρ U θ ≃ₗ[ℂ] V :=
  (relations ρ U θ).quotEquivOfEqBot (singleton_relations ρ U θ hu)

section Zero
variable {F : Type uF} [CommRing F]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

variable [TopologicalSpace F]

end Zero
section One
variable {F : Type uF} [CommRing F]

private theorem _root_.Langlands.Derivative.TopLocalization.upperOne_eq_one (u : upperUnipotent 1 F) : u = 1 := by
  apply Subtype.ext
  exact congrArg (fun x : GeneralLinear.mirabolic 0 F => x.val)
    (GeneralLinear.Mirabolic.rankOne_eq_one
      ⟨u.val, upperUnipotent_le_mirabolic u.property⟩)

end One
section Padic
variable {F : LocalFieldPackage.{uF}}

/-- The upper quotient at rank one is the normalized `Ψ⁻` quotient of the
restricted representation, with no replacement of its module carrier. -/
def upperOneEquiv (T : F.TopologicalData) (ψ : AddChar F.Carrier ℂ) :
    letI := T.topology
    (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear 1 F.Carrier)) →
      ((Langlands.Derivative.PartialTensor.upperCoinvariantsFunctor ψ 1).obj A).representation.Equiv
        ((generalLinearRestriction T 0 ⋙ Mirabolic.psiMinus T 0).obj A).representation := by
  letI := T.topology
  intro A
  refine
    { toLinearEquiv :=
        (singletonQuotientEquiv A.representation _ _ upperOne_eq_one).trans
          (singletonQuotientEquiv
            ((generalLinearRestriction T 0).obj A).representation
            (GeneralLinear.Mirabolic.radical 0 F.Carrier) 1
            (fun _ => Subsingleton.elim _ _)).symm
      isIntertwining' := ?_ }
  intro g
  have hg : g = 1 := Subsingleton.elim _ _
  rw [hg]
  ext q
  simp

/-- Both maps are the identity on original representatives. -/
@[simp] theorem upperOneEquiv_mk (T : F.TopologicalData) (ψ : AddChar F.Carrier ℂ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear 1 F.Carrier)) (v : A),
      upperOneEquiv T ψ A
        (mk A.representation (upperUnipotent 1 F.Carrier)
          (Whittaker.entrywiseCharacter ψ 1) v) =
        Mirabolic.psiMinusQuotient T 0 ((generalLinearRestriction T 0).obj A) v := by
  intros
  rfl

/-- The exact rank-zero boundary for the published top derivative. -/
def topLocalizationZeroIso (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    letI := T.topology
    Langlands.Derivative.PartialTensor.upperCoinvariantsFunctor.{uF,uV} ψ.complex 0 ≅ topDerivative T ψ 0 := by
  letI := T.topology
  exact upperCoinvariantsZeroIso ψ.complex ≪≫ (eqToIso (topDerivative_zero T ψ)).symm

end Padic
end Langlands.AllFieldBZ.Derivative.TopLocalization
