import Langlands.Representation.Families.RenardSupercuspidalFamilyEndomorphismStatement
import Langlands.Representation.Families.RenardGenericIrreducibilityStatements
import Langlands.Representation.Families.RenardFamilyEndomorphismProof
import Langlands.Representation.Families.RenardFamilyParabolicFlatnessProof
import Langlands.Representation.Aubert.General.IrreducibleAdmissibleStatement
import Langlands.Representation.Plancherel.UnramifiedRationalConjugateAdmissibility
import Langlands.Representation.Plancherel.RationalUnramifiedFunctionField
import Langlands.Representation.Plancherel.RationalUnramifiedCharacterDensity
import Langlands.Representation.Plancherel.RationalUnramifiedScalarCancellation
import Langlands.Representation.Plancherel.RationalNormKernelTopology
import Langlands.BruhatTits.Unipotent.RationalPointCompactOpen

/-!
# Renard VI.8.6 Example, reduced to three inputs

Renard derives the Example after the VI.8.6 Proposition by applying that Proposition to
`V_B = i_P^G(ρ_B, W_B)`. This module carries out that application. It proves
`SupercuspidalFamilyEndomorphismStatement` from three inputs that are not yet available:

* `GenericInducedIrreducibilityStatement` (Theorem VI.8.5);
* `RationalPointsIrreducibleAdmissibleStatement` (Jacquet: irreducible smooth
  representations of `M(F)` are admissible; Renard VI.2.2 for the supercuspidal ones);
* `SupercuspidalFamilyFiberStatement`, stated here: at the evaluation point of an
  unramified character `ψ`, the fiber of `i_P^G(ρ_B)` is irreducible whenever the
  normalized induction of `ρ ⊗ ψ` is.

The general part is `endomorphismScalar_leviInduced`, the Proposition for a normalized
parabolic induction `i_P^G(σ)` of a flat admissible family `σ` of `M(F)` over a reduced
Noetherian finitely generated `ℂ`-algebra.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Renard.AlgebraicFamily

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

set_option synthInstance.maxHeartbeats 400000 in
/-- The fiber step in Renard's proof of the VI.8.6 Example: let `ψ` be an unramified character
of `M(F)` and `χ : B →ₐ[ℂ] ℂ` evaluation at `ψ`. If the normalized parabolic induction of the
twist `σ ⊗ ψ` is irreducible, then so is the fiber `ℂ ⊗_{B,χ} i_P^G(ρ_B)` of the induced
universal family at `χ`. -/
def SupercuspidalFamilyFiberStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)),
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ (W : Type v) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (rationalPoints M) W)
        (hσ : IsSmooth σ),
          let ν := fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul
          letI : AddCommGroup (Plancherel.unramifiedRegularFunctions ν ⊗[ℂ] W) :=
            TensorProduct.addCommGroup
          letI : Module (Plancherel.unramifiedRegularFunctions ν)
              (Plancherel.unramifiedRegularFunctions ν ⊗[ℂ] W) := TensorProduct.leftModule
          let ρB := Plancherel.universalUnramifiedRepresentation ν σ
          ∀ (ψ : Plancherel.unramifiedCharacters ν)
            (χ : Plancherel.unramifiedRegularFunctions ν →ₐ[ℂ] ℂ),
            (∀ b, χ b = b.val ψ) →
            ((leviInductionFunctor p l r hp hr hl hmul).obj
              ((SmoothRep.of σ hσ).twist ψ.val.toMonoidHom
                (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))).IsIrreducible →
            letI : Algebra (Plancherel.unramifiedRegularFunctions ν) ℂ := χ.toRingHom.toAlgebra
            Representation.IsIrreducible
              ((Module.End.baseChangeHom (Plancherel.unramifiedRegularFunctions ν) ℂ
                (LeviInduced p l r hp hr hl hmul ρB)).toMonoidHom.comp
                (leviInducedRepresentation p l r hp hr hl hmul ρB))

set_option synthInstance.maxHeartbeats 400000 in
/-- Renard VI.8.6 Proposition specialized to a normalized parabolic induction
`i_P^G(σ)` of a flat admissible family `σ` of `M(F)` over `B`: given a set `Ξ` of points
of `B` on which no nonzero element of `B` vanishes identically and at which every fiber of
`i_P^G(σ)` is irreducible, every `G(F)`-equivariant `B`-linear endomorphism of
`i_P^G(σ)` is the action of an element of `B`. -/
theorem endomorphismScalar_leviInduced.{u', uB', uE'} :
    ∀ (k : Type u') [Field k] [ValuativeRel k] [TopologicalSpace k]
      [IsNonarchimedeanLocalField k] [T2Space k]
      (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
      haveI := hG.isAffineHom
      letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
      ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
        (P M U : GroupScheme (Spec (CommRingCat.of k)))
        (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
        (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
        (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
        (hmul : IsIso (subgroupMultiplication l r)),
        haveI := hl.isConnectedReductive.isAffineHom
        letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
        ∀ (B : Type uB') [CommRing B] [Algebra ℂ B] [IsNoetherianRing B]
          [Algebra.FiniteType ℂ B] [IsReduced B]
          (E : Type uE') [AddCommGroup E] [Module B E]
          (σ : Representation B (rationalPoints M) E),
          IsSmooth σ → Module.Flat B E →
            (∀ K : OpenSubgroup (rationalPoints M), IsCompact (K : Set (rationalPoints M)) →
              Module.Finite B (fixedVectors σ K.toSubgroup)) →
            ∀ φ : LeviInduced p l r hp hr hl hmul σ →ₗ[B] LeviInduced p l r hp hr hl hmul σ,
              (∀ (g : rationalPoints G) (f : LeviInduced p l r hp hr hl hmul σ),
                φ (leviInducedRepresentation p l r hp hr hl hmul σ g f) =
                  leviInducedRepresentation p l r hp hr hl hmul σ g (φ f)) →
              ∀ Ξ : Set (B →ₐ[ℂ] ℂ),
                (∀ b : B, (∀ χ ∈ Ξ, χ b = 0) → ∀ χ : B →ₐ[ℂ] ℂ, χ b = 0) →
                (∀ χ ∈ Ξ,
                  letI : Algebra B ℂ := χ.toRingHom.toAlgebra
                  Representation.IsIrreducible
                    ((Module.End.baseChangeHom B ℂ
                      (LeviInduced p l r hp hr hl hmul σ)).toMonoidHom.comp
                        (leviInducedRepresentation p l r hp hr hl hmul σ))) →
                ∃ b : B, ∀ f : LeviInduced p l r hp hr hl hmul σ, φ f = b • f := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  intro B _ _ _ _ _ E _ _ σ hσ hE hfin φ hφ Ξ hdense hirr
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth G.X.hom := hG.smooth
  have hGlp : Langlands.Topology.IsLocallyProfinite (rationalPoints G) :=
    BruhatTits.rationalPoint_isLocallyProfinite k G
  exact endomorphismScalar B (rationalPoints G) hGlp (LeviInduced p l r hp hr hl hmul σ)
    (leviInducedRepresentation p l r hp hr hl hmul σ) (isSmooth_inducedRepresentation _ _ _)
    (inductionFlat k G hG P M U p l r hp hl hr hmul B E σ hσ hE)
    (inductionAdmissible k G hG P M U p l r hp hl hr hmul B E σ hσ hE hfin) φ hφ Ξ hdense hirr

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Renard VI.8.6 Example, from Theorem VI.8.5, the admissibility of irreducible smooth
representations of `M(F)`, and the fiber step `SupercuspidalFamilyFiberStatement`. -/
theorem supercuspidalFamilyEndomorphism_of_statements
    (hGen : GenericInducedIrreducibilityStatement.{u, v})
    (hAdm : RationalPointsIrreducibleAdmissibleStatement.{u, v})
    (hFiber : SupercuspidalFamilyFiberStatement.{u, v}) :
    SupercuspidalFamilyEndomorphismStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  intro W _ _ σ hσ hirr hsc ν ρB φ hφ
  have hM : IsConnectedReductive M := hl.isConnectedReductive
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have : Smooth M.X.hom := hM.smooth
  have hproj : Continuous (Plancherel.rationalValuationImageProjection M) :=
    Plancherel.continuous_rationalValuationImageProjection M
  have : Algebra.FiniteType ℂ (Plancherel.unramifiedRegularFunctions ν) :=
    Plancherel.rationalUnramifiedRegularFunctions_finiteType M hproj hM
  have : IsNoetherianRing (Plancherel.unramifiedRegularFunctions ν) :=
    Plancherel.rationalUnramifiedRegularFunctions_isNoetherianRing M hproj hM
  have : IsDomain (Plancherel.unramifiedRegularFunctions ν) :=
    Plancherel.rationalUnramifiedRegularFunctions_isDomain M hproj hM
  have hσadm : IsAdmissible σ := hAdm k M hM (SmoothRep.of σ hσ) hirr
  have hν : ∀ χ, Continuous (ν χ) := fun χ =>
    (Plancherel.rationalNormContinuousCharacter M χ).continuous
  have hρBadm := Plancherel.isAdmissible_universalUnramifiedRepresentation
    (L := rationalPoints M) ν hν σ hσadm
  refine (hGen k G hG P M U p l r hp hl hr hmul (SmoothRep.of σ hσ) hirr hsc).elim
    fun f hfs => ?_
  let ev : Plancherel.unramifiedCharacters ν →
      (Plancherel.unramifiedRegularFunctions ν →ₐ[ℂ] ℂ) := fun ψ =>
    (Pi.evalAlgHom ℂ (fun _ => ℂ) ψ).comp (Plancherel.unramifiedRegularFunctions ν).val
  have hev : ∀ ψ b, ev ψ b = b.val ψ := fun _ _ => rfl
  refine @endomorphismScalar_leviInduced k _ _ _ _ _ G hG _ _ P M U p l r hp hl hr hmul
    (Plancherel.unramifiedRegularFunctions ν) _ _ _ _ _
    (Plancherel.unramifiedRegularFunctions ν ⊗[ℂ] W) TensorProduct.addCommGroup
    TensorProduct.leftModule ρB hρBadm.1 (Module.Flat.baseChange ..) (fun K _ => hρBadm.2 K)
    φ hφ (ev '' Plancherel.rationalUnramifiedPrincipalOpen M hM f) ?_ ?_
  · intro b hb χ
    have hval : b.val = 0 := by
      refine Continuous.ext_on (Plancherel.dense_rationalUnramifiedPrincipalOpen M hM f hfs.1)
        (Plancherel.continuous_unramifiedRegularFunction ν b) continuous_const ?_
      intro ψ hψ
      exact hb (ev ψ) ⟨ψ, hψ, rfl⟩
    have : b = 0 := Subtype.ext hval
    rw [this, map_zero]
  · rintro _ ⟨ψ, hψ, rfl⟩
    have h := hFiber k G hG P M U p l r hp hl hr hmul W σ hσ ψ (ev ψ) (hev ψ) (hfs.2 ψ hψ)
    convert h using 2

end Langlands.Renard.AlgebraicFamily
