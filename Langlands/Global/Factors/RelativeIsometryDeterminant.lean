import Langlands.Global.Factors.RelativeIsometryOperationReduction
import Langlands.Global.Factors.RelativeIsometryFactorStatement
import Langlands.Automorphic.AssociatedCentralCharacterProof
import Langlands.ClassFieldTheory.Global.LocalRelativeWeilTransferProof
import Langlands.Automorphic.LocalComponentCentralCharacter
import Langlands.VirtualRepresentation.Supercuspidal.UnitaryCentralCharacter

/-!
# Determinant compatibility of the relative generated isometry

The determinant clause of the relative analogue of Henniart's Proposition 2.6 (a).
For a witnessed generator, the global central character `Ω` of the cuspidal
realization satisfies `det S = Ω ∘ τ`; restricted along the local map, whose
transfer is the inverse of local reciprocity, this gives `det(x) = Ω_v ∘ rec`. On
the automorphic side `Ω_v` is the scalar character of the local component, hence
the central character of its supercuspidal support. Both sides are multiplicative,
so the identity extends from generators to the generated span and, through the
graph of the isometry, to all of its inputs.
-/

noncomputable section

universe uF uW uP uV

namespace Langlands.VirtualRepresentation.LocalWeil

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

-- The same additive monoid as in `unitaryDeterminant` and
-- `ExactGrothendieckGroup.determinant`.
private local instance {G : Type*} [Group G] : AddCommMonoid (Additive (G →* ℂˣ)) :=
  (inferInstance : AddCommGroup (Additive (G →* ℂˣ))).toAddCommMonoid

/-- The virtual determinant of a unitary class is the determinant of its image in
exact K0 of continuous representations. -/
theorem unitaryDeterminant_eq_determinant_realizeExact (x : UnitaryLattice.{uF, uV} F) :
    unitaryDeterminant F x =
      ExactGrothendieckGroup.determinant _ (realizeExact F (includeUnitary F x)) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single b z =>
    have hs : Finsupp.single b z = z • generator b := by simp [generator]
    have hi : includeUnitary F (generator b) = generator b.val := by
      simp [includeUnitary, Weil.includeUnitary, includeSubset, VirtualRepresentation.map,
        generator]
    rw [hs, map_smul, map_smul, map_smul, map_smul, unitaryDeterminant_generator, hi,
      realizeExact_generator, ExactGrothendieckGroup.determinant_ofClass]
    unfold ExactGrothendieckGroup.classDeterminant
    rw [Weil.forgetProperty_basisContinuousClass]

end Langlands.VirtualRepresentation.LocalWeil

namespace Langlands.Global.PoleComparison

open Langlands.VirtualRepresentation Langlands.VirtualRepresentation.RelativeGlobal
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Global
open Langlands.Global.AdelicFunctoriality

variable (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
  (c : FundamentalClass.ClassFamily.{uF}) (v : FinitePlace F)

/-- On a witnessed generator, the central character of the supercuspidal support,
pulled back along a geometric reciprocity candidate, is the determinant of the
unitary Weil class. -/
theorem witnessedGenerator_determinant (hc : RelativeWeilGroup.IsArithmeticClassFamily c)
    (d : WitnessedGenerator.{uF, uW, uP} F E c v)
    (e : Correspondence.ReciprocityCandidate (padicField v))
    (he : Correspondence.IsGeometricReciprocity (padicField v) e)
    (w : Weil.Local.localWeilGroup (padicField v)) :
    PadicSupercuspidal.latticeCentralCharacter (padicField v) d.automorphicElement
        (Correspondence.reciprocityHom (padicField v) e w) =
      Additive.toMul (LocalWeil.unitaryDeterminant (padicField v) d.weilElement) w := by
  obtain ⟨Ω, hΩT, hdet, -, -⟩ := RelativeWeilGroup.associatedCentralCharacter.{uF, uW, uP}
    c hc F E d.weil d.cuspidal d.associatedClass
  have : d.placeOver.1.asIdeal.LiesOver v.asIdeal := d.placeOver.2
  have hι := RelativeWeilGroup.localTransferReciprocity c F E v d.placeOver.1 d.reciprocity
    d.localMap d.localMap_spec
  -- Automorphic side: `Ω_v` is the central character of the support.
  have hcc : PadicSupercuspidal.IsUnitaryCentralCharacter (padicField v) d.automorphicElement
      (Ω.finiteComponent v).toMonoidHom := by
    apply PadicSupercuspidal.isUnitaryCentralCharacter_of_isUnitaryLatticeSupport
      (padicField v) _ d.automorphic_support
    intro a f
    exact (d.presentation.localComponent v).representation_scalar_of_hasCentralCharacter Ω
      (d.presentation.localComponent_hasCentralCharacter v Ω hΩT) a f
  rw [← (PadicSupercuspidal.isUnitaryCentralCharacter_iff _ _ _).mp hcc]
  -- Weil side: the determinant of the local restriction.
  rw [LocalWeil.unitaryDeterminant_eq_determinant_realizeExact, d.weil_expansion]
  apply Units.ext
  change ((Ω.finiteComponent v (LocalFactor.RankOne.reciprocityUnits (padicField v) e w) :
      ℂˣ) : ℂ) = (ExactGrothendieckGroup.determinantCharacter _
        (localExactClass F E c v d.weil d.associated.1 d.localMap) w : ℂ)
  rw [localExactClass, ExactGrothendieckGroup.determinantCharacter_ofRepresentation_apply]
  have h := congrArg (fun χ : RelativeWeilGroup c F E →* ℂˣ => (χ (d.localMap w) : ℂ)) hdet
  simp only [RelativeWeilGroup.reciprocityCharacter_apply, hι e he w, map_inv, inv_inv] at h
  exact h.symm

-- The additive monoid used by `LocalWeil.unitaryDeterminant`.
private local instance {G : Type*} [Group G] : AddCommMonoid (Additive (G →* ℂˣ)) :=
  (inferInstance : AddCommGroup (Additive (G →* ℂˣ))).toAddCommMonoid

/-- The determinant identity holds on the whole generated paired span. -/
theorem pairedLattice_determinant (hc : RelativeWeilGroup.IsArithmeticClassFamily c)
    (e : Correspondence.ReciprocityCandidate (padicField v))
    (he : Correspondence.IsGeometricReciprocity (padicField v) e)
    {z : LocalWeil.UnitaryLattice.{uF, uW} (padicField v) ×
      PadicSupercuspidal.UnitaryLattice.{uF, uF} (padicField v)}
    (hz : z ∈ pairedLattice.{uF, uW, uP} F E c v)
    (w : Weil.Local.localWeilGroup (padicField v)) :
    PadicSupercuspidal.latticeCentralCharacter (padicField v) z.2
        (Correspondence.reciprocityHom (padicField v) e w) =
      Additive.toMul (LocalWeil.unitaryDeterminant (padicField v) z.1) w := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨d, rfl⟩ := hz
    exact witnessedGenerator_determinant F E c v hc d e he w
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Prod.fst_add, Prod.snd_add, PadicSupercuspidal.latticeCentralCharacter_add,
      MonoidHom.mul_apply, map_add, toMul_add, hx, hy]
  | smul k x _ hx =>
    simp only [Prod.smul_fst, Prod.smul_snd, PadicSupercuspidal.latticeCentralCharacter_zsmul,
      MonoidHom.zpow_apply, map_zsmul, toMul_zsmul, hx]

/-- The determinant clause of the relative analogue of Henniart's Proposition
2.6 (a): for every geometric reciprocity candidate, the image of each generated
Weil class has a central character whose pullback is its determinant. -/
theorem relativeIsometryDeterminantCompatibility
    (hc : RelativeWeilGroup.IsArithmeticClassFamily c)
    (T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ] automorphicImage.{uF, uW, uP} F E c v)
    (hT : RelativeGeneratedPositiveIsometry F E c v T)
    (e : Correspondence.ReciprocityCandidate (padicField v))
    (he : Correspondence.IsGeometricReciprocity (padicField v) e) :
    RelativeIsometryDeterminantCompatibility.{uF, uW, uP} F E c v T e := fun x =>
  ⟨PadicSupercuspidal.latticeCentralCharacter (padicField v) (T x).1,
    PadicSupercuspidal.isUnitaryCentralCharacter_latticeCentralCharacter _ _,
    fun w => pairedLattice_determinant F E c v hc e he
      (relative_graph_mem_pair F E c v T hT x) w⟩

end Langlands.Global.PoleComparison
