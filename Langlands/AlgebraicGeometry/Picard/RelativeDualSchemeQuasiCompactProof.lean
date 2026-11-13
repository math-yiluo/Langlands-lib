import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeQuasiCompactStatement
import Langlands.AlgebraicGeometry.Picard.RelativeMumfordFibreImage
import Langlands.AlgebraicGeometry.Picard.NoetherianAmpleFibreCover
import Langlands.AlgebraicGeometry.Picard.DualSchemeBaseChange
import Langlands.AlgebraicGeometry.Picard.PicardZeroUniversalBaseChangeProof
import Langlands.AlgebraicGeometry.Picard.MumfordBundlePicardZeroProof
import Langlands.AlgebraicGeometry.Picard.LineBundleDualEvaluation
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof

/-! # Quasi-compactness of the chosen dual parameter scheme -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.NoetherianApproximation
  Langlands.Scheme.Modules

/-- Every affine open of the base has an ample-fibre cover for an abelian scheme. -/
theorem hasAmpleFibreCover_of_isAffineOpen {S : Scheme.{u}} (A : AbelianScheme S)
    {U : S.Opens} (hU : IsAffineOpen U) : HasAmpleFibreCover A.X.hom (U : Set S) := by
  let h := hU.fromSpec
  let AR := (baseChange h).obj A
  obtain ⟨R₀, hR₀, φ, A₀, a, -, -, hpb, -, -, -⟩ :=
    abelianSchemeNoetherianModelReduction Langlands.AbelianScheme.subalgebraDescent
      lineBundleSubalgebraDescent lineBundleIsoSubalgebraDescent Γ(S, U) AR
      (RigidifiedLineBundle.trivial _) (RigidifiedLineBundle.trivial _)
  have h₁ : HasAmpleFibreCover AR.X.hom Set.univ :=
    HasAmpleFibreCover.baseChange hpb (noetherian_hasAmpleFibreCover A₀)
  have h₂ := HasAmpleFibreCover.of_isPullback (IsPullback.of_hasPullback A.X.hom h) h₁
  rwa [Set.image_univ, hU.range_fromSpec] at h₂

/-- Over a set with an ample-fibre cover, the preimage in the chosen dual is quasi-compact:
it is the union of the images of finitely many Mumford maps of base-changed abelian
schemes over affine schemes. -/
theorem isCompact_preimage_of_hasAmpleFibreCover {S : Scheme.{u}} (A : AbelianScheme S)
    (hA : HasDualScheme A) {V : Set S} (hV : HasAmpleFibreCover A.X.hom V) :
    IsCompact ((dualScheme A hA).hom ⁻¹' V) := by
  obtain ⟨ι, hι, T, W, g, a, q, L, hpb, haff, hrange, hcov⟩ := hV
  let P := dualScheme A hA
  have key : ∀ i, ∃ (Z : Scheme.{u}) (φ : Z ⟶ P.left), CompactSpace Z ∧
      Set.range φ ⊆ P.hom ⁻¹' V ∧
      ∀ y : P.left, ∀ t : T i, g i t = P.hom y →
        t ∈ ampleFibreLocus (q i) (L i) → y ∈ Set.range φ := by
    intro i
    have : IsAffine (T i) := haff i
    let B := (baseChange (g i)).obj A
    let hB : HasDualScheme B := hasDualScheme_baseChange picardZeroUniversalBaseChange (g i) A hA
    let e := (hpb i).isoPullback
    let L' : LineBundle B.X.left := (LineBundle.pullback e.inv).obj (L i)
    obtain ⟨Bb, ⟨evaluationB⟩⟩ :=
      ((LineBundle.pullback (unitSection B)).obj L').exists_tensorObj_iso_structureSheaf
    let N := LineBundle.normalize pullbackTensorComparisonIsIso B.X.hom (unitSection B)
      (unitSection_comp B) L' Bb evaluationB
    obtain ⟨M, ⟨evaluation⟩⟩ :=
      ((RigidifiedLineBundle.forget (unitSection B)).obj N).exists_tensorObj_iso_structureSheaf
    let m := mumfordSchemeMapOfLineBundle pullbackTensorComparisonIsIso B L' Bb evaluationB M
      evaluation mumfordBundlePicardZero hB
    let c := dualSchemeBaseChangeIso picardZeroUniversalBaseChange (g i) A hA hB
    let φ : B.X.left ⟶ P.left := m.left ≫ c.inv.left ≫ pullback.fst P.hom (g i)
    refine ⟨B.X.left, φ, QuasiCompact.compactSpace_of_compactSpace B.X.hom, ?_, ?_⟩
    · rintro _ ⟨z, rfl⟩
      have hcomm : φ ≫ P.hom = (m.left ≫ c.inv.left ≫ pullback.snd P.hom (g i)) ≫ g i := by
        simp only [φ, Category.assoc, pullback.condition]
      change (φ ≫ P.hom) z ∈ V
      rw [hcomm]
      exact hrange i ⟨_, rfl⟩
    · intro y t ht htL
      obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback y t ht.symm
      let w := c.hom.left z
      have hw : (dualScheme B hB).hom w = t := by
        change (c.hom.left ≫ (dualScheme B hB).hom) z = t
        rw [Over.w c.hom]
        exact hz₂
      have hsq : IsPullback e.inv (pullback.snd A.X.hom (g i)) (q i) (𝟙 (T i)) :=
        IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact (hpb i).isoPullback_inv_snd⟩
      have hwL : (dualScheme B hB).hom w ∈ ampleFibreLocus B.X.hom L' := by
        rw [hw]
        exact (mem_ampleFibreLocus_iff_of_isPullback hsq (L i) t).mpr htL
      obtain ⟨z', hz'⟩ := mem_range_mumfordSchemeMapOfLineBundle pullbackTensorComparisonIsIso
        mumfordBundlePicardZero B L' Bb evaluationB M evaluation hB w hwL
      refine ⟨z', ?_⟩
      have hinv : c.inv.left (c.hom.left z) = z := by
        change (c.hom.left ≫ c.inv.left) z = z
        rw [← Over.comp_left, c.hom_inv_id]
        rfl
      change pullback.fst P.hom (g i) (c.inv.left (m.left z')) = y
      rw [hz', hinv, hz₁]
  choose Z φ hZ hφV hφ using key
  have heq : P.hom ⁻¹' V = ⋃ i, Set.range (φ i) := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, t, ht, htL⟩ := hcov _ hy
      exact Set.mem_iUnion.mpr ⟨i, hφ i y t ht htL⟩
    · intro hy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      exact hφV i hi
  rw [heq]
  exact isCompact_iUnion fun i ↦ isCompact_range (φ i).continuous

/-- Over a quasi-separated base, the structural morphism of the chosen dual parameter
scheme is quasi-compact. -/
theorem relativeDualSchemeQuasiCompact : RelativeDualSchemeQuasiCompactStatement.{u} := by
  intro S _ A hA
  rw [quasiCompact_iff_forall_isAffineOpen]
  intro U hU
  exact isCompact_preimage_of_hasAmpleFibreCover A hA (hasAmpleFibreCover_of_isAffineOpen A hU)

end Langlands.AbelianScheme
