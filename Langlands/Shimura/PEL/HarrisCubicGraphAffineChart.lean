import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicEmbeddingReduction
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFieldEmbeddingProof
import Langlands.AlgebraicGeometry.LinearSystem.CoefficientComparison
import Langlands.AlgebraicGeometry.Picard.NoetherianLineBundleSeesawProof
import Langlands.AlgebraicGeometry.ProjectiveSpace.TwistOnePresentation
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq

/-! # Affine section embeddings for the canonical cubic bundle -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry
open Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.ProjectiveBundle
open Langlands.AlgebraicGeometry.LinearSystem
open Langlands.Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option quotPrecheck false
set_option maxHeartbeats 1200000

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

variable {P : Prerequisites.{u}} {S : Scheme.{u}} {g d n : ℕ} (a : Datum P S g d n)

/-- An affine open in the base with a frame of the cubic direct image. -/
abbrev Datum.AffineCubicFrame :=
  {U : FrameOpen a.rigidificationModule (cubicProjectiveDimension g d) // IsAffineOpen U.val}

namespace Datum.AffineCubicFrame

variable {a}

/-- The ring of the actual affine frame open. -/
abbrev ring (i : a.AffineCubicFrame) : CommRingCat.{u} := Γ(S, i.val.val)

instance [IsLocallyNoetherian S] (i : a.AffineCubicFrame) : IsNoetherianRing i.ring :=
  IsLocallyNoetherian.component_noetherian ⟨i.val.val, i.property⟩

/-- The open inclusion from the spectrum of the affine frame ring. -/
def toBase (i : a.AffineCubicFrame) : Spec i.ring ⟶ S :=
  i.property.isoSpec.inv ≫ i.val.val.ι

instance (i : a.AffineCubicFrame) : IsOpenImmersion i.toBase := by
  dsimp only [toBase]
  infer_instance

end Datum.AffineCubicFrame

/-- The affine frame inclusions cover the original base. -/
theorem Datum.exists_affineCubicFrame_point [IsLocallyNoetherian S] (hd : 0 < d) (x : S) :
    ∃ (i : a.AffineCubicFrame) (y : Spec i.ring), i.toBase y = x := by
  let hM := (cubicDirectImage P S g d n hd a).1
  obtain ⟨U, hx, hU⟩ := exists_affine_frameOpen (a.cubicProjectiveRank hd hM) x
  let z : U.val.toScheme := ⟨x, hx⟩
  refine ⟨⟨U, hU⟩, hU.isoSpec.hom z, ?_⟩
  change U.val.ι (hU.isoSpec.inv (hU.isoSpec.hom z)) = x
  have hz := congrArg (fun f : U.val.toScheme ⟶ U.val.toScheme => f z) hU.isoSpec.hom_inv_id
  exact congrArg (fun t => U.val.ι t) hz

/-- The actual twist of a cubic graph embedding on the base-changed datum. -/
structure CubicGraphAffineChart (i : a.AffineCubicFrame) where
  module : (a.pullback i.toBase).abelian.X.left.Modules
  invertible : Scheme.Modules.IsInvertibleFLT module
  embedding : Scheme.Modules.ClosedImmersionBySections module (a.pullback i.toBase).abelian.X.hom
  isoCubic : module ≅ (a.pullback i.toBase).cubicBundle.obj

private theorem exists_cubicGraphAffineChart [IsLocallyNoetherian S] (hd : 0 < d)
    (i : a.AffineCubicFrame) : Nonempty (CubicGraphAffineChart a i) := by
  let U := i.val
  let R := i.ring
  let e : U.val.toScheme ≅ Spec R := i.property.isoSpec
  let p := a.abelian.X.hom
  let V := p ⁻¹ᵁ U.val
  let L := a.cubicBundle
  let r := cubicProjectiveDimension g d
  let hM := (cubicDirectImage P S g d n hd a).1
  let hgen := a.cubicEvaluationGenerates_of_fieldEmbedding cubicFieldEmbedding hd
  have hclosed := a.isClosedImmersion_cubicProjectiveEvaluation_of_fieldEmbedding
    cubicFieldEmbedding hd hM hgen
  let hs := hgen.frameEvaluationGenerates p L (𝟙 a.rigidificationModule) U
  let ψ := localEvaluationMap p L (𝟙 a.rigidificationModule)
    (frame a.rigidificationModule r U) U.val le_rfl hs
  have hψ : IsClosedImmersion ψ :=
    (a.isClosedImmersion_cubicProjectiveEvaluation_iff hd hM hgen).mp hclosed U
  let b := evaluationBase p U.val ≫ e.hom
  let φ := ψ ≫ RelativeProjectiveSpace.toPolynomial r e.hom
  have : IsIso (RelativeProjectiveSpace.map r e.hom) :=
    inferInstanceAs (IsIso ((RelativeProjectiveSpace.functor r).map e.hom))
  have hφ : IsClosedImmersion φ := by
    dsimp only [φ, RelativeProjectiveSpace.toPolynomial]
    infer_instance
  have hφeq : φ = linearSystemMap b hs :=
    relativeLinearSystemMap_toPolynomial (evaluationBase p U.val) e.hom hs
  have hφbase : φ ≫ projectiveSpaceToSpec R r = b := by
    rw [hφeq, linearSystemMap_toSpec]
  let L₀ := twistOne R r
  let L₁ := (Scheme.Modules.pullback φ).obj L₀
  let t : L₁ ≅ (evaluationLineBundle p L U.val).obj :=
    (Scheme.Modules.pullbackCongr hφeq).app L₀ ≪≫
      linearSystemTwistIso b _ hs
  have hleft : IsPullback (𝟙 V.toScheme) b (evaluationBase p U.val) e.inv :=
    IsPullback.of_horiz_isIso ⟨by simp [b]⟩
  have hright : IsPullback V.ι (evaluationBase p U.val) p U.val.ι := by
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using
      (isPullback_morphismRestrict p U.val).flip
  have hsq : IsPullback V.ι b p i.toBase := by
    simpa only [Category.id_comp, Datum.AffineCubicFrame.toBase] using hleft.paste_horiz hright
  let c := hsq.isoPullback
  let j := c.inv ≫ φ
  have hj : IsClosedImmersion j := by
    dsimp only [j]
    infer_instance
  have hjbase : j ≫ projectiveSpaceToSpec R r = (a.pullback i.toBase).abelian.X.hom := by
    change (c.inv ≫ φ) ≫ projectiveSpaceToSpec R r = pullback.snd p i.toBase
    rw [Category.assoc, hφbase]
    exact hsq.isoPullback_inv_snd
  let M := (Scheme.Modules.pullback j).obj L₀
  obtain ⟨pres, -, hpres⟩ :=
    Scheme.Modules.ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq j
      (twistOneProjPresentation R r)
  have hpresClosed : IsClosedImmersion pres.toProj := by
    rw [hpres]
    change IsClosedImmersion (j ≫ 𝟙 _)
    simpa only [Category.comp_id] using hj
  have hEmbed : Scheme.Modules.ClosedImmersionBySections M (j ≫ projectiveSpaceToSpec R r) :=
    ⟨r, pres, hpresClosed⟩
  refine ⟨⟨M, Scheme.Modules.IsInvertible.pullbackFLT (hL := twistOne_isInvertible R r) j,
    hjbase ▸ hEmbed, ?_⟩⟩
  exact ((Scheme.Modules.pullbackComp c.inv φ).app L₀).symm ≪≫
    (Scheme.Modules.pullback c.inv).mapIso t ≪≫
    (Scheme.Modules.pullbackComp c.inv V.ι).app L.obj ≪≫
    (Scheme.Modules.pullbackCongr hsq.isoPullback_inv_fst).app L.obj ≪≫
    ((LineBundle.forget _).mapIso (a.cubicBundlePullbackIso i.toBase)).symm

/-- The section embedding for the actual canonical cubic bundle on a specified
affine chart of the ordinary datum. -/
def Datum.cubicGraphAffineChart [IsLocallyNoetherian S] (hd : 0 < d)
    (i : a.AffineCubicFrame) : CubicGraphAffineChart a i :=
  Classical.choice (exists_cubicGraphAffineChart a hd i)

end Langlands.AbelianScheme.PolarizedFiniteLevel
