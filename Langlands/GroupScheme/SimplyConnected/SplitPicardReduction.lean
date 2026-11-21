import Langlands.GroupScheme.SimplyConnected.SplitPicardReductionStatement
import Langlands.GroupScheme.SimplyConnected.SplitPicardCharacterLifting
import Langlands.GroupScheme.SimplyConnected.SplitPicardTrivialCoverProof
import Langlands.GroupScheme.Absolute.CharacterUnipotence
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.CentralIsogeny.SplitMaximalTorusLiftProof
import Langlands.GroupScheme.Reductive.TitsIndexSplitRankProof
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Simple connectedness and trivial Picard group for split semisimple groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {H G : GroupScheme (Spec (CommRingCat.of k))}

/-- A central isogeny with split connected reductive source is invertible if
every rational character of its full scheme-theoretic kernel vanishes. -/
theorem IsCentralIsogeny.isIso_of_kernel_characters_eq_zero
    {f : H ⟶ G} (hf : IsCentralIsogeny f) (hH : IsConnectedReductive H)
    (hsplit : HasSplitMaximalTorus H)
    (hχ : ∀ χ : rationalCharacters (kernel f), χ = 0) : IsIso f := by
  obtain ⟨T, j, hT, hj⟩ := hsplit
  have : IsClosedImmersion j.hom.hom.left := hj.2.1
  have hjrep : (SubgroupFunctor.range j).IsRepresentedBy j :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hker : SubgroupFunctor.range (kernelι f) ≤ SubgroupFunctor.range j := by
    rw [← maximalTorusCentralizer k H hH T j hj]
    exact hf.kernel_range_le_center.trans (center_le_torusCentralizer j)
  let i := hjrep.factorHom (kernelι f) hker
  have hi : i ≫ j = kernelι f := hjrep.factorHom_comp (kernelι f) hker
  have hi0 : i = 0 := hT.hom_eq_zero_of_characters_eq_zero hχ i
  have hι0 : kernelι f = 0 := by rw [← hi, hi0, zero_comp]
  have : Mono f.hom.hom := by
    constructor
    intro U a b hab
    apply div_eq_one.mp
    have hk : (a / b) ≫ f.hom.hom = 1 := by
      rw [GrpObj.div_comp, hab, div_self']
    obtain ⟨x, hx⟩ := SubgroupFunctor.mem_range.mp
      ((mem_range_kernelι_iff f (a / b)).mpr hk)
    rw [← hx, hι0]
    exact MonObj.comp_one x
  have : Mono f.hom.hom.left := Over.mono_left_of_mono _
  have : IsFinite f.hom.hom.left := hf.isFinite
  have : Flat f.hom.hom.left := hf.flat
  have : Surjective f.hom.hom.left := hf.surjective
  have : IsIso f.hom.hom.left := Flat.isIso_of_surjective_of_mono _
  have : IsIso ((Over.forget (Spec (CommRingCat.of k))).map f.hom.hom) := by
    change IsIso f.hom.hom.left
    infer_instance
  have : IsIso f.hom.hom :=
    isIso_of_reflects_iso f.hom.hom (Over.forget (Spec (CommRingCat.of k)))
  let e : H ≅ G := Grp.mkIso' (asIso f.hom.hom)
  change IsIso e.hom
  infer_instance

/-- The two geometric inputs imply the unchanged split semisimple Picard
criterion in every universe. -/
theorem splitSemisimplePicardReduction :
    SplitSemisimplePicardReductionStatement.{u} := by
  rintro ⟨hlift, hcover⟩ k _ G hG hsplit
  constructor
  · intro hsc
    obtain ⟨H, f, hH, hf, hpicH⟩ := hcover k G hG hsplit
    have : IsIso f := hsc.central_isogeny_isIso H f hH hf
    have : IsIso f.hom.hom := (Grp.forget _).map_isIso f
    have : IsIso f.hom.hom.left := (Over.forget _).map_isIso f.hom.hom
    exact SplitPicardCharacterLifting.lineBundlesTrivial_of_isIso f.hom.hom.left hpicH
  · intro hpic
    refine ⟨hG, ?_⟩
    intro H f hH hf
    obtain ⟨T, j, hT, hj⟩ := hsplit
    obtain ⟨T', j', -, hT', hj', -⟩ :=
      centralIsogenySplitMaximalTorusLift k H G hH.isConnectedReductive
        hG.isConnectedReductive f hf T j hT hj
    have hsplitH : HasSplitMaximalTorus H := ⟨T', j', hT', hj'⟩
    have hsurj := hlift k H G hH.isConnectedReductive hG.isConnectedReductive
      hsplitH ⟨T, j, hT, hj⟩ f hf hpic
    apply hf.isIso_of_kernel_characters_eq_zero hH.isConnectedReductive hsplitH
    intro χ
    obtain ⟨ψ, hψ⟩ := hsurj χ
    have := hH.subsingleton_rationalCharacters
    rw [← hψ, Subsingleton.elim ψ 0, map_zero]

/-- A semisimple group over a field with a split maximal torus is simply connected
if and only if each line bundle on its underlying scheme is trivial. -/
theorem splitSemisimpleSimplyConnectedPicard :
    SplitSemisimpleSimplyConnectedPicardStatement.{u} :=
  splitSemisimplePicardReduction
    ⟨splitCentralIsogenyPicardCharacterLifting, splitSemisimplePicardTrivialCover⟩

end Langlands.GroupScheme
