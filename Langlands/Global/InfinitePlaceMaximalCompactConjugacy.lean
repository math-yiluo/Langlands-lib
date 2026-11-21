import Langlands.Global.InfiniteCompletionRCLike
import Langlands.Global.InfinitePlaceLeviIwasawaBaseChange
import Langlands.Group.PolynomialStarCompactConjugacy
import Langlands.GroupScheme.AffinePolarCompact
import Langlands.GroupScheme.Reductive.SelfAdjointRealizationProof

/-! # Conjugacy of archimedean maximal compact subgroups -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.InfinitePlaceGroupPoints

open Langlands.GroupScheme Langlands.CompactIwasawa

private theorem exists_conj_maximalCompact_to_unitary
    {F : Type u} [RCLike F] {X : Type v} [Group X] [TopologicalSpace X]
    [SeparatelyContinuousMul X] {d : ℕ} (ρ : X →* Matrix.GeneralLinearGroup (Fin d) F)
    (hρ : Topology.IsClosedEmbedding ρ)
    (hpoly : Langlands.Group.AlgebraicMatrixPowers.IsPolynomiallyDefined ρ.range)
    (hstar : ∀ g ∈ ρ.range, star g ∈ ρ.range)
    (K : Subgroup X) (hK : IsMaximalCompact K) :
    ∃ a : X, K.map (MulAut.conj a⁻¹).toMonoidHom =
      Langlands.Group.MatrixPolarCompact.unitarySubgroup ρ := by
  have hcompact : IsCompact (K.map ρ : Set (Matrix.GeneralLinearGroup (Fin d) F)) := by
    rw [Subgroup.coe_map]
    exact hK.1.image hρ.continuous
  obtain ⟨m, ⟨a, rfl⟩, hm⟩ := Langlands.Group.PolynomialStarCompactConjugacy.exists_conj_unitary
    ρ.range (K.map ρ) hρ.isClosed_range hpoly hstar hcompact (by
      rintro _ ⟨g, _, rfl⟩
      exact ⟨g, rfl⟩)
  let e : X ≃ₜ* X := {
    toMulEquiv := MulAut.conj a⁻¹
    continuous_toFun := IsTopologicalGroup.continuous_conj a⁻¹
    continuous_invFun := by
      change Continuous (fun x => (MulAut.conj a⁻¹).symm x)
      simp only [MulAut.conj_symm_apply, inv_inv]
      exact IsTopologicalGroup.continuous_conj a }
  have hmax := hK.map e
  refine ⟨a, (hmax.2 _ (Langlands.Group.MatrixPolarCompact.isCompact_unitarySubgroup ρ hρ) ?_).symm⟩
  rintro _ ⟨g, hg, rfl⟩
  apply (Langlands.Group.MatrixPolarCompact.mem_unitarySubgroup ρ _).mpr
  change (ρ (a⁻¹ * g * (a⁻¹)⁻¹)).val ∈ Matrix.unitaryGroup (Fin d) F
  simpa only [map_mul, map_inv, inv_inv] using hm (ρ g) ⟨g, hg, rfl⟩

private theorem map_conj_map_conj {X : Type v} [Group X] (K : Subgroup X) (a b : X) :
    (K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      K.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  change b * (a * x * a⁻¹) * b⁻¹ = (b * a) * x * (b * a)⁻¹
  group

/-- Any two maximal compact subgroups of a connected reductive group's
actual infinite completion-point group are conjugate by a point of that group. -/
def InfinitePlaceMaximalCompactConjugacyStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (v : NumberField.InfinitePlace F)
    (K L : Subgroup (InfinitePlaceGroupPoints F G v)),
    IsConnectedReductive G → IsMaximalCompact K → IsMaximalCompact L →
    ∃ a : InfinitePlaceGroupPoints F G v, K.map (MulAut.conj a).toMonoidHom = L

theorem infinitePlaceMaximalCompactConjugacy : InfinitePlaceMaximalCompactConjugacyStatement.{u} := by
  intro F _ _ G v K L hG hK hL
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsTopologicalGroup (InfinitePlaceGroupPoints F G v) :=
    G.affinePointsIsTopologicalGroup (CommAlgCat.of F v.Completion)
  let Gv := completionBaseChange F G v
  have hGv : IsConnectedReductive Gv := isConnectedReductive_completionBaseChange F G hG v
  let : IsAffineHom Gv.X.hom := hGv.isAffineHom
  let : IsAffine Gv.X.left := isAffine_of_isAffineHom Gv.X.hom
  let : IsRCLikeNormedField v.Completion := v.completion_isRCLikeNormedField
  let : RCLike v.Completion := IsRCLikeNormedField.rclike v.Completion
  let e := completionBaseChangeHomeomorph F G v
  obtain ⟨d, ρ, hclosed, hstar⟩ :=
    SelfAdjointRealization.connectedReductiveSelfAdjointRealizationStatement v.Completion Gv hGv
  let : IsClosedImmersion ρ.hom.hom.left := hclosed
  let S := CommAlgCat.of v.Completion v.Completion
  let : TopologicalSpace (Gv.affinePoints S) := Gv.affinePointsTopologicalSpace S
  let ρ' := (ρ.affineMatrix S).comp e.toMonoidHom
  have hρ : Topology.IsClosedEmbedding ρ' :=
    (ρ.isClosedEmbedding_affineMatrix S hclosed).comp e.toHomeomorph.isClosedEmbedding
  have hrange : ρ'.range = (ρ.affineMatrix S).range := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨e.symm x, congrArg (ρ.affineMatrix S) (e.apply_symm_apply x)⟩
  have hpoly : Langlands.Group.AlgebraicMatrixPowers.IsPolynomiallyDefined ρ'.range :=
    hrange.symm ▸ ρ.affineMatrix_range_isPolynomiallyDefined v.Completion
  have hstar' : ∀ g ∈ ρ'.range, star g ∈ ρ'.range := hrange.symm ▸ hstar
  obtain ⟨a, ha⟩ := exists_conj_maximalCompact_to_unitary ρ' hρ hpoly hstar' K hK
  obtain ⟨b, hb⟩ := exists_conj_maximalCompact_to_unitary ρ' hρ hpoly hstar' L hL
  have h := congrArg (fun A => A.map (MulAut.conj b).toMonoidHom) (ha.trans hb.symm)
  have hone : (MulAut.conj (1 : InfinitePlaceGroupPoints F G v)).toMonoidHom =
      MonoidHom.id _ := by
    ext x
    simp
  rw [map_conj_map_conj, map_conj_map_conj, mul_inv_cancel, hone, Subgroup.map_id] at h
  exact ⟨b * a⁻¹, h⟩

end Langlands.Global.InfinitePlaceGroupPoints
