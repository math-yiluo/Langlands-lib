import Langlands.GroupScheme.Lie.UnipotentNilpotentDifferentialStatement
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.Lie.PrimePowerFieldExtension
import Langlands.GroupScheme.Lie.SemisimpleNilpotentMatrix
import Langlands.GroupScheme.Lie.SplitTorusSemisimple
import Langlands.GroupScheme.Lie.UnipotentTangent
import Langlands.GroupScheme.Lie.ZeroTangentTriviality
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.Torus.ImageProof
import Langlands.GroupScheme.Torus.NoTorusUnipotent

/-! # Unipotence via nilpotent differentials of representations -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

private theorem tangentMatrix_eq_zero_of_isTorus
    {k : Type u} [Field k] {T : GroupScheme (Spec (CommRingCat.of k))}
    (hT : IsTorus T) {n : ℕ} (ρ : MatrixRepresentation T (Fin n))
    (X : lieKernel T k) (hN : IsNilpotent (ρ.tangentMatrix k X)) :
    ρ.tangentMatrix k X = 0 := by
  obtain ⟨K, _, _, hsplit⟩ := hT
  let XK := (Lie.kernelBaseChangeEquiv k K T K).symm
    (lieKernelMap T (Algebra.ofId k K) X)
  have hbase : (ρ.baseChange (algebraBaseMap k K)).tangentMatrix K XK =
      (algebraMap k K).mapMatrix (ρ.tangentMatrix k X) := by
    rw [ρ.tangentMatrix_baseChange]
    dsimp only [XK]
    rw [MulEquiv.apply_symm_apply, ρ.tangentMatrix_naturality]
    rfl
  have hsem := Lie.isSemisimpleElement_of_isSplitTorus hsplit XK n
    (ρ.baseChange (algebraBaseMap k K))
  rw [hbase] at hsem
  have hz := hsem.eq_zero_of_isNilpotent (hN.map (algebraMap k K).mapMatrix)
  apply Matrix.map_injective (algebraMap k K).injective
  exact hz.trans (map_zero (algebraMap k K).mapMatrix).symm

private theorem isUnipotent_of_faithful_nilpotent_differential
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {n : ℕ} (ρ : MatrixRepresentation G (Fin n)) (hρ : IsClosedSubgroup ρ)
    (hN : ∀ X : lieKernel G k, IsNilpotent (ρ.tangentMatrix k X)) : IsUnipotent G := by
  apply noTorusUnipotent k G
  intro T hT e
  obtain ⟨Z, i, f, hZ, hi, hfac⟩ := torusImageClosedTorusStatement k G T.toGrp hT e
  let σ := ρ.restrict i
  let : IsClosedImmersion σ.hom.hom.left := hi.comp hρ
  let : IsClosedImmersion i.hom.hom.left := hi
  let : IsAffineHom Z.toGrp.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  let : Smooth Z.toGrp.X.hom := hZ.smooth
  let : ConnectedSpace Z.toGrp.X.left := hZ.connectedSpace
  have hone (X : lieKernel Z.toGrp k) : X = 1 := by
    have hnil : IsNilpotent (σ.tangentMatrix k X) := by
      rw [MatrixRepresentation.tangentMatrix_restrict]
      exact hN (Lie.targetMap i k X)
    apply σ.tangentMatrix_injective (Over.mono_of_mono_left _) k
    rw [σ.tangentMatrix_one, tangentMatrix_eq_zero_of_isTorus hZ σ X hnil]
  let : Subsingleton (lieKernel Z.toGrp k) := ⟨fun X Y => (hone X).trans (hone Y).symm⟩
  rw [← hfac]
  apply SubgroupFunctor.ext
  intro U
  rw [SubgroupFunctor.bot_carrier, Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  rw [Grp.comp_hom_hom, ← Category.assoc,
    Lie.points_eq_one_of_subsingleton_lieKernel Z.toGrp U (y ≫ f.hom.hom), MonObj.one_comp]

/-- Milne 2017, Corollary 16.61 (a), (c), and (d), for smooth connected affine
algebraic groups over any field. -/
theorem unipotentNilpotentDifferential : UnipotentNilpotentDifferentialStatement.{u} := by
  intro k _ G _ _ _
  have forward (hG : IsUnipotent G) (n : ℕ) (ρ : MatrixRepresentation G (Fin n))
      (X : lieKernel G k) : IsNilpotent (ρ.tangentMatrix k X) :=
    ρ.isNilpotent_tangentMatrix_of_isUnipotent hG k X
  obtain ⟨n, ρ, hρ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  refine ⟨⟨forward, ?_⟩, ⟨fun hG => ⟨n, ρ, hρ, forward hG n ρ⟩, ?_⟩⟩
  · intro h
    exact isUnipotent_of_faithful_nilpotent_differential ρ hρ (h n ρ)
  · rintro ⟨m, σ, hσ, hN⟩
    exact isUnipotent_of_faithful_nilpotent_differential σ hσ hN

end Langlands.GroupScheme
