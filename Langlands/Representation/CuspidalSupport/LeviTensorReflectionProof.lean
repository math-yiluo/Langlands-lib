import Langlands.Representation.CuspidalSupport.LeviTensorReflectionStatement
import Langlands.Representation.Tensor.CoinvariantReflection

/-! Supercuspidality reflected by the actual standard-Levi tensor. -/

namespace Langlands.GeneralLinear.BlockShape

universe uF

/-- The actual unipotent subgroup of a one-block shape is trivial. -/
theorem singleBlock_unipotentSubgroup_eq_bot {n : ℕ} (B : BlockShape n)
    (hB : B.length = 1) (R : Type uF) [CommRing R] :
    B.unipotentSubgroup R = ⊥ := by
  apply le_antisymm _ bot_le
  intro g hg
  rw [Subgroup.mem_bot]
  apply Units.ext
  ext a b
  obtain ⟨⟨i, x⟩, rfl⟩ := B.indexEquiv.surjective a
  obtain ⟨⟨j, y⟩, rfl⟩ := B.indexEquiv.surjective b
  have he : j = i := (B.eq_singleBlockIndex hB j).trans
    (B.eq_singleBlockIndex hB i).symm
  subst j
  have h := ((B.mem_unipotentSubgroup_iff R g).mp hg).2 i x y
  change g (B.index i x) (B.index i y) =
    (1 : Matrix (Fin n) (Fin n) R) (B.index i x) (B.index i y)
  simpa only [Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq] using h

end Langlands.GeneralLinear.BlockShape

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric

universe uF uW

/-- Proof of the exact published Levi tensor supercuspidality reflection target. -/
theorem padicLeviTensorSupercuspidalReflection :
    PadicLeviTensorSupercuspidalReflectionStatement.{uF, uW} := by
  classical
  intro p _ F T n _ B
  let := T.topology
  intro A hirr hadm hqui j
  rw [isSupercuspidal_iff_standard]
  refine ⟨hadm j, ?_⟩
  intro C hC
  let S₀ : BlockRefinement B := fun i =>
    { length := 1
      size := fun _ => B.size i
      positive := fun _ => B.positive i
      sum_eq := by simp }
  let S : BlockRefinement B := Function.update S₀ j C
  have hproper : refinedParabolic F.Carrier B S ≠ ⊤ := by
    intro htop
    apply hC
    apply top_unique
    intro g _
    have hg : Pi.mulSingle j g ∈ refinedParabolic F.Carrier B S := by
      rw [htop]
      trivial
    have hgj : (Pi.mulSingle j g : B.Levi F.Carrier) j ∈
        (S j).parabolic F.Carrier :=
      hg j (Set.mem_univ j)
    simpa [S] using hgj
  have hN : ∀ i, i ≠ j → (S i).unipotentSubgroup F.Carrier = ⊥ := by
    intro i hi
    have hSi : S i = S₀ i := by simp [S, hi]
    rw [hSi]
    exact (S₀ i).singleBlock_unipotentSubgroup_eq_bot rfl F.Carrier
  have hne : ∀ i, i ≠ j → Nontrivial (A i).obj.V := by
    intro i _
    let := hirr i
    exact IsSimpleModule.nontrivial
      (MonoidAlgebra ℂ (GeneralLinear (B.size i) F.Carrier)) (A i).representation.asModule
  have h := FiniteTensor.coinvariants_factor_subsingleton
    (fun i => (A i).representation) (fun i => (S i).unipotentSubgroup F.Carrier)
    j hN hne (hqui S hproper)
  simpa [S] using h

end Langlands.CuspidalSupport
