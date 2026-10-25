import Langlands.Representation.Parabolic.OppositeRefinementExactnessStatement
import Langlands.Representation.Parabolic.UnipotentFiniteContainment
import Langlands.Group.GL.InverseTransposeIwahoriProof
import Langlands.Representation.Jacquet.ExactProof

noncomputable section

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Geometric Representation

universe uF uU uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- Inverse transpose transfers finite containment from the upper refined
radical to the actual opposite refined radical. -/
theorem refinedOppositeUnipotent_finite_containment :
    letI := T.topology
    ∀ s : Finset (refinedOppositeUnipotent F.Carrier B S),
      ∃ K : OpenSubgroup (refinedOppositeUnipotent F.Carrier B S),
        IsCompact (K : Set (refinedOppositeUnipotent F.Carrier B S)) ∧
        ∀ u ∈ s, u ∈ K := by
  classical
  let := T.topology
  intro s
  let e : refinedOppositeUnipotent F.Carrier B S ≃ₜ*
      refinedUnipotent F.Carrier B S :=
    { toFun := fun g => ⟨fun i => inverseTranspose (B.size i) F.Carrier (g.val i),
        (mem_refinedUnipotent F.Carrier B S _).mpr fun i =>
          ((S i).inverseTranspose_mem_unipotentSubgroup_iff F.Carrier (g.val i)).mpr
            ((mem_refinedOppositeUnipotent F.Carrier B S g.val).mp g.property i)⟩
      invFun := fun g => ⟨fun i => inverseTranspose (B.size i) F.Carrier (g.val i),
        (mem_refinedOppositeUnipotent F.Carrier B S _).mpr fun i =>
          ((S i).inverseTranspose_mem_oppositeUnipotentSubgroup_iff F.Carrier
            (g.val i)).mpr
            ((mem_refinedUnipotent F.Carrier B S g.val).mp g.property i)⟩
      left_inv := by
        intro g
        apply Subtype.ext
        funext i
        exact inverseTranspose_involutive _ _ _
      right_inv := by
        intro g
        apply Subtype.ext
        funext i
        exact inverseTranspose_involutive _ _ _
      map_mul' := by
        intro g h
        apply Subtype.ext
        funext i
        exact map_mul (inverseTranspose (B.size i) F.Carrier) _ _
      continuous_toFun := (continuous_pi fun i =>
        (T.generalLinearInverseTranspose (B.size i)).continuous.comp
          ((continuous_apply i).comp continuous_subtype_val)).subtype_mk _
      continuous_invFun := (continuous_pi fun i =>
        (T.generalLinearInverseTranspose (B.size i)).continuous.comp
          ((continuous_apply i).comp continuous_subtype_val)).subtype_mk _ }
  obtain ⟨K, hK, hs⟩ := T.refinedUnipotent_finite_containment B S (s.image e)
  refine ⟨OpenSubgroup.comap e.toMonoidHom e.continuous K, ?_, ?_⟩
  · exact e.toHomeomorph.isClosedEmbedding.isCompact_preimage hK
  · intro u hu
    exact hs _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)

variable {U : Type uU} {V : Type uV} {W : Type uW}
  [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

theorem normalizedRefinedOppositeJacquetMap_injective
    {ρ : Representation ℂ (B.Levi F.Carrier) U}
    {σ : Representation ℂ (B.Levi F.Carrier) V} (i : ρ.IntertwiningMap σ) :
    letI := T.topology
    IsSmooth σ → Function.Injective i →
      Function.Injective (T.normalizedRefinedOppositeJacquetMap B S i) := by
  let := T.topology
  let := T.leviTopologicalGroup B
  intro hσ hi
  let N := refinedOppositeUnipotent F.Carrier B S
  have hs : IsSmooth (σ.comp N.subtype) :=
    isSmooth_comp N.subtype continuous_subtype_val hσ
  exact coinvariants_map_injective_of_smooth
    (T.refinedOppositeUnipotent_finite_containment B S) (Jacquet.restrictMap i N) hi hs

theorem normalizedRefinedOppositeJacquetMap_right_exact
    {ρ : Representation ℂ (B.Levi F.Carrier) U}
    {σ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W}
    (i : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap τ)
    (hq : Function.Surjective q)
    (hex : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap) :
    LinearMap.range (T.normalizedRefinedOppositeJacquetMap B S i).toLinearMap =
      LinearMap.ker (T.normalizedRefinedOppositeJacquetMap B S q).toLinearMap ∧
    Function.Surjective (T.normalizedRefinedOppositeJacquetMap B S q) := by
  let N := refinedOppositeUnipotent F.Carrier B S
  exact ⟨coinvariants_map_range_eq_ker (Jacquet.restrictMap i N)
      (Jacquet.restrictMap q N) hq hex,
    coinvariants_map_surjective (Jacquet.restrictMap q N) hq⟩

theorem normalizedRefinedOppositeJacquet_binary_product
    (ρ : Representation ℂ (B.Levi F.Carrier) U)
    (σ : Representation ℂ (B.Levi F.Carrier) V) :
    ∃ E : (T.normalizedRefinedOppositeJacquet B S (ρ.prod σ)).Equiv
      ((T.normalizedRefinedOppositeJacquet B S ρ).prod
        (T.normalizedRefinedOppositeJacquet B S σ)),
      ∀ (u : U) (v : V),
        E (refinedOppositeJacquetMk B S (ρ.prod σ) (u, v)) =
          (refinedOppositeJacquetMk B S ρ u, refinedOppositeJacquetMk B S σ v) := by
  let f := (T.normalizedRefinedOppositeJacquetMap B S
      (IntertwiningMap.fst ℂ ρ σ)).prod
    (T.normalizedRefinedOppositeJacquetMap B S (IntertwiningMap.snd ℂ ρ σ))
  let g := (T.normalizedRefinedOppositeJacquetMap B S
      (IntertwiningMap.inl ℂ ρ σ)).comp
        (IntertwiningMap.fst ℂ (T.normalizedRefinedOppositeJacquet B S ρ)
          (T.normalizedRefinedOppositeJacquet B S σ)) +
    (T.normalizedRefinedOppositeJacquetMap B S
      (IntertwiningMap.inr ℂ ρ σ)).comp
        (IntertwiningMap.snd ℂ (T.normalizedRefinedOppositeJacquet B S ρ)
          (T.normalizedRefinedOppositeJacquet B S σ))
  have hf (u : U) (v : V) :
      f (refinedOppositeJacquetMk B S (ρ.prod σ) (u, v)) =
        (refinedOppositeJacquetMk B S ρ u, refinedOppositeJacquetMk B S σ v) := rfl
  have hg (u : U) (v : V) :
      g (refinedOppositeJacquetMk B S ρ u, refinedOppositeJacquetMk B S σ v) =
        refinedOppositeJacquetMk B S (ρ.prod σ) (u, v) := by
    change refinedOppositeJacquetMk B S (ρ.prod σ) (u, 0) +
      refinedOppositeJacquetMk B S (ρ.prod σ) (0, v) = _
    rw [← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  have hgf : Function.LeftInverse g f := by
    intro x
    obtain ⟨⟨u, v⟩, rfl⟩ := refinedOppositeJacquetMk_surjective B S (ρ.prod σ) x
    rw [hf, hg]
  have hfg : Function.RightInverse g f := by
    rintro ⟨x, y⟩
    obtain ⟨u, rfl⟩ := refinedOppositeJacquetMk_surjective B S ρ x
    obtain ⟨v, rfl⟩ := refinedOppositeJacquetMk_surjective B S σ y
    rw [hg, hf]
  exact ⟨f.ofBijective ⟨hgf.injective, hfg.surjective⟩, hf⟩

end Langlands.PadicField.TopologicalData

namespace Langlands.Parabolic

universe uF uU uV uW

theorem normalizedRefinedOppositeJacquetExactness :
    NormalizedRefinedOppositeJacquetExactnessStatement.{uF, uU, uV, uW} := by
  intro p hp F T n B S
  refine ⟨?_, ?_, ?_⟩
  · intro U V hU hMU hV hMV ρ σ i
    exact T.normalizedRefinedOppositeJacquetMap_injective B S i
  · intro U V W hU hMU hV hMV hW hMW ρ σ τ i q hq hex
    exact T.normalizedRefinedOppositeJacquetMap_right_exact B S i q hq hex
  · intro U V hU hMU hV hMV ρ σ
    exact T.normalizedRefinedOppositeJacquet_binary_product B S ρ σ

end Langlands.Parabolic
