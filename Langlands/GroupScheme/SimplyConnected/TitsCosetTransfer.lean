import Langlands.GroupScheme.Reductive.TitsTransfer
import Langlands.GroupScheme.Reductive.TitsObstructionSimplyConnected
import Langlands.GroupScheme.SimplyConnected.StarFixedWeightsBaseChange
import Langlands.GroupScheme.SimplyConnected.StarVertexFieldWeights
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof
import Mathlib.FieldTheory.Normal.Closure

/-! # The transfer law for the Tits obstruction in coset-sum form -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry IntermediateField

namespace Langlands.GroupScheme

namespace GaloisPinningData

open Langlands.BrauerCorestriction

/-! ## Embeddings into the normal closure and a transversal of `Gal(K/E)` -/

section Embeddings

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [Normal k K]
  (E : IntermediateField k K)

/-- An automorphism of `K / k` extending an embedding `σ : E → N` of `E` into its normal
closure `N` in `K`. -/
def embeddingLift (σ : E →ₐ[k] normalClosure k E K) : K ≃ₐ[k] K :=
  AlgEquiv.ofBijective (σ.liftNormal K) (Algebra.IsAlgebraic.algHom_bijective _)

/-- `embeddingLift E σ` extends `σ`. -/
theorem embeddingLift_algebraMap (σ : E →ₐ[k] normalClosure k E K) (x : E) :
    embeddingLift E σ (algebraMap E K x) = algebraMap (normalClosure k E K) K (σ x) :=
  σ.liftNormal_commutes K x

theorem embeddingLift_coe (σ : E →ₐ[k] normalClosure k E K) (x : E) :
    embeddingLift E σ (x : K) = (σ x : K) :=
  embeddingLift_algebraMap E σ x

/-- `g` lies in the left coset of `embeddingLift E σ` modulo `Gal(K/E)` exactly when `g`
restricts to `σ` on `E`. -/
theorem embeddingLift_inv_mul_mem_fixingSubgroup_iff (σ : E →ₐ[k] normalClosure k E K)
    (g : K ≃ₐ[k] K) :
    (embeddingLift E σ)⁻¹ * g ∈ E.fixingSubgroup ↔ ∀ x : E, g x = (σ x : K) := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x
    have hx := h x x.2
    rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] at hx
    rw [hx, embeddingLift_coe]
  · intro h x hx
    rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, h ⟨x, hx⟩]
    exact (embeddingLift_coe E σ ⟨x, hx⟩).symm

/-- Distinct embeddings have distinct extensions. -/
theorem embeddingLift_injective : Function.Injective (embeddingLift E) := by
  intro σ τ h
  ext x
  have h1 := embeddingLift_coe E σ x
  rw [h, embeddingLift_coe] at h1
  exact h1.symm

/-- The extensions of the embeddings `E → N` form a left transversal of `Gal(K/E)` in
`Gal(K/k)`. -/
theorem isComplement_range_embeddingLift :
    Subgroup.IsComplement (Set.range (embeddingLift E))
      (E.fixingSubgroup : Set (K ≃ₐ[k] K)) := by
  rw [Subgroup.isComplement_subgroup_right_iff_bijective]
  constructor
  · rintro ⟨_, σ, rfl⟩ ⟨_, τ, rfl⟩ h
    simp only [Set.domRestrict_apply] at h
    rw [QuotientGroup.eq, embeddingLift_inv_mul_mem_fixingSubgroup_iff] at h
    have hστ : σ = τ := by
      ext x
      exact (h x).symm.trans (embeddingLift_coe E τ x)
    subst hστ
    rfl
  · intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      let σ : E →ₐ[k] normalClosure k E K :=
        (normalClosure.algHomEquiv k E K).symm ((g : K →ₐ[k] K).comp E.val)
      refine ⟨⟨embeddingLift E σ, σ, rfl⟩, ?_⟩
      simp only [Set.domRestrict_apply]
      rw [QuotientGroup.eq, embeddingLift_inv_mul_mem_fixingSubgroup_iff]
      intro x
      rfl

variable [IsGalois k K] [FiniteDimensional k E]

omit [FiniteDimensional k E] in
/-- There are exactly `[E : k]` embeddings of `E` into its normal closure. -/
theorem card_embeddings : Nat.card (E →ₐ[k] normalClosure k E K) = Module.finrank k E := by
  have : Algebra.IsSeparable k E := Algebra.isSeparable_tower_bot_of_isSeparable k E K
  rw [Nat.card_congr (normalClosure.algHomEquiv k E K),
    ← Field.finSepDegree_eq_finrank_of_isSeparable]
  refine (Field.finSepDegree_eq_of_adjoin_splits (F := k) (E := E) (K := K) (S := Set.univ)
    (IntermediateField.adjoin_univ k E) fun s _ => ⟨Algebra.IsIntegral.isIntegral s, ?_⟩).symm
  rw [IntermediateField.minpoly_eq]
  exact Normal.splits inferInstance (s : K)

instance finite_embeddings : Finite (E →ₐ[k] normalClosure k E K) :=
  Nat.finite_of_card_ne_zero (by rw [card_embeddings]; exact Module.finrank_pos.ne')

/-- An enumeration of the embeddings of `E` into its normal closure. -/
def embeddingEnum : (E →ₐ[k] normalClosure k E K) ≃ Fin (Module.finrank k E - 1 + 1) :=
  (Finite.equivFin _).trans
    (finCongr (by rw [card_embeddings]; exact (Nat.sub_add_cancel Module.finrank_pos).symm))

end Embeddings

/-- The base change of a simply connected group to an intermediate field is simply
connected (Library `isSimplyConnectedFieldExtension`). -/
theorem isSimplyConnected_baseChange {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsSimplyConnected G)
    (E : IntermediateField k K) :
    IsSimplyConnected ((GroupScheme.baseChange (algebraBaseMap k E)).obj G) :=
  isSimplyConnectedFieldExtension k E G hG

/-! ## The coset sum as a sum over embeddings -/

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : GaloisPinningData k K G)

/-- For a weight fixed by `Gal(K/E)`, the sum of its star translates by the extensions of the
embeddings `E → N`, in any enumeration, is the coset sum. -/
theorem sum_embeddingLift_eq_cosetSum [Normal k K] (E : IntermediateField k K)
    {lam : characterLattice d.toSplitPinning.torus} (hlam : lam ∈ d.fixedWeights E.fixingSubgroup)
    {m : ℕ} (e : (E →ₐ[k] normalClosure k E K) ≃ Fin (m + 1)) :
    ∑ i, (d.starAction (embeddingLift E (e.symm i))).val • lam = d.cosetSum E lam := by
  classical
  have : Fintype (E →ₐ[k] normalClosure k E K) := Fintype.ofEquiv _ e.symm
  rw [e.symm.sum_comp (fun σ => (d.starAction (embeddingLift E σ)).val • lam),
    ← Finset.sum_image (f := fun g => (d.starAction g).val • lam)
      (fun σ _ τ _ h => embeddingLift_injective E h)]
  simp_rw [smul_eq_weightEquiv]
  apply d.sum_transversal_eq_cosetSum hlam
  simpa [Finset.coe_image, Set.image_univ] using isComplement_range_embeddingLift E

/-- The same identity stated with `embeddingConjSum`: with the extensions `embeddingLift E`,
the embedding-indexed conjugate sum of a weight fixed by `Gal(K/E)` is its coset sum. -/
theorem embeddingConjSum_embeddingLift [Normal k K] (E : IntermediateField k K)
    {lam : characterLattice d.toSplitPinning.torus} (hlam : lam ∈ d.fixedWeights E.fixingSubgroup)
    {m : ℕ} (e : (E →ₐ[k] normalClosure k E K) ≃ Fin (m + 1)) :
    d.embeddingConjSum e (embeddingLift E) lam = d.cosetSum E lam :=
  d.sum_embeddingLift_eq_cosetSum E hlam e

/-! ## The transfer law -/

variable [IsGalois k K]

/-- **Transfer law, coset-sum form.** Let `E` be an intermediate field of `K / k`, finite over
`k`, and `λ` a weight fixed by the star action of `Γ_E = Gal(K/E)`. The Tits obstruction of `G`
at the coset sum `∑_{σ ∈ Γ/Γ_E} σ ⋆ λ` is the corestriction from `E` to `k` of the Tits
obstruction of `G_E` at the transported weight `λ_E`. -/
theorem titsObstruction_cosetSum (hG : IsSimplyConnected G) (E : IntermediateField k K)
    [FiniteDimensional k E] (lam : d.fixedWeights E.fixingSubgroup) :
    d.titsObstruction hG ⟨d.cosetSum E lam, d.cosetSum_mem_starFixedWeights lam.2⟩ =
      corHom k E ((d.baseChange E).titsObstruction (isSimplyConnected_baseChange hG E)
        (d.fixedWeightsBaseChangeEquiv E lam)) := by
  have : Algebra.IsSeparable k E := Algebra.isSeparable_tower_bot_of_isSeparable k E K
  have hfixE : (d.baseChange E).IsStarFixedWeight (d.weightTransport E lam) :=
    ((d.baseChange E).mem_starFixedWeights_iff_isStarFixedWeight _).mp
      ((d.weightTransport_mem_starFixedWeights_iff E lam).mpr lam.2)
  have h := d.titsObstructionValue_transfer (d.corootSpan_eq_top_of_simplyConnected hG)
    (E := E) (N := normalClosure k E K) (card_embeddings E)
    ((d.baseChange E).corootSpan_eq_top_of_simplyConnected (isSimplyConnected_baseChange hG E))
    (embeddingEnum E) (embeddingLift E) (embeddingLift_algebraMap E) hfixE
  rw [titsObstruction_apply]
  convert h using 2
  · exact (d.sum_embeddingLift_eq_cosetSum E lam.2 (embeddingEnum E)).symm
  · rfl

/-- **Transfer law, as an identity of additive maps.** On the weights fixed by `Gal(K/E)`,
the obstruction of `G` composed with the coset sum is the corestriction of the obstruction
of `G_E` composed with the weight transport. -/
theorem titsObstruction_comp_cosetSumHom (hG : IsSimplyConnected G) (E : IntermediateField k K)
    [FiniteDimensional k E] (lam : d.fixedWeights E.fixingSubgroup) :
    d.titsObstruction hG ⟨d.cosetSum E lam, d.cosetSum_mem_starFixedWeights lam.2⟩ =
      ((corHom k E).comp (((d.baseChange E).titsObstruction
        (isSimplyConnected_baseChange hG E)).comp
          (d.fixedWeightsBaseChangeEquiv E).toAddMonoidHom)) lam :=
  d.titsObstruction_cosetSum hG E lam

end GaloisPinningData

/-! ## Specialization to the simple-vertex field -/

namespace TitsIndexData

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G) (hsc : IsSimplyConnected G)

/-- The sum of the actual fundamental weights over the star orbit of a vertex `a`, each
vertex once, is star fixed. -/
theorem finsum_orbit_mem_starFixedWeights (a : d.Vertex) :
    (∑ᶠ b ∈ {b : d.Vertex | ∃ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K,
        d.star σ a = b}, d.absoluteFundamentalCharacter hsc b) ∈
      d.pinning.starFixedWeights := by
  rw [← d.cosetSum_starVertexField hsc a]
  exact d.pinning.cosetSum_mem_starFixedWeights
    (d.absoluteFundamentalCharacter_mem_fixedWeights hsc a)

/-- **Transfer law on the simple-vertex field.** For a vertex `a` with simple-vertex field
`k_a`, the Tits obstruction of `G` at the sum of the fundamental weights over the star orbit
of `a`, each vertex once, is the corestriction from `k_a` of the Tits obstruction of `G_{k_a}`
at the transported fundamental weight of `a`. -/
theorem titsObstruction_finsum_orbit (a : d.Vertex) :
    d.pinning.titsObstruction hsc
        ⟨∑ᶠ b ∈ {b : d.Vertex | ∃ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K,
          d.star σ a = b}, d.absoluteFundamentalCharacter hsc b,
          d.finsum_orbit_mem_starFixedWeights hsc a⟩ =
      Langlands.BrauerCorestriction.corHom K (d.starVertexField a)
        ((d.pinning.baseChange (d.starVertexField a)).titsObstruction
          (GaloisPinningData.isSimplyConnected_baseChange hsc (d.starVertexField a))
          (d.pinning.fixedWeightsBaseChangeEquiv (d.starVertexField a)
            ⟨d.absoluteFundamentalCharacter hsc a,
              d.absoluteFundamentalCharacter_mem_fixedWeights hsc a⟩)) := by
  rw [← d.pinning.titsObstruction_cosetSum hsc (d.starVertexField a)
    ⟨d.absoluteFundamentalCharacter hsc a, d.absoluteFundamentalCharacter_mem_fixedWeights hsc a⟩]
  congr 2
  exact (d.cosetSum_starVertexField hsc a).symm

end TitsIndexData

end Langlands.GroupScheme
