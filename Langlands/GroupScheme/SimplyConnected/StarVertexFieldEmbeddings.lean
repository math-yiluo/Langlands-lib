import Langlands.GroupScheme.SimplyConnected.VertexFieldWeightOrbits
import Mathlib.FieldTheory.Normal.Closure

/-! # Embeddings of an actual star vertex field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped BigOperators

namespace Langlands.GroupScheme.TitsIndexData

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)

/-- The finite Galois normal closure of a vertex field inside the original
separable closure. -/
abbrev starVertexNormalClosure (a : d.Vertex) : IntermediateField K (SeparableClosure K) :=
  IntermediateField.normalClosure K (d.starVertexField a) (SeparableClosure K)

/-- Lift an embedding of the actual vertex field to an absolute Galois automorphism. -/
def starVertexEmbeddingLift (a : d.Vertex)
    (f : d.starVertexField a →ₐ[K] d.starVertexNormalClosure a) :
    SeparableClosure K ≃ₐ[K] SeparableClosure K :=
  (Algebra.IsAlgebraic.algEquivEquivAlgHom K (SeparableClosure K)).symm
    (f.liftNormal (SeparableClosure K))

theorem starVertexEmbeddingLift_apply (a : d.Vertex)
    (f : d.starVertexField a →ₐ[K] d.starVertexNormalClosure a)
    (x : d.starVertexField a) :
    d.starVertexEmbeddingLift a f (algebraMap (d.starVertexField a) (SeparableClosure K) x) =
      algebraMap (d.starVertexNormalClosure a) (SeparableClosure K) (f x) :=
  f.liftNormal_commutes (SeparableClosure K) x

private theorem star_eq_star_iff_agree_on_vertexField (a : d.Vertex)
    (σ τ : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
    d.star σ a = d.star τ a ↔ ∀ x : d.starVertexField a, σ x = τ x := by
  constructor
  · intro h x
    have hfix : d.star (σ⁻¹ * τ) a = a := by
      rw [d.star_mul, ← h, ← d.star_mul, inv_mul_cancel, d.star_one]
    have hx := (d.fixes_starVertexField_iff a (σ⁻¹ * τ)).mpr hfix x x.property
    change σ.symm (τ x) = x at hx
    simpa only [σ.apply_symm_apply] using (congrArg σ hx).symm
  · intro h
    have hfix : d.star (σ⁻¹ * τ) a = a := by
      apply (d.fixes_starVertexField_iff a (σ⁻¹ * τ)).mp
      intro x hx
      change σ.symm (τ x) = x
      exact (congrArg σ.symm (h ⟨x, hx⟩)).symm.trans (σ.symm_apply_apply x)
    calc
      d.star σ a = d.star σ (d.star (σ⁻¹ * τ) a) := congrArg (d.star σ) hfix.symm
      _ = d.star τ a := by rw [← d.star_mul, mul_inv_cancel_left]

/-- Embeddings of the actual vertex field in its normal closure are in
bijection with vertices in the full star orbit. -/
def starVertexEmbeddingOrbitEquiv (a : d.Vertex) :
    (d.starVertexField a →ₐ[K] d.starVertexNormalClosure a) ≃ ↥(d.starOrbitVertices a) := by
  refine Equiv.ofBijective (fun f =>
    ⟨d.star (d.starVertexEmbeddingLift a f) a, (d.mem_starOrbitVertices a _).mpr
      ⟨d.starVertexEmbeddingLift a f, rfl⟩⟩) ⟨?_, ?_⟩
  · intro f g h
    have hv := (d.star_eq_star_iff_agree_on_vertexField a _ _).mp (congrArg Subtype.val h)
    apply AlgHom.ext
    intro x
    apply Subtype.ext
    exact ((d.starVertexEmbeddingLift_apply a f x).symm.trans (hv x)).trans
      (d.starVertexEmbeddingLift_apply a g x)
  · intro b
    obtain ⟨σ, hσ⟩ := (d.mem_starOrbitVertices a b.val).mp b.property
    let e := normalClosure.algHomEquiv K (d.starVertexField a) (SeparableClosure K)
    let ψ := σ.toAlgHom.domRestrict (d.starVertexField a)
    let f := e.symm ψ
    refine ⟨f, Subtype.ext ?_⟩
    change d.star (d.starVertexEmbeddingLift a f) a = b.val
    rw [← hσ]
    apply (d.star_eq_star_iff_agree_on_vertexField a _ _).mpr
    intro x
    change d.starVertexEmbeddingLift a f (algebraMap (d.starVertexField a) (SeparableClosure K) x) =
      ψ x
    rw [d.starVertexEmbeddingLift_apply]
    change (e (e.symm ψ)) x = ψ x
    rw [e.apply_symm_apply]

/-- The embeddings into this actual finite Galois overfield are counted by
the degree of the vertex field. -/
theorem natCard_starVertexEmbeddings (a : d.Vertex) :
    Nat.card (d.starVertexField a →ₐ[K] d.starVertexNormalClosure a) =
      Module.finrank K (d.starVertexField a) := by
  rw [d.finrank_starVertexField_eq_card_starOrbitVertices]
  exact (Nat.card_congr (d.starVertexEmbeddingOrbitEquiv a)).trans (Nat.card_eq_finsetCard _)

/-- The embedding sum of Galois translates of the actual fundamental weight
is the full orbit weight, with one term for each orbit vertex. -/
theorem sum_starVertexEmbeddings_eq_absoluteOrbitWeight (hsc : IsSimplyConnected G)
    (a : d.Vertex) [Fintype (d.starVertexField a →ₐ[K] d.starVertexNormalClosure a)] :
    (∑ f : d.starVertexField a →ₐ[K] d.starVertexNormalClosure a,
      (d.pinning.starAction (d.starVertexEmbeddingLift a f)).val.weightEquiv
        (d.absoluteFundamentalCharacter hsc a)) = d.absoluteOrbitWeight hsc a := by
  classical
  simp only [d.absoluteFundamentalCharacter_star]
  calc
    _ = ∑ b : ↥(d.starOrbitVertices a), d.absoluteFundamentalCharacter hsc b.val :=
      Fintype.sum_equiv (d.starVertexEmbeddingOrbitEquiv a) _ _ (fun _ => rfl)
    _ = d.absoluteOrbitWeight hsc a :=
      Finset.sum_coe_sort (d.starOrbitVertices a) (d.absoluteFundamentalCharacter hsc)

end Langlands.GroupScheme.TitsIndexData
