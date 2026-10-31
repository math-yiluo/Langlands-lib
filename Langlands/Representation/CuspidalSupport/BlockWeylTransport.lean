import Langlands.Representation.CuspidalSupport.GroupTransport
import Langlands.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.Representation.CuspidalSupport.MinimalConjugatingCosetsProof
import Langlands.Representation.CuspidalSupport.AssociationReduction
import Langlands.Representation.Geometric.BruhatDescent
import Langlands.Representation.Smooth.Admissibility.EquivalenceProof
import Langlands.Representation.Smooth.Admissibility.Extension

/-! Weyl transport along block-Weyl cosets, and admissibility of transports
and of filtrations with transported graded pieces. -/

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric

universe uF uV uW

variable {F : Type uF} [Field F] {n : ℕ}
  (B C : BlockShape n)
  {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The diagonal-block projection of the permutation matrix of a block-Weyl
element. It is an actual element of the source Levi. -/
def blockWeylLeviElement {b : Equiv.Perm (Fin n)} (hb : b ∈ blockWeyl B) : B.Levi F :=
  B.leviProjection F ⟨permutation n F b, permutation_mem_parabolic_of_mem_blockWeyl F B hb⟩

/-- Inverse conjugation by `v * b`, with `b` in the source block-Weyl group,
is inverse conjugation by `v` followed by conjugation in the source Levi. -/
theorem leviConjugation_symm_mul_blockWeyl {v b : Equiv.Perm (Fin n)}
    (hb : b ∈ blockWeyl B) (hv : ConjugatesLevi (F := F) B C v)
    (hw : ConjugatesLevi (F := F) B C (v * b)) (m : C.Levi F) :
    (leviConjugation B C (v * b) hw).symm m =
      (blockWeylLeviElement B hb)⁻¹ * (leviConjugation B C v hv).symm m *
        blockWeylLeviElement B hb := by
  let pb : B.parabolic F :=
    ⟨permutation n F b, permutation_mem_parabolic_of_mem_blockWeyl F B hb⟩
  have hpar : B.leviInParabolic F ((leviConjugation B C (v * b) hw).symm m) =
      pb⁻¹ * B.leviInParabolic F ((leviConjugation B C v hv).symm m) * pb := by
    apply Subtype.ext
    change B.leviEmbedding F ((leviConjugation B C (v * b) hw).symm m) =
      (permutation n F b)⁻¹ * B.leviEmbedding F ((leviConjugation B C v hv).symm m) *
        permutation n F b
    rw [leviConjugation_symm_embedding, leviConjugation_symm_embedding]
    simp only [map_mul, mul_inv_rev, mul_assoc]
  have h := congrArg (B.leviProjection F) hpar
  rw [BlockShape.leviProjection_section] at h
  rw [h, map_mul, map_mul, map_inv, BlockShape.leviProjection_section]
  rfl

/-- Transport along `v * b`, with `b` in the source block-Weyl group, is
equivalent to transport along `v`; the equivalence is the action of the
source Levi element attached to `b`. -/
def transportBlockWeylEquiv {v b : Equiv.Perm (Fin n)}
    (hb : b ∈ blockWeyl B) (hv : ConjugatesLevi (F := F) B C v)
    (hw : ConjugatesLevi (F := F) B C (v * b))
    (ρ : Representation ℂ (B.Levi F) V) :
    (transport B C (v * b) hw ρ).Equiv (transport B C v hv ρ) :=
  Representation.Equiv.mk
    (LinearEquiv.ofLinearMap (ρ (blockWeylLeviElement B hb))
      (ρ (blockWeylLeviElement B hb)⁻¹)
      (LinearMap.ext fun x => ρ.self_inv_apply _ x)
      (LinearMap.ext fun x => ρ.inv_self_apply _ x))
    (by
      intro m
      apply LinearMap.ext
      intro x
      change ρ (blockWeylLeviElement B hb)
          (ρ ((leviConjugation B C (v * b) hw).symm m) x) =
        ρ ((leviConjugation B C v hv).symm m) (ρ (blockWeylLeviElement B hb) x)
      rw [leviConjugation_symm_mul_blockWeyl B C hb hv hw, map_mul, map_mul]
      change ρ (blockWeylLeviElement B hb) (ρ (blockWeylLeviElement B hb)⁻¹
          (ρ ((leviConjugation B C v hv).symm m) (ρ (blockWeylLeviElement B hb) x))) = _
      rw [ρ.self_inv_apply])

/-- If every conjugating permutation lies in the right block-Weyl coset of a
minimal conjugating permutation, association is realized by a minimal one. -/
theorem exists_minimal_transport_equiv
    (hcos : ∀ w : Equiv.Perm (Fin n), ConjugatesLevi (F := F) B C w →
      ∃ v : MinimalConjugatingPermutations (F := F) B C,
        ∃ b : blockWeyl B, w = v.val.val * b.val)
    {ρ : Representation ℂ (B.Levi F) V} {σ : Representation ℂ (C.Levi F) W}
    (h : RepresentationsAssociated (F := F) B C ρ σ) :
    ∃ v : MinimalConjugatingPermutations (F := F) B C,
      Nonempty ((transport B C v.val.val v.property ρ).Equiv σ) := by
  obtain ⟨w, hw, ⟨e⟩⟩ := h
  obtain ⟨v, b, rfl⟩ := hcos w hw
  exact ⟨v, ⟨(transportBlockWeylEquiv B C b.property v.property hw ρ).symm.trans e⟩⟩

/-- Any association is realized by a minimal conjugating permutation. -/
theorem exists_minimal_transport_equiv_of_associated
    {ρ : Representation ℂ (B.Levi F) V} {σ : Representation ℂ (C.Levi F) W}
    (h : RepresentationsAssociated (F := F) B C ρ σ) :
    ∃ v : MinimalConjugatingPermutations (F := F) B C,
      Nonempty ((transport B C v.val.val v.property ρ).Equiv σ) :=
  exists_minimal_transport_equiv B C
    (fun w hw => (minimalConjugatingCosets w hw).exists) h

section Topology

variable [TopologicalSpace F] [IsTopologicalRing F]

/-- A smooth representation of the target Levi with a finite filtration whose
graded pieces are equivalent to Weyl transports of one admissible source
representation is admissible. -/
theorem isAdmissible_of_transportFiltration {A : Rep.{uW} ℂ (C.Levi F)} {r : ℕ}
    (s : ObjectRepFiltration A r) (hA : IsSmooth A.ρ)
    (e : Fin r → ConjugatingPermutations (F := F) B C)
    {ρ : Representation ℂ (B.Levi F) V} (hρ : IsAdmissible ρ)
    (h : ∀ i, Nonempty ((s.gradedRepresentation i).ρ.Equiv
      (transport B C (e i).val (e i).property ρ))) :
    IsAdmissible A.ρ :=
  isAdmissible_of_objectRepFiltration s hA fun i =>
    let ⟨f⟩ := h i
    isAdmissible_of_equiv f.symm (isAdmissible_transport _ _ hρ)

end Topology

end Langlands.CuspidalSupport
