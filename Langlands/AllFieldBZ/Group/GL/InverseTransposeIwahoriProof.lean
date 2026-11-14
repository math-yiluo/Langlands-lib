import Langlands.AllFieldBZ.Group.GL.InverseTransposeIwahoriStatement
import Langlands.AllFieldBZ.Group.GL.ReverseBlocks
import Langlands.Group.GL.InverseTransposeIwahoriProof

/-!
# All-field port of `Langlands.Group.GL.InverseTransposeIwahoriProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.InverseTransposeIwahoriProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
universe u

section Ring
variable {n : ℕ} (B : Langlands.GeneralLinear.BlockShape n) (R : Type u) [CommRing R]

private theorem _root_.Langlands.GeneralLinear.BlockShape.inverseTranspose_upper_to_lower {g : GeneralLinear n R}
    (hg : g ∈ B.unipotentSubgroup R) :
    Langlands.GeneralLinear.inverseTranspose n R g ∈ B.oppositeUnipotentSubgroup R := by
  have hi := (B.mem_unipotentSubgroup_iff R g⁻¹).mp
    ((B.unipotentSubgroup R).inv_mem hg)
  apply (B.mem_oppositeUnipotentSubgroup_iff R _).mpr
  refine ⟨(B.inverseTranspose_mem_oppositeParabolic_iff R g).mpr
    ((B.mem_unipotentSubgroup_iff R g).mp hg).1, ?_⟩
  intro i a b
  simpa only [Langlands.GeneralLinear.inverseTranspose_entry, eq_comm] using hi.2 i b a

private theorem _root_.Langlands.GeneralLinear.BlockShape.inverseTranspose_lower_to_upper {g : GeneralLinear n R}
    (hg : g ∈ B.oppositeUnipotentSubgroup R) :
    Langlands.GeneralLinear.inverseTranspose n R g ∈ B.unipotentSubgroup R := by
  have hi := (B.mem_oppositeUnipotentSubgroup_iff R g⁻¹).mp
    ((B.oppositeUnipotentSubgroup R).inv_mem hg)
  apply (B.mem_unipotentSubgroup_iff R _).mpr
  constructor
  · apply (B.inverseTranspose_mem_oppositeParabolic_iff R _).mp
    simpa only [Langlands.GeneralLinear.inverseTranspose_involutive] using
      ((B.mem_oppositeUnipotentSubgroup_iff R g).mp hg).1
  · intro i a b
    simpa only [Langlands.GeneralLinear.inverseTranspose_entry, eq_comm] using hi.2 i b a

private theorem _root_.Langlands.GeneralLinear.BlockShape.inverseTranspose_leviEmbedding (m : B.Levi R) :
    Langlands.GeneralLinear.inverseTranspose n R (B.leviEmbedding R m) =
      B.leviEmbedding R (fun i => Langlands.GeneralLinear.inverseTranspose (B.size i) R (m i)) := by
  apply Units.ext
  ext x y
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective y
  change Langlands.GeneralLinear.inverseTranspose n R (B.leviEmbedding R m) (B.index i a) (B.index j b) =
    B.leviEmbedding R (fun k => Langlands.GeneralLinear.inverseTranspose (B.size k) R (m k))
      (B.index i a) (B.index j b)
  rw [Langlands.GeneralLinear.inverseTranspose_entry, ← map_inv]
  by_cases hij : i = j
  · subst j
    simp only [leviEmbedding_apply_same, Pi.inv_apply, Langlands.GeneralLinear.inverseTranspose_entry]
  · rw [B.leviEmbedding_apply_ne R _ b a (Ne.symm hij),
      B.leviEmbedding_apply_ne R _ a b hij]

private theorem _root_.Langlands.GeneralLinear.BlockShape.inverseTranspose_levi_mem {g : GeneralLinear n R}
    (hg : g ∈ B.leviSubgroup R) : Langlands.GeneralLinear.inverseTranspose n R g ∈ B.leviSubgroup R := by
  rcases hg with ⟨m, rfl⟩
  exact ⟨_, (B.inverseTranspose_leviEmbedding R m).symm⟩

/-- Internal equivalence induced by inversion followed by inverse transpose. -/
private def _root_.Langlands.GeneralLinear.BlockShape.inverseTransposeInvSubtypeEquiv
    (H H' : Subgroup (GeneralLinear n R))
    (h : ∀ g, Langlands.GeneralLinear.inverseTranspose n R g ∈ H ↔ g ∈ H') : H' ≃ H where
  toFun g := ⟨Langlands.GeneralLinear.inverseTranspose n R (g.val⁻¹), by
    rw [map_inv, H.inv_mem_iff]
    exact (h g.val).mpr g.property⟩
  invFun g := ⟨Langlands.GeneralLinear.inverseTranspose n R (g.val⁻¹), by
    apply (h _).mp
    simpa only [Langlands.GeneralLinear.inverseTranspose_involutive] using H.inv_mem g.property⟩
  left_inv g := by
    apply Subtype.ext
    simp only [map_inv, inv_inv, Langlands.GeneralLinear.inverseTranspose_involutive]
  right_inv g := by
    apply Subtype.ext
    simp only [map_inv, inv_inv, Langlands.GeneralLinear.inverseTranspose_involutive]

private theorem _root_.Langlands.GeneralLinear.BlockShape.inverseTranspose_iwahoriProduct_bijective
    (K : Subgroup (GeneralLinear n R))
    (hK : Function.Bijective (B.iwahoriProduct R K)) :
    Function.Bijective
      (B.iwahoriProduct R (K.comap (Langlands.GeneralLinear.inverseTranspose n R).toMonoidHom)) := by
  let K' := K.comap (Langlands.GeneralLinear.inverseTranspose n R).toMonoidHom
  let q : K' ≃ K := inverseTransposeInvSubtypeEquiv R K K' (fun _ => Iff.rfl)
  let l : B.iwahoriLower R K' ≃ B.iwahoriUpper R K :=
    inverseTransposeInvSubtypeEquiv R (B.iwahoriUpper R K) (B.iwahoriLower R K') (by
      intro g
      change (Langlands.GeneralLinear.inverseTranspose n R g ∈ K ∧ Langlands.GeneralLinear.inverseTranspose n R g ∈ B.unipotentSubgroup R) ↔
        (Langlands.GeneralLinear.inverseTranspose n R g ∈ K ∧ g ∈ B.oppositeUnipotentSubgroup R)
      rw [B.inverseTranspose_mem_unipotentSubgroup_iff])
  let m : B.iwahoriLevi R K' ≃ B.iwahoriLevi R K :=
    inverseTransposeInvSubtypeEquiv R (B.iwahoriLevi R K) (B.iwahoriLevi R K') (by
      intro g
      change (Langlands.GeneralLinear.inverseTranspose n R g ∈ K ∧ Langlands.GeneralLinear.inverseTranspose n R g ∈ B.leviSubgroup R) ↔
        (Langlands.GeneralLinear.inverseTranspose n R g ∈ K ∧ g ∈ B.leviSubgroup R)
      rw [B.inverseTranspose_mem_leviSubgroup_iff])
  let u : B.iwahoriUpper R K' ≃ B.iwahoriLower R K :=
    inverseTransposeInvSubtypeEquiv R (B.iwahoriLower R K) (B.iwahoriUpper R K') (by
      intro g
      change (Langlands.GeneralLinear.inverseTranspose n R g ∈ K ∧
        Langlands.GeneralLinear.inverseTranspose n R g ∈ B.oppositeUnipotentSubgroup R) ↔
        (Langlands.GeneralLinear.inverseTranspose n R g ∈ K ∧ g ∈ B.unipotentSubgroup R)
      rw [B.inverseTranspose_mem_oppositeUnipotentSubgroup_iff])
  let t : (B.iwahoriLower R K' × B.iwahoriLevi R K' × B.iwahoriUpper R K') ≃
      (B.iwahoriLower R K × B.iwahoriLevi R K × B.iwahoriUpper R K) :=
    { toFun := fun x => (u x.2.2, m x.2.1, l x.1)
      invFun := fun y => (l.symm y.2.2, m.symm y.2.1, u.symm y.1)
      left_inv := by intro x; simp
      right_inv := by intro y; simp }
  have comm (x) : B.iwahoriProduct R K (t x) = q (B.iwahoriProduct R K' x) := by
    apply Subtype.ext
    change Langlands.GeneralLinear.inverseTranspose n R (x.2.2.val⁻¹) * Langlands.GeneralLinear.inverseTranspose n R (x.2.1.val⁻¹) *
      Langlands.GeneralLinear.inverseTranspose n R (x.1.val⁻¹) =
      Langlands.GeneralLinear.inverseTranspose n R ((x.1.val * x.2.1.val * x.2.2.val)⁻¹)
    simp only [mul_inv_rev, map_mul, mul_assoc]
  constructor
  · intro x y hxy
    apply t.injective
    apply hK.1
    rw [comm, comm, hxy]
  · intro y
    obtain ⟨x, hx⟩ := hK.2 (q y)
    refine ⟨t.symm x, q.injective ?_⟩
    rw [← comm, t.apply_symm_apply, hx]

end Ring
section Padic
variable {F : LocalFieldPackage.{u}} (T : F.TopologicalData)

/-- Compactness of the actual open comap follows from its defining homeomorphism. -/
theorem _root_.Langlands.GeneralLinear.BlockShape.inverseTranspose_compact_comap_allFieldBZ (n : ℕ) :
    Langlands.GeneralLinear.BlockShape.InverseTransposeCompactComapClause_allFieldBZ T n := by
  let := T.topology
  intro K hK
  exact (T.generalLinearInverseTranspose n).toHomeomorph.isClosedEmbedding.isCompact_preimage hK

/-- Inverse transpose preserves the actual weak-chamber Iwahori factorization. -/
theorem _root_.Langlands.GeneralLinear.BlockShape.inverseTranspose_iwahoriFactorization_allFieldBZ {n : ℕ} (B : Langlands.GeneralLinear.BlockShape n) :
    B.InverseTransposeIwahoriFactorizationClause_allFieldBZ T := by
  let := T.topology
  intro K hK
  refine ⟨B.inverseTranspose_iwahoriProduct_bijective F.Carrier K.toSubgroup hK.1, ?_⟩
  intro a ha
  constructor
  · intro g hg
    have he : Langlands.GeneralLinear.inverseTranspose n F.Carrier g ∈ B.iwahoriLower F.Carrier K.toSubgroup :=
      ⟨hg.1, (B.inverseTranspose_mem_oppositeUnipotentSubgroup_iff F.Carrier g).mpr hg.2⟩
    have hc := (hK.2 a ha).2 _ he
    constructor
    · change Langlands.GeneralLinear.inverseTranspose n F.Carrier
        (B.blockScalar F.Carrier a * g * (B.blockScalar F.Carrier a)⁻¹) ∈ K
      rw [map_mul, map_mul, map_inv, B.inverseTranspose_blockScalar F.Carrier a, inv_inv]
      exact hc.1
    · exact B.blockScalar_conj_mem_unipotentSubgroup F.Carrier a hg.2
  · intro g hg
    have he : Langlands.GeneralLinear.inverseTranspose n F.Carrier g ∈ B.iwahoriUpper F.Carrier K.toSubgroup :=
      ⟨hg.1, (B.inverseTranspose_mem_unipotentSubgroup_iff F.Carrier g).mpr hg.2⟩
    have hc := (hK.2 a ha).1 _ he
    constructor
    · change Langlands.GeneralLinear.inverseTranspose n F.Carrier
        ((B.blockScalar F.Carrier a)⁻¹ * g * B.blockScalar F.Carrier a) ∈ K
      rw [map_mul, map_mul, map_inv, B.inverseTranspose_blockScalar F.Carrier a, inv_inv]
      exact hc.1
    · exact B.blockScalar_inv_conj_mem_oppositeUnipotentSubgroup F.Carrier a hg.2

end Padic
end Langlands.AllFieldBZ.GeneralLinear.BlockShape
