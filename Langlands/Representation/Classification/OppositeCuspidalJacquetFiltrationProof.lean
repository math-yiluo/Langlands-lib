import Langlands.Representation.Geometric.CoarseLeviReversal
import Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationStatement
import Langlands.Representation.Induction.OppositeProductReversalProof
import Langlands.Representation.CuspidalSupport.MinimalWeylTransportProof
import Langlands.Representation.Filtration.ObjectTransport
import Langlands.Representation.Tensor.ProductFiltration

/-!
# Opposite associated Jacquet filtration from the upper theorem

Conjugation by the block-reversal matrix identifies the opposite Jacquet module along `C`
with the upper Jacquet module along `C.reverse`, pulled back along the reversed-label Levi
isomorphism. Left multiplication by the reversal permutation identifies the two sets of
minimal whole-Levi conjugating permutations.
-/

noncomputable section

namespace Langlands.OppositeCuspidalJacquetFiltration

open GeneralLinear Geometric CuspidalSupport
open scoped NNReal

universe uF uV uW

section Permutations

variable {F : Type uF} [Field F] {n : ℕ} {B C : BlockShape n}

/-- The reversal permutation conjugates the reversed Levi onto the original Levi. -/
theorem conjugatesLevi_reverse (C : BlockShape n) :
    ConjugatesLevi (F := F) C.reverse C C.reversePermutation := by
  apply Subgroup.ext
  intro g
  constructor
  · rintro ⟨_, ⟨m', rfl⟩, rfl⟩
    refine ⟨(leviReverseEquiv C).symm m', ?_⟩
    change C.leviEmbedding F ((leviReverseEquiv C).symm m') =
      C.reverseMatrix F * C.reverse.leviEmbedding F m' * (C.reverseMatrix F)⁻¹
    rw [← reverseMatrix_mul_leviEmbedding C, MulEquiv.apply_symm_apply]
  · rintro ⟨m, rfl⟩
    refine ⟨C.reverse.leviEmbedding F (leviReverseEquiv C m), ⟨_, rfl⟩, ?_⟩
    exact reverseMatrix_mul_leviEmbedding C m

/-- Inside one reversed block, the reversal permutation preserves order. -/
theorem reversePermutation_lt_of_blockIndex_eq (C : BlockShape n) {x y : Fin n}
    (hxy : blockIndex C.reverse x = blockIndex C.reverse y) (hlt : x < y) :
    C.reversePermutation x < C.reversePermutation y := by
  obtain ⟨⟨i, a⟩, rfl⟩ := C.reverse.indexEquiv.surjective x
  change blockIndex C.reverse (C.reverse.index i a) = _ at hxy
  rw [blockIndex_index C.reverse i a] at hxy
  obtain ⟨b, rfl⟩ := exists_index_of_blockIndex_eq C.reverse hxy.symm
  change C.reverse.index i a < C.reverse.index i b at hlt
  change C.reversePermutation (C.reverse.index i a) <
    C.reversePermutation (C.reverse.index i b)
  have ha := C.reversePermutation_index (i : Fin C.length) a
  have hb := C.reversePermutation_index (i : Fin C.length) b
  erw [ha, hb]
  exact index_strictMono C _ ((index_strictMono C.reverse _).lt_iff_lt.mp hlt)

/-- Inside one original block, the inverse reversal permutation preserves order. -/
theorem reversePermutation_symm_index_strictMono (C : BlockShape n) (j : Fin C.length) :
    StrictMono (fun a : Fin (C.size j) => C.reversePermutation.symm (C.index j a)) := by
  obtain ⟨j, rfl⟩ := Fin.rev_surjective j
  intro a b hab
  simp only [C.reversePermutation_symm_index]
  exact index_strictMono C.reverse j hab

/-- Left multiplication by the reversal permutation preserves minimality. -/
theorem isMinimalRepresentative_reverse_mul {v : Equiv.Perm (Fin n)}
    (hmin : IsMinimalRepresentative B C.reverse v)
    (hv : ConjugatesLevi (F := F) B C.reverse v) :
    IsMinimalRepresentative B C (C.reversePermutation * v) := by
  constructor
  · intro i a b hab
    simp only [Equiv.Perm.mul_apply]
    apply reversePermutation_lt_of_blockIndex_eq C
    · rw [blockIndex_eq_iff_of_conjugatesLevi hv, blockIndex_index, blockIndex_index]
    · exact hmin.1 i hab
  · intro j
    obtain ⟨j, rfl⟩ := Fin.rev_surjective j
    intro a b hab
    simp only [Equiv.Perm.mul_def, Equiv.symm_trans_apply, C.reversePermutation_symm_index]
    exact hmin.2 j hab

/-- Left multiplication by the inverse reversal permutation preserves minimality. -/
theorem isMinimalRepresentative_reverse_inv_mul {w : Equiv.Perm (Fin n)}
    (hmin : IsMinimalRepresentative B C w) (hw : ConjugatesLevi (F := F) B C w) :
    IsMinimalRepresentative B C.reverse (C.reversePermutation⁻¹ * w) := by
  constructor
  · intro i a b hab
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.coe_inv]
    rw [apply_index_eq hmin hw i a, apply_index_eq hmin hw i b]
    exact reversePermutation_symm_index_strictMono C _ (Fin.cast_strictMono _ hab)
  · intro j a b hab
    simp only [Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.Perm.inv_def,
      Equiv.symm_symm]
    have ha := C.reversePermutation_index j a
    have hb := C.reversePermutation_index j b
    erw [ha, hb]
    exact hmin.2 j.rev hab

variable (B C) in
/-- Minimal whole-Levi conjugating permutations into `C.reverse` and into `C` correspond by
`v ↦ C.reversePermutation * v`, with inverse `w ↦ C.reversePermutation⁻¹ * w`. -/
def minimalReverseEquiv :
    MinimalConjugatingPermutations (F := F) B C.reverse ≃
      MinimalConjugatingPermutations (F := F) B C where
  toFun v := ⟨⟨C.reversePermutation * v.val.val,
      isMinimalRepresentative_reverse_mul v.val.property v.property⟩,
    conjugatesLevi_mul v.property (conjugatesLevi_reverse C)⟩
  invFun w := ⟨⟨C.reversePermutation⁻¹ * w.val.val,
      isMinimalRepresentative_reverse_inv_mul w.val.property w.property⟩,
    conjugatesLevi_mul w.property (conjugatesLevi_inv (conjugatesLevi_reverse C))⟩
  left_inv _ := Subtype.ext (Subtype.ext (inv_mul_cancel_left _ _))
  right_inv _ := Subtype.ext (Subtype.ext (mul_inv_cancel_left _ _))

@[simp]
theorem minimalReverseEquiv_apply (v : MinimalConjugatingPermutations (F := F) B C.reverse) :
    (minimalReverseEquiv B C v).val.val = C.reversePermutation * v.val.val := rfl

/-- Inverse whole-Levi conjugation along `t * v` is inverse conjugation along `v` after
relabelling the target blocks. -/
theorem leviConjugation_symm_leviReverseEquiv {v : Equiv.Perm (Fin n)}
    (hv : ConjugatesLevi (F := F) B C.reverse v)
    (h : ConjugatesLevi (F := F) B C (C.reversePermutation * v)) (m : C.Levi F) :
    (leviConjugation B C.reverse v hv).symm (leviReverseEquiv C m) =
      (leviConjugation B C (C.reversePermutation * v) h).symm m := by
  apply B.leviEmbedding_injective F
  rw [leviConjugation_symm_embedding, leviConjugation_symm_embedding,
    reverse_leviEmbedding_leviReverseEquiv, map_mul]
  change (permutation n F v)⁻¹ * ((permutation n F C.reversePermutation)⁻¹ *
      C.leviEmbedding F m * permutation n F C.reversePermutation) * permutation n F v = _
  group

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Weyl transport along `t * v` is transport along `v` pulled back by block relabelling. -/
def transportReverseEquiv {v : Equiv.Perm (Fin n)}
    (hv : ConjugatesLevi (F := F) B C.reverse v)
    (h : ConjugatesLevi (F := F) B C (C.reversePermutation * v))
    (ρ : Representation ℂ (B.Levi F) V) :
    Representation.Equiv
      ((transport B C.reverse v hv ρ).comp (leviReverseEquiv C).toMonoidHom)
      (transport B C (C.reversePermutation * v) h ρ) :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ V) (fun m => by
    apply LinearMap.ext
    intro x
    change ρ ((leviConjugation B C.reverse v hv).symm (leviReverseEquiv C m)) x =
      ρ ((leviConjugation B C (C.reversePermutation * v) h).symm m) x
    rw [leviConjugation_symm_leviReverseEquiv hv h m])

end Permutations

section Quotient

variable {R : Type uF} [CommRing R] {n : ℕ} (C : BlockShape n)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear n R) V)

/-- The action of the reversal matrix descends from the reversed upper radical coinvariants
to the original opposite radical coinvariants: `[x] ↦ [π q x]`. -/
def reverseCoinvariantsEquiv :
    Jacquet.Coinvariants π (C.reverse.unipotentSubgroup R) ≃ₗ[ℂ]
      Jacquet.Coinvariants π (C.oppositeUnipotentSubgroup R) := by
  let q := C.reverseMatrix R
  let U := C.reverse.unipotentSubgroup R
  let N := C.oppositeUnipotentSubgroup R
  let f : Jacquet.Coinvariants π U →ₗ[ℂ] Jacquet.Coinvariants π N :=
    Jacquet.lift π U ((Jacquet.mk π N).comp (π q)) (by
      intro u
      apply LinearMap.ext
      intro x
      have hu : q * (u : GeneralLinear n R) * q⁻¹ ∈ N :=
        (C.reverseMatrix_conj_mem_oppositeUnipotentSubgroup_iff R u).mpr u.property
      have h := Jacquet.mk_apply_subgroup π N ⟨_, hu⟩ (π q x)
      change Jacquet.mk π N (π q (π u x)) = Jacquet.mk π N (π q x)
      rw [← h]
      change _ = Jacquet.mk π N (π (q * (u : GeneralLinear n R) * q⁻¹) (π q x))
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        Representation.inv_self_apply])
  let b : Jacquet.Coinvariants π N →ₗ[ℂ] Jacquet.Coinvariants π U :=
    Jacquet.lift π N ((Jacquet.mk π U).comp (π q⁻¹)) (by
      intro u
      apply LinearMap.ext
      intro x
      have hu : q⁻¹ * (u : GeneralLinear n R) * q ∈ U := by
        apply (C.reverseMatrix_conj_mem_oppositeUnipotentSubgroup_iff R _).mp
        change q * (q⁻¹ * (u : GeneralLinear n R) * q) * q⁻¹ ∈ N
        simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using u.property
      have h := Jacquet.mk_apply_subgroup π U ⟨_, hu⟩ (π q⁻¹ x)
      change Jacquet.mk π U (π q⁻¹ (π u x)) = Jacquet.mk π U (π q⁻¹ x)
      rw [← h]
      change _ = Jacquet.mk π U (π (q⁻¹ * (u : GeneralLinear n R) * q) (π q⁻¹ x))
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        Representation.self_inv_apply])
  exact
    { f with
      invFun := b
      left_inv := by
        intro x
        obtain ⟨v, rfl⟩ := Jacquet.mk_surjective π U x
        change Jacquet.mk π U (π q⁻¹ (π q v)) = Jacquet.mk π U v
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      right_inv := by
        intro x
        obtain ⟨v, rfl⟩ := Jacquet.mk_surjective π N x
        change Jacquet.mk π N (π q (π q⁻¹ v)) = Jacquet.mk π N v
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] }

@[simp]
theorem reverseCoinvariantsEquiv_mk (x : V) :
    reverseCoinvariantsEquiv C π (Jacquet.mk π (C.reverse.unipotentSubgroup R) x) =
      Jacquet.mk π (C.oppositeUnipotentSubgroup R) (π (C.reverseMatrix R) x) := rfl

/-- The reversed upper Jacquet carrier is linearly equivalent to the original opposite
coinvariants: `[x] ↦ [π q x]`, through the ambient radical model. -/
def reverseJacquetEquiv :
    C.reverse.JacquetModule π ≃ₗ[ℂ] Jacquet.Coinvariants π (C.oppositeUnipotentSubgroup R) :=
  (C.reverse.jacquetModuleEquiv π).trans (reverseCoinvariantsEquiv C π)

@[simp]
theorem reverseJacquetEquiv_mk (x : V) :
    reverseJacquetEquiv C π (C.reverse.jacquetMk π x) =
      Jacquet.mk π (C.oppositeUnipotentSubgroup R) (π (C.reverseMatrix R) x) := rfl

end Quotient

section Normalized

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}
  (C : BlockShape n)

/-- The opposite normalized Jacquet module along `C` is the upper normalized Jacquet module
along `C.reverse`, pulled back along block relabelling. -/
def oppositeJacquetReverseEquiv (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)) :
    Representation.Equiv
      ((T.normalizedJacquet C.reverse A.ρ).comp (leviReverseEquiv C).toMonoidHom)
      (CuspidalJacquetMultiplicity.oppositeJacquet T C A).ρ :=
  Representation.Equiv.mk (reverseJacquetEquiv C A.ρ) (fun m => by
    apply Representation.Coinvariants.hom_ext
    apply LinearMap.ext
    intro x
    change reverseJacquetEquiv C A.ρ (T.normalizedJacquet C.reverse A.ρ (leviReverseEquiv C m)
        (C.reverse.jacquetMk A.ρ x)) =
      Jacquet.normalizedActionOfModulus A.ρ (C.oppositeUnipotentSubgroup F.Carrier)
        (C.leviSubgroup F.Carrier)
        (C.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier)
        ((T.leviModulus C).comp (C.leviEquiv F.Carrier).symm.toMonoidHom)⁻¹
        (C.leviEquiv F.Carrier m)
        (reverseJacquetEquiv C A.ρ (C.reverse.jacquetMk A.ρ x))
    rw [T.normalizedJacquet_mk, map_smul, reverseJacquetEquiv_mk, reverseJacquetEquiv_mk,
      Jacquet.normalizedActionOfModulus_mk, MonoidHom.inv_apply, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    have hmod : T.leviModulus C.reverse (leviReverseEquiv C m) = (T.leviModulus C m)⁻¹ :=
      T.leviModulus_reverse C m
    rw [hmod]
    congr 1
    change Jacquet.mk A.ρ _ (A.ρ (C.reverseMatrix F.Carrier)
        (A.ρ (C.reverse.leviEmbedding F.Carrier (leviReverseEquiv C m)) x)) =
      Jacquet.mk A.ρ _ (A.ρ (C.leviEmbedding F.Carrier m) (A.ρ (C.reverseMatrix F.Carrier) x))
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
      ← reverseMatrix_mul_leviEmbedding C m, inv_mul_cancel_right])

end Normalized

end Langlands.OppositeCuspidalJacquetFiltration

namespace Langlands

open GeneralLinear Geometric CuspidalSupport OppositeCuspidalJacquetFiltration

universe uF uV

/-- The upper associated Jacquet filtration theorem gives the opposite associated Jacquet
filtration, indexed by the original minimal whole-Levi conjugating permutations. -/
theorem glOppositeCuspidalJacquetFiltrationFromUpper :
    GLOppositeCuspidalJacquetFiltrationFromUpperStatement.{uF, uV} := by
  intro p _ F T n hupper
  let := T.topology
  intro B C ρ hρ hBC
  have hBC' : LevisAssociated (F := F.Carrier) B C.reverse := by
    obtain ⟨⟨w, hw⟩⟩ := hBC
    exact ⟨⟨C.reversePermutation⁻¹ * w,
      conjugatesLevi_mul hw (conjugatesLevi_inv (conjugatesLevi_reverse C))⟩⟩
  obtain ⟨_, r, e, s, hs⟩ := hupper B C.reverse ρ hρ hBC'
  let I := CuspidalJacquetMultiplicity.induced T B (Rep.of ρ.representation)
  let E := oppositeJacquetReverseEquiv T C I
  let θ := (leviReverseEquiv (R := F.Carrier) C).toMonoidHom
  refine ⟨r, e.trans (minimalReverseEquiv B C), LengthTwo.transport E (s.comp θ), fun i => ?_⟩
  obtain ⟨g⟩ := hs i
  exact ⟨((ObjectRepFiltration.equivTransportGradedEquiv (s.comp θ) E i).symm.trans
    (ObjectRepFiltration.compGradedEquiv s θ i)).trans
    ((FiniteTensorFiltration.compCongr g θ).trans (transportReverseEquiv (e i).property _ ρ.representation))⟩

end Langlands
