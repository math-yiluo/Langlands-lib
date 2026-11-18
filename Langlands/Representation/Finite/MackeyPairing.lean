import Langlands.Representation.Finite.CharacterTheoryProof
import Langlands.Representation.Finite.InducedCharacterProof
import Langlands.Representation.Geometric.ClosedSubgroupDefinitions
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Tactic.Group

/-! # Finite-group Mackey pairing for complex representations -/

noncomputable section

open Module Representation

namespace Langlands.FiniteRep

open Geometric

variable {G : Type*} [Group G]

section Reciprocity

variable [Fintype G]

open Classical in
/-- Frobenius reciprocity for the dimension of the intertwiner space of an induced source. -/
theorem finrank_intertwiningMap_induceRep_left (Q : Subgroup G) (V : FDRep ℂ Q)
    {A : Type*} [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
    (ρ : Representation ℂ G A) :
    finrank ℂ (IntertwiningMap (induceRep Q V).ρ ρ) =
      finrank ℂ (IntertwiningMap V.ρ (ρ.comp Q.subtype)) := by
  let : Fintype Q := inferInstanceAs (Fintype {g : G // g ∈ (Q : Set G)})
  apply Nat.cast_injective (R := ℂ)
  rw [← FiniteCharacter.card_inv_mul_sum_eq_finrank, ← FiniteCharacter.card_inv_mul_sum_eq_finrank]
  have hInd := InducedCharacter.inducedCharacterFormula (G := G)
  unfold FiniteInducedCharacterFormulaStatement at hInd
  let f (x g : G) : ℂ :=
    (if h : x⁻¹ * g⁻¹ * x ∈ Q then V.character ⟨x⁻¹ * g⁻¹ * x, h⟩ else 0) * ρ.character g
  let c : ℂ := ∑ q : Q, V.character q⁻¹ * ρ.character (q : G)
  have hx (x : G) : (∑ g : G, f x g) = c := by
    rw [← (MulAut.conj x).toEquiv.sum_comp (f x)]
    have h (g : G) : x⁻¹ * (x * g * x⁻¹)⁻¹ * x = g⁻¹ := by group
    change (∑ g : G, f x (x * g * x⁻¹)) = ∑ q : Q, V.character q⁻¹ * ρ.character (q : G)
    refine Finset.sum_congr_set (Q : Set G) (fun g => f x (x * g * x⁻¹))
      (fun q : Q => V.character q⁻¹ * ρ.character (q : G)) (fun g hg => ?_) (fun g hg => ?_)
    · simp only [f, h, dite_eq_left (Q.inv_mem hg), Representation.char_conj]
      rfl
    · simp only [f, h, dite_eq_right (show g⁻¹ ∉ Q from fun h' => hg (Q.inv_mem_iff.mp h')),
        zero_mul]
  change (Fintype.card G : ℂ)⁻¹ *
    ∑ g : G, (induceRep Q V).character g⁻¹ * ρ.character g = (Fintype.card Q : ℂ)⁻¹ * c
  simp_rw [hInd Q V]
  change (Fintype.card G : ℂ)⁻¹ * ∑ g : G,
    ((Nat.card Q : ℂ)⁻¹ * ∑ x : G,
      if h : x⁻¹ * g⁻¹ * x ∈ Q then V.character ⟨x⁻¹ * g⁻¹ * x, h⟩ else 0) *
        ρ.character g = (Fintype.card Q : ℂ)⁻¹ * c
  calc
    _ = (Fintype.card G : ℂ)⁻¹ * ((Nat.card Q : ℂ)⁻¹ * ∑ g : G, ∑ x : G, f x g) := by
      simp only [f, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    _ = _ := by
      rw [Finset.sum_comm, Finset.sum_congr rfl (fun x _ => hx x)]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
      have hg : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      field_simp

end Reciprocity

section Orbits

variable (P Q : Subgroup G) (V : FDRep ℂ Q) (W : FDRep ℂ P)

/-- The space of intertwiners for two inducing representations at one double coset. -/
abbrev MackeyIntertwining (w : G) :=
  IntertwiningMap (V.ρ.comp (orbitStabilizer P Q w).subtype)
    (W.ρ.comp (stabilizerToInducing P Q w))

/-- The contribution of one `Q \ G / P` representative to the finite Mackey pairing. -/
def mackeyTerm (w : G) : ℕ := finrank ℂ (MackeyIntertwining P Q V W w)

private abbrev RestrictedCoindHom :=
  IntertwiningMap V.ρ ((Representation.coind P.subtype W.ρ).comp Q.subtype)

private lemma restrictedCoind_intertwines (F : RestrictedCoindHom P Q V W) (q : Q) (v : V) :
    F (V.ρ q v) = Representation.coind P.subtype W.ρ q.val (F v) :=
  IntertwiningMap.isIntertwining V.ρ ((Representation.coind P.subtype W.ρ).comp Q.subtype) F q v

private def mackeyEvaluate (F : RestrictedCoindHom P Q V W) (w : G) :
    MackeyIntertwining P Q V W w where
  toLinearMap := LinearMap.proj w⁻¹ ∘ₗ (Representation.coindV P.subtype W.ρ).subtype ∘ₗ F.toLinearMap
  isIntertwining' q := by
    ext v
    change (F (V.ρ q.val v)).val w⁻¹ = W.ρ (stabilizerToInducing P Q w q) ((F v).val w⁻¹)
    have h := (F v).property (stabilizerToInducing P Q w q) w⁻¹
    rw [restrictedCoind_intertwines P Q V W F q.val]
    change (F v).val (w⁻¹ * q.val.val) = _
    simpa only [Subgroup.subtype_apply, stabilizerToInducing_apply, mul_assoc,
      mul_inv_cancel, mul_one] using h

private lemma mackeyEvaluate_apply (F : RestrictedCoindHom P Q V W) (w : G) (v : V) :
    mackeyEvaluate P Q V W F w v = (F v).val w⁻¹ := rfl

variable {ι : Type*} (r : ι → G) (hr : Function.Bijective (fun i => DoubleCoset.mk Q P (r i)))

private structure MackeyFactorization (x : G) where
  index : ι
  left : P
  right : Q
  eq_mul : x = left.val * (r index)⁻¹ * right.val

private def mackeyFactorization (x : G) : MackeyFactorization P Q r x := by
  apply Classical.choice
  obtain ⟨i, hi⟩ := hr.2 (DoubleCoset.mk Q P x⁻¹)
  obtain ⟨q, hq, p, hp, hx⟩ := DoubleCoset.eq.mp hi
  exact ⟨⟨i, ⟨p⁻¹, P.inv_mem hp⟩, ⟨q⁻¹, Q.inv_mem hq⟩, by
    simpa only [inv_inv, mul_inv_rev, mul_assoc] using congrArg Inv.inv hx⟩⟩

private lemma mackeyFactorization_class {i : ι} (p : P) (q : Q) :
    DoubleCoset.mk Q P ((p.val * (r i)⁻¹ * q.val)⁻¹) = DoubleCoset.mk Q P (r i) :=
  (DoubleCoset.eq.mpr ⟨q.val⁻¹, Q.inv_mem q.property, p.val⁻¹, P.inv_mem p.property,
    by simp [mul_inv_rev, mul_assoc]⟩).symm

include hr in
private lemma mackeyExtend_value_eq (L : ∀ i, MackeyIntertwining P Q V W (r i)) (v : V)
    {i j : ι} (p p' : P) (q q' : Q)
    (h : p.val * (r i)⁻¹ * q.val = p'.val * (r j)⁻¹ * q'.val) :
    W.ρ p (L i (V.ρ q v)) = W.ρ p' (L j (V.ρ q' v)) := by
  have hij : i = j := hr.1 ((mackeyFactorization_class P Q r p q).symm.trans
    ((congrArg (fun x : G => DoubleCoset.mk Q P x⁻¹) h).trans
      (mackeyFactorization_class P Q r p' q')))
  subst j
  have hc : (r i)⁻¹ * (q * q'⁻¹).val * r i = (p⁻¹ * p').val := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc
      _ = p.val⁻¹ * (p.val * (r i)⁻¹ * q.val) * q'.val⁻¹ * r i := by group
      _ = _ := by rw [h]; group
  let s : orbitStabilizer P Q (r i) := ⟨q * q'⁻¹, by
    change (r i)⁻¹ * (q * q'⁻¹).val * (r i)⁻¹⁻¹ ∈ P
    rw [inv_inv, hc]
    exact (p⁻¹ * p').property⟩
  have hs : stabilizerToInducing P Q (r i) s = p⁻¹ * p' := by
    apply Subtype.ext
    rw [stabilizerToInducing_apply]
    exact hc
  have hv : V.ρ q v = V.ρ s.val (V.ρ q' v) := by
    rw [← LinearMap.comp_apply, ← Module.End.mul_eq_comp, ← map_mul]
    simp [s]
  have hw : W.ρ p ∘ₗ W.ρ (p⁻¹ * p') = W.ρ p' := by
    rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel_left]
  rw [hv]
  have hL := IntertwiningMap.isIntertwining (V.ρ.comp (orbitStabilizer P Q (r i)).subtype)
    (W.ρ.comp (stabilizerToInducing P Q (r i))) (L i) s (V.ρ q' v)
  change L i (V.ρ s.val (V.ρ q' v)) = W.ρ (stabilizerToInducing P Q (r i) s) (L i (V.ρ q' v)) at hL
  rw [hL, hs, ← LinearMap.comp_apply, hw]

private def mackeyExtend (L : ∀ i, MackeyIntertwining P Q V W (r i)) :
    RestrictedCoindHom P Q V W := by
  let C := mackeyFactorization P Q r hr
  let f (v : V) (x : G) := W.ρ (C x).left (L (C x).index (V.ρ (C x).right v))
  have hf (v : V) (x : G) (i : ι) (p : P) (q : Q) (h : x = p.val * (r i)⁻¹ * q.val) :
      f v x = W.ρ p (L i (V.ρ q v)) :=
    mackeyExtend_value_eq P Q V W r hr L v _ _ _ _ ((C x).eq_mul.symm.trans h)
  refine {
    toLinearMap := { toFun := fun v => ⟨f v, ?_⟩, map_add' := ?_, map_smul' := ?_ }
    isIntertwining' := ?_ }
  · intro p x
    change f v (p.val * x) = W.ρ p (f v x)
    rw [hf v (p.val * x) (C x).index (p * (C x).left) (C x).right]
    · simp [f, Module.End.mul_apply]
    · have h := congrArg (fun y => p.val * y) (C x).eq_mul
      simpa only [Subgroup.coe_mul, mul_assoc] using h
  · intro v v'
    apply Subtype.ext
    funext x
    change f (v + v') x = f v x + f v' x
    simp [f]
  · intro a v
    apply Subtype.ext
    funext x
    change f (a • v) x = a • f v x
    simp [f]
  · intro q
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext x
    change f (V.ρ q v) x = f v (x * q.val)
    rw [hf v (x * q.val) (C x).index (C x).left ((C x).right * q)]
    · simp [f, Module.End.mul_apply]
    · have h := congrArg (fun y => y * q.val) (C x).eq_mul
      simpa only [Subgroup.coe_mul, mul_assoc] using h

private lemma mackeyExtend_apply (L : ∀ i, MackeyIntertwining P Q V W (r i)) (v : V)
    (i : ι) (p : P) (q : Q) :
    (mackeyExtend P Q V W r hr L v).val (p.val * (r i)⁻¹ * q.val) =
      W.ρ p (L i (V.ρ q v)) := by
  let x := p.val * (r i)⁻¹ * q.val
  let C := mackeyFactorization P Q r hr x
  exact mackeyExtend_value_eq P Q V W r hr L v _ _ _ _ C.eq_mul.symm

/-- Restriction of a coinduced representation, tested against `V`, decomposes by double cosets.
The coordinates are evaluations at the inverses of the representatives. -/
def mackeyIntertwiningEquiv :
    IntertwiningMap V.ρ ((Representation.coind P.subtype W.ρ).comp Q.subtype) ≃ₗ[ℂ]
      (∀ i, MackeyIntertwining P Q V W (r i)) where
  toFun F i := mackeyEvaluate P Q V W F (r i)
  invFun := mackeyExtend P Q V W r hr
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv F := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext x
    change (mackeyExtend P Q V W r hr (fun i => mackeyEvaluate P Q V W F (r i)) v).val x =
      (F v).val x
    let C := mackeyFactorization P Q r hr x
    rw [C.eq_mul, mackeyExtend_apply, mackeyEvaluate_apply]
    rw [restrictedCoind_intertwines P Q V W F C.right]
    change W.ρ C.left ((F v).val ((r C.index)⁻¹ * C.right.val)) = _
    rw [mul_assoc]
    exact ((F v).property C.left ((r C.index)⁻¹ * C.right.val)).symm
  right_inv L := by
    funext i
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    change mackeyEvaluate P Q V W (mackeyExtend P Q V W r hr L) (r i) v = L i v
    rw [mackeyEvaluate_apply]
    simpa using mackeyExtend_apply P Q V W r hr L v i 1 1

include hr in
/-- For finite `G`, the intertwining dimension between two induced representations is the sum
of the dimensions for the corresponding intersections over `Q \ G / P`. -/
theorem finrank_intertwiningMap_induceRep [Fintype G] [Fintype ι] :
    finrank ℂ (IntertwiningMap (induceRep Q V).ρ (induceRep P W).ρ) =
      ∑ i, mackeyTerm P Q V W (r i) := by
  rw [finrank_intertwiningMap_induceRep_left]
  let : Fintype Q := Fintype.ofFinite Q
  have hChar := Representation.char_iso ((induceRepEquiv P W).symm.trans (indCoindEquiv P W))
  have h : finrank ℂ (IntertwiningMap V.ρ ((induceRep P W).ρ.comp Q.subtype)) =
      finrank ℂ (RestrictedCoindHom P Q V W) := by
    apply Nat.cast_injective (R := ℂ)
    rw [← FiniteCharacter.card_inv_mul_sum_eq_finrank, ← FiniteCharacter.card_inv_mul_sum_eq_finrank]
    have hc (q : Q) : Representation.character ((induceRep P W).ρ.comp Q.subtype) q =
        Representation.character ((Representation.coind P.subtype W.ρ).comp Q.subtype) q :=
      congrFun hChar q.val
    simp_rw [hc]
  rw [h, (mackeyIntertwiningEquiv P Q V W r hr).finrank_eq, Module.finrank_pi_fintype]
  rfl

end Orbits

end Langlands.FiniteRep
