import Langlands.LocalFactor.SpectralConductorFunctional

/-!
# The conductor functional on induced character differences

For an intermediate field `L ⊆ M` and continuous characters `χ, χ'` of `W_L`
whose restrictions to inertia factor through `Gal(M/F)`, the conductor
functional of `M` takes the value `[W_F : W_L] |H_0| / |G_0|` times the
difference of the class sums of `χ` and `χ'` over the inertia `H_0` of `M/L`.
This is the degree-zero case of Serre, *Local Fields*, VI §2, Proposition 4,
computed with the Frobenius formula for the trace of an induced representation.
-/

noncomputable section

namespace Langlands.LocalFactor.SpectralConductor

open Module Ramification Ramification.Padic CommonClosure ConductorExponent Weil.Local
open VirtualRepresentation
open scoped BigOperators

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))

/-- The Galois group of `M/F`. -/
abbrev GalM := (absoluteFiniteExtension F M).Carrier ≃ₐ[F.Carrier]
  (absoluteFiniteExtension F M).Carrier

/-- Restriction from the local Weil group to `Gal(M/F)`. -/
def restrictionM : localWeilGroup F →* ((absoluteFiniteExtension F M).Carrier ≃ₐ[F.Carrier]
    (absoluteFiniteExtension F M).Carrier) :=
  (absoluteFiniteRestriction F M).toMonoidHom.comp (localProjection F).toMonoidHom

theorem restrictionM_inertia (w : localInertia F) :
    restrictionM F M w = (weilInertiaRestriction F M w : _) := rfl

theorem restrictionM_inertiaSection (γ : inertiaM F M) :
    restrictionM F M (inertiaSection F M γ) = γ := by
  rw [restrictionM_inertia, weilInertiaRestriction_inertiaSection]

instance inertiaM_normal : (inertiaM F M).Normal := by
  have h := lowerRamificationGroup_normal (dataM F M) F.Carrier 0
  rw [lowerRamificationGroup_zero] at h
  exact h

/-- Conjugation of the inertia group of `M/F` by an element of `Gal(M/F)`. -/
def conjInertia (t : (absoluteFiniteExtension F M).Carrier ≃ₐ[F.Carrier]
    (absoluteFiniteExtension F M).Carrier) : inertiaM F M ≃ inertiaM F M where
  toFun γ := ⟨t * γ * t⁻¹, (inertiaM_normal F M).conj_mem _ γ.2 t⟩
  invFun γ := ⟨t⁻¹ * γ * t, by
    simpa using (inertiaM_normal F M).conj_mem _ γ.2 t⁻¹⟩
  left_inv γ := by ext1; simp [mul_assoc]
  right_inv γ := by ext1; simp [mul_assoc]

theorem galoisLowerCount_conj (b : ℕ)
    (t σ : (absoluteFiniteExtension F M).Carrier ≃ₐ[F.Carrier]
      (absoluteFiniteExtension F M).Carrier) :
    galoisLowerCount (dataM F M) F.Carrier b (t * σ * t⁻¹) =
      galoisLowerCount (dataM F M) F.Carrier b σ := by
  classical
  unfold galoisLowerCount
  congr 1
  refine Finset.filter_congr fun i _ => ?_
  have hn := lowerRamificationGroup_normal (dataM F M) F.Carrier i
  constructor
  · intro h
    simpa [mul_assoc] using hn.conj_mem _ h t⁻¹
  · intro h
    exact hn.conj_mem _ h t

/-- The class sum over inertia is invariant under conjugating the argument. -/
theorem sum_conjInertia (t : (absoluteFiniteExtension F M).Carrier ≃ₐ[F.Carrier]
    (absoluteFiniteExtension F M).Carrier) (Φ : inertiaM F M → ℂ) :
    letI := inertiaFintype F M
    ∑ γ : inertiaM F M, (galoisLowerCount (dataM F M) F.Carrier (lowerBound F M) γ : ℂ) *
        Φ (conjInertia F M t γ) =
      ∑ δ : inertiaM F M, (galoisLowerCount (dataM F M) F.Carrier (lowerBound F M) δ : ℂ) *
        Φ δ := by
  let := inertiaFintype F M
  refine Fintype.sum_equiv (conjInertia F M t) _ _ fun γ => ?_
  congr 2
  exact (galoisLowerCount_conj F M _ t γ).symm

/-- The Galois image of a Weil element, as an automorphism of the closure. -/
def projectionAlgEquiv (w : localWeilGroup F) :
    AlgebraicClosure F.Carrier ≃ₐ[F.Carrier] AlgebraicClosure F.Carrier :=
  localProjection F w

/-- Restriction to `M` evaluates as the original automorphism. -/
theorem restrictionM_apply (w : localWeilGroup F) (y : (absoluteFiniteExtension F M).Carrier) :
    ((restrictionM F M w y : (absoluteFiniteExtension F M).Carrier) :
        AlgebraicClosure F.Carrier) =
      projectionAlgEquiv F w (y : AlgebraicClosure F.Carrier) :=
  (projectionAlgEquiv F w).restrictNormal_commutes M y

/-- The elements of `Gal(M/F)` fixing an intermediate field. -/
def fixingM (L : Extension F) : Subgroup ((absoluteFiniteExtension F M).Carrier ≃ₐ[F.Carrier]
    (absoluteFiniteExtension F M).Carrier) where
  carrier := {σ | ∀ y : (absoluteFiniteExtension F M).Carrier,
    (y : AlgebraicClosure F.Carrier) ∈ L.field → σ y = y}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro σ τ hσ hτ y hy
    change σ (τ y) = y
    rw [hτ y hy, hσ y hy]
  inv_mem' := by
    intro σ hσ y hy
    change σ.symm y = y
    conv_lhs => rw [← hσ y hy]
    exact σ.symm_apply_apply y

/-- A Weil element fixes `L` exactly when its restriction to `M ⊇ L` does. -/
theorem mem_weilSubgroup_iff (L : Extension F) (hLM : L.field ≤ M.toIntermediateField)
    (w : localWeilGroup F) :
    w ∈ weilSubgroup F L ↔ restrictionM F M w ∈ fixingM F M L := by
  have h1 : w ∈ weilSubgroup F L ↔ projectionAlgEquiv F w ∈ L.field.fixingSubgroup := Iff.rfl
  rw [h1, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h y hy
    apply Subtype.ext
    rw [restrictionM_apply]
    exact h _ hy
  · intro h x hx
    have := congrArg (fun y : (absoluteFiniteExtension F M).Carrier =>
      (y : AlgebraicClosure F.Carrier)) (h ⟨x, hLM hx⟩ hx)
    rw [restrictionM_apply] at this
    exact this

section Coset

variable {G : Type*} [Group G] (S : Subgroup G)

/-- A right coset is fixed by right multiplication exactly when the conjugate
of the multiplier by the chosen representative lies in the subgroup. -/
theorem coset_out_mul_eq_iff (q : FiniteRepresentation.Induction.Cosets S) (g : G) :
    FiniteRepresentation.Induction.coset S (q.out * g) = q ↔ q.out * g * q.out⁻¹ ∈ S := by
  conv_lhs => rw [← FiniteRepresentation.Induction.coset_out S q]
  unfold FiniteRepresentation.Induction.coset
  rw [Quotient.eq, QuotientGroup.rightRel_apply, ← inv_mem_iff]
  simp [mul_assoc]

/-- In that case the subgroup factor is that conjugate. -/
theorem factor_out_mul (q : FiniteRepresentation.Induction.Cosets S) (g : G)
    (h : FiniteRepresentation.Induction.coset S (q.out * g) = q) :
    (FiniteRepresentation.Induction.factor S (q.out * g) : G) = q.out * g * q.out⁻¹ := by
  simp [FiniteRepresentation.Induction.factor, h]

end Coset

/-- The trace at the identity of inertia is the virtual degree. -/
theorem inertiaTrace_one (x : Virtual.{uF, uV} F (base F)) :
    inertiaTrace F x 1 = (degree F (base F) x : ℂ) := by
  unfold inertiaTrace
  rw [show baseInclusion F ((1 : localInertia F) : localWeilGroup F) = 1 from by simp]
  exact trace_apply_one _ x

section Generator

variable (L : Extension F) (hLM : L.field ≤ M.toIntermediateField)

/-- A character of `W_L` is presented at `M` when it is trivial on the inertia
elements of `W_L` that act trivially on `M`. -/
def IsPresentedAt (χ : weilSubgroup F L →ₜ* ℂˣ) : Prop :=
  ∀ s : weilSubgroup F L, (s : localWeilGroup F) ∈ localInertia F →
    restrictionM F M s = 1 → χ s = 1

/-- A presented character takes the same value on inertia elements with the
same restriction to `M`. -/
theorem IsPresentedAt.eq {χ : weilSubgroup F L →ₜ* ℂˣ} (hχ : IsPresentedAt F M L χ)
    (s s' : weilSubgroup F L) (hs : (s : localWeilGroup F) ∈ localInertia F)
    (hs' : (s' : localWeilGroup F) ∈ localInertia F)
    (h : restrictionM F M s = restrictionM F M s') : χ s = χ s' := by
  have h1 : χ (s'⁻¹ * s) = 1 := by
    apply hχ
    · exact (localInertia F).mul_mem ((localInertia F).inv_mem hs') hs
    · simp [h]
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm

/-- The section element of an inertia element fixing `L`, as an element of `W_L`. -/
def liftL (δ : inertiaM F M) (hδ : (δ : GalM F M) ∈ fixingM F M L) : weilSubgroup F L :=
  ⟨(inertiaSection F M δ : localWeilGroup F),
    (mem_weilSubgroup_iff F M L hLM _).mpr (by rw [restrictionM_inertiaSection]; exact hδ)⟩

open Classical in
/-- The character difference on the inertia of `M/L`, extended by zero. -/
def differenceFunction (χ χ' : weilSubgroup F L →ₜ* ℂˣ) (δ : inertiaM F M) : ℂ :=
  if hδ : (δ : GalM F M) ∈ fixingM F M L then
    (χ (liftL F M L hLM δ hδ) : ℂ) - χ' (liftL F M L hLM δ hδ)
  else 0

/-- The Weil subgroup of `L`, inside the Weil subgroup of the base. -/
abbrev nestedL :=
  (weilSubgroup F L).subgroupOf (weilSubgroup F (base F))

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The Frobenius formula at an inertia section element: a sum over cosets of the
character difference at the conjugated inertia element. -/
theorem inertiaTrace_induce (h : (base F).field ≤ L.field) (χ χ' : weilSubgroup F L →ₜ* ℂˣ)
    (hχ : IsPresentedAt F M L χ) (hχ' : IsPresentedAt F M L χ') (γ : inertiaM F M) :
    inertiaTrace F (induce F (base F) L h (ExactGrothendieckGroup.characterClass χ -
        ExactGrothendieckGroup.characterClass χ')) (inertiaSection F M γ) =
      ∑ q : FiniteRepresentation.Induction.Cosets (nestedL F L),
        differenceFunction F M L hLM χ χ'
          (conjInertia F M (restrictionM F M (q.out : localWeilGroup F)) γ) := by
  unfold inertiaTrace
  rw [CommonClosure.trace_induce, ExactGrothendieckGroup.frobeniusFunctional_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  set w : weilSubgroup F (base F) := baseInclusion F (inertiaSection F M γ : localWeilGroup F)
  set t := restrictionM F M (q.out : localWeilGroup F)
  have hres : restrictionM F M ((q.out * w * q.out⁻¹ : weilSubgroup F (base F)) :
      localWeilGroup F) = (conjInertia F M t γ : GalM F M) := by
    change restrictionM F M ((q.out : localWeilGroup F) * (inertiaSection F M γ : _) *
      (q.out : localWeilGroup F)⁻¹) = t * γ * t⁻¹
    rw [map_mul, map_mul, map_inv, restrictionM_inertiaSection]
  have hiff : FiniteRepresentation.Induction.coset (nestedL F L) (q.out * w) = q ↔
      (conjInertia F M t γ : GalM F M) ∈ fixingM F M L := by
    rw [coset_out_mul_eq_iff, Subgroup.mem_subgroupOf, mem_weilSubgroup_iff F M L hLM, hres]
  unfold differenceFunction
  by_cases hq : FiniteRepresentation.Induction.coset (nestedL F L) (q.out * w) = q
  · rw [ite_eq_left hq, dite_eq_left (hiff.mp hq)]
    have hfac := factor_out_mul (nestedL F L) q w hq
    simp only [Function.comp_apply, map_sub, Pi.sub_apply,
      ExactGrothendieckGroup.trace_characterClass]
    have hin : ((q.out * w * q.out⁻¹ : weilSubgroup F (base F)) : localWeilGroup F) ∈
        localInertia F := by
      change (q.out : localWeilGroup F) * (inertiaSection F M γ : _) *
        (q.out : localWeilGroup F)⁻¹ ∈ localInertia F
      exact (localInertia_normal F).conj_mem _ (inertiaSection F M γ).2 _
    have hval : ((nestedWeilEquiv F (base F) L h
        (FiniteRepresentation.Induction.factor (nestedL F L) (q.out * w)) :
          weilSubgroup F L) : localWeilGroup F) =
        ((q.out * w * q.out⁻¹ : weilSubgroup F (base F)) : localWeilGroup F) := by
      rw [← hfac]
      rfl
    have hsame (ψ : weilSubgroup F L →ₜ* ℂˣ) (hψ : IsPresentedAt F M L ψ) :
        ψ (nestedWeilEquiv F (base F) L h
          (FiniteRepresentation.Induction.factor (nestedL F L) (q.out * w))) =
        ψ (liftL F M L hLM (conjInertia F M t γ) (hiff.mp hq)) := by
      apply hψ.eq
      · rw [hval]; exact hin
      · exact (inertiaSection F M _).2
      · change restrictionM F M ((nestedWeilEquiv F (base F) L h _ : weilSubgroup F L) :
          localWeilGroup F) = restrictionM F M (inertiaSection F M _ : localWeilGroup F)
        rw [hval, hres, restrictionM_inertiaSection]
    rw [hsame χ hχ, hsame χ' hχ']
  · rw [ite_eq_right hq, dite_eq_right (fun h' => hq (hiff.mpr h'))]

/-- The conductor functional of `M` on an induced character difference. -/
theorem conductorFunctional_induce (h : (base F).field ≤ L.field)
    (χ χ' : weilSubgroup F L →ₜ* ℂˣ)
    (hχ : IsPresentedAt F M L χ) (hχ' : IsPresentedAt F M L χ') :
    letI := inertiaFintype F M
    conductorFunctional.{uF, uV} F M (induce F (base F) L h
        (ExactGrothendieckGroup.characterClass χ - ExactGrothendieckGroup.characterClass χ')) =
      -((Fintype.card (FiniteRepresentation.Induction.Cosets (nestedL F L)) : ℂ) *
        (Nat.card (inertiaM F M) : ℂ)⁻¹ *
        ∑ δ : inertiaM F M, (galoisLowerCount (dataM F M) F.Carrier (lowerBound F M) δ : ℂ) *
          differenceFunction F M L hLM χ χ' δ) := by
  let := inertiaFintype F M
  set y := induce F (base F) L h (ExactGrothendieckGroup.characterClass χ -
    ExactGrothendieckGroup.characterClass χ') with hy
  set Φ := differenceFunction F M L hLM χ χ'
  set m : inertiaM F M → ℂ := fun γ =>
    (galoisLowerCount (dataM F M) F.Carrier (lowerBound F M) γ : ℂ)
  set t : FiniteRepresentation.Induction.Cosets (nestedL F L) → GalM F M :=
    fun q => restrictionM F M (q.out : localWeilGroup F)
  have h1 : inertiaTrace F y 1 = 0 := by
    rw [inertiaTrace_one, hy, degree_induce]
    have hz : degree F L (ExactGrothendieckGroup.characterClass χ -
        ExactGrothendieckGroup.characterClass χ') = 0 := by
      rw [map_sub, ExactGrothendieckGroup.degree_characterClass,
        ExactGrothendieckGroup.degree_characterClass, sub_self]
    rw [hz, mul_zero, Int.cast_zero]
  have hT (γ : inertiaM F M) : inertiaTrace F y (inertiaSection F M γ) =
      ∑ q, Φ (conjInertia F M (t q) γ) :=
    inertiaTrace_induce F M L hLM h χ χ' hχ hχ' γ
  show inertiaClassSum F M (inertiaTrace F y) = _
  unfold inertiaClassSum
  calc (Nat.card (inertiaM F M) : ℂ)⁻¹ * ∑ γ : inertiaM F M,
        m γ * (inertiaTrace F y 1 - inertiaTrace F y (inertiaSection F M γ))
      = -((Nat.card (inertiaM F M) : ℂ)⁻¹ *
          ∑ γ : inertiaM F M, ∑ q, m γ * Φ (conjInertia F M (t q) γ)) := by
        simp only [h1, hT, zero_sub, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum]
    _ = -((Nat.card (inertiaM F M) : ℂ)⁻¹ *
          ∑ q, ∑ γ : inertiaM F M, m γ * Φ (conjInertia F M (t q) γ)) := by
        rw [Finset.sum_comm]
    _ = -((Nat.card (inertiaM F M) : ℂ)⁻¹ *
          ∑ _q : FiniteRepresentation.Induction.Cosets (nestedL F L),
            ∑ δ : inertiaM F M, m δ * Φ δ) := by
        congr 2
        refine Finset.sum_congr rfl fun q _ => ?_
        exact sum_conjInertia F M (t q) Φ
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-- The inertia group of `M/L`, inside `Gal(M/F)`. -/
abbrev inertiaL : Subgroup (GalM F M) := fixingM F M L ⊓ inertiaM F M

open Classical in
/-- The class-function conductor sum of a presented character of `W_L` over the
inertia group of `M/L`. -/
def lClassSum (χ : weilSubgroup F L →ₜ* ℂˣ) : ℂ :=
  letI := inertiaFintype F M
  (Nat.card (inertiaL F M L) : ℂ)⁻¹ * ∑ δ : inertiaM F M,
    if hδ : (δ : GalM F M) ∈ fixingM F M L then
      (galoisLowerCount (dataM F M) F.Carrier (lowerBound F M) δ : ℂ) *
        (1 - χ (liftL F M L hLM δ hδ))
    else 0

instance inertiaL_finite : Finite (inertiaL F M L) := by
  have := automorphismGroup_finite' (E := absoluteFiniteExtension F M) F.Carrier
  infer_instance

theorem sum_differenceFunction (χ χ' : weilSubgroup F L →ₜ* ℂˣ) :
    letI := inertiaFintype F M
    ∑ δ : inertiaM F M, (galoisLowerCount (dataM F M) F.Carrier (lowerBound F M) δ : ℂ) *
        differenceFunction F M L hLM χ χ' δ =
      -((Nat.card (inertiaL F M L) : ℂ) *
        (lClassSum F M L hLM χ - lClassSum F M L hLM χ')) := by
  classical
  let := inertiaFintype F M
  have hcard : (Nat.card (inertiaL F M L) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := inertiaL F M L)).ne'
  unfold lClassSum differenceFunction
  rw [mul_sub, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul, one_mul, neg_sub,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun δ _ => ?_
  split_ifs <;> ring

/-- The induction identity with the class sums of `M/L`. -/
theorem conductorFunctional_induce_eq (h : (base F).field ≤ L.field)
    (χ χ' : weilSubgroup F L →ₜ* ℂˣ)
    (hχ : IsPresentedAt F M L χ) (hχ' : IsPresentedAt F M L χ') :
    conductorFunctional.{uF, uV} F M (induce F (base F) L h
        (ExactGrothendieckGroup.characterClass χ - ExactGrothendieckGroup.characterClass χ')) =
      (Fintype.card (FiniteRepresentation.Induction.Cosets (nestedL F L)) : ℂ) *
        (Nat.card (inertiaL F M L) : ℂ) / (Nat.card (inertiaM F M) : ℂ) *
        (lClassSum F M L hLM χ - lClassSum F M L hLM χ') := by
  rw [conductorFunctional_induce F M L hLM h χ χ' hχ hχ', sum_differenceFunction]
  ring

end Generator

end Langlands.LocalFactor.SpectralConductor
