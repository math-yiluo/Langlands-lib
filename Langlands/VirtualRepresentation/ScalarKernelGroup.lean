import Langlands.Weil.Representation.Predicates
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Trace

/-!
# A finite group attached to a representation that is scalar on a finite-index subgroup

Let `ρ : S → GL(V)` be a finite-dimensional complex representation which acts by
scalars on a finite-index subgroup `N`. The determinant-one scalar multiples of
the image of `ρ` form a finite subgroup `normalizedImage ρ` of `GL(V)`, and every
`ρ s` is a nonzero scalar multiple of one of its elements.

For a representation `σ` of this finite group on `Y`, the *tautological part*
`tautPart ρ σ` is the subspace on which every scalar element `c • 1` of the
finite group acts by `c`. The group `S` acts on it by `s ↦ z • σ h` whenever
`ρ s = z • h`; this is independent of the choice and defines `scalarLift ρ σ`.
-/

noncomputable section

universe uS uV uY uY'

namespace Langlands.VirtualRepresentation.ScalarKernel

variable {S : Type uS} [Group S] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ S V)

/-- The determinant-one scalar multiples of the image of `ρ`, as a subgroup of
`GL(V)`. -/
def normalizedImage : Subgroup (Module.End ℂ V)ˣ where
  carrier := {h | LinearMap.det (h : Module.End ℂ V) = 1 ∧
    ∃ (s : S) (z : ℂˣ), (h : Module.End ℂ V) = (z : ℂ) • ρ s}
  mul_mem' := by
    rintro a b ⟨ha, s, z, hz⟩ ⟨hb, t, w, hw⟩
    refine ⟨by rw [Units.val_mul, map_mul, ha, hb, one_mul], s * t, z * w, ?_⟩
    rw [Units.val_mul, hz, hw, smul_mul_smul_comm, ← map_mul, Units.val_mul]
  one_mem' := ⟨by simp, 1, 1, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, s, z, hz⟩
    have hinv : ((z⁻¹ : ℂˣ) : ℂ) • ρ s⁻¹ * (a : Module.End ℂ V) = 1 := by
      rw [hz, smul_mul_smul_comm, ← map_mul, inv_mul_cancel, map_one, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, one_smul]
    refine ⟨?_, s⁻¹, z⁻¹, Units.inv_eq_of_mul_eq_one_left hinv⟩
    have h1 := congrArg LinearMap.det a.inv_mul
    rw [map_mul, ha, mul_one, map_one] at h1
    exact h1

/-- The underlying endomorphism of an element of the normalized image. -/
abbrev endOf (h : normalizedImage ρ) : Module.End ℂ V :=
  ((h : (Module.End ℂ V)ˣ) : Module.End ℂ V)

/-- The tautological representation of the normalized image on `V`. -/
def tautological : Representation ℂ (normalizedImage ρ) V :=
  (Units.coeHom (Module.End ℂ V)).comp (normalizedImage ρ).subtype

@[simp]
theorem tautological_apply (h : normalizedImage ρ) : tautological ρ h = endOf ρ h := rfl

/-- Every element of the normalized image is a scalar multiple of some `ρ s`. -/
theorem exists_pre (h : normalizedImage ρ) :
    ∃ (s : S) (c : ℂˣ), ρ s = (c : ℂ) • endOf ρ h := by
  obtain ⟨-, s, z, hz⟩ := h.2
  exact ⟨s, z⁻¹, by rw [endOf, hz, smul_smul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_smul]⟩

/-- A chosen element of `S` over an element of the normalized image. -/
def preElem (h : normalizedImage ρ) : S := (exists_pre ρ h).choose

/-- The scalar relating `ρ (preElem ρ h)` and `h`. -/
def preScalar (h : normalizedImage ρ) : ℂˣ := (exists_pre ρ h).choose_spec.choose

theorem pre_spec (h : normalizedImage ρ) :
    ρ (preElem ρ h) = (preScalar ρ h : ℂ) • endOf ρ h :=
  (exists_pre ρ h).choose_spec.choose_spec

/-- A scalar element of the normalized image is central. -/
theorem commute_of_scalar {h : normalizedImage ρ} {c : ℂ} (hc : endOf ρ h = c • 1)
    (k : normalizedImage ρ) : h * k = k * h := by
  apply Subtype.ext
  apply Units.ext
  change endOf ρ h * endOf ρ k = endOf ρ k * endOf ρ h
  rw [hc, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

/-- If two scalar multiples of elements of the normalized image agree, the
quotient of the elements is scalar. -/
theorem scalar_of_smul_eq {h₁ h₂ : normalizedImage ρ} {c₁ c₂ : ℂˣ}
    (he : (c₁ : ℂ) • endOf ρ h₁ = (c₂ : ℂ) • endOf ρ h₂) :
    endOf ρ (h₁ * h₂⁻¹) = ((c₂ / c₁ : ℂˣ) : ℂ) • 1 := by
  have h1 : endOf ρ h₁ = ((c₂ / c₁ : ℂˣ) : ℂ) • endOf ρ h₂ := by
    rw [Units.val_div_eq_div_val, div_eq_mul_inv, mul_comm, ← smul_smul, ← he, smul_smul,
      inv_mul_cancel₀ c₁.ne_zero, one_smul]
  change endOf ρ h₁ * ((h₂ : (Module.End ℂ V)ˣ)⁻¹ : (Module.End ℂ V)ˣ) = _
  rw [h1, smul_mul_assoc, endOf, Units.mul_inv]

section Nontrivial

variable [Nontrivial V]

omit [Nontrivial V] in
theorem det_ne_zero (s : S) : LinearMap.det (ρ s) ≠ 0 := by
  intro h
  have h1 := congrArg LinearMap.det
    (show ρ s * ρ s⁻¹ = 1 by rw [← map_mul, mul_inv_cancel, map_one])
  rw [map_mul, h, zero_mul, map_one] at h1
  exact zero_ne_one h1

/-- A scalar by which some `ρ s` acts is nonzero. -/
theorem scalar_ne_zero {s : S} {c : ℂ} (hc : ρ s = c • 1) : c ≠ 0 := by
  rintro rfl
  rw [zero_smul] at hc
  have h1 : (1 : Module.End ℂ V) = 0 := by
    rw [← map_one ρ, ← mul_inv_cancel s, map_mul, hc, zero_mul]
  exact one_ne_zero h1

variable [FiniteDimensional ℂ V]

/-- Every `ρ s` is a nonzero scalar multiple of an element of the normalized image. -/
theorem exists_lift (s : S) :
    ∃ (z : ℂˣ) (h : normalizedImage ρ), ρ s = (z : ℂ) • endOf ρ h := by
  have hd : 0 < Module.finrank ℂ V := Module.finrank_pos
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (LinearMap.det (ρ s)) hd
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow hd.ne'] at hw
    exact det_ne_zero ρ s hw.symm
  let z : ℂˣ := Units.mk0 w hw0
  let u : (Module.End ℂ V)ˣ :=
    { val := ((z⁻¹ : ℂˣ) : ℂ) • ρ s
      inv := (z : ℂ) • ρ s⁻¹
      val_inv := by
        rw [smul_mul_smul_comm, ← map_mul, mul_inv_cancel, map_one, ← Units.val_mul,
          inv_mul_cancel, Units.val_one, one_smul]
      inv_val := by
        rw [smul_mul_smul_comm, ← map_mul, inv_mul_cancel, map_one, ← Units.val_mul,
          mul_inv_cancel, Units.val_one, one_smul] }
  have hu : u ∈ normalizedImage ρ := by
    refine ⟨?_, s, z⁻¹, rfl⟩
    change LinearMap.det (((z⁻¹ : ℂˣ) : ℂ) • ρ s) = 1
    rw [LinearMap.det_smul, ← hw, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero _ hw0)]
  refine ⟨z, ⟨u, hu⟩, ?_⟩
  change ρ s = (z : ℂ) • (((z⁻¹ : ℂˣ) : ℂ) • ρ s)
  rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

/-- The chosen scalar in `ρ s = z • h`. -/
def liftScalar (s : S) : ℂˣ := (exists_lift ρ s).choose

/-- The chosen element of the normalized image in `ρ s = z • h`. -/
def liftElem (s : S) : normalizedImage ρ := (exists_lift ρ s).choose_spec.choose

theorem lift_spec (s : S) : ρ s = (liftScalar ρ s : ℂ) • endOf ρ (liftElem ρ s) :=
  (exists_lift ρ s).choose_spec.choose_spec

/-- The normalized image is finite when `ρ` is scalar on a finite-index subgroup. -/
theorem finite_normalizedImage (N : Subgroup S) [N.FiniteIndex]
    (hN : ∀ n ∈ N, ∃ c : ℂ, ρ n = c • 1) : Finite (normalizedImage ρ) := by
  classical
  have hd : 0 < Module.finrank ℂ V := Module.finrank_pos
  let P : S ⧸ N → Polynomial ℂ := fun q =>
    Polynomial.C (LinearMap.det (ρ q.out)) * Polynomial.X ^ Module.finrank ℂ V - 1
  have hP : ∀ q, P q ≠ 0 := by
    intro q hq
    have h0 := congrArg (Polynomial.eval 0) hq
    simp [P, zero_pow hd.ne'] at h0
  let F : Set (Module.End ℂ V) :=
    ⋃ q : S ⧸ N, (fun w : ℂ => w • ρ q.out) '' {w | (P q).IsRoot w}
  have hF : F.Finite :=
    Set.finite_iUnion fun q => (Polynomial.finite_setOfPred_isRoot (hP q)).image _
  have hsub : (normalizedImage ρ : Set (Module.End ℂ V)ˣ) ⊆ Units.val ⁻¹' F := by
    rintro h ⟨hdet, s, z, hz⟩
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N s
    obtain ⟨c, hc⟩ := hN ((n⁻¹ : N) : S) (n⁻¹).2
    have hs' : s = (QuotientGroup.mk s : S ⧸ N).out * ((n⁻¹ : N) : S) := by
      rw [hn, Subgroup.coe_inv, mul_inv_cancel_right]
    have hs : ρ s = c • ρ (QuotientGroup.mk s : S ⧸ N).out := by
      conv_lhs => rw [hs']
      rw [map_mul, hc, mul_smul_comm, mul_one]
    have hval : (h : Module.End ℂ V) =
        ((z : ℂ) * c) • ρ (QuotientGroup.mk s : S ⧸ N).out := by
      rw [hz, hs, smul_smul]
    refine Set.mem_iUnion.mpr ⟨(QuotientGroup.mk s : S ⧸ N), (z : ℂ) * c, ?_, hval.symm⟩
    have h1 := hdet
    rw [hval, LinearMap.det_smul] at h1
    simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, P, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one]
    rw [mul_comm, h1, sub_self]
  exact ((hF.preimage Units.val_injective.injOn).subset hsub).to_subtype

end Nontrivial

section TautPart

variable {Y : Type uY} [AddCommGroup Y] [Module ℂ Y]
  (σ : Representation ℂ (normalizedImage ρ) Y)

/-- The subspace on which every scalar element `c • 1` of the normalized image
acts by the scalar `c`. -/
def tautPart : Submodule ℂ Y where
  carrier := {y | ∀ (h : normalizedImage ρ) (c : ℂ), endOf ρ h = c • 1 → σ h y = c • y}
  add_mem' := by
    intro a b ha hb h c hc
    rw [map_add, ha h c hc, hb h c hc, smul_add]
  zero_mem' := by
    intro h c _
    rw [map_zero, smul_zero]
  smul_mem' := by
    intro r a ha h c hc
    rw [map_smul, ha h c hc, smul_comm]

theorem mem_tautPart {y : Y} :
    y ∈ tautPart ρ σ ↔
      ∀ (h : normalizedImage ρ) (c : ℂ), endOf ρ h = c • 1 → σ h y = c • y :=
  Iff.rfl

theorem tautPart_stable (k : normalizedImage ρ) {y : Y} (hy : y ∈ tautPart ρ σ) :
    σ k y ∈ tautPart ρ σ := by
  intro h c hc
  rw [← Module.End.mul_apply, ← map_mul, commute_of_scalar ρ hc k, map_mul,
    Module.End.mul_apply, hy h c hc, map_smul]

/-- On the tautological part, `c₁ • σ h₁ = c₂ • σ h₂` whenever
`c₁ • h₁ = c₂ • h₂` in `End V`. -/
theorem tautPart_key {y : Y} (hy : y ∈ tautPart ρ σ) {h₁ h₂ : normalizedImage ρ}
    {c₁ c₂ : ℂˣ} (he : (c₁ : ℂ) • endOf ρ h₁ = (c₂ : ℂ) • endOf ρ h₂) :
    (c₁ : ℂ) • σ h₁ y = (c₂ : ℂ) • σ h₂ y := by
  have hk := scalar_of_smul_eq ρ he
  have hσ : σ h₁ y = ((c₂ / c₁ : ℂˣ) : ℂ) • σ h₂ y := by
    calc σ h₁ y = σ ((h₁ * h₂⁻¹) * h₂) y := by rw [inv_mul_cancel_right]
      _ = σ (h₁ * h₂⁻¹) (σ h₂ y) := by rw [map_mul, Module.End.mul_apply]
      _ = _ := tautPart_stable ρ σ h₂ hy _ _ hk
  rw [hσ, smul_smul, Units.val_div_eq_div_val]
  congr 1
  field_simp

/-- The whole space is the tautological part of the tautological representation. -/
theorem tautPart_tautological : tautPart ρ (tautological ρ) = ⊤ := by
  rw [eq_top_iff]
  intro y _ h c hc
  rw [tautological_apply, hc, LinearMap.smul_apply, Module.End.one_apply]

variable [Nontrivial V] [FiniteDimensional ℂ V]

/-- The action of `S` on the tautological part, before bundling. -/
def scalarLiftFun (s : S) : Module.End ℂ (tautPart ρ σ) :=
  (liftScalar ρ s : ℂ) • (σ (liftElem ρ s)).restrict (fun _ hy => tautPart_stable ρ σ _ hy)

theorem scalarLiftFun_coe (s : S) (y : tautPart ρ σ) :
    ((scalarLiftFun ρ σ s y : tautPart ρ σ) : Y) =
      (liftScalar ρ s : ℂ) • σ (liftElem ρ s) y := rfl

/-- The action of `s` is computed by any decomposition `ρ s = c • h`. -/
theorem scalarLiftFun_of_eq {s : S} {c : ℂˣ} {h : normalizedImage ρ}
    (hs : ρ s = (c : ℂ) • endOf ρ h) (y : tautPart ρ σ) :
    ((scalarLiftFun ρ σ s y : tautPart ρ σ) : Y) = (c : ℂ) • σ h y := by
  rw [scalarLiftFun_coe]
  exact tautPart_key ρ σ y.2 (by rw [← lift_spec, hs])

/-- The representation of `S` on the tautological part: `s` acts by `z • σ h`
whenever `ρ s = z • h`. -/
def scalarLift : Representation ℂ S (tautPart ρ σ) where
  toFun := scalarLiftFun ρ σ
  map_one' := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    rw [scalarLiftFun_of_eq ρ σ (c := 1) (h := 1)
      (by rw [map_one, Units.val_one, one_smul]; rfl)]
    simp
  map_mul' s t := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    have hst : ρ (s * t) = ((liftScalar ρ s * liftScalar ρ t : ℂˣ) : ℂ) •
        endOf ρ (liftElem ρ s * liftElem ρ t) := by
      rw [map_mul, lift_spec ρ s, lift_spec ρ t, smul_mul_smul_comm, Units.val_mul]
      rfl
    rw [scalarLiftFun_of_eq ρ σ hst, Module.End.mul_apply, scalarLiftFun_coe,
      scalarLiftFun_coe, map_smul, smul_smul, map_mul, Module.End.mul_apply, Units.val_mul]

theorem scalarLift_of_eq {s : S} {c : ℂˣ} {h : normalizedImage ρ}
    (hs : ρ s = (c : ℂ) • endOf ρ h) (y : tautPart ρ σ) :
    ((scalarLift ρ σ s y : tautPart ρ σ) : Y) = (c : ℂ) • σ h y :=
  scalarLiftFun_of_eq ρ σ hs y

end TautPart

section Functoriality

theorem equiv_apply {G : Type*} [Group G] {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    {Y' : Type*} [AddCommGroup Y'] [Module ℂ Y'] {σ : Representation ℂ G Y}
    {σ' : Representation ℂ G Y'} (e : Representation.Equiv σ σ') (g : G) (v : Y) :
    e (σ g v) = σ' g (e v) :=
  LinearMap.congr_fun (e.isIntertwining' g) v

variable [Nontrivial V] [FiniteDimensional ℂ V] {Y : Type uY} [AddCommGroup Y] [Module ℂ Y]
  {Y' : Type uY'} [AddCommGroup Y'] [Module ℂ Y']
  {σ : Representation ℂ (normalizedImage ρ) Y} {σ' : Representation ℂ (normalizedImage ρ) Y'}

/-- An equivalence of representations of the normalized image restricts to the
tautological parts. -/
def tautPartLinearEquiv (e : Representation.Equiv σ σ') :
    tautPart ρ σ ≃ₗ[ℂ] tautPart ρ σ' where
  toFun y := ⟨e y, by
    intro h c hc
    rw [← equiv_apply e, y.2 h c hc, map_smul]⟩
  invFun y := ⟨e.symm y, by
    intro h c hc
    rw [← equiv_apply e.symm, y.2 h c hc, map_smul]⟩
  left_inv y := Subtype.ext (e.toLinearEquiv.symm_apply_apply y)
  right_inv y := Subtype.ext (e.toLinearEquiv.apply_symm_apply y)
  map_add' _ _ := Subtype.ext (map_add e _ _)
  map_smul' _ _ := Subtype.ext (map_smul e _ _)

/-- Equivalent representations have equivalent scalar lifts. -/
def scalarLiftEquiv (e : Representation.Equiv σ σ') :
    Representation.Equiv (scalarLift ρ σ) (scalarLift ρ σ') :=
  Representation.Equiv.mk (tautPartLinearEquiv ρ e) (by
    intro s
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    change e ((scalarLift ρ σ s y : tautPart ρ σ) : Y) =
      ((scalarLift ρ σ' s ⟨e y, _⟩ : tautPart ρ σ') : Y')
    rw [scalarLift_of_eq ρ σ (lift_spec ρ s), scalarLift_of_eq ρ σ' (lift_spec ρ s), map_smul,
      equiv_apply e])

/-- The tautological part of a product is the product of the tautological parts. -/
def tautPartProdLinearEquiv :
    tautPart ρ (σ.prod σ') ≃ₗ[ℂ] tautPart ρ σ × tautPart ρ σ' where
  toFun y := (⟨(y : Y × Y').1, fun h c hc => congrArg Prod.fst (y.2 h c hc)⟩,
    ⟨(y : Y × Y').2, fun h c hc => congrArg Prod.snd (y.2 h c hc)⟩)
  invFun y := ⟨((y.1 : Y), (y.2 : Y')), fun h c hc =>
    Prod.ext (y.1.2 h c hc) (y.2.2 h c hc)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The scalar lift of a product is the product of the scalar lifts. -/
def scalarLiftProdEquiv :
    Representation.Equiv (scalarLift ρ (σ.prod σ'))
      ((scalarLift ρ σ).prod (scalarLift ρ σ')) :=
  Representation.Equiv.mk (tautPartProdLinearEquiv ρ) (by
    intro s
    apply LinearMap.ext
    intro y
    apply Prod.ext <;> apply Subtype.ext
    · change ((scalarLift ρ (σ.prod σ') s y : tautPart ρ (σ.prod σ')) : Y × Y').1 =
        ((scalarLift ρ σ s _ : tautPart ρ σ) : Y)
      rw [scalarLift_of_eq ρ _ (lift_spec ρ s), scalarLift_of_eq ρ σ (lift_spec ρ s)]
      rfl
    · change ((scalarLift ρ (σ.prod σ') s y : tautPart ρ (σ.prod σ')) : Y × Y').2 =
        ((scalarLift ρ σ' s _ : tautPart ρ σ') : Y')
      rw [scalarLift_of_eq ρ _ (lift_spec ρ s), scalarLift_of_eq ρ σ' (lift_spec ρ s)]
      rfl)

/-- The scalar lift of the tautological representation is `ρ`. -/
def scalarLiftTautologicalEquiv :
    Representation.Equiv (scalarLift ρ (tautological ρ)) ρ :=
  Representation.Equiv.mk
    ((LinearEquiv.ofEq _ _ (tautPart_tautological ρ)).trans (Submodule.topEquiv)) (by
    intro s
    apply LinearMap.ext
    intro y
    change ((scalarLift ρ (tautological ρ) s y : tautPart ρ (tautological ρ)) : V) =
      ρ s (y : V)
    rw [scalarLift_of_eq ρ _ (lift_spec ρ s), lift_spec ρ s, tautological_apply,
      LinearMap.smul_apply])

end Functoriality

end Langlands.VirtualRepresentation.ScalarKernel
