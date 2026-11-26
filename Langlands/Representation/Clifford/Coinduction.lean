import Langlands.Weil.Representation.InductionSemisimplicityProof
import Langlands.Representation.CyclicRestriction

/-!
# Clifford theory for coinduction from a finite-index subgroup
-/

noncomputable section

namespace Langlands.Clifford

open Representation Langlands.Weil.InductionSemisimplicity
open Langlands.FiniteRepresentation.Induction

universe uG uV uW

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

section ExtendByZero

variable {G : Type uG} [Group G] (H : Subgroup G)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] (θ : Representation ℂ H V)

open Classical in
/-- The equivariant function supported on the subgroup with value `v` at one. -/
def extendByZero : V →ₗ[ℂ] coindV H.subtype θ where
  toFun v := ⟨fun y => if h : y ∈ H then θ ⟨y, h⟩ v else 0, by
    intro s y
    by_cases hy : y ∈ H
    · have hsy : H.subtype s * y ∈ H := H.mul_mem s.2 hy
      dsimp only
      rw [dite_eq_left_of_eq_true (eq_true hsy), dite_eq_left_of_eq_true (eq_true hy),
        ← Module.End.mul_apply, ← map_mul]
      rfl
    · have hsy : H.subtype s * y ∉ H := fun h => hy (by
        simpa using H.mul_mem (H.inv_mem s.2) h)
      dsimp only
      rw [dite_eq_right_of_eq_false (eq_false hsy), dite_eq_right_of_eq_false (eq_false hy),
        map_zero]⟩
  map_add' v w := by
    apply Subtype.ext
    funext y
    by_cases hy : y ∈ H
    · simp only [hy, ↓reduceDIte, map_add, Submodule.coe_add, Pi.add_apply]
    · simp only [hy, ↓reduceDIte, add_zero, Submodule.coe_add, Pi.add_apply]
  map_smul' c v := by
    apply Subtype.ext
    funext y
    by_cases hy : y ∈ H
    · simp only [hy, ↓reduceDIte, map_smul, Submodule.coe_smul, Pi.smul_apply,
        RingHom.id_apply]
    · simp only [hy, ↓reduceDIte, smul_zero, Submodule.coe_smul, Pi.smul_apply,
        RingHom.id_apply]

variable {H θ}

theorem extendByZero_apply_of_mem (v : V) {y : G} (hy : y ∈ H) :
    (extendByZero H θ v).1 y = θ ⟨y, hy⟩ v := by
  classical
  change (if h : y ∈ H then θ ⟨y, h⟩ v else 0) = _
  rw [dite_eq_left_of_eq_true (eq_true hy)]

theorem extendByZero_apply_of_not_mem (v : V) {y : G} (hy : y ∉ H) :
    (extendByZero H θ v).1 y = 0 := by
  classical
  change (if h : y ∈ H then θ ⟨y, h⟩ v else 0) = _
  rw [dite_eq_right_of_eq_false (eq_false hy)]

theorem extendByZero_apply_one (v : V) : (extendByZero H θ v).1 1 = v := by
  rw [extendByZero_apply_of_mem v H.one_mem]
  exact (congrArg (fun T => T v) (map_one θ)).trans rfl

/-- Extension by zero is equivariant for the inducing subgroup. -/
theorem coind_extendByZero (h : H) (v : V) :
    θ.coind H.subtype (h : G) (extendByZero H θ v) = extendByZero H θ (θ h v) := by
  apply Subtype.ext
  funext y
  change (extendByZero H θ v).1 (y * h) = (extendByZero H θ (θ h v)).1 y
  by_cases hy : y ∈ H
  · have hyh : y * h ∈ H := H.mul_mem hy h.2
    rw [extendByZero_apply_of_mem _ hyh, extendByZero_apply_of_mem _ hy,
      ← Module.End.mul_apply, ← map_mul]
    rfl
  · have hyh : y * h ∉ H := fun h' => hy (by simpa using H.mul_mem h' (H.inv_mem h.2))
    rw [extendByZero_apply_of_not_mem _ hyh, extendByZero_apply_of_not_mem _ hy]

/-- Coset decomposition of an equivariant function, for a subgroup of finite index. -/
theorem sum_coind_extendByZero [H.FiniteIndex] (f : coindV H.subtype θ) :
    ∑ q : Cosets H, θ.coind H.subtype (q.out)⁻¹ (extendByZero H θ (f.1 q.out)) = f := by
  classical
  apply Subtype.ext
  funext y
  rw [Submodule.coe_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single (coset H y)]
  · change (extendByZero H θ (f.1 (coset H y).out)).1 (y * ((coset H y).out)⁻¹) = f.1 y
    have hy : y * ((coset H y).out)⁻¹ ∈ H := by
      have := (factor H y).2
      simpa [factor] using this
    rw [extendByZero_apply_of_mem _ hy]
    have h := f.2 ⟨_, hy⟩ (coset H y).out
    simp only [Subgroup.coe_subtype, inv_mul_cancel_right] at h
    exact h.symm
  · intro q _ hq
    change (extendByZero H θ (f.1 q.out)).1 (y * (q.out)⁻¹) = 0
    apply extendByZero_apply_of_not_mem
    intro hmem
    apply hq
    rw [← coset_out H q]
    apply Quotient.sound
    exact QuotientGroup.rightRel_apply.mpr hmem
  · intro h
    exact absurd (Finset.mem_univ _) h

end ExtendByZero

section Clifford

variable {G : Type uG} [Group G] (H N : Subgroup G) [N.Normal] (hNH : N ≤ H)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] (θ : Representation ℂ H V)
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Every intertwiner from a conjugate of the restriction of `θ` to `N` by an element
outside `H` to the restriction of `σ` to `N` vanishes. -/
def ConjugatesDisjoint (σ : Representation ℂ H W) : Prop :=
  ∀ x : G, x ∉ H → ∀ T : IntertwiningMap (θ.comp (conjugateInclusion H N hNH x))
    (σ.comp (Subgroup.inclusion hNH)), T = 0

variable {H N hNH θ}

/-- The restriction of an intertwiner to a subgroup. -/
def restrictIntertwining {G' : Type*} [Group G'] {U : Type*} [AddCommGroup U] [Module ℂ U]
    {ρ : Representation ℂ G U} {ρ' : Representation ℂ G W} (φ : G' →* G)
    (F : IntertwiningMap ρ ρ') : IntertwiningMap (ρ.comp φ) (ρ'.comp φ) where
  toLinearMap := F.toLinearMap
  isIntertwining' g := F.isIntertwining' (φ g)

/-- For `H` of finite index, an intertwiner out of restricted coinduction is determined by its
values on functions supported on `H`, when the conjugates of `θ` are disjoint from the target. -/
theorem intertwining_apply_eq [H.FiniteIndex] {σ : Representation ℂ H W}
    (ψ : IntertwiningMap ((θ.coind H.subtype).comp H.subtype) σ)
    (hd : ConjugatesDisjoint H N hNH θ σ) (f : coindV H.subtype θ) :
    ψ f = ψ (extendByZero H θ (f.1 1)) := by
  classical
  conv_lhs => rw [← sum_coind_extendByZero f]
  rw [map_sum, Finset.sum_eq_single (coset H 1)]
  · have hq : (coset H 1).out ∈ H := by
      have h := Quotient.exact (coset H (1 : G)).out_eq
      have h' := QuotientGroup.rightRel_apply.mp h
      simpa using H.inv_mem h'
    have h1 := coind_extendByZero (θ := θ) ⟨((coset H 1).out)⁻¹, H.inv_mem hq⟩
      (f.1 (coset H 1).out)
    change ψ (θ.coind H.subtype (((⟨((coset H 1).out)⁻¹, H.inv_mem hq⟩ : H) : G)) _) = _
    rw [h1]
    congr 2
    have h2 := f.2 ⟨((coset H 1).out)⁻¹, H.inv_mem hq⟩ (coset H 1).out
    simp only [Subgroup.coe_subtype, inv_mul_cancel] at h2
    exact h2.symm
  · intro q _ hq
    have hx : q.out ∉ H := by
      intro hmem
      apply hq
      rw [← coset_out H q]
      apply Quotient.sound
      exact QuotientGroup.rightRel_apply.mpr (by simpa using hmem)
    let T : IntertwiningMap (θ.comp (conjugateInclusion H N hNH q.out))
        (σ.comp (Subgroup.inclusion hNH)) :=
      { toLinearMap := ψ.toLinearMap ∘ₗ ((θ.coind H.subtype (q.out)⁻¹) ∘ₗ extendByZero H θ)
        isIntertwining' := fun n => by
          apply LinearMap.ext
          intro v
          change ψ (θ.coind H.subtype (q.out)⁻¹ (extendByZero H θ
              (θ (conjugateInclusion H N hNH q.out n) v))) =
            σ (Subgroup.inclusion hNH n) (ψ (θ.coind H.subtype (q.out)⁻¹ (extendByZero H θ v)))
          rw [← coind_extendByZero, ← Module.End.mul_apply, ← map_mul]
          have hmul : (q.out)⁻¹ * ((conjugateInclusion H N hNH q.out n : H) : G) =
              ((Subgroup.inclusion hNH n : H) : G) * (q.out)⁻¹ := by
            simp [conjugateInclusion, mul_assoc]
          rw [hmul, map_mul, Module.End.mul_apply]
          exact Representation.IntertwiningMap.isIntertwining _ _ ψ (Subgroup.inclusion hNH n) _ }
    have hT := hd q.out hx T
    exact congrArg (fun T' : IntertwiningMap _ _ => T' (f.1 q.out)) hT
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The value at `x` of an equivariant function is the value at one of its translate by `x`. -/
theorem coind_apply_eq_one (f : coindV H.subtype θ) (x : G) :
    f.1 x = (θ.coind H.subtype x f).1 1 := by
  change f.1 x = f.1 (1 * x)
  rw [one_mul]

/-- Evaluation at one after an intertwiner between two coinductions, as an intertwiner of the
restriction to `H`. -/
def evalOneComp {V' : Type*} [AddCommGroup V'] [Module ℂ V'] {θ' : Representation ℂ H V'}
    (F : IntertwiningMap (θ'.coind H.subtype) (θ.coind H.subtype)) :
    IntertwiningMap ((θ'.coind H.subtype).comp H.subtype) θ :=
  (evaluationOne H θ).comp (restrictIntertwining H.subtype F)

theorem evalOneComp_apply {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    {θ' : Representation ℂ H V'}
    (F : IntertwiningMap (θ'.coind H.subtype) (θ.coind H.subtype)) (f : coindV H.subtype θ') :
    evalOneComp F f = (F f).1 1 := rfl

/-- An intertwiner between coinductions is recovered from evaluation at one. -/
theorem intertwining_coind_apply {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    {θ' : Representation ℂ H V'}
    (F : IntertwiningMap (θ'.coind H.subtype) (θ.coind H.subtype)) (f : coindV H.subtype θ')
    (x : G) : (F f).1 x = evalOneComp F (θ'.coind H.subtype x f) := by
  rw [evalOneComp_apply, coind_apply_eq_one, ← Representation.IntertwiningMap.isIntertwining]

/-- Extension by zero as an intertwiner of `H`-representations. -/
def extendByZeroIntertwining : IntertwiningMap θ ((θ.coind H.subtype).comp H.subtype) where
  toLinearMap := extendByZero H θ
  isIntertwining' h := by
    apply LinearMap.ext
    intro v
    exact (coind_extendByZero h v).symm

variable [H.FiniteIndex]

/-- For `H` of finite index and an irreducible finite-dimensional `θ` whose conjugates are
disjoint from it, every endomorphism of the coinduction is scalar. -/
theorem coind_end_scalar [FiniteDimensional ℂ V] (hθ : θ.IsIrreducible)
    (hd : ConjugatesDisjoint H N hNH θ θ)
    (E : IntertwiningMap (θ.coind H.subtype) (θ.coind H.subtype)) :
    ∃ c : ℂ, E.toLinearMap = c • (1 : Module.End ℂ (coindV H.subtype θ)) := by
  let ψ := evalOneComp E
  obtain ⟨c, hc⟩ := CyclicRestriction.end_eq_smul_one θ hθ (ψ.comp extendByZeroIntertwining)
  refine ⟨c, ?_⟩
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  change (E f).1 x = c • f.1 x
  rw [intertwining_coind_apply, intertwining_apply_eq ψ hd]
  have h := congrArg (fun T : Module.End ℂ V => T ((θ.coind H.subtype x f).1 1)) hc
  change ψ (extendByZero H θ _) = _ at h
  rw [h, LinearMap.smul_apply, Module.End.one_apply, ← coind_apply_eq_one]

omit [H.FiniteIndex] in
theorem extendByZero_injective : Function.Injective (extendByZero H θ) := by
  intro v w h
  have h' := congrArg (fun f : coindV H.subtype θ => f.1 1) h
  simpa only [extendByZero_apply_one] using h'

/-- For `H` of finite index, the coinduction of an irreducible finite-dimensional
representation whose conjugates are disjoint from it is irreducible. -/
theorem coind_isIrreducible [FiniteDimensional ℂ V] [Nontrivial V] (hθ : θ.IsIrreducible)
    (hd : ConjugatesDisjoint H N hNH θ θ) : (θ.coind H.subtype).IsIrreducible := by
  have : Nontrivial (coindV H.subtype θ) := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    refine ⟨⟨extendByZero H θ v, 0, fun h => hv ?_⟩⟩
    exact extendByZero_injective (h.trans (map_zero _).symm)
  have hsemi : θ.IsSemisimpleRepresentation := by
    rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
    have : IsSimpleModule (MonoidAlgebra ℂ H) θ.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule θ).mp hθ
    infer_instance
  exact CyclicRestriction.isIrreducible_of_scalar_ends _ (coind_semisimple H θ hsemi)
    (coind_end_scalar hθ hd)

/-- For `H` of finite index, if the conjugates of the source `θ'` are disjoint from the target
`θ`, a nonzero intertwiner between the coinductions gives a nonzero intertwiner `θ' → θ`. -/
theorem exists_ne_zero_of_coind {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    {θ' : Representation ℂ H V'} (hd : ConjugatesDisjoint H N hNH θ' θ)
    (F : IntertwiningMap (θ'.coind H.subtype) (θ.coind H.subtype)) (hF : F ≠ 0) :
    ∃ T : IntertwiningMap θ' θ, T ≠ 0 := by
  refine ⟨(evalOneComp F).comp extendByZeroIntertwining, fun hT => hF ?_⟩
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  change (F f).1 x = 0
  rw [intertwining_coind_apply, intertwining_apply_eq _ hd]
  have h := congrArg (fun T : IntertwiningMap θ' θ => T ((θ'.coind H.subtype x f).1 1)) hT
  exact h

end Clifford

section Vanishing

variable {G : Type uG} [Group G] {H N : Subgroup G} [N.Normal] {hNH : N ≤ H}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] {θ : Representation ℂ H V}
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- For `H` of finite index, an intertwiner from the restriction of a coinduction to `N`
vanishes if no conjugate
of the restriction of `θ` to `N` maps nontrivially to its target. -/
theorem intertwining_eq_zero [H.FiniteIndex] {σ : Representation ℂ N W}
    (ψ : IntertwiningMap ((θ.coind H.subtype).comp N.subtype) σ)
    (hd : ∀ x : G, ∀ T : IntertwiningMap (θ.comp (conjugateInclusion H N hNH x)) σ, T = 0) :
    ψ = 0 := by
  classical
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  change ψ f = 0
  rw [← sum_coind_extendByZero f, map_sum]
  apply Finset.sum_eq_zero
  intro q _
  let T : IntertwiningMap (θ.comp (conjugateInclusion H N hNH q.out)) σ :=
    { toLinearMap := ψ.toLinearMap ∘ₗ ((θ.coind H.subtype (q.out)⁻¹) ∘ₗ extendByZero H θ)
      isIntertwining' := fun n => by
        apply LinearMap.ext
        intro v
        change ψ (θ.coind H.subtype (q.out)⁻¹ (extendByZero H θ
            (θ (conjugateInclusion H N hNH q.out n) v))) =
          σ n (ψ (θ.coind H.subtype (q.out)⁻¹ (extendByZero H θ v)))
        rw [← coind_extendByZero, ← Module.End.mul_apply, ← map_mul]
        have hmul : (q.out)⁻¹ * ((conjugateInclusion H N hNH q.out n : H) : G) =
            (n : G) * (q.out)⁻¹ := by
          simp [conjugateInclusion, mul_assoc]
        rw [hmul, map_mul, Module.End.mul_apply]
        exact Representation.IntertwiningMap.isIntertwining _ _ ψ n _ }
  exact congrArg (fun T' : IntertwiningMap _ _ => T' (f.1 q.out)) (hd q.out T)

end Vanishing

section Conjugation

variable {G : Type uG} [Group G] {H : Subgroup G}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] (θ : Representation ℂ H V)

/-- An automorphism preserving the inducing subgroup, restricted to it. -/
def restrictAut (α : G ≃* G) (hα : ∀ x, x ∈ H ↔ α x ∈ H) : H →* H where
  toFun h := ⟨α h, (hα h).mp h.2⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp

/-- Coinduction commutes with pulling back along an automorphism preserving the inducing
subgroup: precomposition with the automorphism is an equivalence. -/
def coindCompEquiv (α : G ≃* G) (hα : ∀ x, x ∈ H ↔ α x ∈ H) :
    Representation.Equiv ((θ.coind H.subtype).comp α.toMonoidHom)
      (Representation.coind H.subtype (θ.comp (restrictAut α hα))) where
  toFun f := ⟨fun x => f.1 (α x), by
    intro s x
    change f.1 (α (s * x)) = θ (restrictAut α hα s) (f.1 (α x))
    rw [map_mul]
    exact f.2 (restrictAut α hα s) (α x)⟩
  invFun f := ⟨fun x => f.1 (α.symm x), by
    intro s x
    have hs : α.symm s ∈ H := (hα _).mpr (by simp)
    have h := f.2 ⟨α.symm s, hs⟩ (α.symm x)
    change f.1 (α.symm (s * x)) = θ s (f.1 (α.symm x))
    rw [map_mul]
    convert h using 2
    · rfl
    · change θ s = θ (restrictAut α hα ⟨α.symm s, hs⟩)
      congr 1
      apply Subtype.ext
      simp [restrictAut]⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    simp
  right_inv f := by
    apply Subtype.ext
    funext x
    simp
  map_add' f f' := rfl
  map_smul' a f := rfl
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext x
    change f.1 (α x * α g) = f.1 (α (x * g))
    rw [map_mul]

/-- Coinduction of an equivalence. -/
def coindEquivOfEquiv {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    {θ' : Representation ℂ H V'} (e : θ.Equiv θ') :
    (θ.coind H.subtype).Equiv (θ'.coind H.subtype) where
  toFun f := ⟨fun x => e (f.1 x), by
    intro s x
    change e (f.1 (H.subtype s * x)) = θ' s (e (f.1 x))
    rw [f.2 s x]
    exact Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap s _⟩
  invFun f := ⟨fun x => e.symm (f.1 x), by
    intro s x
    change e.symm (f.1 (H.subtype s * x)) = θ s (e.symm (f.1 x))
    rw [f.2 s x]
    exact Representation.IntertwiningMap.isIntertwining _ _ e.symm.toIntertwiningMap s _⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    simp
  right_inv f := by
    apply Subtype.ext
    funext x
    simp
  map_add' f f' := by
    apply Subtype.ext
    funext x
    simp
  map_smul' a f := by
    apply Subtype.ext
    funext x
    simp
  isIntertwining' g := rfl

end Conjugation

section Reciprocity

variable {G : Type uG} [Group G] (H : Subgroup G)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] {θ : Representation ℂ H V}
variable {W : Type uW} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W)

/-- Frobenius reciprocity into coinduction. -/
def coindLift (P : IntertwiningMap (σ.comp H.subtype) θ) :
    IntertwiningMap σ (θ.coind H.subtype) where
  toFun v := ⟨fun x => P (σ x v), by
    intro s x
    change P (σ (s * x) v) = θ s (P (σ x v))
    rw [map_mul, Module.End.mul_apply]
    exact Representation.IntertwiningMap.isIntertwining _ _ P s _⟩
  map_add' v w := by
    apply Subtype.ext
    funext x
    simp
  map_smul' c v := by
    apply Subtype.ext
    funext x
    simp
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext x
    change P (σ x (σ g v)) = P (σ (x * g) v)
    rw [map_mul, Module.End.mul_apply]

variable {σ}

theorem coindLift_ne_zero {P : IntertwiningMap (σ.comp H.subtype) θ} (hP : P ≠ 0) :
    coindLift H σ P ≠ 0 := by
  intro h
  apply hP
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  have h1 := congrArg (fun F : IntertwiningMap σ (θ.coind H.subtype) => (F v).1 1) h
  change P (σ 1 v) = 0 at h1
  rw [map_one, Module.End.one_apply] at h1
  exact h1

end Reciprocity

end Langlands.Clifford
