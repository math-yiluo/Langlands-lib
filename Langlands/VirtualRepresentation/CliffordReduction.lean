import Langlands.VirtualRepresentation.ExactInduction
import Langlands.Weil.Representation.SubquotientContinuity
import Langlands.Weil.Representation.InductionContinuity
import Langlands.Group.LieKolchin.CommonEigenvector

/-!
# Clifford reduction to representations that are scalar on a commutative normal subgroup

Let `N` be a commutative normal subgroup of finite index in `G`, and let `A` be a
nonzero finite-dimensional complex representation. The operators of `N` have a
common eigenvector, with eigenvalue function `χ`. Let `S` be the stabilizer of
`χ` under conjugation and `W` the simultaneous eigenspace of `χ`; then `S`
contains `N` and acts on `W`, on which `N` acts by scalars. The map
`Ind_S^G W → A`, `f ↦ ∑_{q ∈ S\G} ρ(q⁻¹) f(q)`, is an injective intertwiner,
because the summands lie in eigenspaces of distinct eigenvalue functions. So the
class of `A` is `[Ind_S^G W]` plus the class of a quotient of smaller dimension.
No semisimplicity is used.
-/

noncomputable section

universe uG uV

namespace Langlands.VirtualRepresentation.Clifford

open FiniteRepresentation

section Algebra

variable {G : Type uG} [Group G] (N : Subgroup G) [hN : N.Normal]

/-- Conjugation of `N` by an element of `G`. -/
def conjN (g : G) (n : N) : N := ⟨g * n * g⁻¹, hN.conj_mem n n.2 g⟩

theorem conjN_coe (g : G) (n : N) : (conjN N g n : G) = g * n * g⁻¹ := rfl

theorem conjN_mul (g h : G) (n : N) : conjN N (g * h) n = conjN N g (conjN N h n) :=
  Subtype.ext (by simp only [conjN_coe, mul_inv_rev, mul_assoc])

theorem conjN_one (n : N) : conjN N 1 n = n :=
  Subtype.ext (by simp only [conjN_coe, one_mul, inv_one, mul_one])

/-- The stabilizer of a function on `N` under conjugation. -/
def weightStabilizer (χ : N → ℂ) : Subgroup G where
  carrier := {g | ∀ n : N, χ (conjN N g n) = χ n}
  one_mem' := fun n => by rw [conjN_one]
  mul_mem' := fun {a b} ha hb n => by rw [conjN_mul, ha, hb]
  inv_mem' := fun {g} hg n => by
    have h := hg (conjN N g⁻¹ n)
    rw [← conjN_mul, mul_inv_cancel, conjN_one] at h
    exact h.symm

theorem le_weightStabilizer (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (χ : N → ℂ) :
    N ≤ weightStabilizer N χ := by
  intro g hg n
  congr 1
  apply Subtype.ext
  rw [conjN_coe, hcomm g hg n n.2, mul_inv_cancel_right]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

/-- The simultaneous eigenspace of `N` with eigenvalue function `χ`. -/
abbrev weightSpace (χ : N → ℂ) : Submodule ℂ V :=
  LieKolchin.weightSpace (ρ.comp N.subtype) χ

omit hN in
theorem mem_weightSpace {χ : N → ℂ} {w : V} :
    w ∈ weightSpace N ρ χ ↔ ∀ n : N, ρ n w = χ n • w :=
  LieKolchin.mem_weightSpace

theorem apply_mem_weightSpace {χ : N → ℂ} {s : G} (hs : s ∈ weightStabilizer N χ) {w : V}
    (hw : w ∈ weightSpace N ρ χ) : ρ s w ∈ weightSpace N ρ χ := by
  rw [mem_weightSpace] at hw ⊢
  intro n
  have hc : (n : G) * s = s * (conjN N s⁻¹ n : G) := by
    rw [conjN_coe, inv_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  have hsn : χ (conjN N s⁻¹ n) = χ n := (weightStabilizer N χ).inv_mem hs n
  rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply, hw, map_smul, hsn]

/-- `ρ(g⁻¹)` carries the eigenspace of `χ` into that of `χ ∘ conj g`. -/
theorem inv_apply_mem_weightSpace {χ : N → ℂ} (g : G) {w : V} (hw : w ∈ weightSpace N ρ χ) :
    ρ g⁻¹ w ∈ weightSpace N ρ (fun n => χ (conjN N g n)) := by
  rw [mem_weightSpace] at hw ⊢
  intro n
  have hc : (n : G) * g⁻¹ = g⁻¹ * (conjN N g n : G) := by
    rw [conjN_coe, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply, hw, map_smul]

/-- The action of the stabilizer on the eigenspace. -/
def weightRep (χ : N → ℂ) : Representation ℂ (weightStabilizer N χ) (weightSpace N ρ χ) where
  toFun s := (ρ s).restrict (fun _ hw => apply_mem_weightSpace N ρ s.2 hw)
  map_one' := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp
  map_mul' s t := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp

theorem weightRep_coe (χ : N → ℂ) (s : weightStabilizer N χ) (w : weightSpace N ρ χ) :
    ((weightRep N ρ χ s w : weightSpace N ρ χ) : V) = ρ s w := rfl

/-- `N` acts on the eigenspace by scalars. -/
theorem weightRep_scalar (χ : N → ℂ) (s : weightStabilizer N χ) (hs : (s : G) ∈ N) :
    weightRep N ρ χ s = χ ⟨s, hs⟩ • 1 := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  rw [weightRep_coe, (mem_weightSpace N ρ).mp w.2 ⟨s, hs⟩]
  rfl

end Algebra

section Cosets

variable {G : Type uG} [Group G] (S : Subgroup G)

theorem coset_out_mul_mul_inv (q : Induction.Cosets S) (g : G) :
    Induction.coset S ((Induction.coset S (q.out * g)).out * g⁻¹) = q := by
  have h1 := Induction.factor_mul_out S (q.out * g)
  have h2 : (Induction.coset S (q.out * g)).out * g⁻¹ =
      ((Induction.factor S (q.out * g))⁻¹ : S) * q.out := by
    rw [eq_inv_mul_of_mul_eq h1, Subgroup.coe_inv, mul_assoc, mul_assoc, mul_inv_cancel,
      mul_one]
  rw [h2, Induction.coset_mul, Induction.coset_out]

/-- Right multiplication by `g` on right cosets. -/
def cosetsMulRight (g : G) : Induction.Cosets S ≃ Induction.Cosets S where
  toFun q := Induction.coset S (q.out * g)
  invFun q := Induction.coset S (q.out * g⁻¹)
  left_inv q := coset_out_mul_mul_inv S q g
  right_inv q := by simpa only [inv_inv] using coset_out_mul_mul_inv S q g⁻¹

end Cosets

section Map

variable {G : Type uG} [Group G] (N : Subgroup G) [N.Normal] {V : Type uV} [AddCommGroup V]
  [Module ℂ V] (ρ : Representation ℂ G V) (χ : N → ℂ) [(weightStabilizer N χ).FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The Frobenius map `f ↦ ∑_{q ∈ S\G} ρ(q⁻¹) f(q)` from the induced representation. -/
def cliffordLinearMap :
    Representation.coindV (weightStabilizer N χ).subtype (weightRep N ρ χ) →ₗ[ℂ] V where
  toFun f := ∑ q : Induction.Cosets (weightStabilizer N χ),
    ρ (q.out)⁻¹ ((f.1 q.out : weightSpace N ρ χ) : V)
  map_add' f f' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← map_add]
    rfl
  map_smul' c f := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← map_smul]
    rfl

theorem cliffordLinearMap_apply
    (f : Representation.coindV (weightStabilizer N χ).subtype (weightRep N ρ χ)) :
    cliffordLinearMap N ρ χ f = ∑ q : Induction.Cosets (weightStabilizer N χ),
      ρ (q.out)⁻¹ ((f.1 q.out : weightSpace N ρ χ) : V) := rfl

theorem cliffordLinearMap_intertwining (g : G)
    (f : Representation.coindV (weightStabilizer N χ).subtype (weightRep N ρ χ)) :
    cliffordLinearMap N ρ χ
        (Representation.coind (weightStabilizer N χ).subtype (weightRep N ρ χ) g f) =
      ρ g (cliffordLinearMap N ρ χ f) := by
  let S := weightStabilizer N χ
  let φ : Induction.Cosets S → V := fun q => ρ (q.out)⁻¹ ((f.1 q.out : weightSpace N ρ χ) : V)
  have hterm : ∀ q : Induction.Cosets S,
      ρ (q.out)⁻¹ ((f.1 (q.out * g) : weightSpace N ρ χ) : V) =
        ρ g (φ (cosetsMulRight S g q)) := by
    intro q
    let x := q.out * g
    have hx : f.1 x = weightRep N ρ χ (Induction.factor S x) (f.1 (Induction.coset S x).out) := by
      have h := f.2 (Induction.factor S x) (Induction.coset S x).out
      rw [Subgroup.coe_subtype, Induction.factor_mul_out] at h
      exact h
    change ρ (q.out)⁻¹ ((f.1 x : weightSpace N ρ χ) : V) =
      ρ g (ρ ((Induction.coset S x).out)⁻¹ ((f.1 (Induction.coset S x).out :
        weightSpace N ρ χ) : V))
    rw [hx, weightRep_coe, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply,
      ← map_mul]
    congr 2
    change (q.out)⁻¹ * ((q.out * g) * (Induction.coset S (q.out * g)).out⁻¹) =
      g * ((Induction.coset S (q.out * g)).out)⁻¹
    group
  rw [cliffordLinearMap_apply, cliffordLinearMap_apply, map_sum]
  change ∑ q : Induction.Cosets S, ρ (q.out)⁻¹ ((f.1 (q.out * g) : weightSpace N ρ χ) : V) = _
  simp_rw [hterm]
  exact Equiv.sum_comp (cosetsMulRight S g) (fun q => ρ g (φ q))

/-- The Frobenius map as an intertwiner from the induced representation. -/
def cliffordMap :
    (Representation.coind (weightStabilizer N χ).subtype (weightRep N ρ χ)).IntertwiningMap ρ where
  toLinearMap := cliffordLinearMap N ρ χ
  isIntertwining' g := LinearMap.ext fun f => cliffordLinearMap_intertwining N ρ χ g f

omit [(weightStabilizer N χ).FiniteIndex] in
/-- Distinct right cosets of the stabilizer give distinct conjugate eigenvalue
functions. -/
theorem conj_weight_injective :
    Function.Injective (fun q : Induction.Cosets (weightStabilizer N χ) =>
      fun n : N => χ (conjN N q.out n)) := by
  intro q₁ q₂ h
  have hmem : q₁.out * (q₂.out)⁻¹ ∈ weightStabilizer N χ := by
    intro m
    have h1 := congrFun h (conjN N (q₂.out)⁻¹ m)
    simp only at h1
    rw [← conjN_mul, ← conjN_mul, mul_inv_cancel, conjN_one] at h1
    exact h1
  have hrel : QuotientGroup.rightRel (weightStabilizer N χ) q₂.out q₁.out :=
    QuotientGroup.rightRel_apply.mpr hmem
  have h2 : (Quotient.mk _ q₂.out : Induction.Cosets (weightStabilizer N χ)) =
      Quotient.mk _ q₁.out := Quotient.sound hrel
  rw [q₁.out_eq, q₂.out_eq] at h2
  exact h2.symm

theorem cliffordMap_injective [FiniteDimensional ℂ V] : Function.Injective (cliffordMap N ρ χ) := by
  let S := weightStabilizer N χ
  change Function.Injective (cliffordLinearMap N ρ χ)
  rw [← LinearMap.ker_eq_bot (f := cliffordLinearMap N ρ χ), LinearMap.ker_eq_bot']
  intro f hf
  rw [cliffordLinearMap_apply] at hf
  have hind := (LieKolchin.iSupIndep_weightSpace (ρ.comp N.subtype)).comp
    (conj_weight_injective N χ)
  have hzero := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp hind Finset.univ
    (fun q : Induction.Cosets S => ρ (q.out)⁻¹ ((f.1 q.out : weightSpace N ρ χ) : V))
    (fun q _ => inv_apply_mem_weightSpace N ρ q.out (f.1 q.out).2) hf
  apply (Induction.coordinates S (FiniteRepresentation.of (weightRep N ρ χ))).injective
  funext q
  have hq := hzero q (Finset.mem_univ q)
  have h2 : ((f.1 q.out : weightSpace N ρ χ) : V) = 0 := by
    have h3 := congrArg (ρ q.out) hq
    rw [map_zero, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply] at h3
    exact h3
  change f.1 q.out = (0 : Representation.coindV S.subtype (weightRep N ρ χ)).1 q.out
  exact Subtype.ext h2

end Map

end Langlands.VirtualRepresentation.Clifford
