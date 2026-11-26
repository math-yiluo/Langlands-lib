import Langlands.Weil.Representation.Induction
import Langlands.Weil.Representation.Twist
import Langlands.Weil.Representation.CyclicExtensionTwistStatement
import Langlands.Representation.Filtration.CentralEigenspaceSplitting
import Langlands.VirtualRepresentation.ExactMackey
import Langlands.Weil.Representation.Restriction
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

/-!
# Induction of a character with separated conjugates on a normal subgroup

Let `S` be a finite-index subgroup of `G`, `N ≤ S` a normal subgroup of `G` and `φ` a
character of `S` with values in the units of a field `K`. In the coset coordinates of the
induced representation, `N` acts diagonally, the coordinate at the coset of `x` carrying the
character `n ↦ φ (x n x⁻¹)`. If these characters are pairwise distinct, every invariant
subspace and every commuting endomorphism is determined coordinatewise, and the transitive
action of `G` on the cosets makes the representation irreducible with scalar endomorphisms.
-/

noncomputable section

universe uK uG uI uX uV uW

set_option autoImplicit false

namespace Langlands.FiniteRepresentation

section LinearAlgebra

variable {K : Type uK} [Field K]

private theorem single_mem_of_diagonal_separation
    {ι : Type uI} [Fintype ι] [DecidableEq ι] {X : Type uX}
    (W : Submodule K (ι → K)) (a : X → ι → K)
    (stable : ∀ x v, v ∈ W → (fun i => a x i * v i) ∈ W)
    (separate : ∀ i j, i ≠ j → ∃ x, a x i ≠ a x j)
    (v : ι → K) (hv : v ∈ W) (i : ι) :
    Pi.single i (v i) ∈ W := by
  classical
  have eliminate : ∀ s : Finset ι, i ∉ s →
      ∃ w ∈ W, w i = v i ∧ ∀ j ∈ s, w j = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨v, hv, rfl, by simp⟩
    | @insert j s hjs ih =>
      intro his
      obtain ⟨w, hw, hwi, hws⟩ := ih (fun h => his (Finset.mem_insert_of_mem h))
      obtain ⟨x, hx⟩ := separate i j (by
        intro h
        exact his (by simp [h]))
      let w' : ι → K := (a x i - a x j)⁻¹ •
        ((fun k => a x k * w k) - a x j • w)
      refine ⟨w', W.smul_mem _ (W.sub_mem (stable x w hw) (W.smul_mem _ hw)), ?_, ?_⟩
      · dsimp [w']
        rw [← sub_mul, ← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr hx), one_mul, hwi]
      · intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · simp [w']
        · simp [w', hws k hk]
  obtain ⟨w, hw, hwi, hws⟩ := eliminate (Finset.univ.erase i) (by simp)
  have heq : w = Pi.single i (v i) := by
    funext j
    by_cases h : j = i
    · subst j
      simpa using hwi
    · simp [h, hws j (by simp [h])]
  exact heq ▸ hw

/-- Diagonal coordinates with separated eigenvalue functions and a transitive coordinate
action give an irreducible representation. -/
theorem irreducible_of_diagonal_coordinates
    {G : Type uG} [Group G] {V : Type*} [AddCommGroup V] [Module K V]
    {ι : Type uI} [Fintype ι] [Nonempty ι] {X : Type uX}
    (ρ : Representation K G V) (e : V ≃ₗ[K] (ι → K))
    (b : X → G) (a : X → ι → K)
    (diagonal : ∀ x v i, e (ρ (b x) v) i = a x i * e v i)
    (separate : ∀ i j, i ≠ j → ∃ x, a x i ≠ a x j)
    (move : ∀ i j, ∃ g : G, ∀ v, e (ρ g v) j = e v i) :
    Representation.IsIrreducible ρ := by
  classical
  have hbot : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    let v := e.symm (fun _ => 1)
    have hv : v ∈ (⊥ : Subrepresentation ρ) := h ▸ Set.mem_univ v
    have hv0 : v = 0 := hv
    have := congrArg (fun w => e w (Classical.choice ‹Nonempty ι›)) hv0
    simp [v] at this
  refine { exists_pair_ne := ⟨⊥, ⊤, hbot⟩, eq_bot_or_eq_top := ?_ }
  intro U
  by_cases hU : U = ⊥
  · exact Or.inl hU
  right
  have hU' : U.toSubmodule ≠ ⊥ := fun h => hU
    (Subrepresentation.toSubmodule_injective h)
  obtain ⟨v, hv, hv0⟩ := U.toSubmodule.ne_bot_iff.mp hU'
  have hev : e v ≠ 0 := by simpa using hv0
  obtain ⟨i, hi⟩ : ∃ i, e v i ≠ 0 := by
    by_contra! h
    exact hev (funext h)
  let W := U.toSubmodule.map e.toLinearMap
  have stable : ∀ x w, w ∈ W → (fun j => a x j * w j) ∈ W := by
    intro x w hw
    obtain ⟨z, hz, rfl⟩ := hw
    refine ⟨ρ (b x) z, U.apply_mem_toSubmodule _ hz, ?_⟩
    funext j
    exact diagonal x z j
  have project := single_mem_of_diagonal_separation W a stable separate
  have hsingle : Pi.single i (e v i) ∈ W :=
    project (e v) ⟨v, hv, rfl⟩ i
  have hequiv : ∀ w : ι → K, w ∈ W ↔ e.symm w ∈ U :=
    fun _ => Submodule.mem_map_equiv U.toSubmodule
  have hall : ∀ (j : ι) (c : K), Pi.single j c ∈ W := by
    intro j c
    obtain ⟨g, hg⟩ := move i j
    let z := e.symm (Pi.single i (e v i))
    have hz : z ∈ U := (hequiv _).mp hsingle
    have hgz : e (ρ g z) ∈ W :=
      ⟨ρ g z, U.apply_mem_toSubmodule g hz, rfl⟩
    have hp := project _ hgz j
    have hval : e (ρ g z) j = e v i := by simpa [z] using hg z
    rw [hval] at hp
    have hc := W.smul_mem (c / e v i) hp
    convert hc using 1
    ext k
    by_cases h : k = j
    · subst k
      simp [div_mul_cancel₀ c hi]
    · simp [h]
  apply le_antisymm le_top
  intro z _
  have hez : e z ∈ W := by
    rw [← Finset.univ_sum_single (e z)]
    exact W.sum_mem (fun j _ => hall j (e z j))
  simpa using (hequiv _).mp hez

/-- Diagonal coordinates with separated eigenvalue functions and a transitive coordinate
action make every commuting linear endomorphism a scalar. -/
theorem scalar_of_diagonal_coordinates
    {G : Type uG} [Group G] {V : Type*} [AddCommGroup V] [Module K V]
    {ι : Type uI} [Fintype ι] [Nonempty ι] {X : Type uX}
    (ρ : Representation K G V) (e : V ≃ₗ[K] (ι → K))
    (b : X → G) (a : X → ι → K)
    (diagonal : ∀ x v i, e (ρ (b x) v) i = a x i * e v i)
    (separate : ∀ i j, i ≠ j → ∃ x, a x i ≠ a x j)
    (move : ∀ i j, ∃ g : G, ∀ v, e (ρ g v) j = e v i)
    (T : V →ₗ[K] V) (hT : ∀ g v, T (ρ g v) = ρ g (T v)) :
    ∃ c : K, T = c • LinearMap.id := by
  classical
  let u : ι → V := fun i => e.symm (Pi.single i 1)
  have hu (i j : ι) : e (u i) j = (Pi.single i (1 : K) : ι → K) j := by simp [u]
  have hexpand (v : V) : v = ∑ k, e v k • u k := by
    apply e.injective
    funext j
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hu]
    simp [Pi.single_apply]
  have hdiag_u (x : X) (i : ι) : ρ (b x) (u i) = a x i • u i := by
    apply e.injective
    funext j
    rw [diagonal x (u i) j, map_smul, Pi.smul_apply, smul_eq_mul, hu]
    by_cases h : j = i
    · subst h
      simp
    · simp [h]
  have hoff (i j : ι) (hij : i ≠ j) : e (T (u i)) j = 0 := by
    obtain ⟨x, hx⟩ := separate i j hij
    have h1 := diagonal x (T (u i)) j
    rw [← hT, hdiag_u, map_smul, map_smul, Pi.smul_apply, smul_eq_mul] at h1
    have h2 : (a x i - a x j) * e (T (u i)) j = 0 := by
      rw [sub_mul, h1, sub_self]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hx)
  let c : ι → K := fun i => e (T (u i)) i
  have hTu (i : ι) : e (T (u i)) = c i • Pi.single i 1 := by
    funext j
    by_cases h : j = i
    · subst h
      simp [c]
    · rw [hoff i j (Ne.symm h)]
      simp [h]
  have hconst (i j : ι) : c i = c j := by
    obtain ⟨g, hg⟩ := move i j
    have h1 : e (T (ρ g (u i))) j = c i := by
      rw [hT, hg]
    have h2 : e (T (ρ g (u i))) j = e (ρ g (u i)) j * c j := by
      conv_lhs => rw [hexpand (ρ g (u i))]
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hTu]
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hk
        simp [Ne.symm hk]
      · simp
    rw [h1, hg, hu] at h2
    simpa using h2
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨c i₀, LinearMap.ext fun v => ?_⟩
  apply e.injective
  funext j
  conv_lhs => rw [hexpand v]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hTu,
    LinearMap.smul_apply, LinearMap.id_apply]
  rw [Finset.sum_eq_single j]
  · simp [hconst j i₀, mul_comm]
  · intro k _ hk
    simp [Ne.symm hk]
  · simp

end LinearAlgebra

section Induction

variable {K : Type uK} [Field K] {G : Type uG} [Group G]

/-- The coset coordinates of the induction of the scalar line of `φ`. -/
private def lineCoordinates (S : Subgroup G) (φ : S →* Kˣ) :
    Representation.coindV S.subtype
        (twist φ (of (1 : Representation K S K))).representation ≃ₗ[K]
      (Induction.Cosets S → K) :=
  Induction.coordinates S (twist φ (of (1 : Representation K S K)))

private theorem lineCoordinates_apply (S : Subgroup G) (φ : S →* Kˣ)
    (f : Representation.coindV S.subtype
      (twist φ (of (1 : Representation K S K))).representation)
    (q : Induction.Cosets S) :
    lineCoordinates S φ f q = f.1 q.out := rfl

/-- Under the separation hypothesis, the induction of the scalar line of `φ` is irreducible and
every intertwining endomorphism is a scalar. -/
theorem induce_twist_irreducible_scalar_of_separation
    (S N : Subgroup G) [S.FiniteIndex] [N.Normal] (hNS : N ≤ S) (φ : S →* Kˣ)
    (separate : ∀ x y : G, Induction.coset S x ≠ Induction.coset S y →
      ∃ n : N,
        (φ.comp (Subgroup.inclusion hNS)) (MulAut.conjNormal x n) ≠
        (φ.comp (Subgroup.inclusion hNS)) (MulAut.conjNormal y n)) :
    (induce S (twist φ (of (1 : Representation K S K)))).representation.IsIrreducible ∧
      HasScalarEndomorphisms (induce S (twist φ (of (1 : Representation K S K)))) := by
  classical
  let := Subgroup.fintypeQuotientOfFiniteIndex (H := S)
  let : Nonempty (Induction.Cosets S) := ⟨Induction.coset S 1⟩
  let a (n : N) (q : Induction.Cosets S) : K :=
    ((φ.comp (Subgroup.inclusion hNS)) (MulAut.conjNormal q.out n) : K)
  let ρ := (induce S (twist φ (of (1 : Representation K S K)))).representation
  have diagonal : ∀ (n : N) (f : Representation.coindV S.subtype
      (twist φ (of (1 : Representation K S K))).representation) (q : Induction.Cosets S),
      lineCoordinates S φ (ρ (n : G) f) q = a n q * lineCoordinates S φ f q := by
    intro n f q
    have hf := f.2 (Subgroup.inclusion hNS (MulAut.conjNormal q.out n)) q.out
    have hmul : (S.subtype (Subgroup.inclusion hNS (MulAut.conjNormal q.out n))) * q.out =
        q.out * n := by
      simp only [Subgroup.coe_subtype, Subgroup.coe_inclusion, MulAut.conjNormal_apply]
      group
    rw [hmul] at hf
    exact hf
  have sep : ∀ q r : Induction.Cosets S, q ≠ r → ∃ n : N, a n q ≠ a n r := by
    intro q r hqr
    obtain ⟨n, hn⟩ := separate q.out r.out (by
      simpa only [Induction.coset_out] using hqr)
    exact ⟨n, Units.val_injective.ne hn⟩
  have move : ∀ q r : Induction.Cosets S, ∃ g : G, ∀ f,
      lineCoordinates S φ (ρ g f) r = lineCoordinates S φ f q := by
    intro q r
    refine ⟨r.out⁻¹ * q.out, ?_⟩
    intro f
    change f.1 (r.out * (r.out⁻¹ * q.out)) = f.1 q.out
    simp
  refine ⟨irreducible_of_diagonal_coordinates ρ (lineCoordinates S φ) (fun n : N => n.1) a
    diagonal sep move, ?_⟩
  intro T
  exact scalar_of_diagonal_coordinates ρ (lineCoordinates S φ) (fun n : N => n.1) a
    diagonal sep move T.toLinearMap (fun g v =>
      LinearMap.congr_fun (T.isIntertwining' g) v)

end Induction

section Transfer

variable {K : Type uK} [Field K] {G : Type uG} [Group G]

/-- Scalar endomorphisms are transported along an equivalence of representations. -/
theorem hasScalarEndomorphisms_of_equiv
    {A : FiniteRepresentation.{uK, uG, uV} K G} {B : FiniteRepresentation.{uK, uG, uW} K G}
    (e : Equiv A B) (hA : HasScalarEndomorphisms A) : HasScalarEndomorphisms B := by
  intro f
  obtain ⟨a, ha⟩ := hA ((e.symm.toIntertwiningMap.comp f).comp e.toIntertwiningMap)
  refine ⟨a, LinearMap.ext fun v => ?_⟩
  have h := LinearMap.congr_fun ha (e.symm v)
  simp only [Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.id_apply] at h
  have h' := congrArg e h
  change e (e.symm (f (e (e.symm v)))) = e (a • e.symm v) at h'
  rw [Representation.Equiv.apply_symm_apply, Representation.Equiv.apply_symm_apply,
    map_smul, Representation.Equiv.apply_symm_apply] at h'
  simpa using h'

/-- Irreducibility is transported along an equivalence of representations. -/
theorem isIrreducible_of_equiv
    {A : FiniteRepresentation.{uK, uG, uV} K G} {B : FiniteRepresentation.{uK, uG, uW} K G}
    (e : Equiv A B) (hA : A.representation.IsIrreducible) : B.representation.IsIrreducible :=
  (CentralEigenspaceSplitting.isIrreducible_iff_of_equiv e).mp hA

end Transfer

section OneCoset

variable {K : Type uK} [Field K] {G Γ : Type uG} [Group G] [Group Γ]

/-- Mackey restriction with a single double coset: if `G = H x ι(Γ)` and `S` is the subgroup of
`Γ` that `x` conjugates into `H`, the restriction to `Γ` of the induction from `H` is the
induction from `S` of the restriction along conjugation by `x`. -/
def restrictInduceEquivOfOneCoset (H : Subgroup G) (ι : Γ →* G) (x : G) (S : Subgroup Γ)
    (κ : S →* H) [H.FiniteIndex] [S.FiniteIndex]
    (hκ : ∀ s : S, (κ s : G) = x * ι s * x⁻¹)
    (hS : ∀ ℓ : Γ, x * ι ℓ * x⁻¹ ∈ H → ℓ ∈ S)
    (hcover : ∀ g : G, ∃ (h : H) (ℓ : Γ), g = h * (x * ι ℓ))
    (A : FiniteRepresentation.{uK, uG, uV} K H) :
    Equiv (restrict ι (induce H A)) (induce S (restrict κ A)) :=
  let e := mackeyEquiv H ι (fun _ : Unit => x) (fun _ => S) (fun _ => κ) (fun _ s => hκ s)
    (fun _ ℓ hℓ => hS ℓ hℓ)
    (fun g => by obtain ⟨h, ℓ, rfl⟩ := hcover g; exact ⟨h, (), ℓ, rfl⟩)
    (fun _ _ _ _ _ _ _ => Subsingleton.elim _ _) A
  { toLinearEquiv := e.trans (LinearEquiv.funUnique Unit K (induce S (restrict κ A)).obj)
    isIntertwining' := fun u => LinearMap.ext fun f => by
      change e ((restrict ι (induce H A)).representation u f) () =
        (induce S (restrict κ A)).representation u (e f ())
      exact mackeyMap_intertwines H ι (fun _ => x) (fun _ => S) (fun _ => κ) (fun _ s => hκ s)
        A u f () }

end OneCoset

section Line

variable {K : Type uK} [Field K] {G Γ : Type uG} [Group G] [Group Γ]

/-- The restriction of the scalar line of `φ` is the scalar line of the composite. -/
def restrictTwistLineEquiv (κ : Γ →* G) (φ : G →* Kˣ) :
    Equiv (restrict κ (twist φ (of (1 : Representation K G K))))
      (twist (φ.comp κ) (of (1 : Representation K Γ K))) :=
  { toLinearEquiv := LinearEquiv.refl K K
    isIntertwining' := fun _ => rfl }

/-- Equal characters give equivalent scalar lines. -/
def twistLineEquivOfEq {φ φ' : G →* Kˣ} (h : φ = φ') :
    Equiv (twist φ (of (1 : Representation K G K))) (twist φ' (of (1 : Representation K G K))) :=
  { toLinearEquiv := LinearEquiv.refl K K
    isIntertwining' := fun g => by subst h; rfl }

end Line

end Langlands.FiniteRepresentation
