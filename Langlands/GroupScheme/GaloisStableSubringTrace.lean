import Langlands.GroupScheme.LocalUnramifiedIntegralCocycle
import Mathlib.FieldTheory.Finite.Basic

/-! # Trace identities in Galois-stable subrings of unramified integer rings -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open IsLocalRing

namespace Langlands.GroupScheme

namespace GaloisRingCover

section Residues

variable {B : Type u} [CommRing B] [IsLocalRing B]

/-- In a local ring with finite residue field, a subring containing every square of a unit
meets every residue class. Every element of a finite field is a sum of two squares. -/
theorem exists_mem_residue_eq_of_sq_mem [Finite (ResidueField B)]
    (P : Subring B) (hsq : ∀ x : B, IsUnit x → x ^ 2 ∈ P) (x : B) :
    ∃ p ∈ P, residue B p = residue B x := by
  classical
  have hsqres : ∀ s : ResidueField B, ∃ p ∈ P, residue B p = s ^ 2 := by
    intro s
    by_cases hs : s = 0
    · exact ⟨0, P.zero_mem, by simp [hs]⟩
    · obtain ⟨y, rfl⟩ := residue_surjective s
      exact ⟨y ^ 2, hsq y ((residue_ne_zero_iff_isUnit y).mp hs), by simp⟩
  let : Fintype (ResidueField B) := Fintype.ofFinite _
  obtain ⟨a, b, hab⟩ : ∃ a b : ResidueField B, a ^ 2 + b ^ 2 = residue B x := by
    by_cases h2 : ringChar (ResidueField B) = 2
    · obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two h2 (residue B x)
      exact ⟨r, 0, by rw [hr]; ring⟩
    · obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
        (f := Polynomial.X ^ 2) (g := Polynomial.X ^ 2 - Polynomial.C (residue B x))
        (Polynomial.degree_X_pow 2) (Polynomial.degree_X_pow_sub_C (by norm_num) _)
        (FiniteField.odd_card_of_char_ne_two h2)
      refine ⟨a, b, ?_⟩
      simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub,
        Polynomial.eval_C] at hab
      linear_combination hab
  obtain ⟨p, hp, hpa⟩ := hsqres a
  obtain ⟨p', hp', hpb⟩ := hsqres b
  exact ⟨p + p', P.add_mem hp hp', by rw [map_add, hpa, hpb, hab]⟩

omit [IsLocalRing B] in
/-- A subring containing every square of a unit contains the inverse of each of its units. -/
theorem inv_mem_of_sq_mem (P : Subring B) (hsq : ∀ x : B, IsUnit x → x ^ 2 ∈ P)
    (x : B) (hx : IsUnit x) (hxP : x ∈ P) : (hx.unit⁻¹ : Bˣ).val ∈ P := by
  have hinv : IsUnit (hx.unit⁻¹ : Bˣ).val := (hx.unit⁻¹).isUnit
  have h := P.mul_mem hxP (hsq _ hinv)
  have heq : x * (hx.unit⁻¹ : Bˣ).val ^ 2 = (hx.unit⁻¹ : Bˣ).val := by
    rw [sq, ← mul_assoc, hx.mul_val_inv, one_mul]
  rwa [heq] at h

end Residues

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable {Γ : Type u} [Group Γ] (ρ : Γ →* (B ≃ₐ[R] B))
variable [IsLocalRing B]

/-- Conjugates of elements with equal residues have equal residues. -/
theorem residue_apply_eq_of_residue_eq (g : Γ) {x y : B} (h : residue B x = residue B y) :
    residue B (ρ g x) = residue B (ρ g y) := by
  have hxy : x - y ∈ maximalIdeal B := by
    rw [← residue_eq_zero_iff, map_sub, h, sub_self]
  have hg : ρ g (x - y) ∈ maximalIdeal B := by
    rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff (ρ g)]
    exact (mem_maximalIdeal _).mp hxy
  rw [← sub_eq_zero, ← map_sub, ← map_sub, residue_eq_zero_iff]
  exact hg

variable [Module.Free R B] [Module.Finite R B] [Fintype Γ] [DecidableEq Γ]

/-- **Dual family in a Galois-stable subring.** Let `B` be local and finite free over `R`, with a
Galois group `Γ` of order the rank acting faithfully on the residue field. Let `P` be a
`Γ`-stable subring of `B` that is closed under inverses of its units and meets every residue
class. Then there are `a_j, c_j ∈ P` with `∑_j a_j g(c_j) = δ_{g,1}` for every `g ∈ Γ`. -/
theorem exists_dual_family_of_subring
    (hcard : Nat.card Γ = Module.finrank R B)
    (hfaithful : ∀ g : Γ, (∀ x : B, residue B (ρ g x) = residue B x) → g = 1)
    (P : Subring B) (hρ : ∀ (g : Γ) (x : B), x ∈ P → ρ g x ∈ P)
    (hinv : ∀ (x : B) (hx : IsUnit x), x ∈ P → (hx.unit⁻¹ : Bˣ).val ∈ P)
    (hres : ∀ x : B, ∃ p ∈ P, residue B p = residue B x) :
    ∃ (n : ℕ) (a c : Fin n → B), (∀ j, a j ∈ P) ∧ (∀ j, c j ∈ P) ∧
      ∀ g : Γ, ∑ j, a j * ρ g (c j) = if g = 1 then 1 else 0 := by
  classical
  have : Nontrivial R := (algebraMap R B).domain_nontrivial
  have hbij := tensorHom_bijective ρ hcard hfaithful
  let J := Module.Free.ChooseBasisIndex R B
  let b : Module.Basis J R B := Module.Free.chooseBasis R B
  have hJ : Fintype.card J = Fintype.card Γ := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, ← hcard, Nat.card_eq_fintype_card]
  let ε : J ≃ Γ := Fintype.equivOfCardEq hJ
  let v : Module.Basis J B (TensorProduct R B B) := Algebra.TensorProduct.basis B b
  let v' : Module.Basis J B (Γ → B) := (Pi.basisFun B Γ).reindex ε.symm
  let f : TensorProduct R B B →ₗ[B] (Γ → B) := (tensorHom ρ).toLinearMap
  let M := LinearMap.toMatrix v v' f
  have hM : ∀ i j, M i j = ρ (ε i) (b j) := by
    intro i j
    simp [M, LinearMap.toMatrix_apply, v, v', f]
  have hMdet : IsUnit M.det := LinearEquiv.isUnit_det (LinearEquiv.ofBijective f hbij) v v'
  choose c hcP hcres using fun j => hres (b j)
  let N : Matrix J J P := fun i j => ⟨ρ (ε i) (c j), hρ _ _ (hcP j)⟩
  have hNdetB : IsUnit (N.det : B) := by
    rw [show (N.det : B) = P.subtype N.det from rfl, RingHom.map_det,
      ← residue_ne_zero_iff_isUnit, RingHom.map_det]
    have hmat : (residue B).mapMatrix (P.subtype.mapMatrix N) = (residue B).mapMatrix M := by
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hM]
      exact residue_apply_eq_of_residue_eq ρ (ε i) (hcres j)
    rw [hmat, ← RingHom.map_det, residue_ne_zero_iff_isUnit]
    exact hMdet
  have hNdet : IsUnit N.det := by
    refine IsUnit.of_mul_eq_one ⟨_, hinv _ hNdetB N.det.property⟩ ?_
    apply Subtype.ext
    exact hNdetB.mul_val_inv
  let i₀ : J := ε.symm 1
  let avec : J → P := Matrix.mulVec N⁻¹ (Pi.single i₀ 1)
  have hNa : Matrix.mulVec N avec = Pi.single i₀ 1 := by
    simp only [avec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv N hNdet, Matrix.one_mulVec]
  let eJ := Fintype.equivFin J
  refine ⟨Fintype.card J, fun k => (avec (eJ.symm k) : B), fun k => c (eJ.symm k),
    fun k => (avec (eJ.symm k)).property, fun k => hcP _, ?_⟩
  intro g
  have hrow := congrArg P.subtype (congrFun hNa (ε.symm g))
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul] at hrow
  rw [Equiv.sum_comp eJ.symm (fun j => (avec j : B) * ρ g (c j))]
  have hleft : ∑ j, P.subtype (N (ε.symm g) j) * P.subtype (avec j) =
      ∑ j, (avec j : B) * ρ g (c j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    change ρ (ε (ε.symm g)) (c j) * (avec j : B) = _
    rw [Equiv.apply_symm_apply, mul_comm]
  rw [← hleft, hrow]
  by_cases hg : g = 1
  · subst hg
    simp [i₀]
  · have hne : ε.symm g ≠ i₀ := fun h => hg (ε.symm.injective h)
    simp [hne, hg]

omit [DecidableEq Γ] in
/-- **Trace-one element in a Galois-stable subring.** Under the hypotheses of
`exists_dual_family_of_subring`, the subring contains an element of trace one. -/
theorem exists_trace_eq_one_of_subring
    (hcard : Nat.card Γ = Module.finrank R B)
    (hfaithful : ∀ g : Γ, (∀ x : B, residue B (ρ g x) = residue B x) → g = 1)
    (P : Subring B) (hρ : ∀ (g : Γ) (x : B), x ∈ P → ρ g x ∈ P)
    (hinv : ∀ (x : B) (hx : IsUnit x), x ∈ P → (hx.unit⁻¹ : Bˣ).val ∈ P)
    (hres : ∀ x : B, ∃ p ∈ P, residue B p = residue B x) :
    ∃ θ ∈ P, ∑ g : Γ, ρ g θ = 1 := by
  classical
  obtain ⟨n, a, c, -, hc, hid⟩ :=
    exists_dual_family_of_subring ρ hcard hfaithful P hρ hinv hres
  have hsum : ∑ j, a j * ∑ g : Γ, ρ g (c j) = 1 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [hid]
    simp
  obtain ⟨j, hj⟩ : ∃ j, IsUnit (a j * ∑ g : Γ, ρ g (c j)) := by
    by_contra h
    push Not at h
    have hmem : (∑ j, a j * ∑ g : Γ, ρ g (c j)) ∈ maximalIdeal B :=
      Ideal.sum_mem _ fun j _ => (mem_maximalIdeal _).mpr (h j)
    rw [hsum] at hmem
    exact (maximalIdeal.isMaximal B).ne_top ((Ideal.eq_top_iff_one _).mpr hmem)
  set T := ∑ g : Γ, ρ g (c j) with hT
  have hTu : IsUnit T := isUnit_of_mul_isUnit_right hj
  have hTP : T ∈ P := P.sum_mem fun g _ => hρ g _ (hc j)
  have hTfix : ∀ g, ρ g T = T := by
    intro g
    simp only [T, map_sum]
    exact Fintype.sum_bijective (g * ·) (Group.mulLeft_bijective g) _ _
      (fun h => by rw [map_mul, AlgEquiv.mul_apply])
  set t := (hTu.unit⁻¹ : Bˣ).val with ht
  have htP : t ∈ P := hinv T hTu hTP
  have htT : t * T = 1 := hTu.val_inv_mul
  have htfix : ∀ g, ρ g t = t := by
    intro g
    have h : ρ g t * T = t * T := by
      conv_lhs => rw [← hTfix g]
      rw [← map_mul, htT, map_one]
    exact hTu.mul_right_cancel h
  refine ⟨c j * t, P.mul_mem (hc j) htP, ?_⟩
  simp only [map_mul, htfix, ← Finset.sum_mul]
  rw [← hT, mul_comm, htT]

end GaloisRingCover

namespace LocalUnramified

open ValuativeRel LocalGalois LocalGalois.Separable

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (E : IntermediateField F (SeparableClosure F)) [FiniteDimensional F E]

/-- The residue field of the ring of integers of a finite extension is finite. -/
theorem finite_residueField : Finite (ResidueField (integers F E)) := by
  have : FaithfulSMul 𝒪[F] (integers F E) := by
    refine (faithfulSMul_iff_algebraMap_injective _ _).mpr fun x y hxy => ?_
    have h := congrArg (fun z : integers F E => (z : E)) hxy
    exact Subtype.val_injective ((algebraMap F E).injective h)
  have : Algebra.IsIntegral 𝒪[F] (integers F E) := inferInstance
  have : IsLocalHom (algebraMap 𝒪[F] (integers F E)) :=
    Algebra.IsIntegral.isLocalHom 𝒪[F] (integers F E)
  exact ResidueField.finite_of_finite (R := 𝒪[F]) inferInstance

variable [IsGalois F E]

open scoped Classical in
/-- **Dual family in a Galois-stable subring of an unramified integer ring.** Let `E/F` be a
finite Galois extension inside the maximal unramified extension, and `P` a Galois-stable subring
of its ring of integers containing every square of a unit. Then there are `a_j, c_j ∈ P` with
`∑_j a_j g(c_j) = δ_{g,1}` for every `g ∈ Gal(E/F)`. -/
theorem exists_dual_family_of_sq_mem (hE : E ≤ inertiaFixedField F)
    (P : Subring (integers F E))
    (hP : ∀ (g : E ≃ₐ[F] E) (x : integers F E), x ∈ P → galoisAction F E g x ∈ P)
    (hsq : ∀ x : integers F E, IsUnit x → x ^ 2 ∈ P) :
    ∃ (n : ℕ) (a c : Fin n → integers F E), (∀ j, a j ∈ P) ∧ (∀ j, c j ∈ P) ∧
      ∀ g : E ≃ₐ[F] E, ∑ j, a j * galoisAction F E g (c j) = if g = 1 then 1 else 0 := by
  have := finite_residueField F E
  exact GaloisRingCover.exists_dual_family_of_subring (galoisAction F E) (card_galois F E)
    (galoisAction_faithful F E hE) P hP (GaloisRingCover.inv_mem_of_sq_mem P hsq)
    (GaloisRingCover.exists_mem_residue_eq_of_sq_mem P hsq)

/-- **Trace-one element in a Galois-stable subring of an unramified integer ring.** -/
theorem exists_trace_eq_one_of_sq_mem (hE : E ≤ inertiaFixedField F)
    (P : Subring (integers F E))
    (hP : ∀ (g : E ≃ₐ[F] E) (x : integers F E), x ∈ P → galoisAction F E g x ∈ P)
    (hsq : ∀ x : integers F E, IsUnit x → x ^ 2 ∈ P) :
    ∃ θ ∈ P, ∑ g : E ≃ₐ[F] E, galoisAction F E g θ = 1 := by
  have := finite_residueField F E
  exact GaloisRingCover.exists_trace_eq_one_of_subring (galoisAction F E) (card_galois F E)
    (galoisAction_faithful F E hE) P hP (GaloisRingCover.inv_mem_of_sq_mem P hsq)
    (GaloisRingCover.exists_mem_residue_eq_of_sq_mem P hsq)

end LocalUnramified

end Langlands.GroupScheme
