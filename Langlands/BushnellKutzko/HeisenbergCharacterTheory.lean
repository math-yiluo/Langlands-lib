import Langlands.BushnellKutzko.IntertwiningAveraging
import Langlands.BushnellKutzko.RepresentationIntertwining
import Langlands.Weil.Representation.IsomorphismInvarianceProof
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RingTheory.HopkinsLevitzki

/-! # The character argument for Heisenberg representations -/

noncomputable section

open scoped commutatorElement MonoidAlgebra

namespace Langlands.BushnellKutzko.HeisenbergCharacter

universe u v w

variable {G : Type u} [Group G] {H : Subgroup G} {χ : H →* ℂˣ}
variable {V : Type v} [AddCommGroup V] [Module ℂ V] {W : Type w} [AddCommGroup W] [Module ℂ W]

section Scalar

variable [H.Normal]
variable (hχ : ∀ (g : G) (h : H), χ ⟨g * h * g⁻¹, Subgroup.Normal.conj_mem inferInstance _ h.2 g⟩ = χ h)

include hχ in
/-- An irreducible representation containing an invariant character acts by that character
on its entire carrier. -/
theorem scalar_of_contains (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (h : ∃ f : (characterRepresentation χ).IntertwiningMap (ρ.comp H.subtype), f ≠ 0) :
    ∀ a : H, ρ a = (χ a : ℂ) • LinearMap.id := by
  obtain ⟨f, hf⟩ := h
  have hf1 : f 1 ≠ 0 := by
    intro hf0
    apply hf
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro z
    have hz := map_smul f z (1 : ℂ)
    simpa [hf0] using hz
  have he (a : H) : ρ a (f 1) = (χ a : ℂ) • f 1 := by
    have h := Representation.IntertwiningMap.isIntertwining _ _ f a (1 : ℂ)
    rw [characterRepresentation_apply, ← smul_eq_mul, map_smul] at h
    exact h.symm
  intro a
  apply LinearMap.ext
  intro z
  obtain ⟨c, hc⟩ := exists_finsupp_sum_eq ρ hf1 z
  have horbit (g : G) : ρ a (ρ g (f 1)) = (χ a : ℂ) • ρ g (f 1) := by
    let b : H := ⟨g⁻¹ * a * g, by simpa using Subgroup.Normal.conj_mem inferInstance _ a.2 g⁻¹⟩
    have hb : χ b = χ a := by simpa [b] using hχ g⁻¹ a
    calc
      ρ a (ρ g (f 1)) = ρ ((a : G) * g) (f 1) := by rw [map_mul, Module.End.mul_apply]
      _ = ρ (g * (b : G)) (f 1) := by congr 2; dsimp [b]; group
      _ = (χ a : ℂ) • ρ g (f 1) := by rw [map_mul, Module.End.mul_apply, he, hb, map_smul]
  rw [← hc]
  change ρ a (c.sum fun g r => r • ρ g (f 1)) =
    (χ a : ℂ) • (c.sum fun g r => r • ρ g (f 1))
  simp only [Finsupp.sum, map_sum, map_smul, horbit, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun _ _ => smul_comm _ _ _)

open QuotientGroup in
include hχ in
set_option backward.isDefEq.respectTransparency false in
/-- Coinduction from the invariant character is finite-dimensional at finite index. Taking
a simple submodule gives an irreducible scalar extension on a finite coordinate space. -/
theorem exists_irreducible_scalar [H.FiniteIndex] :
    ∃ (d : ℕ) (ρ : Representation ℂ G (Fin d → ℂ)),
      ρ.IsIrreducible ∧ ∀ a : H, ρ a = (χ a : ℂ) • LinearMap.id := by
  classical
  let C := Representation.coindV H.subtype (characterRepresentation χ)
  let τ : Representation ℂ G C := Representation.coind H.subtype (characterRepresentation χ)
  have heval (f : C) (h : H) (g : G) : (f : G → ℂ) (h * g) = (χ h : ℂ) * f.1 g :=
    f.2 h g
  let e : C →ₗ[ℂ] ((G ⧸ H) → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (fun q : G ⧸ H => q.out)).comp C.subtype
  have he : Function.Injective e := by
    intro f f' hff'
    apply Subtype.ext
    funext g
    let q : G ⧸ H := mk g
    obtain ⟨a, ha⟩ := mk_out_eq_mul (s := H) g
    let b : H := ⟨g * (a : G)⁻¹ * g⁻¹, Subgroup.Normal.conj_mem inferInstance _ (H.inv_mem a.2) g⟩
    have hg : g = (b : G) * q.out := by
      change g = (g * (a : G)⁻¹ * g⁻¹) * (mk g : G ⧸ H).out
      rw [ha]
      group
    have hq : f.1 q.out = f'.1 q.out := congrFun hff' q
    calc
      f.1 g = (χ b : ℂ) * f.1 q.out := by rw [← heval, ← hg]
      _ = f'.1 g := by rw [hq, ← heval, ← hg]
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  let : FiniteDimensional ℂ C := FiniteDimensional.of_injective e he
  let v : C := ⟨fun g => if hg : g ∈ H then (χ ⟨g, hg⟩ : ℂ) else 0, by
    intro a g
    change (if hg : (a : G) * g ∈ H then (χ ⟨_, hg⟩ : ℂ) else 0) =
      (χ a : ℂ) * (if hg : g ∈ H then (χ ⟨_, hg⟩ : ℂ) else 0)
    by_cases hg : g ∈ H
    · rw [dite_eq_left hg, dite_eq_left (H.mul_mem a.2 hg)]
      exact congrArg Units.val (map_mul χ a ⟨g, hg⟩)
    · rw [dite_eq_right hg, dite_eq_right (fun h => hg ((H.mul_mem_cancel_left a.2).mp h)),
        mul_zero]⟩
  have hv : v.1 1 = 1 := by
    change (if h : (1 : G) ∈ H then (χ ⟨1, h⟩ : ℂ) else 0) = 1
    rw [dite_eq_left H.one_mem]
    change (χ (1 : H) : ℂ) = 1
    rw [map_one, Units.val_one]
  have : Nontrivial C := ⟨⟨v, 0, fun h => by simpa [hv] using congrArg (fun f : C => f.1 1) h⟩⟩
  have hτ (a : H) (f : C) : τ a f = (χ a : ℂ) • f := by
    apply Subtype.ext
    funext g
    let b : H := ⟨g * a * g⁻¹, Subgroup.Normal.conj_mem inferInstance _ a.2 g⟩
    change f.1 (g * a) = (χ a : ℂ) * f.1 g
    have hg : g * (a : G) = (b : G) * g := by dsimp [b]; group
    rw [hg, heval, hχ g a]
  let : Nontrivial τ.asModule := τ.asModuleEquiv.toEquiv.nontrivial
  let : IsArtinian ℂ τ.asModule := isArtinian_of_linearEquiv τ.asModuleEquiv.symm
  let : IsArtinian ℂ[G] τ.asModule := isArtinian_of_tower ℂ (S := ℂ[G]) ‹_›
  obtain ⟨S, hS⟩ : ∃ S : Submodule ℂ[G] τ.asModule, IsAtom S :=
    IsAtomic.exists_atom (Submodule ℂ[G] τ.asModule)
  let : AddCommGroup S := Submodule.addCommGroup (R := ℂ[G]) (M := τ.asModule) S
  have : IsSimpleModule ℂ[G] S :=
    (isSimpleModule_iff_isAtom (R := ℂ[G]) (M := τ.asModule) (m := S)).mpr hS
  let σ := Representation.ofModule (k := ℂ) (G := G) S
  let j₀ : RestrictScalars ℂ ℂ[G] S →ₗ[ℂ] τ.asModule :=
    { toFun := fun s => (RestrictScalars.addEquiv ℂ ℂ[G] S s : τ.asModule)
      map_add' := fun _ _ => rfl
      map_smul' := fun c s => by
        let t : τ.asModule := (RestrictScalars.addEquiv ℂ ℂ[G] S s : S)
        change algebraMap ℂ ℂ[G] c • t = c • t
        exact IsScalarTower.algebraMap_smul ℂ[G] c t }
  let j : RestrictScalars ℂ ℂ[G] S →ₗ[ℂ] C :=
    τ.asModuleEquiv.toLinearMap.comp j₀
  have hj : Function.Injective j := τ.asModuleEquiv.injective.comp
    (Subtype.val_injective.comp (RestrictScalars.addEquiv ℂ ℂ[G] S).injective)
  let : FiniteDimensional ℂ (RestrictScalars ℂ ℂ[G] S) := FiniteDimensional.of_injective j hj
  have hσ (a : H) (s : RestrictScalars ℂ ℂ[G] S) : σ a s = (χ a : ℂ) • s := by
    apply hj
    rw [map_smul, ← hτ]
    change τ.asModuleEquiv ((RestrictScalars.addEquiv ℂ ℂ[G] S (σ a s) : S) : τ.asModule) = _
    rw [← τ.asModuleEquiv.apply_symm_apply (τ (a : G) (j s)), τ.asModuleEquiv_symm_map_rho]
    apply congrArg τ.asModuleEquiv
    change _ = MonoidAlgebra.of ℂ G (a : G) • ((RestrictScalars.addEquiv ℂ ℂ[G] S s : S) : τ.asModule)
    have hs : RestrictScalars.addEquiv ℂ ℂ[G] S (σ (a : G) s) =
        MonoidAlgebra.of ℂ G (a : G) • RestrictScalars.addEquiv ℂ ℂ[G] S s := by
      rw [← σ.asAlgebraHom_of, Representation.ofModule_asAlgebraHom_apply_apply,
        AddEquiv.apply_symm_apply]
    exact congrArg (fun t : S => (t : τ.asModule)) hs
  let b := (Module.finBasis ℂ (RestrictScalars ℂ ℂ[G] S)).equivFun
  let ρ : Representation ℂ G (Fin (Module.finrank ℂ (RestrictScalars ℂ ℂ[G] S)) → ℂ) :=
    b.conjRingEquiv.toMonoidHom.comp σ
  let i : σ.Equiv ρ := Representation.Equiv.mk b fun g => by
    apply LinearMap.ext
    intro s
    change b (σ g s) = b ((σ g) (b.symm (b s)))
    rw [b.symm_apply_apply]
  refine ⟨_, ρ, (Langlands.Weil.IsomorphismInvariance.irreducible_iff i).mp
    ((Representation.isSimpleModule_iff_irreducible_ofModule (k := ℂ) (G := G) S).mp inferInstance), ?_⟩
  intro a
  apply LinearMap.ext
  intro x
  change b (σ a (b.symm x)) = (χ a : ℂ) • x
  rw [hσ, map_smul, b.apply_symm_apply]

end Scalar

/-- Acting by a nontrivial scalar commutator forces the trace at the conjugated element to vanish. -/
theorem character_eq_zero_of_commutator (ρ : Representation ℂ G V) (x y : G) (c : ℂ)
    (hc : c ≠ 1) (h : ρ ⁅y, x⁆ = c • LinearMap.id) : ρ.character x = 0 := by
  have hconj : ρ.character x = c * ρ.character x := calc
    ρ.character x = ρ.character (y * x * y⁻¹) := (ρ.char_conj x y).symm
    _ = c * ρ.character x := by
      rw [← MulAut.conj_apply, conj_eq_commutatorElement_mul]
      simp [Representation.character, h, ← Module.End.one_eq_id]
  have hzero : (c - 1) * ρ.character x = 0 := by
    rw [sub_mul, one_mul, ← hconj, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hc)

/-- If the product of the two character traces is a constant on a subgroup and vanishes
elsewhere, its finite average is that constant divided by the subgroup index. -/
theorem finrank_intertwiningMap_mul_index [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (N : Subgroup G)
    [N.Normal] [N.FiniteIndex] (hNρ : N ≤ ρ.ker) (hNσ : N ≤ σ.ker) (hNH : N ≤ H) (c : ℕ)
    (hinside : ∀ g ∈ H, σ.character g * ρ.character g⁻¹ = (c : ℂ))
    (houtside : ∀ g ∉ H, σ.character g * ρ.character g⁻¹ = 0) :
    Module.finrank ℂ (ρ.IntertwiningMap σ) * H.index = c := by
  classical
  let Q := G ⧸ N
  let π := QuotientGroup.mk' N
  let D := H.map π
  let ρQ : Representation ℂ Q V := QuotientGroup.lift N ρ hNρ
  let σQ : Representation ℂ Q W := QuotientGroup.lift N σ hNσ
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hρ (g : G) : ρQ (π g) = ρ g := rfl
  have hσ (g : G) : σQ (π g) = σ g := rfl
  let toQuotient (f : ρ.IntertwiningMap σ) : ρQ.IntertwiningMap σQ :=
    ⟨f.toLinearMap, fun q => by
      obtain ⟨g, rfl⟩ := hπ q
      rw [hρ, hσ]
      exact f.2 g⟩
  let fromQuotient (f : ρQ.IntertwiningMap σQ) : ρ.IntertwiningMap σ :=
    ⟨f.toLinearMap, fun g => by simpa only [hρ, hσ] using f.2 (π g)⟩
  let e : (ρ.IntertwiningMap σ) ≃ₗ[ℂ] (ρQ.IntertwiningMap σQ) :=
    { toFun := toQuotient
      invFun := fromQuotient
      left_inv := fun _ => Representation.IntertwiningMap.ext rfl
      right_inv := fun _ => Representation.IntertwiningMap.ext rfl
      map_add' := fun _ _ => Representation.IntertwiningMap.ext rfl
      map_smul' := fun _ _ => Representation.IntertwiningMap.ext rfl }
  let : Fintype Q := Fintype.ofFinite Q
  have hQ : (Nat.card Q : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Q ≠ 0)
  let : Invertible (Nat.card Q : ℂ) := invertibleOfNonzero hQ
  have hmem (g : G) : π g ∈ D ↔ g ∈ H := by
    change g ∈ (H.map π).comap π ↔ _
    rw [QuotientGroup.comap_map_mk', sup_eq_right.mpr hNH]
  have hprod (q : Q) : σQ.character q * ρQ.character q⁻¹ = if q ∈ D then (c : ℂ) else 0 := by
    obtain ⟨g, rfl⟩ := hπ q
    rw [← map_inv π, Representation.character, hσ, Representation.character, hρ, hmem]
    split
    · exact hinside g ‹_›
    · exact houtside g ‹_›
  have hsum : ∑ q : Q, (if q ∈ D then (c : ℂ) else 0) = (Nat.card D : ℂ) * c := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    congr 2
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have havg := Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρQ σQ
  rw [← e.finrank_eq, Finset.sum_congr rfl (fun q _ => hprod q), hsum] at havg
  have hindex : D.index = H.index := H.index_map_eq hπ (by simpa [π] using hNH)
  have hcard : (Nat.card D : ℂ) * H.index = Nat.card Q := by exact_mod_cast hindex ▸ D.card_mul_index
  have hc' : (Module.finrank ℂ (ρ.IntertwiningMap σ) : ℂ) * H.index = c := calc
    _ = (Nat.card Q : ℂ)⁻¹ * ((Nat.card D : ℂ) * H.index) * c := by rw [← havg]; ring
    _ = _ := by rw [hcard, inv_mul_cancel₀ hQ, one_mul]
  exact_mod_cast hc'

end Langlands.BushnellKutzko.HeisenbergCharacter
