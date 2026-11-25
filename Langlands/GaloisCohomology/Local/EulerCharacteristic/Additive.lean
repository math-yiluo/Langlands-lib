import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.FreeModule.ModN
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RepresentationTheory.Basic
import Langlands.Cohomology.Profinite.EulerCharacteristic

/-!
# Additive functions on finite modular representations
-/

noncomputable section

universe u v

namespace Langlands.GaloisCohomology.Local

open Representation

-- from AdditiveDefs.lean
open Representation

abbrev TorsN (A : Type*) [AddCommGroup A] (n : ℕ) : Type _ :=
  ↥(LinearMap.ker (LinearMap.lsmul ℤ A (n : ℤ)))

theorem mem_ker_lsmul_iff {A : Type*} [AddCommGroup A] (n : ℕ) (x : A) :
    x ∈ LinearMap.ker (LinearMap.lsmul ℤ A (n : ℤ)) ↔ n • x = 0 := by
  simp

theorem TorsN.nsmul_eq_zero {A : Type*} [AddCommGroup A] {n : ℕ} (x : TorsN A n) :
    n • x = 0 :=
  Subtype.ext (by simpa using (mem_ker_lsmul_iff n (x : A)).1 x.2)

instance TorsN.instModule (A : Type*) [AddCommGroup A] (n : ℕ) : Module (ZMod n) (TorsN A n) :=
  AddCommGroup.zmodModule TorsN.nsmul_eq_zero

instance additiveDistribMulAction {Γ M : Type*} [Monoid Γ] [Monoid M] [MulDistribMulAction Γ M] :
    DistribMulAction Γ (Additive M) where
  smul γ a := Additive.ofMul (γ • a.toMul)
  one_smul a := congrArg Additive.ofMul (one_smul Γ a.toMul)
  mul_smul γ δ a := congrArg Additive.ofMul (mul_smul γ δ a.toMul)
  smul_zero γ := congrArg Additive.ofMul (smul_one γ)
  smul_add γ a b := congrArg Additive.ofMul (smul_mul' γ a.toMul b.toMul)

@[simp]
theorem toMul_smul_additive {Γ M : Type*} [Monoid Γ] [Monoid M] [MulDistribMulAction Γ M] (γ : Γ)
    (a : Additive M) : (γ • a).toMul = γ • a.toMul :=
  rfl

@[simp]
theorem smul_ofMul_additive {Γ M : Type*} [Monoid Γ] [Monoid M] [MulDistribMulAction Γ M] (γ : Γ)
    (a : M) : γ • Additive.ofMul a = Additive.ofMul (γ • a) :=
  rfl

section Rep

def piRep {k Γ X : Type*} [CommSemiring k] [Monoid Γ] [AddCommMonoid X] [Module k X] (ι : Type*)
    (ρ : Representation k Γ X) : Representation k Γ (ι → X) where
  toFun γ := LinearMap.pi fun i => ρ γ ∘ₗ LinearMap.proj i
  map_one' := by ext; simp
  map_mul' γ δ := by ext; simp

@[simp]
theorem piRep_apply {k Γ X : Type*} [CommSemiring k] [Monoid Γ] [AddCommMonoid X] [Module k X]
    (ι : Type*) (ρ : Representation k Γ X) (γ : Γ) (x : ι → X) (i : ι) :
    piRep ι ρ γ x i = ρ γ (x i) :=
  rfl

variable {Γ : Type*} [Group Γ]

def intRepToZMod (n : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod n) V]
    (ρ : Representation ℤ Γ V) : Representation (ZMod n) Γ V where
  toFun γ := (ρ γ).toAddMonoidHom.toZModLinearMap n
  map_one' := by ext x; simp
  map_mul' γ δ := by ext x; simp

@[simp]
theorem intRepToZMod_apply (n : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod n) V]
    (ρ : Representation ℤ Γ V) (γ : Γ) (x : V) : intRepToZMod n ρ γ x = ρ γ x :=
  rfl

variable (Γ) (A : Type*) [AddCommGroup A] [DistribMulAction Γ A] (n : ℕ)

theorem range_lsmul_le_comap (γ : Γ) :
    LinearMap.range (LinearMap.lsmul ℤ A (n : ℤ)) ≤
      (LinearMap.range (LinearMap.lsmul ℤ A (n : ℤ))).comap (ofDistribMulAction ℤ Γ A γ) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨γ • x, by simp⟩

theorem ker_lsmul_le_comap (γ : Γ) :
    LinearMap.ker (LinearMap.lsmul ℤ A (n : ℤ)) ≤
      (LinearMap.ker (LinearMap.lsmul ℤ A (n : ℤ))).comap (ofDistribMulAction ℤ Γ A γ) := by
  intro x hx
  simp only [LinearMap.mem_ker, LinearMap.lsmul_apply, Submodule.mem_comap,
    ofDistribMulAction_apply_apply] at hx ⊢
  rw [← smul_comm γ (n : ℤ) x, hx, smul_zero]

noncomputable def modNRep : Representation (ZMod n) Γ (ModN A n) :=
  intRepToZMod n ((ofDistribMulAction ℤ Γ A).quotient _ (range_lsmul_le_comap Γ A n))

def torsNRep : Representation (ZMod n) Γ (TorsN A n) :=
  intRepToZMod n ((ofDistribMulAction ℤ Γ A).subrepresentation _ (ker_lsmul_le_comap Γ A n))

@[simp]
theorem modNRep_mk (γ : Γ) (x : A) :
    modNRep Γ A n γ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (γ • x) :=
  rfl

@[simp]
theorem coe_torsNRep_apply (γ : Γ) (x : TorsN A n) :
    ((torsNRep Γ A n γ x : TorsN A n) : A) = γ • (x : A) :=
  rfl

end Rep

structure AdditiveFunction (l : ℕ) (Γ : Type v) [Group Γ] where

  toFun : ∀ (X : Type u) [AddCommGroup X] [Module (ZMod l) X] [Finite X],
    Representation (ZMod l) Γ X → ℤ

  additive : ∀ {X₁ X₂ X₃ : Type u} [AddCommGroup X₁] [Module (ZMod l) X₁] [Finite X₁]
    [AddCommGroup X₂] [Module (ZMod l) X₂] [Finite X₂]
    [AddCommGroup X₃] [Module (ZMod l) X₃] [Finite X₃]
    (ρ₁ : Representation (ZMod l) Γ X₁) (ρ₂ : Representation (ZMod l) Γ X₂)
    (ρ₃ : Representation (ZMod l) Γ X₃) (f : X₁ →ₗ[ZMod l] X₂) (g : X₂ →ₗ[ZMod l] X₃),
    ρ₁.IsIntertwiningMap ρ₂ f → ρ₂.IsIntertwiningMap ρ₃ g →
    Function.Injective f → Function.Exact f g → Function.Surjective g →
    toFun X₂ ρ₂ = toFun X₁ ρ₁ + toFun X₃ ρ₃

namespace AdditiveFunction

variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)

noncomputable def g (A : Type u) [AddCommGroup A] [DistribMulAction Γ A] : ℤ :=
  open Classical in
  if h : Finite (ModN A l) ∧ Finite (TorsN A l) then
    haveI := h.1
    haveI := h.2
    d.toFun (ModN A l) (modNRep Γ A l) - d.toFun (TorsN A l) (torsNRep Γ A l)
  else 0

theorem g_eq (A : Type u) [AddCommGroup A] [DistribMulAction Γ A] [Finite (ModN A l)]
    [Finite (TorsN A l)] :
    d.g A = d.toFun (ModN A l) (modNRep Γ A l) - d.toFun (TorsN A l) (torsNRep Γ A l) := by
  rw [g, dite_eq_left ⟨‹_›, ‹_›⟩]

theorem g_of_not_finite (A : Type u) [AddCommGroup A] [DistribMulAction Γ A]
    (h : ¬ (Finite (ModN A l) ∧ Finite (TorsN A l))) : d.g A = 0 := by
  rw [g, dite_eq_right h]

noncomputable def one [NeZero l] : ℤ :=
  d.toFun (ULift.{u} (ZMod l)) (Representation.trivial (ZMod l) Γ (ULift.{u} (ZMod l)))

end AdditiveFunction

-- from AdditiveInvariants.lean
universe w

open Representation TensorProduct

section Invariants

variable {k Γ : Type*} [Field k] [Group Γ] [Fintype Γ]
  {X₁ X₂ X₃ : Type*} [AddCommGroup X₁] [Module k X₁] [AddCommGroup X₂] [Module k X₂]
  [AddCommGroup X₃] [Module k X₃]
  {ρ₁ : Representation k Γ X₁} {ρ₂ : Representation k Γ X₂} {ρ₃ : Representation k Γ X₃}

omit [Fintype Γ] in

theorem mapsTo_invariants {f : X₁ →ₗ[k] X₂} (hf : ρ₁.IsIntertwiningMap ρ₂ f) (x : X₁)
    (hx : x ∈ ρ₁.invariants) : f x ∈ ρ₂.invariants := fun γ => by
  rw [← hf.isIntertwining, hx γ]

theorem exists_invariant_preimage (hΓ : (Fintype.card Γ : k) ≠ 0) {g : X₂ →ₗ[k] X₃}
    (hg : ρ₂.IsIntertwiningMap ρ₃ g) (hs : Function.Surjective g) (y : X₃)
    (hy : y ∈ ρ₃.invariants) : ∃ x ∈ ρ₂.invariants, g x = y := by
  obtain ⟨x, rfl⟩ := hs y
  refine ⟨(Fintype.card Γ : k)⁻¹ • ρ₂.norm x, fun γ => by rw [map_smul, self_norm_apply], ?_⟩
  have hnorm : g (ρ₂.norm x) = ρ₃.norm (g x) := by
    simp [Representation.norm, LinearMap.sum_apply, map_sum, hg.isIntertwining]
  have hinv : ρ₃.norm (g x) = (Fintype.card Γ : k) • g x := by
    have hy' : ∀ γ, ρ₃ γ (g x) = g x := hy
    simp only [Representation.norm, LinearMap.sum_apply, hy', Finset.sum_const, Finset.card_univ]
    exact (Nat.cast_smul_eq_nsmul k _ _).symm
  rw [map_smul, hnorm, hinv, smul_smul, inv_mul_cancel₀ hΓ, one_smul]

theorem finrank_invariants_additive [FiniteDimensional k X₂] (hΓ : (Fintype.card Γ : k) ≠ 0)
    (f : X₁ →ₗ[k] X₂) (g : X₂ →ₗ[k] X₃) (hf : ρ₁.IsIntertwiningMap ρ₂ f)
    (hg : ρ₂.IsIntertwiningMap ρ₃ g) (hinj : Function.Injective f) (hfg : Function.Exact f g)
    (hs : Function.Surjective g) :
    Module.finrank k ρ₂.invariants =
      Module.finrank k ρ₁.invariants + Module.finrank k ρ₃.invariants := by
  let f' : ρ₁.invariants →ₗ[k] ρ₂.invariants := f.restrict (mapsTo_invariants hf)
  let g' : ρ₂.invariants →ₗ[k] ρ₃.invariants := g.restrict (mapsTo_invariants hg)
  have hf' : Function.Injective f' := fun a b hab =>
    Subtype.ext (hinj (congrArg Subtype.val hab))
  have hg' : Function.Surjective g' := fun y => by
    obtain ⟨x, hx, hxy⟩ := exists_invariant_preimage hΓ hg hs y y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hker : LinearMap.ker g' = LinearMap.range f' := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := (hfg (x : X₂)).1 (congrArg Subtype.val hx)
      have ha' : a ∈ ρ₁.invariants := fun γ => hinj (by
        rw [hf.isIntertwining, ha, x.2 γ])
      exact ⟨⟨a, ha'⟩, Subtype.ext ha⟩
    · rintro ⟨a, rfl⟩
      exact Subtype.ext ((hfg _).2 ⟨a, rfl⟩)
  have h₁ := LinearMap.finrank_range_add_finrank_ker g'
  rw [LinearMap.range_eq_top.2 hg', finrank_top, hker, LinearMap.finrank_range_of_inj hf'] at h₁
  omega

end Invariants

theorem isIntertwiningMap_rTensor {k Γ X Y N : Type*} [CommRing k] [Monoid Γ] [AddCommGroup X]
    [Module k X] [AddCommGroup Y] [Module k Y] [AddCommGroup N] [Module k N]
    {ρ : Representation k Γ X} {ρ' : Representation k Γ Y} (σ : Representation k Γ N)
    {f : X →ₗ[k] Y} (hf : ρ.IsIntertwiningMap ρ' f) :
    (ρ.tprod σ).IsIntertwiningMap (ρ'.tprod σ) (f.rTensor N) :=
  ⟨fun γ v => by
    induction v using TensorProduct.inductionOn with
    | tmul x n => simp [hf.isIntertwining]
    | add v w hv hw => simp only [map_add, hv, hw]⟩

namespace AdditiveFunction

noncomputable def invariantsTensor (l : ℕ) [Fact l.Prime] (Γ : Type v) [Group Γ] [Finite Γ]
    (hΓ : Nat.Coprime (Nat.card Γ) l) {N : Type w} [AddCommGroup N] [Module (ZMod l) N]
    [Module.Finite (ZMod l) N] (σ : Representation (ZMod l) Γ N) : AdditiveFunction.{u} l Γ where
  toFun X _ _ _ ρ := Module.finrank (ZMod l) (ρ.tprod σ).invariants
  additive := by
    intro X₁ X₂ X₃ _ _ _ _ _ _ _ _ _ ρ₁ ρ₂ ρ₃ f g hf hg hinj hfg hs
    have := Fintype.ofFinite Γ
    have hΓ' : (Fintype.card Γ : ZMod l) ≠ 0 := by
      rw [← Nat.card_eq_fintype_card, Ne, ZMod.natCast_eq_zero_iff]
      exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).1 hΓ.symm
    have := Module.Finite.of_finite (R := ZMod l) (M := X₂)
    have : Module.Free (ZMod l) N := Module.Free.of_divisionRing (ZMod l) N
    have : Module.Flat (ZMod l) N := Module.Flat.of_free
    have hinj' : Function.Injective (f.rTensor N) :=
      Module.Flat.rTensor_preserves_injective_linearMap f hinj
    have hex : Function.Exact (f.rTensor N) (g.rTensor N) := rTensor_exact N hfg hs
    have hs' : Function.Surjective (g.rTensor N) := LinearMap.rTensor_surjective N hs
    have key := finrank_invariants_additive hΓ' (f.rTensor N) (g.rTensor N)
      (isIntertwiningMap_rTensor σ hf) (isIntertwiningMap_rTensor σ hg) hinj' hex hs'
    exact_mod_cast key

theorem invariantsTensor_apply (l : ℕ) [Fact l.Prime] (Γ : Type v) [Group Γ] [Finite Γ]
    (hΓ : Nat.Coprime (Nat.card Γ) l) {N : Type w} [AddCommGroup N] [Module (ZMod l) N]
    [Module.Finite (ZMod l) N] (σ : Representation (ZMod l) Γ N) (X : Type u) [AddCommGroup X]
    [Module (ZMod l) X] [Finite X] (ρ : Representation (ZMod l) Γ X) :
    (invariantsTensor.{u} l Γ hΓ σ).toFun X ρ = Module.finrank (ZMod l) (ρ.tprod σ).invariants :=
  rfl

end AdditiveFunction

-- from AdditiveSnake.lean
open Representation

section Intertwining

variable {k Γ X Y : Type*} [CommRing k] [Monoid Γ] [AddCommGroup X] [Module k X]
  [AddCommGroup Y] [Module k Y] {ρ : Representation k Γ X} {σ : Representation k Γ Y}
  {φ : X →ₗ[k] Y}

theorem ker_le_comap_of_isIntertwiningMap (hφ : ρ.IsIntertwiningMap σ φ) (γ : Γ) :
    LinearMap.ker φ ≤ (LinearMap.ker φ).comap (ρ γ) := fun x hx => by
  simp only [Submodule.mem_comap, LinearMap.mem_ker] at hx ⊢
  rw [hφ.isIntertwining, hx, map_zero]

theorem range_le_comap_of_isIntertwiningMap (hφ : ρ.IsIntertwiningMap σ φ) (γ : Γ) :
    LinearMap.range φ ≤ (LinearMap.range φ).comap (σ γ) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨ρ γ x, hφ.isIntertwining γ x⟩

end Intertwining

theorem finite_of_exact {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    (f : X →+ Y) (g : Y →+ Z) (hfg : Function.Exact f g) [Finite X] [Finite Z] : Finite Y := by
  refine (AddMonoidHom.finite_iff_finite_ker_range g).2 ⟨?_, inferInstance⟩
  have hs : (g.ker : Set Y) ⊆ Set.range f := fun y hy => (hfg y).1 hy
  exact ((Set.finite_range f).subset hs).to_subtype

namespace AdditiveFunction

variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)

section Basic

variable {X Y : Type u} [AddCommGroup X] [Module (ZMod l) X] [Finite X]
  [AddCommGroup Y] [Module (ZMod l) Y] [Finite Y]

theorem toFun_eq_zero_of_subsingleton [Subsingleton X] (ρ : Representation (ZMod l) Γ X) :
    d.toFun X ρ = 0 := by
  have h := d.additive ρ ρ ρ 0 0 ⟨fun _ _ => Subsingleton.elim _ _⟩
    ⟨fun _ _ => Subsingleton.elim _ _⟩ (fun _ _ _ => Subsingleton.elim _ _)
    (fun _ => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩)
    (fun _ => ⟨0, Subsingleton.elim _ _⟩)
  omega

theorem toFun_congr (ρ : Representation (ZMod l) Γ X) (σ : Representation (ZMod l) Γ Y)
    (e : X ≃ₗ[ZMod l] Y) (he : ∀ γ x, e (ρ γ x) = σ γ (e x)) :
    d.toFun X ρ = d.toFun Y σ := by
  have h := d.additive ρ σ (Representation.trivial (ZMod l) Γ PUnit.{u + 1}) e.toLinearMap 0
    ⟨he⟩ ⟨fun _ _ => Subsingleton.elim _ _⟩ e.injective
    (fun y => ⟨fun _ => ⟨e.symm y, by simp⟩, fun _ => Subsingleton.elim _ _⟩)
    (fun _ => ⟨0, Subsingleton.elim _ _⟩)
  rw [h, d.toFun_eq_zero_of_subsingleton (X := PUnit.{u + 1}), add_zero]

theorem toFun_eq_ker_add_range (ρ : Representation (ZMod l) Γ X)
    (σ : Representation (ZMod l) Γ Y) (φ : X →ₗ[ZMod l] Y) (hφ : ρ.IsIntertwiningMap σ φ) :
    d.toFun X ρ = d.toFun (LinearMap.ker φ)
        (ρ.subrepresentation _ (ker_le_comap_of_isIntertwiningMap hφ)) +
      d.toFun (LinearMap.range φ)
        (σ.subrepresentation _ (range_le_comap_of_isIntertwiningMap hφ)) :=
  d.additive _ ρ _ (LinearMap.ker φ).subtype φ.rangeRestrict ⟨fun _ _ => rfl⟩
    ⟨fun γ x => Subtype.ext (hφ.isIntertwining γ x)⟩ (Submodule.injective_subtype _)
    (fun y => by
      rw [← LinearMap.exact_subtype_ker_map φ y, Subtype.ext_iff]
      rfl)
    (LinearMap.surjective_rangeRestrict φ)

theorem toFun_subrep_congr (ρ : Representation (ZMod l) Γ X) {p q : Submodule (ZMod l) X}
    (h : p = q) (hp : ∀ γ, p ≤ p.comap (ρ γ)) (hq : ∀ γ, q ≤ q.comap (ρ γ)) :
    d.toFun p (ρ.subrepresentation p hp) = d.toFun q (ρ.subrepresentation q hq) := by
  subst h
  rfl

theorem toFun_range_of_injective (ρ : Representation (ZMod l) Γ X)
    (σ : Representation (ZMod l) Γ Y) (φ : X →ₗ[ZMod l] Y) (hφ : ρ.IsIntertwiningMap σ φ)
    (hinj : Function.Injective φ) :
    d.toFun (LinearMap.range φ)
        (σ.subrepresentation _ (range_le_comap_of_isIntertwiningMap hφ)) = d.toFun X ρ := by
  have : Subsingleton (LinearMap.ker φ) :=
    ⟨fun a b => Subtype.ext (hinj (by rw [LinearMap.mem_ker.1 a.2, LinearMap.mem_ker.1 b.2]))⟩
  rw [d.toFun_eq_ker_add_range ρ σ φ hφ,
    d.toFun_eq_zero_of_subsingleton (X := LinearMap.ker φ), zero_add]

omit [Finite X] in

theorem toFun_range_of_surjective (ρ : Representation (ZMod l) Γ X)
    (σ : Representation (ZMod l) Γ Y) (φ : X →ₗ[ZMod l] Y) (hφ : ρ.IsIntertwiningMap σ φ)
    (hs : Function.Surjective φ) :
    d.toFun (LinearMap.range φ)
        (σ.subrepresentation _ (range_le_comap_of_isIntertwiningMap hφ)) = d.toFun Y σ :=
  d.toFun_congr _ _ (LinearEquiv.ofTop _ (LinearMap.range_eq_top.2 hs)) (fun _ _ => rfl)

end Basic

theorem alternating_sum_six {T₁ T₂ T₃ Q₁ Q₂ Q₃ : Type u}
    [AddCommGroup T₁] [Module (ZMod l) T₁] [Finite T₁]
    [AddCommGroup T₂] [Module (ZMod l) T₂] [Finite T₂]
    [AddCommGroup T₃] [Module (ZMod l) T₃] [Finite T₃]
    [AddCommGroup Q₁] [Module (ZMod l) Q₁] [Finite Q₁]
    [AddCommGroup Q₂] [Module (ZMod l) Q₂] [Finite Q₂]
    [AddCommGroup Q₃] [Module (ZMod l) Q₃] [Finite Q₃]
    (τ₁ : Representation (ZMod l) Γ T₁) (τ₂ : Representation (ZMod l) Γ T₂)
    (τ₃ : Representation (ZMod l) Γ T₃) (κ₁ : Representation (ZMod l) Γ Q₁)
    (κ₂ : Representation (ZMod l) Γ Q₂) (κ₃ : Representation (ZMod l) Γ Q₃)
    (φ₁ : T₁ →ₗ[ZMod l] T₂) (φ₂ : T₂ →ₗ[ZMod l] T₃) (φ₃ : T₃ →ₗ[ZMod l] Q₁)
    (φ₄ : Q₁ →ₗ[ZMod l] Q₂) (φ₅ : Q₂ →ₗ[ZMod l] Q₃)
    (i₁ : τ₁.IsIntertwiningMap τ₂ φ₁) (i₂ : τ₂.IsIntertwiningMap τ₃ φ₂)
    (i₃ : τ₃.IsIntertwiningMap κ₁ φ₃) (i₄ : κ₁.IsIntertwiningMap κ₂ φ₄)
    (i₅ : κ₂.IsIntertwiningMap κ₃ φ₅)
    (h₁ : Function.Injective φ₁) (e₁₂ : Function.Exact φ₁ φ₂) (e₂₃ : Function.Exact φ₂ φ₃)
    (e₃₄ : Function.Exact φ₃ φ₄) (e₄₅ : Function.Exact φ₄ φ₅) (h₅ : Function.Surjective φ₅) :
    d.toFun T₁ τ₁ - d.toFun T₂ τ₂ + d.toFun T₃ τ₃ - d.toFun Q₁ κ₁ + d.toFun Q₂ κ₂ -
      d.toFun Q₃ κ₃ = 0 := by
  have a₂ := d.toFun_eq_ker_add_range τ₂ τ₃ φ₂ i₂
  have a₃ := d.toFun_eq_ker_add_range τ₃ κ₁ φ₃ i₃
  have a₄ := d.toFun_eq_ker_add_range κ₁ κ₂ φ₄ i₄
  have a₅ := d.toFun_eq_ker_add_range κ₂ κ₃ φ₅ i₅
  have k₂ := (d.toFun_subrep_congr τ₂ (LinearMap.exact_iff.1 e₁₂)
    (ker_le_comap_of_isIntertwiningMap i₂) (range_le_comap_of_isIntertwiningMap i₁)).trans
    (d.toFun_range_of_injective τ₁ τ₂ φ₁ i₁ h₁)
  have k₃ := d.toFun_subrep_congr τ₃ (LinearMap.exact_iff.1 e₂₃)
    (ker_le_comap_of_isIntertwiningMap i₃) (range_le_comap_of_isIntertwiningMap i₂)
  have k₄ := d.toFun_subrep_congr κ₁ (LinearMap.exact_iff.1 e₃₄)
    (ker_le_comap_of_isIntertwiningMap i₄) (range_le_comap_of_isIntertwiningMap i₃)
  have k₅ := d.toFun_subrep_congr κ₂ (LinearMap.exact_iff.1 e₄₅)
    (ker_le_comap_of_isIntertwiningMap i₅) (range_le_comap_of_isIntertwiningMap i₄)
  have r₅ := d.toFun_range_of_surjective κ₂ κ₃ φ₅ i₅ h₅
  omega

end AdditiveFunction

instance modN_finite (A : Type*) [AddCommGroup A] [Finite A] (n : ℕ) : Finite (ModN A n) :=
  Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)

section Maps

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (n : ℕ)

def torsNMap (f : A →+ B) : TorsN A n →ₗ[ZMod n] TorsN B n :=
  (f.toIntLinearMap.restrict (p := LinearMap.ker (LinearMap.lsmul ℤ A (n : ℤ)))
    (q := LinearMap.ker (LinearMap.lsmul ℤ B (n : ℤ))) (fun x hx => by
      rw [mem_ker_lsmul_iff] at hx ⊢
      simp [← map_nsmul, hx])).toAddMonoidHom.toZModLinearMap n

@[simp]
theorem coe_torsNMap_apply (f : A →+ B) (x : TorsN A n) :
    ((torsNMap n f x : TorsN B n) : B) = f x :=
  rfl

def modNMap (f : A →+ B) : ModN A n →ₗ[ZMod n] ModN B n :=
  (Submodule.mapQ _ _ f.toIntLinearMap (by
    rintro _ ⟨x, rfl⟩
    exact ⟨f x, by simp⟩)).toAddMonoidHom.toZModLinearMap n

@[simp]
theorem modNMap_mk (f : A →+ B) (x : A) :
    modNMap n f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) :=
  rfl

theorem modN_mk_eq_zero_iff (x : A) :
    (Submodule.Quotient.mk x : ModN A n) = 0 ↔ ∃ y : A, n • y = x := by
  rw [Submodule.Quotient.mk_eq_zero]
  simp

section Connecting

variable {n} (f : A →+ B) (h : B →+ C) (hh : Function.Surjective h)

noncomputable def connectingFun (c : TorsN C n) : ModN A n :=
  Submodule.Quotient.mk (Function.invFun f (n • Function.surjInv hh (c : C)))

variable {f h}
variable (hfh : Function.Exact f h)
include hh hfh

theorem exists_lift (c : TorsN C n) : ∃ b a, h b = c ∧ f a = n • b := by
  refine ⟨Function.surjInv hh (c : C), Function.invFun f (n • Function.surjInv hh (c : C)),
    Function.surjInv_eq hh _, Function.invFun_eq ?_⟩
  refine (hfh _).1 ?_
  rw [map_nsmul, Function.surjInv_eq hh]
  exact (mem_ker_lsmul_iff n (c : C)).1 c.2

variable (hf : Function.Injective f)
include hf

theorem connectingFun_spec (c : TorsN C n) (b : B) (a : A) (hb : h b = c) (ha : f a = n • b) :
    connectingFun f h hh c = Submodule.Quotient.mk a := by
  have h₀ : f (Function.invFun f (n • Function.surjInv hh (c : C))) =
      n • Function.surjInv hh (c : C) :=
    Function.invFun_eq (by
      refine (hfh _).1 ?_
      rw [map_nsmul, Function.surjInv_eq hh]
      exact (mem_ker_lsmul_iff n (c : C)).1 c.2)
  obtain ⟨a₁, ha₁⟩ := (hfh (b - Function.surjInv hh (c : C))).1 (by
    rw [map_sub, hb, Function.surjInv_eq hh, sub_self])
  have key : a - Function.invFun f (n • Function.surjInv hh (c : C)) = n • a₁ := hf (by
    rw [map_sub, ha, h₀, map_nsmul, ha₁, smul_sub])
  rw [connectingFun, Submodule.Quotient.eq]
  exact ⟨-a₁, by simp [← key]⟩

theorem connectingFun_zero : connectingFun f h hh (0 : TorsN C n) = 0 := by
  rw [connectingFun_spec hh hfh hf 0 0 0 (by simp) (by simp)]
  rfl

theorem connectingFun_add (c c' : TorsN C n) :
    connectingFun f h hh (c + c') = connectingFun f h hh c + connectingFun f h hh c' := by
  obtain ⟨b, a, hb, ha⟩ := exists_lift hh hfh c
  obtain ⟨b', a', hb', ha'⟩ := exists_lift hh hfh c'
  rw [connectingFun_spec hh hfh hf c b a hb ha, connectingFun_spec hh hfh hf c' b' a' hb' ha',
    connectingFun_spec hh hfh hf (c + c') (b + b') (a + a') (by simp [hb, hb'])
      (by simp [ha, ha', smul_add])]
  rfl

noncomputable def connecting : TorsN C n →ₗ[ZMod n] ModN A n :=
  AddMonoidHom.toZModLinearMap n
    { toFun := connectingFun f h hh
      map_zero' := connectingFun_zero hh hfh hf
      map_add' := connectingFun_add hh hfh hf }

theorem connecting_apply (c : TorsN C n) : connecting hh hfh hf c = connectingFun f h hh c :=
  rfl

theorem connecting_spec (c : TorsN C n) (b : B) (a : A) (hb : h b = c) (ha : f a = n • b) :
    connecting hh hfh hf c = Submodule.Quotient.mk a :=
  connectingFun_spec hh hfh hf c b a hb ha

omit hh hfh in

theorem torsNMap_injective : Function.Injective (torsNMap n f) := fun _ _ hxy =>
  Subtype.ext (hf (congrArg Subtype.val hxy))

omit hh in

theorem exact_torsNMap_torsNMap : Function.Exact (torsNMap n f) (torsNMap n h) := by
  intro y
  constructor
  · intro hy
    obtain ⟨a, ha⟩ := (hfh (y : B)).1 (congrArg Subtype.val hy)
    refine ⟨⟨a, (mem_ker_lsmul_iff n a).2 (hf ?_)⟩, Subtype.ext ha⟩
    rw [map_nsmul, ha, map_zero]
    exact (mem_ker_lsmul_iff n (y : B)).1 y.2
  · rintro ⟨x, rfl⟩
    exact Subtype.ext ((hfh _).2 ⟨x, rfl⟩)

theorem exact_torsNMap_connecting : Function.Exact (torsNMap n h) (connecting hh hfh hf) := by
  intro c
  obtain ⟨b, a, hb, ha⟩ := exists_lift hh hfh c
  rw [connecting_spec hh hfh hf c b a hb ha, modN_mk_eq_zero_iff]
  constructor
  · rintro ⟨a₁, ha₁⟩
    have hb₁ : n • (b - f a₁) = 0 := by rw [smul_sub, ← ha, ← map_nsmul, ha₁, sub_self]
    refine ⟨⟨b - f a₁, (mem_ker_lsmul_iff n _).2 hb₁⟩, Subtype.ext ?_⟩
    simp [hb, (hfh _).2 ⟨a₁, rfl⟩]
  · rintro ⟨t, rfl⟩
    have h₀ := connecting_spec hh hfh hf (torsNMap n h t) t 0 rfl
      (by rw [map_zero, (mem_ker_lsmul_iff n (t : B)).1 t.2])
    rw [connecting_spec hh hfh hf _ b a hb ha, Submodule.Quotient.eq, sub_zero] at h₀
    simpa [eq_comm] using h₀

theorem exact_connecting_modNMap : Function.Exact (connecting hh hfh hf) (modNMap n f) := by
  intro q
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [modNMap_mk, modN_mk_eq_zero_iff]
  constructor
  · rintro ⟨b, hb⟩
    have hc : h b ∈ LinearMap.ker (LinearMap.lsmul ℤ C (n : ℤ)) := by
      rw [mem_ker_lsmul_iff, ← map_nsmul, hb]
      exact (hfh _).2 ⟨a, rfl⟩
    exact ⟨⟨h b, hc⟩, connecting_spec hh hfh hf _ b a rfl hb.symm⟩
  · rintro ⟨c, hc⟩
    obtain ⟨b, a', hb, ha'⟩ := exists_lift hh hfh c
    rw [connecting_spec hh hfh hf c b a' hb ha', Submodule.Quotient.eq] at hc
    obtain ⟨y, hy⟩ := hc
    refine ⟨b - f y, ?_⟩
    simp only [LinearMap.lsmul_apply, natCast_zsmul] at hy
    rw [smul_sub, ← ha', ← map_nsmul, ← map_sub, hy, sub_sub_cancel]

omit hf in

theorem exact_modNMap_modNMap : Function.Exact (modNMap n f) (modNMap n h) := by
  intro q
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [modNMap_mk, modN_mk_eq_zero_iff]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨b', rfl⟩ := hh c
    obtain ⟨a, ha⟩ := (hfh (b - n • b')).1 (by rw [map_sub, map_nsmul, hc, sub_self])
    refine ⟨Submodule.Quotient.mk a, ?_⟩
    rw [modNMap_mk, ha, Submodule.Quotient.eq]
    exact ⟨-b', by simp⟩
  · rintro ⟨q', hq'⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q'
    rw [modNMap_mk, Submodule.Quotient.eq] at hq'
    obtain ⟨y, hy⟩ := hq'
    simp only [LinearMap.lsmul_apply, natCast_zsmul] at hy
    refine ⟨-h y, ?_⟩
    rw [smul_neg, ← map_nsmul, hy, map_sub, (hfh _).2 ⟨a, rfl⟩, zero_sub, neg_neg]

omit hfh hf in

theorem modNMap_surjective : Function.Surjective (modNMap n h) := by
  intro q
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨b, rfl⟩ := hh c
  exact ⟨Submodule.Quotient.mk b, rfl⟩

end Connecting

end Maps

section Equivariant

variable {Γ : Type*} [Group Γ] {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [DistribMulAction Γ A] [DistribMulAction Γ B] [DistribMulAction Γ C] (n : ℕ)

theorem isIntertwiningMap_torsNMap {f : A →+ B} (hfγ : ∀ (γ : Γ) (a : A), f (γ • a) = γ • f a) :
    (torsNRep Γ A n).IsIntertwiningMap (torsNRep Γ B n) (torsNMap n f) :=
  ⟨fun γ x => Subtype.ext (hfγ γ x)⟩

theorem isIntertwiningMap_modNMap {f : A →+ B} (hfγ : ∀ (γ : Γ) (a : A), f (γ • a) = γ • f a) :
    (modNRep Γ A n).IsIntertwiningMap (modNRep Γ B n) (modNMap n f) :=
  ⟨fun γ x => by
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact congrArg Submodule.Quotient.mk (hfγ γ a)⟩

theorem isIntertwiningMap_connecting {n : ℕ} {f : A →+ B} {h : B →+ C}
    (hh : Function.Surjective h) (hfh : Function.Exact f h) (hf : Function.Injective f)
    (hfγ : ∀ (γ : Γ) (a : A), f (γ • a) = γ • f a) (hhγ : ∀ (γ : Γ) (b : B), h (γ • b) = γ • h b) :
    (torsNRep Γ C n).IsIntertwiningMap (modNRep Γ A n) (connecting hh hfh hf) :=
  ⟨fun γ c => by
    obtain ⟨b, a, hb, ha⟩ := exists_lift hh hfh c
    rw [connecting_spec hh hfh hf c b a hb ha,
      connecting_spec hh hfh hf _ (γ • b) (γ • a) (by rw [hhγ, hb]; rfl)
        (by rw [hfγ, ha, smul_comm])]
    rfl⟩

end Equivariant

section Finiteness

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] {n : ℕ}
  {f : A →+ B} {h : B →+ C}

theorem finite_torsN_of_exact (hfh : Function.Exact f h) (hf : Function.Injective f)
    [Finite (TorsN A n)] [Finite (TorsN C n)] : Finite (TorsN B n) :=
  finite_of_exact (torsNMap n f).toAddMonoidHom (torsNMap n h).toAddMonoidHom
    (exact_torsNMap_torsNMap hfh hf)

theorem finite_modN_of_exact (hh : Function.Surjective h) (hfh : Function.Exact f h)
    [Finite (ModN A n)] [Finite (ModN C n)] : Finite (ModN B n) :=
  finite_of_exact (modNMap n f).toAddMonoidHom (modNMap n h).toAddMonoidHom
    (exact_modNMap_modNMap hh hfh)

theorem finite_torsN_of_injective (hf : Function.Injective f) [Finite (TorsN B n)] :
    Finite (TorsN A n) :=
  Finite.of_injective _ (torsNMap_injective hf)

theorem finite_modN_of_surjective (hh : Function.Surjective h) [Finite (ModN B n)] :
    Finite (ModN C n) :=
  Finite.of_surjective _ (modNMap_surjective hh)

end Finiteness

section Actions

variable {Γ : Type*} [Monoid Γ] {A : Type*} [AddCommGroup A] [DistribMulAction Γ A]

abbrev subgroupDistribMulAction (H : AddSubgroup A) (hH : ∀ (γ : Γ) (a : A), a ∈ H → γ • a ∈ H) :
    DistribMulAction Γ H where
  smul γ a := ⟨γ • (a : A), hH γ a a.2⟩
  one_smul a := Subtype.ext (one_smul Γ (a : A))
  mul_smul γ δ a := Subtype.ext (mul_smul γ δ (a : A))
  smul_zero γ := Subtype.ext (smul_zero γ)
  smul_add γ a b := Subtype.ext (smul_add γ (a : A) b)

abbrev quotientDistribMulAction (H : AddSubgroup A) (hH : ∀ (γ : Γ) (a : A), a ∈ H → γ • a ∈ H) :
    DistribMulAction Γ (A ⧸ H) where
  smul γ := QuotientAddGroup.map H H (DistribSMul.toAddMonoidHom A γ) (fun a ha => hH γ a ha)
  one_smul x := by
    induction x using QuotientAddGroup.induction_on with
    | H a => exact congrArg QuotientAddGroup.mk (one_smul Γ a)
  mul_smul γ δ x := by
    induction x using QuotientAddGroup.induction_on with
    | H a => exact congrArg QuotientAddGroup.mk (mul_smul γ δ a)
  smul_zero γ := map_zero _
  smul_add γ x y := map_add _ x y

end Actions

namespace AdditiveFunction

variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)

theorem g_add {A B C : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [DistribMulAction Γ A] [DistribMulAction Γ B] [DistribMulAction Γ C] (f : A →+ B)
    (h : B →+ C) (hfγ : ∀ (γ : Γ) (a : A), f (γ • a) = γ • f a)
    (hhγ : ∀ (γ : Γ) (b : B), h (γ • b) = γ • h b) (hf : Function.Injective f)
    (hfh : Function.Exact f h) (hh : Function.Surjective h)
    [Finite (ModN A l)] [Finite (TorsN A l)] [Finite (ModN C l)] [Finite (TorsN C l)] :
    d.g B = d.g A + d.g C := by
  have := finite_torsN_of_exact (n := l) hfh hf
  have := finite_modN_of_exact (n := l) hh hfh
  rw [d.g_eq A, d.g_eq B, d.g_eq C]
  have := d.alternating_sum_six (torsNRep Γ A l) (torsNRep Γ B l) (torsNRep Γ C l)
    (modNRep Γ A l) (modNRep Γ B l) (modNRep Γ C l) (torsNMap l f) (torsNMap l h)
    (connecting hh hfh hf) (modNMap l f) (modNMap l h) (isIntertwiningMap_torsNMap l hfγ)
    (isIntertwiningMap_torsNMap l hhγ) (isIntertwiningMap_connecting hh hfh hf hfγ hhγ)
    (isIntertwiningMap_modNMap l hfγ) (isIntertwiningMap_modNMap l hhγ) (torsNMap_injective hf)
    (exact_torsNMap_torsNMap hfh hf) (exact_torsNMap_connecting hh hfh hf)
    (exact_connecting_modNMap hh hfh hf) (exact_modNMap_modNMap hh hfh) (modNMap_surjective hh)
  linarith

end AdditiveFunction

-- from Additive.lean
open Representation

namespace AdditiveFunction

variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)

theorem toFun_prod {X Y : Type u} [AddCommGroup X] [Module (ZMod l) X] [Finite X]
    [AddCommGroup Y] [Module (ZMod l) Y] [Finite Y] (ρ : Representation (ZMod l) Γ X)
    (σ : Representation (ZMod l) Γ Y) :
    d.toFun (X × Y) (ρ.prod σ) = d.toFun X ρ + d.toFun Y σ :=
  d.additive ρ _ σ (LinearMap.inl _ X Y) (LinearMap.snd _ X Y)
    ⟨fun _ _ => by ext <;> simp⟩ ⟨fun _ _ => rfl⟩ LinearMap.inl_injective
    Function.Exact.inl_snd LinearMap.snd_surjective

theorem toFun_pi {X : Type u} [AddCommGroup X] [Module (ZMod l) X] [Finite X]
    (ρ : Representation (ZMod l) Γ X) (n : ℕ) :
    d.toFun (Fin n → X) (piRep (Fin n) ρ) = n * d.toFun X ρ := by
  induction n with
  | zero => simp [d.toFun_eq_zero_of_subsingleton (X := Fin 0 → X)]
  | succ n ih =>
    rw [← d.toFun_congr (ρ.prod (piRep (Fin n) ρ)) (piRep (Fin (n + 1)) ρ)
      (Fin.consLinearEquiv (ZMod l) (fun _ => X)) ?_, d.toFun_prod, ih]
    · push_cast
      ring
    · intro γ x
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem g_eq_of_torsion_trivial (A : Type u) [AddCommGroup A] [DistribMulAction Γ A]
    [Finite (ModN A l)] (hA : ∀ a : A, l • a = 0 → a = 0) :
    d.g A = d.toFun (ModN A l) (modNRep Γ A l) := by
  have : Subsingleton (TorsN A l) := ⟨fun x y => Subtype.ext (by
    rw [hA x ((mem_ker_lsmul_iff l (x : A)).1 x.2), hA y ((mem_ker_lsmul_iff l (y : A)).1 y.2)])⟩
  rw [d.g_eq A, d.toFun_eq_zero_of_subsingleton (X := TorsN A l), sub_zero]

theorem g_eq_zero_of_nsmul_eq_zero (A : Type u) [AddCommGroup A] [DistribMulAction Γ A]
    (hA : ∀ a : A, l • a = 0) : d.g A = 0 := by
  by_cases hfin : Finite (ModN A l) ∧ Finite (TorsN A l)
  · obtain ⟨_, _⟩ := hfin
    rw [d.g_eq A, sub_eq_zero]
    let φ : A →ₗ[ℤ] TorsN A l :=
      LinearMap.codRestrict _ LinearMap.id (fun a => (mem_ker_lsmul_iff l a).2 (hA a))
    let ψ := (LinearMap.range (LinearMap.lsmul ℤ A (l : ℤ))).liftQ φ (by
      rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker]
      exact Subtype.ext (by simpa [φ] using hA y))
    refine d.toFun_congr _ _ (LinearEquiv.ofBijective (ψ.toAddMonoidHom.toZModLinearMap l)
      ⟨fun x y hxy => ?_, fun t => ⟨Submodule.Quotient.mk (t : A), Subtype.ext rfl⟩⟩) ?_
    · obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact congrArg _ (congrArg Subtype.val hxy : (a : A) = b)
    · intro γ x
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl
  · exact d.g_of_not_finite A hfin

theorem g_eq_zero_of_finite (A : Type u) [AddCommGroup A] [DistribMulAction Γ A] [Finite A] :
    d.g A = 0 := by
  suffices H : ∀ (N : ℕ) (A : Type u) [AddCommGroup A] [DistribMulAction Γ A] [Finite A],
      Nat.card A = N → d.g A = 0 from H _ A rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro A _ _ _ hN
  by_cases hA : ∀ a : A, l • a = 0 → a = 0
  · have hs : Function.Surjective (fun a : A => l • a) :=
      Finite.injective_iff_surjective.1 (fun a b hab =>
        sub_eq_zero.1 (hA (a - b) (by rw [smul_sub, sub_eq_zero]; exact hab)))
    have : Subsingleton (ModN A l) := ⟨fun x y => by
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨a', rfl⟩ := hs a
      obtain ⟨b', rfl⟩ := hs b
      rw [(modN_mk_eq_zero_iff l _).2 ⟨a', rfl⟩, (modN_mk_eq_zero_iff l _).2 ⟨b', rfl⟩]⟩
    rw [d.g_eq_of_torsion_trivial A hA, d.toFun_eq_zero_of_subsingleton (X := ModN A l)]
  · push Not at hA
    obtain ⟨a₀, ha₀, hne⟩ := hA
    let m : A →+ A := (LinearMap.lsmul ℤ A (l : ℤ)).toAddMonoidHom
    have hm : ∀ a, m a = l • a := fun a => by simp [m]
    have hK : ∀ (γ : Γ) (a : A), a ∈ m.ker → γ • a ∈ m.ker := fun γ a ha => by
      rw [AddMonoidHom.mem_ker, hm] at ha ⊢
      rw [← smul_comm γ l a, ha, smul_zero]
    have hH : ∀ (γ : Γ) (a : A), a ∈ m.range → γ • a ∈ m.range := by
      rintro γ _ ⟨b, rfl⟩
      exact ⟨γ • b, by rw [hm, hm, smul_comm]⟩
    let _ := subgroupDistribMulAction m.ker hK
    let _ := subgroupDistribMulAction m.range hH
    have hKl : ∀ x : m.ker, l • x = 0 := fun x =>
      Subtype.ext (by rw [AddSubgroup.coe_nsmul, ← hm]; exact x.2)
    have hcard : Nat.card m.range < N := by
      have h₁ : Nat.card A = Nat.card m.range * Nat.card m.ker := by
        rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup m.ker,
          Nat.card_congr (QuotientAddGroup.quotientKerEquivRange m).toEquiv]
      have h₂ : 1 < Nat.card m.ker := by
        have : Nontrivial m.ker :=
          ⟨⟨⟨a₀, by rw [AddMonoidHom.mem_ker, hm, ha₀]⟩, 0, fun h => hne (congrArg Subtype.val h)⟩⟩
        exact Finite.one_lt_card
      have h₃ : 0 < Nat.card m.range := Nat.card_pos
      rw [← hN, h₁]
      nlinarith
    have e := d.g_add m.ker.subtype m.rangeRestrict (fun _ _ => rfl)
      (fun γ a => Subtype.ext (show m (γ • a) = γ • m a by rw [hm, hm, smul_comm]))
      (AddSubgroup.subtype_injective _)
      (fun y => ⟨fun hy => ⟨⟨y, congrArg Subtype.val hy⟩, rfl⟩,
        by rintro ⟨x, rfl⟩; exact Subtype.ext (AddMonoidHom.mem_ker.1 x.2)⟩)
      m.rangeRestrict_surjective
    rw [e, d.g_eq_zero_of_nsmul_eq_zero _ hKl, ih _ hcard _ rfl, add_zero]

theorem g_eq_of_finite_cokernel {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction Γ A] [DistribMulAction Γ B] (f : B →+ A)
    (hfγ : ∀ (γ : Γ) (b : B), f (γ • b) = γ • f b) (hf : Function.Injective f)
    [Finite (A ⧸ f.range)] [Finite (ModN B l)] [Finite (TorsN B l)] : d.g A = d.g B := by
  have hR : ∀ (γ : Γ) (a : A), a ∈ f.range → γ • a ∈ f.range := by
    rintro γ _ ⟨b, rfl⟩
    exact ⟨γ • b, hfγ γ b⟩
  let _ := quotientDistribMulAction f.range hR
  rw [d.g_add f (QuotientAddGroup.mk' f.range) hfγ (fun _ _ => rfl) hf
    (fun y => by rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]; rfl)
    (QuotientAddGroup.mk'_surjective _), d.g_eq_zero_of_finite (A ⧸ f.range), add_zero]

theorem g_eq_of_finite_cokernel' {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction Γ A] [DistribMulAction Γ B] (f : B →+ A)
    (hfγ : ∀ (γ : Γ) (b : B), f (γ • b) = γ • f b) (hf : Function.Injective f)
    [Finite (A ⧸ f.range)] [Finite (ModN A l)] [Finite (TorsN A l)] : d.g A = d.g B := by
  have hfh : Function.Exact f (QuotientAddGroup.mk' f.range) :=
    fun y => by rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]; rfl
  have hh := QuotientAddGroup.mk'_surjective f.range
  have := finite_torsN_of_injective (n := l) hf
  have : Finite (ModN B l) :=
    finite_of_exact (connecting hh hfh hf).toAddMonoidHom (modNMap l f).toAddMonoidHom
      (exact_connecting_modNMap hh hfh hf)
  exact d.g_eq_of_finite_cokernel f hfγ hf

theorem g_of_trivial_int [NeZero l] (A : Type u) [AddCommGroup A] [DistribMulAction Γ A]
    (htriv : ∀ (γ : Γ) (a : A), γ • a = a) (e : A ≃+ ℤ) : d.g A = d.one := by
  have hA : ∀ a : A, l • a = 0 → a = 0 := fun a ha => by
    have h := congrArg e ha
    rw [map_nsmul, map_zero, nsmul_eq_mul] at h
    have h' := (mul_eq_zero.1 h).resolve_left (by exact_mod_cast NeZero.ne l)
    exact e.injective (by rw [h', map_zero])
  let b : Module.Basis Unit ℤ A := (Module.Basis.singleton Unit ℤ).map e.symm.toIntLinearEquiv
  let E : ModN A l ≃ₗ[ZMod l] ULift.{u} (ZMod l) := (ModN.basis b).equivFun.trans
    ((LinearEquiv.funUnique Unit (ZMod l) (ZMod l)).trans ULift.moduleEquiv.symm)
  have : Finite (ModN A l) := Finite.of_equiv _ E.symm.toEquiv
  rw [d.g_eq_of_torsion_trivial A hA]
  refine d.toFun_congr _ _ E (fun γ x => ?_)
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [modNRep_mk, htriv]
  rfl

end AdditiveFunction

end Langlands.GaloisCohomology.Local
