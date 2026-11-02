import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationComodule
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.Flat.Basic

/-! # Invariant rings and exactness for groupoid coactions -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}
variable {M N P : Type v} [AddCommGroup M] [Module B M]
  [AddCommGroup N] [Module B N] [AddCommGroup P] [Module B P]

@[simp]
lemma coactionCompose_tmul {T : Type u} [CommRing T] [Algebra B T]
    (θ : M →+ C ⊗[B] M)
    (hθ : ∀ (b : B) (m : M), θ (b • m) = t b • θ m)
    (φ₁ : C →+* T) (φ₂ : C →ₐ[B] T)
    (h : φ₁.comp (algebraMap B C) = (φ₂ : C →+* T).comp t) (c : C) (m : M) :
    coactionCompose t M θ hθ φ₁ φ₂ h (c ⊗ₜ m) =
      φ₁ c • LinearMap.rTensor M φ₂.toLinearMap (θ m) := by
  rfl

namespace GroupoidCoaction

/-- The ring of functions whose two pullbacks agree. -/
def invariantRing (t : B →+* C) : Subring B :=
  t.eqLocus (algebraMap B C)

@[simp]
lemma mem_invariantRing (b : B) :
    b ∈ invariantRing t ↔ t b = algebraMap B C b :=
  Iff.rfl

/-- The published additive invariants, as a module over the invariant ring. -/
def invariantSubmodule (θ : GroupoidCoaction t M) : Submodule (invariantRing t) M where
  carrier := θ.invariants
  zero_mem' := θ.invariants.zero_mem
  add_mem' := θ.invariants.add_mem
  smul_mem' a m hm := by
    change θ.coaction ((a : B) • m) = (1 : C) ⊗ₜ ((a : B) • m)
    rw [θ.map_smul, show θ.coaction m = (1 : C) ⊗ₜ m from hm, a.property]
    simp [Algebra.algebraMap_eq_smul_one, smul_tmul', tmul_smul]

@[simp]
lemma mem_invariantSubmodule (θ : GroupoidCoaction t M) (m : M) :
    m ∈ θ.invariantSubmodule ↔ m ∈ θ.invariants :=
  Iff.rfl

lemma IsHom.mapsTo_invariants {θM : GroupoidCoaction t M} {θN : GroupoidCoaction t N}
    {f : M →ₗ[B] N} (hf : θM.IsHom θN f) {m : M} (hm : m ∈ θM.invariants) :
    f m ∈ θN.invariants := by
  change θN.coaction (f m) = (1 : C) ⊗ₜ f m
  rw [hf, show θM.coaction m = (1 : C) ⊗ₜ m from hm, LinearMap.lTensor_tmul]

/-- The map on invariant modules induced by an equivariant linear map. -/
def invariantsMap (θM : GroupoidCoaction t M) (θN : GroupoidCoaction t N)
    (f : M →ₗ[B] N) (hf : θM.IsHom θN f) :
    θM.invariantSubmodule →ₗ[invariantRing t] θN.invariantSubmodule where
  toFun m := ⟨f m, hf.mapsTo_invariants m.property⟩
  map_add' m n := Subtype.ext (f.map_add m n)
  map_smul' a m := Subtype.ext (f.map_smul (a : B) m)

@[simp]
lemma invariantsMap_coe (θM : GroupoidCoaction t M) (θN : GroupoidCoaction t N)
    (f : M →ₗ[B] N) (hf : θM.IsHom θN f) (m : θM.invariantSubmodule) :
    (θM.invariantsMap θN f hf m : N) = f m :=
  rfl

lemma IsHom.id (θ : GroupoidCoaction t M) :
    θ.IsHom θ (LinearMap.id : M →ₗ[B] M) := by
  intro m
  simp

lemma IsHom.comp {θM : GroupoidCoaction t M} {θN : GroupoidCoaction t N}
    {θP : GroupoidCoaction t P} {f : M →ₗ[B] N} {g : N →ₗ[B] P}
    (hg : θN.IsHom θP g) (hf : θM.IsHom θN f) :
    θM.IsHom θP (g.comp f) := by
  intro m
  simp only [LinearMap.comp_apply, LinearMap.lTensor_comp_apply]
  rw [hg (f m), hf m]

@[simp]
lemma invariantsMap_id (θ : GroupoidCoaction t M) :
    θ.invariantsMap θ LinearMap.id (IsHom.id θ) = LinearMap.id := by
  rfl

lemma invariantsMap_comp (θM : GroupoidCoaction t M) (θN : GroupoidCoaction t N)
    (θP : GroupoidCoaction t P) (f : M →ₗ[B] N) (g : N →ₗ[B] P)
    (hf : θM.IsHom θN f) (hg : θN.IsHom θP g) :
    θM.invariantsMap θP (g.comp f) (hg.comp hf) =
      (θN.invariantsMap θP g hg).comp (θM.invariantsMap θN f hf) := by
  rfl

lemma invariantsMap_injective (θM : GroupoidCoaction t M) (θN : GroupoidCoaction t N)
    (f : M →ₗ[B] N) (hf : θM.IsHom θN f) (hinj : Function.Injective f) :
    Function.Injective (θM.invariantsMap θN f hf) := by
  intro m n h
  exact Subtype.ext (hinj (congrArg Subtype.val h))

/-- An injective equivariant map reflects invariance when the source algebra is flat. -/
lemma IsHom.mem_invariants_iff [Module.Flat B C]
    {θM : GroupoidCoaction t M} {θN : GroupoidCoaction t N}
    {f : M →ₗ[B] N} (hf : θM.IsHom θN f) (hinj : Function.Injective f) (m : M) :
    f m ∈ θN.invariants ↔ m ∈ θM.invariants := by
  refine ⟨fun hm => ?_, fun hm => hf.mapsTo_invariants hm⟩
  change θM.coaction m = (1 : C) ⊗ₜ m
  apply Module.Flat.lTensor_preserves_injective_linearMap f hinj
  rw [← hf, LinearMap.lTensor_tmul]
  exact hm

/-- Taking invariants preserves exactness at the middle term. -/
lemma invariantsMap_exact [Module.Flat B C]
    (θM : GroupoidCoaction t M) (θN : GroupoidCoaction t N)
    (θP : GroupoidCoaction t P) (i : M →ₗ[B] N) (p : N →ₗ[B] P)
    (hi : θM.IsHom θN i) (hp : θN.IsHom θP p)
    (hinj : Function.Injective i) (hex : LinearMap.range i = LinearMap.ker p) :
    LinearMap.range (θM.invariantsMap θN i hi) =
      LinearMap.ker (θN.invariantsMap θP p hp) := by
  ext n
  constructor
  · rintro ⟨m, rfl⟩
    apply Subtype.ext
    change p (i (m : M)) = 0
    exact LinearMap.mem_ker.mp (hex ▸ LinearMap.mem_range_self i m)
  · intro hn
    have hpn : p (n : N) = 0 := congrArg Subtype.val hn
    obtain ⟨m, hm⟩ := LinearMap.mem_range.mp (hex ▸ LinearMap.mem_ker.mpr hpn)
    have hminv : m ∈ θM.invariants :=
      (hi.mem_invariants_iff hinj m).mp (hm ▸ n.property)
    exact ⟨⟨m, hminv⟩, Subtype.ext hm⟩

/-- The published acyclicity condition gives surjectivity on invariant modules. -/
lemma invariantsMap_surjective_of_isAcyclic
    (θM : GroupoidCoaction t M) (θN : GroupoidCoaction t N)
    (θP : GroupoidCoaction t P) (i : M →ₗ[B] N) (p : N →ₗ[B] P)
    (hi : θM.IsHom θN i) (hp : θN.IsHom θP p)
    (hinj : Function.Injective i) (hsurj : Function.Surjective p)
    (hex : LinearMap.range i = LinearMap.ker p) (hacyclic : θM.IsAcyclic) :
    Function.Surjective (θN.invariantsMap θP p hp) := by
  intro q
  obtain ⟨n, hn, heq⟩ := hacyclic N P θN θP i p hi hp hinj hsurj hex q q.property
  exact ⟨⟨n, hn⟩, Subtype.ext heq⟩

end GroupoidCoaction

end Langlands.AlgebraicGeometry
