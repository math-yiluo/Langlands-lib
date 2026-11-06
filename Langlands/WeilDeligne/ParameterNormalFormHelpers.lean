import Langlands.WeilDeligne.BlockStatements
import Langlands.Weil.Representation.FiniteIndexRestrictionSemisimplicityProof
import Langlands.Weil.Representation.ContinuityProof
import Langlands.Weil.Representation.InertiaOperations
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Semisimple

/-!
# Helper lemmas for the block normal form of Frobenius-semisimple parameters

Semisimplicity of componentwise endomorphisms, and both directions of Tate's
criterion (Tate 1979, 4.1.3): with finite inertia image, a representation is
semisimple exactly when Frobenius acts semisimply.
-/

noncomputable section

open Polynomial

namespace Langlands.WeilDeligneRepresentation.ParameterNormalForm

section SemisimpleEndomorphisms

variable {K : Type*} [Field K]

/-- A componentwise endomorphism of a finite product is semisimple when every
component is. -/
theorem isSemisimple_pi {ι : Type*} [Finite ι] {V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (f : ∀ i, Module.End K (V i)) (hf : ∀ i, Module.End.IsSemisimple (f i)) :
    Module.End.IsSemisimple
      (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i : Module.End K (∀ i, V i)) := by
  have : ∀ i, IsSemisimpleModule K[X] (Module.AEval' (f i)) := hf
  let e : Module.AEval' (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i :
      Module.End K (∀ i, V i)) ≃ₗ[K[X]] ∀ i, Module.AEval' (f i) :=
    LinearEquiv.ofAEval _ (LinearEquiv.piCongrRight fun i => Module.AEval'.of (f i))
      (fun m => by
        funext i
        simp [Module.AEval'.X_smul_of])
  exact IsSemisimpleModule.congr e

/-- A componentwise endomorphism of a direct sum is semisimple when every
component is. -/
theorem isSemisimple_lmap {ι : Type*} {V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (f : ∀ i, Module.End K (V i)) (hf : ∀ i, Module.End.IsSemisimple (f i)) :
    Module.End.IsSemisimple (DirectSum.lmap f) := by
  have : ∀ i, IsSemisimpleModule K[X] (Module.AEval' (f i)) := hf
  let e : Module.AEval' (DirectSum.lmap f) ≃ₗ[K[X]] Π₀ i, Module.AEval' (f i) :=
    LinearEquiv.ofAEval _
      (DFinsupp.mapRange.linearEquiv fun i => Module.AEval'.of (f i))
      (fun m => by
        ext i
        simp only [DFinsupp.smul_apply]
        exact (Module.AEval'.X_smul_of (f i) (m i)).symm)
  exact IsSemisimpleModule.congr e

/-- On `V ⊗ K^m`, the operator `f ⊗ diag(1, c, ..., c^(m-1))` is semisimple when `f` is. -/
theorem isSemisimple_map_diag {V : Type*} [AddCommGroup V] [Module K V]
    (f : Module.End K V) (hf : Module.End.IsSemisimple f) (c : K) (m : ℕ) :
    Module.End.IsSemisimple (TensorProduct.map f
      (LinearMap.pi fun j : Fin m => c ^ j.val • (LinearMap.proj j : (Fin m → K) →ₗ[K] K))) := by
  classical
  rw [LinearEquiv.isSemisimple_iff _
    (LinearMap.pi fun j : Fin m => (c ^ j.val • f) ∘ₗ LinearMap.proj j)
    (TensorProduct.piScalarRight K K V (Fin m))]
  · exact isSemisimple_pi _ fun j => Module.End.IsSemisimple_smul _ hf
  · apply TensorProduct.ext'
    intro v w
    funext j
    simp [TensorProduct.piScalarRightHom_tmul, smul_smul, mul_comm]

end SemisimpleEndomorphisms

section Zpowers

variable {k : Type*} [Field k] {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module k V]

/-- In finite dimension, a subspace stable under `ρ Φ` is stable under every
integral power `ρ (Φ ^ n)`. -/
theorem zpow_mem_of_mem [FiniteDimensional k V] (ρ : Representation k G V) (Φ : G)
    {p : Submodule k V} (hp : ∀ v ∈ p, ρ Φ v ∈ p) (n : ℤ) : ∀ v ∈ p, ρ (Φ ^ n) v ∈ p := by
  let S : Submonoid G :=
    { carrier := {x | ∀ v ∈ p, ρ x v ∈ p}
      mul_mem' := fun {x y} hx hy v hv => by
        rw [map_mul, Module.End.mul_apply]
        exact hx _ (hy v hv)
      one_mem' := fun v hv => by simpa using hv }
  have hΦ : Φ ∈ S := hp
  have hΦinv : Φ⁻¹ ∈ S := by
    intro v hv
    have hinj : Function.Injective ((ρ Φ).restrict hp) := by
      intro x y hxy
      have h1 : ρ Φ (x : V) = ρ Φ (y : V) := congrArg Subtype.val hxy
      have h2 := congrArg (ρ Φ⁻¹) h1
      simp only [Representation.inv_self_apply] at h2
      exact Subtype.ext h2
    obtain ⟨w, hw⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨v, hv⟩
    have hw' : ρ Φ (w : V) = v := congrArg Subtype.val hw
    rw [← hw', Representation.inv_self_apply]
    exact w.2
  rcases n with n | n
  · rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact S.pow_mem hΦ n
  · rw [zpow_negSucc, ← inv_pow]
    exact S.pow_mem hΦinv (n + 1)

/-- If every element acts as an integral power of `ρ Φ` and `ρ Φ` is
semisimple, then `ρ` is semisimple. -/
theorem isSemisimpleRepresentation_of_zpow [FiniteDimensional k V]
    (ρ : Representation k G V) (Φ : G) (hρ : ∀ g, ∃ n : ℤ, ρ g = ρ (Φ ^ n))
    (hΦ : Module.End.IsSemisimple (ρ Φ)) : Representation.IsSemisimpleRepresentation ρ := by
  refine ⟨fun W => ?_⟩
  obtain ⟨q, hq, hWq⟩ := Module.End.isSemisimple_iff.mp hΦ W.toSubmodule
    ((fun v hv => W.apply_mem_toSubmodule Φ hv))
  refine ⟨⟨q, fun g v hv => ?_⟩, FiniteIndexSemisimplicity.isCompl_of_isCompl_toSubmodule hWq⟩
  obtain ⟨n, hn⟩ := hρ g
  rw [hn]
  exact zpow_mem_of_mem ρ Φ (p := q) (fun v hv => hq hv) n v hv

/-- If every element acts as an integral power of `ρ Φ` and `ρ` is semisimple,
then `ρ Φ` is semisimple. -/
theorem isSemisimple_of_zpow [FiniteDimensional k V]
    (ρ : Representation k G V) (Φ : G) (hρ : ∀ g, ∃ n : ℤ, ρ g = ρ (Φ ^ n))
    (hss : Representation.IsSemisimpleRepresentation ρ) : Module.End.IsSemisimple (ρ Φ) := by
  refine Module.End.isSemisimple_iff.mpr fun p hp => ?_
  have hp' : ∀ v ∈ p, ρ Φ v ∈ p := fun v hv => hp hv
  let W : Subrepresentation ρ := ⟨p, fun g v hv => by
    obtain ⟨n, hn⟩ := hρ g
    rw [hn]
    exact zpow_mem_of_mem ρ Φ hp' n v hv⟩
  obtain ⟨Q, hQ⟩ := hss.exists_isCompl W
  exact ⟨Q.toSubmodule, fun v hv => Q.apply_mem_toSubmodule Φ hv, FiniteIndexSemisimplicity.isCompl_toSubmodule hQ⟩

/-- Every element of `zpowers Φ ⊔ ker ρ` acts as an integral power of `ρ Φ`. -/
theorem exists_zpow_of_mem_sup (ρ : Representation k G V) (Φ : G) {h : G}
    (hh : h ∈ Subgroup.zpowers Φ ⊔ ρ.asGroupHom.ker) : ∃ n : ℤ, ρ h = ρ (Φ ^ n) := by
  have hle : Subgroup.zpowers Φ ⊔ ρ.asGroupHom.ker ≤
      (Subgroup.zpowers (ρ.asGroupHom Φ)).comap ρ.asGroupHom := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_zpowers _
    · intro x hx
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
      exact one_mem _
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hle hh)
  refine ⟨n, ?_⟩
  have := congrArg Units.val hn
  rw [← map_zpow, Representation.asGroupHom_apply, Representation.asGroupHom_apply] at this
  exact this.symm

/-- A finite image of `I` gives finitely many elements of `I` representing
every element of `I` modulo the kernel of `ρ`. -/
theorem exists_finite_transversal (ρ : Representation k G V) (I : Subgroup G)
    (hfin : (Set.range (ρ.comp I.subtype)).Finite) :
    ∃ F : Set G, F.Finite ∧ ∀ i ∈ I, ∃ f ∈ F, f⁻¹ * i ∈ ρ.asGroupHom.ker := by
  have : Finite (Set.range (ρ.comp I.subtype)) := hfin.to_subtype
  let s : Set.range (ρ.comp I.subtype) → I := fun x => Classical.choose (Set.mem_range.mp x.2)
  have hs : ∀ x, ρ (s x : G) = x := fun x => Classical.choose_spec (Set.mem_range.mp x.2)
  refine ⟨Set.range fun x => (s x : G), Set.finite_range _, fun i hi => ?_⟩
  let x : Set.range (ρ.comp I.subtype) := ⟨ρ i, ⟨⟨i, hi⟩, rfl⟩⟩
  refine ⟨(s x : G), ⟨x, rfl⟩, ?_⟩
  have hx : ρ (s x : G) = ρ i := hs x
  rw [MonoidHom.mem_ker]
  apply Units.ext
  rw [Representation.asGroupHom_apply, Units.val_one, map_mul, ← hx, ← map_mul, inv_mul_cancel,
    map_one]

end Zpowers

section Degree

variable {G : Type*} [Group G]

/-- If the degree is onto `ℤ` with `Φ` of degree one, `g` has nonzero degree and
`F` represents the kernel of the degree modulo `N`, then `zpowers g ⊔ N` has
finite index. -/
theorem finite_quotient (degree : G →* Multiplicative ℤ) {Φ : G}
    (hΦ : degree Φ = Multiplicative.ofAdd 1) {g : G} (hg : Multiplicative.toAdd (degree g) ≠ 0)
    (N : Subgroup G) {F : Set G} (hF : F.Finite)
    (hFN : ∀ i ∈ degree.ker, ∃ f ∈ F, f⁻¹ * i ∈ N) :
    Finite (G ⧸ (Subgroup.zpowers g ⊔ N)) := by
  set d := Multiplicative.toAdd (degree g) with hd
  have : Finite F := hF.to_subtype
  refine Finite.of_surjective
    (fun x : Fin d.natAbs × F => (QuotientGroup.mk (Φ ^ (x.1 : ℕ) * x.2) : G ⧸ _)) ?_
  intro y
  induction y using QuotientGroup.induction_on with
  | H x =>
  set e := Multiplicative.toAdd (degree x) with he
  set r := e % d with hr
  set t := e / d with ht
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hg
  have hrd : r < d.natAbs := Int.emod_lt _ hg
  have hdiv : d * t + r = e := Int.mul_ediv_add_emod e d
  have hi : Φ ^ (-r) * x * g ^ (-t) ∈ degree.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_zpow, map_zpow, hΦ]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_zpow, toAdd_ofAdd, toAdd_one, smul_eq_mul]
    rw [← he, ← hd]
    linear_combination -hdiv
  obtain ⟨f, hfF, hfN⟩ := hFN _ hi
  refine ⟨(⟨r.toNat, by omega⟩, ⟨f, hfF⟩), ?_⟩
  rw [QuotientGroup.eq]
  have hpow : (Φ ^ r.toNat : G) = Φ ^ r := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hr0]
  have hx : (Φ ^ r.toNat * f)⁻¹ * x = (f⁻¹ * (Φ ^ (-r) * x * g ^ (-t))) * g ^ t := by
    rw [hpow]
    group
  change (Φ ^ r.toNat * f)⁻¹ * x ∈ _
  rw [hx]
  exact mul_mem (Subgroup.mem_sup_right hfN)
    (Subgroup.mem_sup_left (zpow_mem (Subgroup.mem_zpowers g) t))

end Degree

section Tate

universe uG uV

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V]

/-- **Tate 4.1.3, one direction.** If inertia (the kernel of a surjective degree)
has finite image and an element `Φ` of degree one acts semisimply, then the
representation is semisimple. -/
theorem isSemisimpleRepresentation_of_isSemisimple (ρ : Representation ℂ G V)
    (degree : G →* Multiplicative ℤ) {Φ : G} (hΦ : degree Φ = Multiplicative.ofAdd 1)
    (hfin : (Set.range (ρ.comp degree.ker.subtype)).Finite)
    (hss : Module.End.IsSemisimple (ρ Φ)) :
    Representation.IsSemisimpleRepresentation ρ := by
  obtain ⟨F, hF, hFN⟩ := exists_finite_transversal ρ degree.ker hfin
  let H := Subgroup.zpowers Φ ⊔ ρ.asGroupHom.ker
  have : Finite (G ⧸ H) :=
    finite_quotient degree hΦ (g := Φ) (by simp [hΦ]) _ hF hFN
  have : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine (Langlands.Weil.representationFiniteIndexRestrictionSemisimplicity.{uG, uV}
    G H V ρ).mp ?_
  refine isSemisimpleRepresentation_of_zpow (ρ.comp H.subtype)
    ⟨Φ, Subgroup.mem_sup_left (Subgroup.mem_zpowers Φ)⟩ (fun h => ?_) hss
  obtain ⟨n, hn⟩ := exists_zpow_of_mem_sup ρ Φ h.2
  exact ⟨n, by simpa using hn⟩

/-- **Tate 4.1.3, other direction.** If inertia has finite image and `ρ` is
semisimple, then every element of nonzero degree acts semisimply. -/
theorem isSemisimple_of_isSemisimpleRepresentation (ρ : Representation ℂ G V)
    (degree : G →* Multiplicative ℤ) {Φ : G} (hΦ : degree Φ = Multiplicative.ofAdd 1)
    (hfin : (Set.range (ρ.comp degree.ker.subtype)).Finite)
    (hss : Representation.IsSemisimpleRepresentation ρ) {g : G}
    (hg : Multiplicative.toAdd (degree g) ≠ 0) : Module.End.IsSemisimple (ρ g) := by
  obtain ⟨F, hF, hFN⟩ := exists_finite_transversal ρ degree.ker hfin
  let H := Subgroup.zpowers g ⊔ ρ.asGroupHom.ker
  have : Finite (G ⧸ H) := finite_quotient degree hΦ hg _ hF hFN
  have : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hH := (Langlands.Weil.representationFiniteIndexRestrictionSemisimplicity.{uG, uV}
    G H V ρ).mpr hss
  have := isSemisimple_of_zpow (ρ.comp H.subtype)
    ⟨g, Subgroup.mem_sup_left (Subgroup.mem_zpowers g)⟩ (fun h => ?_) hH
  · simpa using this
  · obtain ⟨n, hn⟩ := exists_zpow_of_mem_sup ρ g h.2
    exact ⟨n, by simpa using hn⟩

end Tate

end Langlands.WeilDeligneRepresentation.ParameterNormalForm
