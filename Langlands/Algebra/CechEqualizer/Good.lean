import Langlands.Algebra.CechEqualizer.NoetherianGoodCriterion
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Lasker
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.TensorProduct.Maps

open TensorProduct

namespace Langlands.Algebra.CechEqualizer

section Good

variable {A₀ C₀ C₁ : Type*} [CommRing A₀] [CommRing C₀] [CommRing C₁] [Algebra A₀ C₀]
  [Algebra A₀ C₁] (d : C₀ →ₗ[A₀] C₁)


variable {d}

lemma good_of_subsingleton (M : Type*) [AddCommGroup M] [Module A₀ M] [Subsingleton M] :
    Good d M := by
  have h0 : ∀ y : M ⊗[A₀] C₀, y = 0 := fun y => by
    induction y using TensorProduct.inductionOn with
    | tmul m c => simp [Subsingleton.elim m 0]
    | add x y hx hy => rw [hx, hy, add_zero]
  intro y _
  exact ⟨0, by rw [h0 y, zero_tmul]⟩

lemma lTensor_rTensor_apply {M N : Type*} [AddCommGroup M] [Module A₀ M] [AddCommGroup N]
    [Module A₀ N] (f : M →ₗ[A₀] N) (y : M ⊗[A₀] C₀) :
    d.lTensor N (f.rTensor C₀ y) = f.rTensor C₁ (d.lTensor M y) := by
  rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
    LinearMap.comp_apply]

variable (hd : d 1 = 0)
include hd

lemma lTensor_tmul_one {M : Type*} [AddCommGroup M] [Module A₀ M] (m : M) :
    d.lTensor M (m ⊗ₜ 1) = 0 := by
  simp [hd]

/-- Good modules are closed under extensions. -/
lemma good_of_exact [Module.Flat A₀ C₁] {M' M M'' : Type*} [AddCommGroup M'] [Module A₀ M']
    [AddCommGroup M] [Module A₀ M] [AddCommGroup M''] [Module A₀ M'']
    {f : M' →ₗ[A₀] M} {g : M →ₗ[A₀] M''} (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) (h' : Good d M') (h'' : Good d M'') : Good d M := by
  intro y hy
  obtain ⟨m'', hm''⟩ := h'' (g.rTensor C₀ y) (by rw [lTensor_rTensor_apply, hy, map_zero])
  obtain ⟨m, rfl⟩ := hg m''
  have hex := rTensor_exact C₀ hfg hg
  obtain ⟨z, hz⟩ := (hex (y - m ⊗ₜ 1)).mp (by
    rw [map_sub, ← hm'', LinearMap.rTensor_tmul, sub_self])
  have hz0 : d.lTensor M' z = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := C₁) f hf
    rw [map_zero, ← lTensor_rTensor_apply, hz, map_sub, hy, lTensor_tmul_one hd, sub_self]
  obtain ⟨m', rfl⟩ := h' z hz0
  refine ⟨m + f m', ?_⟩
  rw [add_tmul, ← LinearMap.rTensor_tmul, hz]
  abel

/-- Good modules are closed under finite products. -/
lemma good_prod [Module.Flat A₀ C₁] {M₁ M₂ : Type*} [AddCommGroup M₁] [Module A₀ M₁]
    [AddCommGroup M₂] [Module A₀ M₂] (h₁ : Good d M₁) (h₂ : Good d M₂) : Good d (M₁ × M₂) :=
  good_of_exact hd (f := LinearMap.inl A₀ M₁ M₂) (g := LinearMap.snd A₀ M₁ M₂)
    LinearMap.inl_injective Function.Exact.inl_snd LinearMap.snd_surjective h₁ h₂

omit hd in
/-- A module is good if all its finitely generated submodules are good. -/
lemma good_of_fg [Module.Flat A₀ C₁] {N : Type*} [AddCommGroup N] [Module A₀ N]
    (h : ∀ M : Submodule A₀ N, M.FG → Good d M) : Good d N := by
  intro y hy
  obtain ⟨M, hM, hsub⟩ :=
    Submodule.exists_fg_le_subset_range_rTensor_subtype {y} (Set.finite_singleton y)
  obtain ⟨y', rfl⟩ := hsub rfl
  have : d.lTensor M y' = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := C₁) M.subtype
      Subtype.val_injective
    rw [map_zero, ← lTensor_rTensor_apply, hy]
  obtain ⟨m, rfl⟩ := h M hM y' this
  exact ⟨m, by simp⟩

omit hd in
/-- Submodules (more generally, sources of injective maps) of good modules are good. -/
lemma good_of_injective [Module.FaithfullyFlat A₀ C₀] {M N : Type*} [AddCommGroup M]
    [Module A₀ M] [AddCommGroup N] [Module A₀ N] {f : M →ₗ[A₀] N} (hf : Function.Injective f)
    (hN : Good d N) : Good d M := by
  intro y hy
  obtain ⟨n, hn⟩ := hN (f.rTensor C₀ y) (by rw [lTensor_rTensor_apply, hy, map_zero])
  let π := (LinearMap.range f).mkQ
  have hπ : π n = 0 := by
    apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := A₀) (B := C₀)
    have h0 : π.rTensor C₀ (n ⊗ₜ 1) = 0 := by
      rw [hn, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, LinearMap.range_mkQ_comp,
        LinearMap.rTensor_zero, LinearMap.zero_apply]
    rw [LinearMap.rTensor_tmul] at h0
    simpa using congr(TensorProduct.comm A₀ _ C₀ $h0)
  obtain ⟨m, rfl⟩ : n ∈ LinearMap.range f := (Submodule.Quotient.mk_eq_zero _).mp hπ
  refine ⟨m, Module.Flat.rTensor_preserves_injective_linearMap f hf ?_⟩
  rw [LinearMap.rTensor_tmul, hn]

/-- If `K` is good, so is every flat `K`-module. -/
lemma good_of_flat {K V : Type*} [CommRing K] [Algebra A₀ K] [AddCommGroup V] [Module K V]
    [Module A₀ V] [IsScalarTower A₀ K V] [Module.Flat K V] (hK : Good d K) : Good d V := by
  let η : K →ₗ[K] K ⊗[A₀] C₀ :=
    (Algebra.TensorProduct.includeLeft : K →ₐ[K] K ⊗[A₀] C₀).toLinearMap
  let D : K ⊗[A₀] C₀ →ₗ[K] K ⊗[A₀] C₁ := TensorProduct.AlgebraTensorModule.lTensor K K d
  have hex : Function.Exact η D := by
    intro y
    constructor
    · intro hy
      obtain ⟨k, hk⟩ := hK y hy
      exact ⟨k, hk⟩
    · rintro ⟨k, rfl⟩
      simp [η, D, hd]
  have hexV := Module.Flat.lTensor_exact V hex
  let e₀ := TensorProduct.AlgebraTensorModule.cancelBaseChange A₀ K K V C₀
  let e₁ := TensorProduct.AlgebraTensorModule.cancelBaseChange A₀ K K V C₁
  have hD : ∀ z, e₁ (D.lTensor V z) = d.lTensor V (e₀ z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul v x =>
      induction x using TensorProduct.inductionOn with
      | tmul k c => simp [e₀, e₁, D]
      | add x x' hx hx' => simp only [tmul_add, map_add] at hx hx' ⊢; rw [hx, hx']
    | add z z' hz hz' => simp only [map_add, hz, hz']
  have hη : ∀ w, e₀ (η.lTensor V w) = (TensorProduct.rid K V w) ⊗ₜ (1 : C₀) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul v k => simp [e₀, η]
    | add w w' hw hw' => simp only [map_add, hw, hw', add_tmul]
  intro y hy
  have h0 : D.lTensor V (e₀.symm y) = 0 := by
    apply e₁.injective
    rw [hD, LinearEquiv.apply_symm_apply, hy, map_zero]
  obtain ⟨w, hw⟩ := (hexV (e₀.symm y)).mp h0
  refine ⟨TensorProduct.rid K V w, ?_⟩
  rw [← hη, hw, LinearEquiv.apply_symm_apply]

/-- A module killed by the prime `q`, on which every element outside `q` acts injectively,
is good as soon as the residue field of `q` is good. -/
lemma good_of_isTorsionBySet_prime [Module.FaithfullyFlat A₀ C₀] (q : Ideal A₀) [q.IsPrime]
    (hq : Good d q.ResidueField) {S : Type*} [AddCommGroup S] [Module A₀ S]
    (htors : ∀ a ∈ q, ∀ x : S, a • x = 0) (hreg : ∀ s ∉ q, ∀ x : S, s • x = 0 → x = 0) :
    Good d S := by
  let L := LocalizedModule q.primeCompl S
  have htorL : Module.IsTorsionBySet (Localization.AtPrime q) L
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) := by
    rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal q (Localization.AtPrime q),
      Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Module.mem_annihilator]
    intro x
    induction x using LocalizedModule.induction_on with
    | h m s =>
      rw [algebraMap_smul, LocalizedModule.smul'_mk, htors a ha m, LocalizedModule.zero_mk]
  let := htorL.module
  let _ : Field (Localization.AtPrime q ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime q)) :=
    Ideal.Quotient.field _
  have : Module.Flat (Localization.AtPrime q ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime q))
    L := Module.Flat.of_free
  have hκ : Good d (Localization.AtPrime q ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime q)) :=
    hq
  have hL : Good d L := good_of_flat hd hκ
  refine good_of_injective (f := LocalizedModule.mkLinearMap q.primeCompl S) ?_ hL
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨u, hu⟩ := (LocalizedModule.mk_eq (S := q.primeCompl)).mp
    (hx.trans (LocalizedModule.zero_mk 1).symm)
  exact hreg u u.2 x (by simpa [Submonoid.smul_def] using hu)

/-- Coprimary dévissage: a module killed by a power of the prime `q`, on which every element
outside `q` acts injectively, is good as soon as the residue field of `q` is good. -/
lemma good_of_isTorsionBySet_pow [Module.FaithfullyFlat A₀ C₀] [Module.Flat A₀ C₁]
    (q : Ideal A₀) [q.IsPrime] (hq : Good d q.ResidueField) (n : ℕ) :
    ∀ (Q : Type*) [AddCommGroup Q] [Module A₀ Q], (∀ a ∈ q ^ n, ∀ x : Q, a • x = 0) →
      (∀ s ∉ q, ∀ x : Q, s • x = 0 → x = 0) → Good d Q := by
  induction n with
  | zero =>
    intro Q _ _ htors _
    have : Subsingleton Q := ⟨fun x y => by
      rw [← one_smul A₀ x, ← one_smul A₀ y, htors 1 (by simp) x, htors 1 (by simp) y]⟩
    exact good_of_subsingleton Q
  | succ n ih =>
    intro Q _ _ htors hreg
    let S := Submodule.torsionBySet A₀ Q q
    have hS : ∀ x : Q, x ∈ S ↔ ∀ a ∈ q, a • x = 0 := fun x => by
      rw [Submodule.mem_torsionBySet_iff]
      exact ⟨fun h a ha => h ⟨a, ha⟩, fun h a => h a a.2⟩
    refine good_of_exact hd (f := S.subtype) (g := S.mkQ) Subtype.val_injective
      (LinearMap.exact_subtype_mkQ S) S.mkQ_surjective ?_ ?_
    · refine good_of_isTorsionBySet_prime hd q hq (fun a ha x => ?_) (fun s hs x hx => ?_)
      · exact Subtype.ext ((hS x).mp x.2 a ha)
      · exact Subtype.ext (hreg s hs x (congrArg Subtype.val hx))
    · refine ih (Q ⧸ S) (fun a ha x => ?_) (fun s hs x hx => ?_)
      · induction x using Submodule.Quotient.induction_on with
        | H x =>
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hS]
          intro b hb
          rw [smul_smul]
          exact htors _ (by rw [pow_succ']; exact Ideal.mul_mem_mul hb ha) x
      · induction x using Submodule.Quotient.induction_on with
        | H x =>
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hS] at hx
          rw [Submodule.Quotient.mk_eq_zero, hS]
          intro a ha
          apply hreg s hs
          rw [smul_comm]
          exact hx a ha

/-- If every primary component of `⊥` in `M` has a good quotient, `M` is good. -/
lemma good_quotient_finsetInf [Module.FaithfullyFlat A₀ C₀] [Module.Flat A₀ C₁] {M : Type*}
    [AddCommGroup M] [Module A₀ M] (s : Finset (Submodule A₀ M))
    (hs : ∀ J ∈ s, Good d (M ⧸ J)) : Good d (M ⧸ s.inf id) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : Subsingleton (M ⧸ (∅ : Finset (Submodule A₀ M)).inf id) := by
      rw [Finset.inf_empty]
      exact Submodule.Quotient.subsingleton_iff.mpr rfl
    exact good_of_subsingleton _
  | insert J s hJ ih =>
    rw [Finset.inf_insert, id]
    have hJs := hs J (Finset.mem_insert_self J s)
    have hss := ih (fun J' hJ' => hs J' (Finset.mem_insert_of_mem hJ'))
    let K := s.inf id
    have hker : J ⊓ K = LinearMap.ker (J.mkQ.prod K.mkQ) := by
      rw [LinearMap.ker_prod, Submodule.ker_mkQ, Submodule.ker_mkQ]
    refine good_of_injective (f := (J ⊓ K).liftQ (J.mkQ.prod K.mkQ) hker.le) ?_
      (good_prod hd hJs hss)
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot' _ _ hker

/-- Noetherian core: over a noetherian ring, a module is good as soon as the residue fields of
all its associated primes are good. -/
theorem good_of_associatedPrimes [IsNoetherianRing A₀] [Module.FaithfullyFlat A₀ C₀]
    [Module.Flat A₀ C₁] {N : Type*} [AddCommGroup N] [Module A₀ N]
    (h : ∀ (q : Ideal A₀) [q.IsPrime], q ∈ associatedPrimes A₀ N → Good d q.ResidueField) :
    Good d N := by
  refine good_of_fg fun M hM => ?_
  have : IsNoetherian A₀ M := isNoetherian_of_fg_of_noetherian M hM
  obtain ⟨t, ht⟩ := Submodule.IsLasker.exists_isMinimalPrimaryDecomposition
    (Submodule.isLasker A₀ M) ⊥
  have hJ : ∀ J ∈ t, Good d (M ⧸ J) := by
    intro J hJt
    have hprim := ht.primary hJt
    have : (J.colon Set.univ).radical.IsPrime := hprim.isPrime_radical_colon
    have hass : (J.colon Set.univ).radical ∈ associatedPrimes A₀ N :=
      associatedPrimes.subset_of_injective (f := M.subtype) Subtype.val_injective
        (ht.mem_associatedPrimes hJt)
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg (le_refl (J.colon Set.univ).radical)
      (IsNoetherian.noetherian _)
    refine good_of_isTorsionBySet_pow hd _ (h _ hass) n (M ⧸ J) (fun a ha x => ?_)
      (fun s hs x hx => ?_)
    · induction x using Submodule.Quotient.induction_on with
      | H x =>
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        exact Submodule.mem_colon.mp (hn ha) x (Set.mem_univ x)
    · induction x using Submodule.Quotient.induction_on with
      | H x =>
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
        rw [Submodule.Quotient.mk_eq_zero]
        exact (hprim.mem_or_mem hx).resolve_right hs
  have hq := good_quotient_finsetInf hd t hJ
  refine good_of_injective (f := (t.inf id).mkQ) ?_ hq
  rw [← LinearMap.ker_eq_bot, Submodule.ker_mkQ, ht.inf_eq]

end Good

/-- The noetherian good-module criterion holds for independent universes. -/
theorem noetherianGoodCriterion : NoetherianGoodCriterion := by
  intro A₀ C₀ C₁ N _ _ _ _ _ _ _ d hd _ _ _ h
  exact good_of_associatedPrimes hd h


end Langlands.Algebra.CechEqualizer
