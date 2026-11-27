import Langlands.Algebra.NilpotentPresentationLift
import Langlands.Algebra.ResidueTensorNilpotentInjectivity
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.LocalRing.Module

/-! # Exactness and freeness detected by an Artinian residue complex -/

noncomputable section

universe u

open IsLocalRing TensorProduct LinearMap

namespace Langlands.Algebra

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsArtinianRing R]
  {M N P Q : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]

local notation "k" => ResidueField R

private theorem maximalIdeal_nilpotent : IsNilpotent (maximalIdeal R) :=
  (isArtinianRing_iff_isNilpotent_maximalIdeal R).mp inferInstance

private theorem injective_of_residue_injective [Module.Flat R N] (f : M →ₗ[R] N)
    (hf : Function.Injective (f.baseChange k)) : Function.Injective f := by
  obtain ⟨n, hn⟩ := maximalIdeal_nilpotent (R := R)
  have H := residueTensorNilpotentInjectivity R M N R f n inferInstance hf (by
    intro r hr x
    have : r = 0 := Ideal.mem_bot.mp (by simpa only [hn, Ideal.zero_eq_bot] using hr)
    rw [this, zero_smul])
  intro x y he
  apply (TensorProduct.lid R M).symm.injective
  apply H
  exact congrArg (fun z : N => (1 : R) ⊗ₜ[R] z) he

/-- A flat module over a local Artinian ring is free, with basis obtained by
lifting a basis of its residue reduction. -/
theorem free_of_flat_artinian [Module.Flat R M] : Module.Free R M := by
  let b := Module.Free.chooseBasis k (k ⊗[R] M)
  let I := Module.Free.ChooseBasisIndex k (k ⊗[R] M)
  obtain ⟨v, hv⟩ := (quotientTensor_unit_surjective R M (maximalIdeal R)).comp_left b
  let l : (I →₀ R) →ₗ[R] M := Finsupp.linearCombination R v
  let d : Module.Basis I R (I →₀ R) := Finsupp.basisSingleOne
  let E := (d.baseChange k).repr.trans b.repr.symm
  have hl : l.baseChange k = E.toLinearMap := by
    apply (d.baseChange k).ext
    intro i
    have hi : E ((d.baseChange k) i) = b i := by
      change b.repr.symm ((d.baseChange k).repr ((d.baseChange k) i)) = b i
      rw [Module.Basis.repr_self, Module.Basis.repr_symm_single_one]
    rw [LinearEquiv.coe_coe, hi, Module.Basis.baseChange_apply, LinearMap.baseChange_tmul]
    change (1 : k) ⊗ₜ[R] Finsupp.linearCombination R v (Finsupp.single i 1) = b i
    rw [Finsupp.linearCombination_single, one_smul]
    exact congrFun hv i
  refine Module.Free.of_equiv (LinearEquiv.ofBijective l ⟨?_, ?_⟩)
  · exact injective_of_residue_injective l (hl.symm ▸ E.injective)
  · exact surjective_of_nilpotent_baseChange R (I →₀ R) M (maximalIdeal R)
      maximalIdeal_nilpotent l (hl.symm ▸ E.surjective)

/-- An injection on the residue modules into a flat target lifts to a split
injection over the local Artinian ring. -/
theorem splitInjection_of_residue [Module.Flat R N] (f : M →ₗ[R] N)
    (hf : Function.Injective (f.baseChange k)) : ∃ r : N →ₗ[R] M, r.comp f = .id := by
  obtain ⟨r₀, hr₀⟩ := (f.baseChange k).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
  let : Module.Free R N := free_of_flat_artinian
  obtain ⟨r, hr⟩ := liftMapOfQuotientTensor R N M (maximalIdeal R) r₀
  change r.baseChange k = r₀ at hr
  let a := r.comp f
  have ha : a.baseChange k = .id := by
    rw [LinearMap.baseChange_comp, hr, hr₀]
  have hs : Function.Surjective a := surjective_of_nilpotent_baseChange R M M
    (maximalIdeal R) maximalIdeal_nilpotent a (by
      change Function.Surjective (a.baseChange k)
      rw [ha]
      exact fun x => ⟨x, rfl⟩)
  have hfa : Function.Injective ((f.comp a).baseChange k) := by
    rw [LinearMap.baseChange_comp, ha, LinearMap.comp_id]
    exact hf
  have hi : Function.Injective a := fun x y hxy =>
    injective_of_residue_injective (f.comp a) hfa (congrArg f hxy)
  let e := LinearEquiv.ofBijective a ⟨hi, hs⟩
  exact ⟨e.symm.toLinearMap.comp r, LinearMap.ext e.symm_apply_apply⟩

private theorem exact_of_split_residue [Module.Flat R M] [Module.Flat R N] [Module.Flat R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hfg : g.comp f = 0)
    (h : Function.Exact (f.baseChange k) (g.baseChange k)) :
    Function.Exact f g ∧ Module.Flat R f.ker := by
  let π := f.range.mkQ
  let j := f.range.liftQ g (by
    rintro _ ⟨x, rfl⟩
    exact LinearMap.congr_fun hfg x)
  have hj : j.comp π = g := rfl
  have hp : π.comp f = 0 := by
    ext x
    exact (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self f x)
  have hj₀ : Function.Injective (j.baseChange k) := by
    apply LinearMap.ker_eq_bot.mp
    refine le_antisymm (fun q hq => ?_) bot_le
    obtain ⟨x, rfl⟩ := LinearMap.baseChange_surjective k (Submodule.mkQ_surjective _) q
    change j.baseChange k (π.baseChange k x) = 0 at hq
    have hq' : g.baseChange k x = 0 := by
      rwa [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hj] at hq
    obtain ⟨y, hy⟩ := (h x).mp hq'
    have H : π.baseChange k (f.baseChange k y) = 0 := by
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hp, LinearMap.baseChange_zero]
      rfl
    exact (Submodule.mem_bot _).mpr (hy ▸ H)
  obtain ⟨l, hl⟩ := splitInjection_of_residue j hj₀
  have inj : Function.Injective j := Function.LeftInverse.injective (LinearMap.congr_fun hl)
  have Hex : Function.Exact f g := by
    intro x
    change j (π x) = 0 ↔ _
    rw [← map_zero j, inj.eq_iff]
    exact Submodule.Quotient.mk_eq_zero _
  have : Module.Flat R (N ⧸ f.range) := Module.Flat.of_retract j l hl
  let : Module.Free R (N ⧸ f.range) := free_of_flat_artinian
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id (Submodule.mkQ_surjective _)
  obtain ⟨t, ht⟩ := ((Function.Exact.split_tfae (LinearMap.exact_subtype_mkQ f.range)
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)).out 1 2 rfl rfl).mp ⟨s, hs⟩
  have : Module.Flat R f.range := Module.Flat.of_retract f.range.subtype t ht
  let : Module.Free R f.range := free_of_flat_artinian
  obtain ⟨v, hv⟩ := Module.projective_lifting_property f.rangeRestrict LinearMap.id f.surjective_rangeRestrict
  have hseq : Function.Exact f.ker.subtype f.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  obtain ⟨u, hu⟩ := ((Function.Exact.split_tfae hseq (Submodule.injective_subtype _)
    f.surjective_rangeRestrict).out 1 2 rfl rfl).mp ⟨v, hv⟩
  exact ⟨Hex, Module.Flat.of_retract f.ker.subtype u hu⟩

/-- Exactness of a flat complex in a degree can be checked on its residue complex. -/
theorem exact_of_residue_exact [Module.Flat R M] [Module.Flat R N] [Module.Flat R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hfg : g.comp f = 0)
    (h : Function.Exact (f.baseChange k) (g.baseChange k)) : Function.Exact f g :=
  (exact_of_split_residue f g hfg h).1

/-- The first cohomology of a four-term flat complex is free if the residue
complex is exact in degree two and its first arrow is injective. -/
theorem free_h1_of_residue [Module.Flat R N] [Module.Flat R P] [Module.Flat R Q]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : P →ₗ[R] Q)
    (hfg : g.comp f = 0) (hgh : h.comp g = 0)
    (hf : Function.Injective (f.baseChange k))
    (hg : Function.Exact (g.baseChange k) (h.baseChange k)) :
    Module.Free R (g.ker ⧸ (f.codRestrict g.ker (fun x => LinearMap.congr_fun hfg x)).range) := by
  have : Module.Flat R g.ker := (exact_of_split_residue g h hgh hg).2
  let u := f.codRestrict g.ker (fun x => LinearMap.congr_fun hfg x)
  have hu : Function.Injective (u.baseChange k) := by
    intro x y hxy
    apply hf
    have e : g.ker.subtype.comp u = f := rfl
    rw [← e, LinearMap.baseChange_comp, LinearMap.comp_apply, LinearMap.comp_apply, hxy]
  obtain ⟨r, hr⟩ := splitInjection_of_residue u hu
  have hi : Function.Injective u := Function.LeftInverse.injective (LinearMap.congr_fun hr)
  let π := u.range.mkQ
  obtain ⟨s, hs⟩ := ((Function.Exact.split_tfae u.exact_map_mkQ_range hi
    (Submodule.mkQ_surjective _)).out 2 1 rfl rfl).mp ⟨r, hr⟩
  have : Module.Flat R (g.ker ⧸ u.range) := Module.Flat.of_retract s π hs
  exact free_of_flat_artinian

end Langlands.Algebra
