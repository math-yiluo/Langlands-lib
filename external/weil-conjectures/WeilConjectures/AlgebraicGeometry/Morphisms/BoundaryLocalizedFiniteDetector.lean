/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.Module

/-!
# Finite restriction detectors at the boundary of an open subscheme

## References

* Stacks Project, Tag 0AVN, finite basic-open restriction argument
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

private lemma common_annihilator {R : Type u} [CommRing R] (D : Submonoid R)
    {ι : Type*} {T : ι → Type u} [∀ i, AddCommGroup (T i)] [∀ i, Module R (T i)]
    (t : (i : ι) → T i) (s : Finset ι) (h : ∀ i ∈ s, ∃ c : D, c • t i = 0) :
    ∃ c : D, ∀ i ∈ s, c • t i = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨a, ha⟩ := h i (Finset.mem_insert_self _ _)
    obtain ⟨b, hb⟩ := ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj))
    refine ⟨a * b, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · rw [mul_comm, mul_smul, ha, smul_zero]
    · rw [mul_smul, hb j hj, smul_zero]

private lemma localized_joint_zero {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {M : Type u} [AddCommGroup M] [Module R M] {n : ℕ}
    (T : Fin n → ModuleCat.{u} R) (g : (i : Fin n) → M →ₗ[R] T i)
    (hg : ∀ m, (∀ i, g i m = 0) → m = 0)
    (z : LocalizedModule.AtPrime p M)
    (hz : ∀ i, IsLocalizedModule.map p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl M)
      (LocalizedModule.mkLinearMap p.primeCompl (T i)) (g i) z = 0) : z = 0 := by
  obtain ⟨⟨m, d⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl M) z
  have h : ∀ i, ∃ c : p.primeCompl, c • g i m = 0 := by
    intro i
    have hi := hz i
    simp only [Function.uncurry_apply_pair, IsLocalizedModule.map_mk',
      IsLocalizedModule.mk'_eq_zero] at hi
    exact (IsLocalizedModule.eq_zero_iff p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl (T i))).mp hi
  obtain ⟨c, hc⟩ := common_annihilator p.primeCompl (fun i ↦ g i m)
    Finset.univ (fun i _ ↦ h i)
  apply (IsLocalizedModule.mk'_eq_zero' _ d).mpr
  refine ⟨c, hg _ (fun i ↦ ?_)⟩
  simpa only [Submonoid.smul_def, map_smul] using hc i (Finset.mem_univ i)

private lemma localized_smul_injective {R : Type u} [CommRing R]
    (p : Ideal R) [p.IsPrime] (T : ModuleCat.{u} R) (r : R)
    (hr : Function.Injective (fun x : T ↦ r • x)) :
    Function.Injective (fun x : LocalizedModule.AtPrime p T ↦ r • x) := by
  let f : T →ₗ[R] T := r • LinearMap.id
  have hf : Function.Injective f := hr
  have hinj := IsLocalizedModule.map_injective p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl T)
    (LocalizedModule.mkLinearMap p.primeCompl T) f hf
  have he : IsLocalizedModule.map p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl T)
      (LocalizedModule.mkLinearMap p.primeCompl T) f = r • LinearMap.id := by
    apply IsLocalizedModule.linearMap_ext p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl T)
      (LocalizedModule.mkLinearMap p.primeCompl T)
    ext x
    simp [f]
  rwa [he] at hinj

set_option backward.isDefEq.respectTransparency false in
/-- Finite localized restriction maps detect sections of a boundary submodule. -/
theorem boundary_localized_finite_detector
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens) (N : L.Modules)
    (hqc : N.IsQuasicoherent) (V : L.Opens) (hV : IsAffineOpen V)
    (S : Submodule (L.presheaf.obj (op V))
      (((Modules.pushforward U.ι).obj
        ((Modules.restrictFunctor U.ι).obj N)).val.obj (op V)))
    (p : Ideal (L.presheaf.obj (op V))) [p.IsPrime]
    (hy : hV.fromSpec ⟨p, inferInstance⟩ ∉ U) :
    ∃ (n : ℕ) (Q : Fin n → ModuleCat.{u} (Localization.AtPrime p))
      (a : Fin n → IsLocalRing.maximalIdeal (Localization.AtPrime p))
      (φ : (i : Fin n) → LocalizedModule.AtPrime p S →ₗ[Localization.AtPrime p] Q i),
      (∀ i, Function.Injective (fun x : Q i ↦ (a i : Localization.AtPrime p) • x)) ∧
      (∀ z, (∀ i, φ i z = 0) → z = 0) := by
  classical
  have _ := hqc
  let R := L.presheaf.obj (op V)
  let F := (Modules.pushforward U.ι).obj ((Modules.restrictFunctor U.ι).obj N)
  have hcompact : IsCompact ((U ⊓ V : L.Opens) : Set L) := by
    have hc := (U.ι.isCompact_preimage hV.isCompact).image U.ι.continuous
    change IsCompact (U.ι.base '' (U.ι.base ⁻¹' (V : Set L))) at hc
    rw [Set.image_preimage_eq_inter_range, Opens.range_ι, Set.inter_comm] at hc
    exact hc
  obtain ⟨s, hs⟩ := hV.exists_finset_basicOpen_eq hcompact (W := U ⊓ V) inf_le_right
  let f : Fin s.card → R := fun i ↦ (s.equivFin.symm i).val
  have hcov : U ⊓ V = ⨆ i, L.basicOpen (f i) := by
    rw [hs, iSup_subtype', ← Equiv.iSup_comp (g := fun x : {x // x ∈ s} ↦
      L.basicOpen x.val) s.equivFin.symm]
  have hle (i : Fin s.card) : L.basicOpen (f i) ≤ U ⊓ V := by
    rw [hcov]
    exact le_iSup (fun i ↦ L.basicOpen (f i)) i
  have hfp (i : Fin s.card) : f i ∈ p := by
    by_contra hi
    apply hy
    have hp : (⟨p, inferInstance⟩ : PrimeSpectrum R) ∈ PrimeSpectrum.basicOpen (f i) := hi
    have hp' : hV.fromSpec ⟨p, inferInstance⟩ ∈ L.basicOpen (f i) := by
      change (⟨p, inferInstance⟩ : PrimeSpectrum R) ∈ hV.fromSpec ⁻¹ᵁ L.basicOpen (f i)
      rwa [hV.fromSpec_preimage_basicOpen]
    exact (hle i hp').1
  let T (i : Fin s.card) : ModuleCat.{u} R :=
    (ModuleCat.restrictScalars
      (L.presheaf.map (homOfLE (L.basicOpen_le (f i))).op).hom).obj
      (F.val.obj (op (L.basicOpen (f i))))
  let g (i : Fin s.card) : S →ₗ[R] T i :=
    { toFun := fun x ↦ F.presheaf.map (homOfLE (L.basicOpen_le (f i))).op x.val
      map_add' := by intros; exact map_add _ _ _
      map_smul' := by
        intro r x
        exact (F.val.map (homOfLE (L.basicOpen_le (f i))).op).hom.map_smul r x.val }
  have hg : ∀ x, (∀ i, g i x = 0) → x = 0 := by
    intro x hx
    apply Subtype.ext
    change (x.val : Γ(F, V)) = 0
    let M := (Modules.restrictFunctor U.ι).obj N
    apply (show TopCat.Sheaf Ab U.toScheme from ⟨M.presheaf, M.isSheaf⟩).eq_of_locally_eq'
      (fun i ↦ U.ι ⁻¹ᵁ L.basicOpen (f i)) (U.ι ⁻¹ᵁ V)
      (fun i ↦ homOfLE (U.ι.preimage_mono (L.basicOpen_le (f i))))
    · intro y hyV
      have hyUV : (y.val : L) ∈ U ⊓ V := ⟨y.property, hyV⟩
      rw [hcov] at hyUV
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hyUV
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
    · intro i
      have hi := hx i
      change F.presheaf.map (homOfLE (L.basicOpen_le (f i))).op x.val = 0 at hi
      change M.presheaf.map
        ((TopologicalSpace.Opens.map U.ι.base).map
          (homOfLE (L.basicOpen_le (f i)))).op x.val = 0 at hi
      have he : (TopologicalSpace.Opens.map U.ι.base).map
          (homOfLE (L.basicOpen_le (f i))) =
          homOfLE (U.ι.preimage_mono (L.basicOpen_le (f i))) := Subsingleton.elim _ _
      rw [he] at hi
      simpa only [map_zero] using hi
  have hreg (i : Fin s.card) : Function.Injective (fun x : T i ↦ f i • x) := by
    have hu := L.toRingedSpace.isUnit_res_basicOpen (f i)
    intro x y hxy
    exact hu.smul_left_cancel.mp hxy
  let Q (i : Fin s.card) : ModuleCat.{u} (Localization.AtPrime p) :=
    ModuleCat.of _ (LocalizedModule.AtPrime p (T i))
  let a (i : Fin s.card) : IsLocalRing.maximalIdeal (Localization.AtPrime p) :=
    ⟨algebraMap R (Localization.AtPrime p) (f i), by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p)]
      exact Ideal.mem_map_of_mem _ (hfp i)⟩
  let φ (i : Fin s.card) : LocalizedModule.AtPrime p S →ₗ[Localization.AtPrime p] Q i :=
    IsLocalizedModule.mapExtendScalars p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl S)
      (LocalizedModule.mkLinearMap p.primeCompl (T i)) (Localization.AtPrime p) (g i)
  refine ⟨s.card, Q, a, φ, ?_, ?_⟩
  · intro i
    change Function.Injective (fun x : LocalizedModule.AtPrime p (T i) ↦
      algebraMap R (Localization.AtPrime p) (f i) • x)
    simpa only [algebraMap_smul] using localized_smul_injective p (T i) (f i) (hreg i)
  · intro z hz
    exact localized_joint_zero p T g hg z hz

end AlgebraicGeometry.Scheme
