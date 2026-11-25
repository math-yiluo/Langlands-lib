/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import WeilConjectures.RingTheory.FormalGlueingData
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Canonical maps for formal glueing

Source: Stacks Project, More on Algebra, Remark 05EL; Algebra, Lemmas 07K0 and 00DK
(blueprint: lem-weil-pbc-formal-glueing-canonical-maps).

## Main statements
* `LocalizedModule.away_map_functorial`: localization preserves composition, addition and identity.
* `FormalGlueing.localizedSModule_properties`: properties of the induced scalar action.
* `FormalGlueing.swap_properties`: interchange of iterated localizations.
* `FormalGlueing.compare_properties`: localization commutes with extension of scalars.
-/

@[expose] public section

universe u v w v₁ v₂ v₃

open scoped TensorProduct

namespace LocalizedModule

/-- Localization preserves composition, addition and identity (clause (1)).
Source: Stacks Project, Algebra, Definition 07JZ and Lemma 07K0
(blueprint: lem-weil-pbc-formal-glueing-canonical-maps).
Proof, step 1: both composites take q/e^n to h(k(q))/e^n; both sums take it to
(h(q)+h'(q))/e^n; the localized identity fixes every fraction. Fractions exhaust the module. -/
theorem away_map_functorial {R : Type u} [CommRing R]
    {Q : Type v₁} {Q' : Type v₂} {Q'' : Type v₃}
    [AddCommGroup Q] [Module R Q] [AddCommGroup Q'] [Module R Q']
    [AddCommGroup Q''] [Module R Q''] (e : R)
    (k : Q →ₗ[R] Q') (h h' : Q' →ₗ[R] Q'') :
    let T := Submonoid.powers e
    let lQ := mkLinearMap T Q
    let lQ' := mkLinearMap T Q'
    let lQ'' := mkLinearMap T Q''
    IsLocalizedModule.map T lQ lQ'' (h.comp k) =
      (IsLocalizedModule.map T lQ' lQ'' h).comp (IsLocalizedModule.map T lQ lQ' k) ∧
    IsLocalizedModule.map T lQ' lQ'' (h + h') =
      IsLocalizedModule.map T lQ' lQ'' h + IsLocalizedModule.map T lQ' lQ'' h' ∧
    IsLocalizedModule.map T lQ lQ LinearMap.id = LinearMap.id := by
  dsimp only
  exact ⟨IsLocalizedModule.map_comp' _ _ _ _ k h,
    (IsLocalizedModule.map _ _ _).map_add h h', IsLocalizedModule.map_id _ _⟩

end LocalizedModule

namespace FormalGlueing

open CategoryTheory

/-- The induced S-action has the given restricted R-action, the localization map is
S-linear, and localizing an S-linear map gives an S-linear map (clause (1)).
Source: Stacks Project, More on Algebra, Remark 05EL and Algebra, Definition 07JZ
(blueprint: lem-weil-pbc-formal-glueing-canonical-maps).
Proof, step 2: localize the R-linear endomorphisms q ↦ s • q. Step 1 preserves
m₁ = id, mₛ₊ₜ = mₛ + mₜ and mₛₜ = mₛ ∘ mₜ, giving the module laws.
The formula on fractions identifies the restricted R-action and makes the localization
map S-linear. For an S-linear h, h(sq)/e^n = s h(q)/e^n, proving its S-linearity.
The action is the existing `localizedSModule`, defined by exactly this fraction formula. -/
theorem localizedSModule_properties {R : Type u} {S : Type w}
    [CommRing R] [CommRing S] (φ : R →+* S) (e : R)
    (Q : ModuleCat.{v₁} S) (Q' : ModuleCat.{v₂} S) (h : Q →ₗ[S] Q') :
    let m := localizedSModule φ e Q
    let m' := localizedSModule φ e Q'
    (∀ (s : S) (q : Q) (n : ℕ),
      m.smul s (LocalizedModule.mk (show restrict φ Q from q)
        ⟨e ^ n, ⟨n, rfl⟩⟩) =
        LocalizedModule.mk (S := Submonoid.powers e)
          (show restrict φ Q from s • q) ⟨e ^ n, ⟨n, rfl⟩⟩) ∧
    (∀ (r : R) (x : localize e (restrict φ Q)), m.smul (φ r) x = r • x) ∧
    (∀ (s : S) (q : Q),
      LocalizedModule.mk (show restrict φ Q from s • q) 1 =
        m.smul s (LocalizedModule.mk (show restrict φ Q from q) 1)) ∧
    (∀ (s : S) (x : localize e (restrict φ Q)),
      localMap e (restrictMap φ h) (m.smul s x) =
        m'.smul s (localMap e (restrictMap φ h) x)) := by
  dsimp only
  have action (M : ModuleCat.{v₁} S) (s : S) (q : M) (t : Submonoid.powers e) :=
    (exists_localized_s_module φ e M).choose_spec s q t
  have action' (s : S) (q : Q') (t : Submonoid.powers e) :=
    (exists_localized_s_module φ e Q').choose_spec s q t
  refine ⟨fun s q n ↦ action Q s q _, ?_, ?_, ?_⟩
  · intro r x
    induction x using LocalizedModule.induction_on with
    | _ q t =>
      rw [action]
      exact (LocalizedModule.smul'_mk r q t).symm
  · intro s q
    exact (action Q s q 1).symm
  · intro s x
    induction x using LocalizedModule.induction_on with
    | _ q t =>
      rw [action]
      simp only [localMap, IsLocalizedModule.map_LocalizedModules]
      rw [action']
      exact congrArg (fun q ↦ LocalizedModule.mk (show restrict φ Q' from q) t)
        (h.map_smul s q)

private theorem fraction_cancel {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] {T : Submonoid R} (m : M) (t : T) :
    (t : R) • LocalizedModule.mk m t = LocalizedModule.mk m 1 := by
  rw [LocalizedModule.smul'_mk]
  exact LocalizedModule.mk_cancel t m

private theorem smul_bijective_localize {R : Type u} [CommRing R]
    (M : ModuleCat.{v} R) (e r : R)
    (hr : Function.Bijective (fun x : M ↦ r • x)) :
    Function.Bijective (fun x : localize e M ↦ r • x) := by
  let h := algebraMap R (Module.End R M) r
  have heq : localMap e h = algebraMap R (Module.End R (localize e M)) r := by
    ext x
    induction x using LocalizedModule.induction_on with
    | _ m t =>
      simp [localMap, h, IsLocalizedModule.map_LocalizedModules,
        Module.algebraMap_end_apply, LocalizedModule.smul'_mk]
  rw [show (fun x : localize e M ↦ r • x) = localMap e h from
    congrArg DFunLike.coe heq.symm]
  exact ⟨IsLocalizedModule.map_injective _ _ _ h hr.1,
    IsLocalizedModule.map_surjective _ _ _ h hr.2⟩

private theorem powers_units {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (f : R)
    (hf : Function.Bijective (fun x : M ↦ f • x)) (t : Submonoid.powers f) :
    IsUnit (algebraMap R (Module.End R M) t) := by
  obtain ⟨_, ⟨n, rfl⟩⟩ := t
  rw [map_pow]
  exact ((Module.End.isUnit_iff _).mpr hf).pow n

private theorem twice_ext {R : Type u} [CommRing R]
    (P : ModuleCat.{v} R) (f g : R) {N : Type w} [AddCommGroup N] [Module R N]
    (hf : Function.Bijective (fun x : N ↦ f • x))
    (hg : Function.Bijective (fun x : N ↦ g • x))
    {h k : localize g (localize f P) →ₗ[R] N}
    (heq : ∀ p : P, h (LocalizedModule.mk (LocalizedModule.mk p 1) 1) =
      k (LocalizedModule.mk (LocalizedModule.mk p 1) 1)) : h = k := by
  apply IsLocalizedModule.ext (Submonoid.powers g)
    (LocalizedModule.mkLinearMap _ (localize f P)) (powers_units g hg)
  apply IsLocalizedModule.ext (Submonoid.powers f)
    (LocalizedModule.mkLinearMap _ P) (powers_units f hf)
  exact LinearMap.ext heq

/-- Both f and g act bijectively on (P_g)_f. The existing canonical swap is the unique
map specified on P; it has the fraction formula and inverse the reverse swap (clause (2)).
Source: Stacks Project, More on Algebra, Remark 05EL and Algebra, Lemma 07K0
(blueprint: lem-weil-pbc-formal-glueing-canonical-maps).
Proof, steps 3–5: f is invertible by the outer localization; localizing the inverse of
multiplication by g on P_g proves g is invertible too, by step 1. Apply the universal
property first at f and then at g to the composite P → P_g → (P_g)_f. Its values on
fractions are (p/f^a)/g^b ↦ (p/g^b)/f^a. Two applications of uniqueness show that the
values on ((p/1)/1) determine the map. Reversing f and g gives the inverse: both composites
fix every fraction. This also applies to zero denominators and zero localizations. -/
theorem swap_properties {R : Type u} [CommRing R]
    (P : ModuleCat.{v} R) (f g : R) :
    Function.Bijective (fun x : localize f (localize g P) ↦ f • x) ∧
    Function.Bijective (fun x : localize f (localize g P) ↦ g • x) ∧
    (∀ (p : P) (a b : ℕ),
      swap f g P (LocalizedModule.mk
        (LocalizedModule.mk p ⟨f ^ a, ⟨a, rfl⟩⟩) ⟨g ^ b, ⟨b, rfl⟩⟩) =
        LocalizedModule.mk (S := Submonoid.powers f)
          (LocalizedModule.mk (S := Submonoid.powers g) p ⟨g ^ b, ⟨b, rfl⟩⟩)
          ⟨f ^ a, ⟨a, rfl⟩⟩) ∧
    (∀ t : localize g (localize f P) →ₗ[R] localize f (localize g P),
      (∀ p : P, t (LocalizedModule.mk (LocalizedModule.mk p 1) 1) =
        LocalizedModule.mk (LocalizedModule.mk p 1) 1) ↔ t = swap f g P) ∧
    (swap g f P).comp (swap f g P) = LinearMap.id ∧
    (swap f g P).comp (swap g f P) = LinearMap.id := by
  have outer (M : ModuleCat.{v} R) (e : R) :
      Function.Bijective (fun x : localize e M ↦ e • x) :=
    (Module.End.isUnit_iff _).mp
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (Submonoid.powers e) M)
        (⟨e, ⟨1, pow_one e⟩⟩ : Submonoid.powers e))
  have hf : Function.Bijective (fun x : localize f (localize g P) ↦ f • x) :=
    (Module.End.isUnit_iff _).mp
      (IsLocalizedModule.map_units
        (LocalizedModule.mkLinearMap (Submonoid.powers f) (localize g P))
        (⟨f, ⟨1, pow_one f⟩⟩ : Submonoid.powers f))
  have hg := smul_bijective_localize (localize g P) f g (outer P g)
  have base (f g : R) (p : P) :
      swap f g P (LocalizedModule.mk (LocalizedModule.mk p 1) 1) =
        LocalizedModule.mk (LocalizedModule.mk p 1) 1 :=
    (exists_swap f g P).exists.choose_spec p
  refine ⟨hf, hg, ?_, ?_, ?_, ?_⟩
  · intro p a b
    apply ((Module.End.isUnit_iff _).mp
      (powers_units f hf ⟨f ^ a, ⟨a, rfl⟩⟩)).1
    apply ((Module.End.isUnit_iff _).mp
      (powers_units g hg ⟨g ^ b, ⟨b, rfl⟩⟩)).1
    simp only [Module.algebraMap_end_apply, ← map_smul]
    rw [smul_comm (g ^ b) (f ^ a)]
    rw [fraction_cancel _ (⟨g ^ b, ⟨b, rfl⟩⟩ : Submonoid.powers g)]
    rw [LocalizedModule.smul'_mk,
      fraction_cancel _ (⟨f ^ a, ⟨a, rfl⟩⟩ : Submonoid.powers f), base]
    rw [fraction_cancel _ (⟨f ^ a, ⟨a, rfl⟩⟩ : Submonoid.powers f)]
    rw [LocalizedModule.smul'_mk,
      fraction_cancel _ (⟨g ^ b, ⟨b, rfl⟩⟩ : Submonoid.powers g)]
  · intro t
    constructor
    · intro ht
      exact (exists_swap f g P).unique ht (base f g)
    · rintro rfl
      exact base f g
  · have hfg := smul_bijective_localize (localize f P) g f (outer P f)
    apply twice_ext P f g hfg
      ((Module.End.isUnit_iff _).mp
        (IsLocalizedModule.map_units
          (LocalizedModule.mkLinearMap (Submonoid.powers g) (localize f P))
          (⟨g, ⟨1, pow_one g⟩⟩ : Submonoid.powers g)))
    intro p
    simp only [LinearMap.comp_apply, LinearMap.id_apply, base]
  · apply twice_ext P g f hg hf
    intro p
    simp only [LinearMap.comp_apply, LinearMap.id_apply, base]

private noncomputable def tensor_restrict_equiv {R : Type u} {S : Type w}
    [CommRing R] [CommRing S] (φ : R →+* S) (M : ModuleCat.{v} R) :
    letI : Algebra R S := φ.toAlgebra
    (S ⊗[R] M) ≃ₗ[R] restrict φ (extend φ M) := by
  let : Algebra R S := φ.toAlgebra
  exact
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ (algebraMap_smul S r x).symm }

set_option backward.isDefEq.respectTransparency false in
/-- The canonical comparison has the pure-tensor fraction formula, is the unique R-linear
map with its specified values, and is an S-linear isomorphism (clause (3)).
Source: Stacks Project, More on Algebra, Remark 05EL and Algebra, Lemmas 07K0, 00DK, 00D2
(blueprint: lem-weil-pbc-formal-glueing-canonical-maps).
Proof, steps 6–7: tensor P → P_f with S. The inverse of multiplication by f on P_f,
tensored with S, proves invertibility on S ⊗ P_f. The universal property extends the
tensored map uniquely, with (s ⊗ p)/f^n ↦ s ⊗ (p/f^n). Pure tensors generate the
source, and fractions generate its localization, giving uniqueness. The induced S-action
from step 2 makes this formula S-linear. The localization-after-tensor theorem
[lem-weil-pbc-localization-tensor-over-base] identifies it with an R-linear isomorphism;
its inverse is S-linear by applying the forward map to s times an inverse image.
The tensor factors are in Mathlib's extension-of-scalars order S ⊗ P. -/
theorem compare_properties {R : Type u} {S : Type w}
    [CommRing R] [CommRing S] (φ : R →+* S) (P : ModuleCat.{v} R) (f : R) :
    letI : Algebra R S := φ.toAlgebra
    Function.Bijective (fun x : restrict φ (extend φ (localize f P)) ↦ f • x) ∧
    (∀ (p : P) (s : S) (n : ℕ),
      compare φ f P (LocalizedModule.mk
        (show restrict φ (extend φ P) from s ⊗ₜ[R] p) ⟨f ^ n, ⟨n, rfl⟩⟩) =
        (show restrict φ (extend φ (localize f P)) from
          s ⊗ₜ[R] LocalizedModule.mk p ⟨f ^ n, ⟨n, rfl⟩⟩)) ∧
    (∀ t : localize f (restrict φ (extend φ P)) →ₗ[R]
        restrict φ (extend φ (localize f P)),
      (∀ (p : P) (s : S),
        t (LocalizedModule.mk (show restrict φ (extend φ P) from s ⊗ₜ[R] p) 1) =
          (show restrict φ (extend φ (localize f P)) from
            s ⊗ₜ[R] LocalizedModule.mk p 1)) ↔ t = compare φ f P) ∧
    (∀ (s : S) (x : localize f (restrict φ (extend φ P))),
      compare φ f P ((localizedSModule φ f (extend φ P)).smul s x) =
        (s • (compare φ f P x : extend φ (localize f P)))) ∧
    Function.Bijective (compare φ f P) := by
  let : Algebra R S := φ.toAlgebra
  let T := Submonoid.powers f
  let ell := LocalizedModule.mkLinearMap T P
  let t : restrict φ (extend φ P) →ₗ[R] restrict φ (extend φ (localize f P)) :=
    restrictMap φ (extendMap φ (M := P) (N := localize f P) ell)
  have : IsLocalizedModule T t := by
    let rt := TensorProduct.AlgebraTensorModule.rTensor R S ell
    let pre := (tensor_restrict_equiv φ P).symm.trans (TensorProduct.comm R S P)
    let post := (TensorProduct.comm R (localize f P) S).trans
      (tensor_restrict_equiv φ (localize f P))
    have hi : IsLocalizedModule T (post.toLinearMap.comp (rt.comp pre.toLinearMap)) :=
      IsLocalizedModule.of_linearEquiv T (rt.comp pre.toLinearMap) post
    have heq : t = post.toLinearMap.comp (rt.comp pre.toLinearMap) := by
      apply LinearMap.ext
      intro x
      change S ⊗[R] P at x
      induction x using TensorProduct.inductionOn with
      | tmul s p =>
        change s ⊗ₜ[R] ell p =
          TensorProduct.comm R (localize f P) S (rt (p ⊗ₜ[R] s))
        simp [rt]
      | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    rw [heq]
    exact hi
  have units := IsLocalizedModule.map_units (S := T) t
  have hf : Function.Bijective
      (fun x : restrict φ (extend φ (localize f P)) ↦ f • x) :=
    (Module.End.isUnit_iff _).mp (units (⟨f, ⟨1, pow_one f⟩⟩ : T))
  have comp : (compare φ f P).comp
      (LocalizedModule.mkLinearMap T (restrict φ (extend φ P))) = t :=
    (exists_compare φ f P).exists.choose_spec
  have base (p : P) (s : S) :
      compare φ f P (LocalizedModule.mk
        (show restrict φ (extend φ P) from s ⊗ₜ[R] p) 1) =
      (show restrict φ (extend φ (localize f P)) from s ⊗ₜ[R] LocalizedModule.mk p 1) := by
    have hb := LinearMap.congr_fun comp (s ⊗ₜ[R] p)
    change compare φ f P (LocalizedModule.mk (s ⊗ₜ[R] p) 1) =
        s ⊗ₜ[R] LocalizedModule.mk p 1 at hb
    exact hb
  refine ⟨hf, ?_, ?_, ?_, ?_⟩
  · intro p s n
    apply ((Module.End.isUnit_iff _).mp (units ⟨f ^ n, ⟨n, rfl⟩⟩)).1
    simp only [Module.algebraMap_end_apply]
    rw [← map_smul, fraction_cancel _ (⟨f ^ n, ⟨n, rfl⟩⟩ : T), base]
    change s ⊗ₜ[R] LocalizedModule.mk p 1 =
      (algebraMap R S (f ^ n)) •
        (s ⊗ₜ[R] LocalizedModule.mk p (⟨f ^ n, ⟨n, rfl⟩⟩ : T))
    rw [algebraMap_smul, ← TensorProduct.tmul_smul,
      fraction_cancel _ (⟨f ^ n, ⟨n, rfl⟩⟩ : T)]
  · intro h
    constructor
    · intro hh
      apply (exists_compare φ f P).unique _ comp
      apply LinearMap.ext
      intro x
      change S ⊗[R] P at x
      induction x using TensorProduct.inductionOn with
      | tmul s p => simpa [t, restrictMap, extendMap, ell] using hh p s
      | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    · rintro rfl
      exact base
  · exact compare_smul φ f P
  · let E := IsLocalizedModule.linearEquiv T
      (LocalizedModule.mkLinearMap T (restrict φ (extend φ P))) t
    have hE : compare φ f P = E.toLinearMap := by
      apply IsLocalizedModule.ext T
        (LocalizedModule.mkLinearMap T (restrict φ (extend φ P))) units
      rw [comp]
      apply LinearMap.ext
      intro x
      exact (IsLocalizedModule.linearEquiv_apply T
        (LocalizedModule.mkLinearMap T (restrict φ (extend φ P))) t x).symm
    rw [hE]
    exact E.bijective



end FormalGlueing
