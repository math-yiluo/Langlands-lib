/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import WeilConjectures.AlgebraicGeometry.ArtinianIdealLengthOneFiltration

/-! # Extending Artinian lifting tests to arbitrary kernels
Source: Stacks Project, Algebra, Tag 02HT, proof of (4) implies (1).
-/

@[expose] public section

universe u v

namespace Algebra

private theorem factor_kernel_length
    {B : Type u} [CommRing B] (I J : Ideal B) (hIJ : I ≤ J)
    (h : Module.length B
      (↥J ⧸ Submodule.comap J.subtype I) = 1) :
    Module.length (B ⧸ I) (RingHom.ker (Ideal.Quotient.factor hIJ)) = 1 := by
  let φ : (B ⧸ I) →+* (B ⧸ J) := Ideal.Quotient.factor hIJ
  let f : J →ₗ[B] RingHom.ker φ :=
    { toFun := fun x => ⟨Ideal.Quotient.mk I x, by
        change Ideal.Quotient.mk J x = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr x.2⟩
      map_add' := by intro x y; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intro r x; apply Subtype.ext; rfl }
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective y.1
    have hxJ : x ∈ J := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have hy := y.2
      change φ y.1 = 0 at hy
      rw [← hx] at hy
      exact hy
    exact ⟨⟨x, hxJ⟩, Subtype.ext hx⟩
  have hk : LinearMap.ker f = Submodule.comap J.subtype I := by
    ext x
    simp [f, LinearMap.mem_ker, Ideal.Quotient.eq_zero_iff_mem, Subtype.ext_iff]
  have he := (LinearMap.quotKerEquivOfSurjective f hf).length_eq
  rw [hk] at he
  have hlen : Module.length B (RingHom.ker φ) = 1 := he.symm.trans h
  rw [← Module.length_eq_of_surjective (M := RingHom.ker φ)
    (Ideal.Quotient.mk_surjective (I := I))]
  exact hlen

/-- Length-one lifting tests suffice for a surjection of Artinian local rings.

Source: Stacks Project, Algebra, Tag 02HT, proof of (4) implies (1), the filtration
of I_N and successive application of the lifting condition.
(blueprint: lem-weil-pbc-artinian-lifting-finite-kernel).

Proof in words: Filter ker phi by the finite ideal filtration with length-one
successive quotients. Every filtration ideal lies in the maximal ideal, since
ker phi does so for a surjection onto a nonzero local ring. Consequently all the
quotients are nonzero Artinian local rings. Identify the final quotient with B.
Starting with a, descend through the filtration by applying hlift to each map
B'/K_i -> B'/K_(i+1). The kernel is K_(i+1)/K_i; restriction along the surjection
B' -> B'/K_i identifies its submodule lattice, hence preserves its length one.
Each lifted map still has inverse image maximal ideal q: composing with a
surjective local map does not change that inverse image. Each application also
preserves the structural map from R. At the bottom identify B'/0 with B'.
To use tests in Type (max u v), transport all quotient rings and their maps along
the ULift ring equivalence, apply hlift, and transport the resulting maps back.
For a zero kernel use the inverse of the bijective ring map; the filtration then
has no steps. This theorem chooses maps only in its existential conclusion. -/
theorem artinian_lifting_finite_kernel
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (q : Ideal A) [q.IsPrime]
    (hlift : ∀ (B' B : Type (max u v)) [CommRing B'] [CommRing B]
      [IsArtinianRing B'] [IsArtinianRing B] [IsLocalRing B'] [IsLocalRing B]
      (φ : B' →+* B), Function.Surjective φ → Module.length B' (RingHom.ker φ) = 1 →
      ∀ (ρ : R →+* B') (a : A →+* B),
        a.comp (algebraMap R A) = φ.comp ρ →
          Ideal.comap a (IsLocalRing.maximalIdeal B) = q →
        ∃ a' : A →+* B', φ.comp a' = a ∧ a'.comp (algebraMap R A) = ρ)
    (B' B : Type u) [CommRing B'] [CommRing B]
    [IsArtinianRing B'] [IsArtinianRing B] [IsLocalRing B'] [IsLocalRing B]
    (φ : B' →+* B) (hφ : Function.Surjective φ)
    (ρ : R →+* B') (a : A →+* B)
    (hcomm : a.comp (algebraMap R A) = φ.comp ρ)
    (hq : Ideal.comap a (IsLocalRing.maximalIdeal B) = q) :
    ∃ a' : A →+* B', φ.comp a' = a ∧ a'.comp (algebraMap R A) = ρ := by
  have liftSmall (E F : Type u) [CommRing E] [CommRing F]
      [IsArtinianRing E] [IsArtinianRing F] [IsLocalRing E] [IsLocalRing F]
      (ψ : E →+* F) (hψ : Function.Surjective ψ)
      (hlen : Module.length E (RingHom.ker ψ) = 1)
      (ρ₀ : R →+* E) (a₀ : A →+* F)
      (hc : a₀.comp (algebraMap R A) = ψ.comp ρ₀)
      (hq₀ : Ideal.comap a₀ (IsLocalRing.maximalIdeal F) = q) :
      ∃ a₁ : A →+* E, ψ.comp a₁ = a₀ ∧ a₁.comp (algebraMap R A) = ρ₀ := by
    let E₁ := ULift.{v} E
    let F₁ := ULift.{v} F
    let e : E₁ ≃+* E := ULift.ringEquiv
    let d : F₁ ≃+* F := ULift.ringEquiv
    have : IsLocalRing E₁ := e.symm.isLocalRing
    have : IsLocalRing F₁ := d.symm.isLocalRing
    have : IsArtinianRing E₁ := e.symm.surjective.isArtinianRing
    have : IsArtinianRing F₁ := d.symm.surjective.isArtinianRing
    let ψ₁ : E₁ →+* F₁ := ψ.ulift
    have hψ₁ : Function.Surjective ψ₁ := by
      intro y
      obtain ⟨x, hx⟩ := hψ y.down
      exact ⟨⟨x⟩, congrArg ULift.up hx⟩
    have : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
    let k : RingHom.ker ψ₁ →ₛₗ[e.toRingHom] RingHom.ker ψ :=
      { toFun := fun x => ⟨x.1.down, by
          have h := congrArg ULift.down x.2
          exact h⟩
        map_add' := by intro x y; rfl
        map_smul' := by intro r x; rfl }
    have hk : Function.Bijective k := by
      constructor
      · intro x y h
        apply Subtype.ext
        apply ULift.ext
        exact congrArg Subtype.val h
      · intro y
        refine ⟨⟨⟨y.1⟩, ?_⟩, rfl⟩
        exact congrArg ULift.up y.2
    have hlen₁ : Module.length E₁ (RingHom.ker ψ₁) = 1 :=
      Module.length_eq_one_iff.mpr
        ((k.isSimpleModule_iff_of_bijective hk).mpr (Module.length_eq_one_iff.mp hlen))
    let ρ₁ : R →+* E₁ := e.symm.toRingHom.comp ρ₀
    let a₁ : A →+* F₁ := d.symm.toRingHom.comp a₀
    have hc₁ : a₁.comp (algebraMap R A) = ψ₁.comp ρ₁ := by
      ext r
      exact DFunLike.congr_fun hc r
    have hdLocal : IsLocalHom d.symm.toRingHom :=
      IsLocalHom.of_surjective _ d.symm.surjective
    have hq₁ : Ideal.comap a₁ (IsLocalRing.maximalIdeal F₁) = q := by
      dsimp only [a₁]
      rw [← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap]
      exact hq₀
    obtain ⟨a₂, ha₂, hρ₂⟩ := hlift E₁ F₁ ψ₁ hψ₁ hlen₁ ρ₁ a₁ hc₁ hq₁
    refine ⟨e.toRingHom.comp a₂, ?_, ?_⟩
    · ext x
      exact congrArg ULift.down (DFunLike.congr_fun ha₂ x)
    · ext r
      exact congrArg ULift.down (DFunLike.congr_fun hρ₂ r)
  obtain ⟨r, F, h0, htop, hstep, hlength⟩ :=
    RingTheory.exists_ideal_filtration_length_one B' (RingHom.ker φ)
  have hmono : Monotone F := Fin.monotone_iff_le_succ.mpr hstep
  have hFK (i : Fin (r + 1)) : F i ≤ RingHom.ker φ := by
    rw [← htop]
    exact hmono (Fin.le_last i)
  have hφLocal : IsLocalHom φ := IsLocalHom.of_surjective _ hφ
  have hKm : RingHom.ker φ ≤ IsLocalRing.maximalIdeal B' := by
    rw [← IsLocalRing.maximalIdeal_comap φ]
    intro x hx
    change φ x ∈ IsLocalRing.maximalIdeal B
    rw [show φ x = 0 from hx]
    exact Ideal.zero_mem _
  have hproper (i : Fin (r + 1)) : F i ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal B').ne_top
      ((hFK i).trans hKm)
  have instNontrivial (i : Fin (r + 1)) : Nontrivial (B' ⧸ F i) :=
    Ideal.Quotient.nontrivial_iff.mpr (hproper i)
  have instLocal (i : Fin (r + 1)) : IsLocalRing (B' ⧸ F i) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (F i)) Ideal.Quotient.mk_surjective
  have instArtinian (i : Fin (r + 1)) : IsArtinianRing (B' ⧸ F i) := inferInstance
  let π (i : Fin (r + 1)) : (B' ⧸ F i) →+* B :=
    Ideal.Quotient.lift (F i) φ (fun x hx => hFK i hx)
  have hπSurj (i : Fin (r + 1)) : Function.Surjective (π i) := by
    intro y
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨Ideal.Quotient.mk (F i) x, rfl⟩
  have hπLocal (i : Fin (r + 1)) : IsLocalHom (π i) :=
    IsLocalHom.of_surjective _ (hπSurj i)
  let ρi (i : Fin (r + 1)) : R →+* (B' ⧸ F i) :=
    (Ideal.Quotient.mk (F i)).comp ρ
  have hall (i : Fin (r + 1)) :
      ∃ ai : A →+* (B' ⧸ F i),
        (π i).comp ai = a ∧ ai.comp (algebraMap R A) = ρi i := by
    refine Fin.reverseInduction ?_ ?_ i
    · have hinj : Function.Injective (π (Fin.last r)) :=
        RingHom.lift_injective_of_ker_le_ideal _ _ (by rw [htop])
      let e : (B' ⧸ F (Fin.last r)) ≃+* B :=
        RingEquiv.ofBijective (π (Fin.last r)) ⟨hinj, hπSurj _⟩
      refine ⟨e.symm.toRingHom.comp a, ?_, ?_⟩
      · ext x
        exact e.apply_symm_apply (a x)
      · apply RingHom.ext
        intro x
        apply hinj
        change e (e.symm (a ((algebraMap R A) x))) = φ (ρ x)
        rw [e.apply_symm_apply]
        exact DFunLike.congr_fun hcomm x
    · intro j ih
      obtain ⟨aj, haj, hρj⟩ := ih
      let ψ : (B' ⧸ F j.castSucc) →+* (B' ⧸ F j.succ) :=
        Ideal.Quotient.factor (hstep j)
      have hψ : Function.Surjective ψ := Ideal.Quotient.factor_surjective (hstep j)
      have hlen : Module.length (B' ⧸ F j.castSucc) (RingHom.ker ψ) = 1 :=
        factor_kernel_length _ _ (hstep j) (hlength j)
      have hψρ : aj.comp (algebraMap R A) = ψ.comp (ρi j.castSucc) := by
        rw [hρj]
        rfl
      have hqj : Ideal.comap aj (IsLocalRing.maximalIdeal (B' ⧸ F j.succ)) = q := by
        rw [← IsLocalRing.maximalIdeal_comap (π j.succ), Ideal.comap_comap, haj]
        exact hq
      obtain ⟨ai, hai, hρi⟩ := liftSmall _ _ ψ hψ hlen (ρi j.castSucc) aj hψρ hqj
      refine ⟨ai, ?_, hρi⟩
      have hπψ : (π j.succ).comp ψ = π j.castSucc := by
        apply RingHom.ext
        intro x
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        rfl
      rw [← hπψ, RingHom.comp_assoc, hai, haj]
  obtain ⟨a₀, ha₀, hρ₀⟩ := hall 0
  let e : (B' ⧸ F 0) ≃+* B' :=
    (Ideal.quotientEquivAlgOfEq B' h0).toRingEquiv.trans (RingEquiv.quotientBot B')
  have he (x : B') : e (Ideal.Quotient.mk (F 0) x) = x := rfl
  refine ⟨e.toRingHom.comp a₀, ?_, ?_⟩
  · have hφe : φ.comp e.toRingHom = π 0 := by
      apply RingHom.ext
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      change φ (e (Ideal.Quotient.mk (F 0) x)) = φ x
      exact congrArg φ (he x)
    rw [← RingHom.comp_assoc, hφe]
    exact ha₀
  · ext x
    change e (a₀ ((algebraMap R A) x)) = ρ x
    rw [show a₀ ((algebraMap R A) x) = Ideal.Quotient.mk (F 0) (ρ x)
      from DFunLike.congr_fun hρ₀ x, he]


end Algebra
