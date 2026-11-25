/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.FullyFaithful

/-!
# Unique finite étale morphism lifts to quotient-power thickenings

## References

* Stacks Project, Tag 0BQB (invariance under a thickening), as used in Tag 0EL8
-/

@[expose] public section

noncomputable section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.FiniteEtale.Adic

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The powers defining the infinitesimal neighbourhoods of a quotient section. -/
abbrev ideal (f : R →+* S) (n : ℕ) : Ideal R := (RingHom.ker f) ^ (n + 1)

/-- The `(n+1)`st quotient-power thickening. -/
def base (f : R →+* S) (n : ℕ) : Scheme.{u} := Spec (.of (R ⧸ ideal f n))

/-- The closed immersion of the quotient-power thickening into the ambient spectrum. -/
def baseMap (f : R →+* S) (n : ℕ) : base f n ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (ideal f n)))

/-- The quotient section factors through every infinitesimal neighbourhood. -/
def baseZero (f : R →+* S) (n : ℕ) : Spec (.of S) ⟶ base f n :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift (ideal f n) f
    (fun _a ha ↦ (Ideal.pow_le_self (Nat.succ_ne_zero n)) ha)))

@[simp]
theorem baseZero_comp_baseMap (f : R →+* S) (n : ℕ) :
    baseZero f n ≫ baseMap f n = Spec.map (CommRingCat.ofHom f) := by
  rw [baseZero, baseMap, ← Spec.map_comp]
  rfl

/-- Transition from one infinitesimal neighbourhood to the next. -/
def baseTransition (f : R →+* S) (n : ℕ) : base f n ⟶ base f (n + 1) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))))

@[simp]
theorem baseTransition_comp_baseMap (f : R →+* S) (n : ℕ) :
    baseTransition f n ≫ baseMap f (n + 1) = baseMap f n := by
  rw [baseTransition, baseMap, ← Spec.map_comp]
  rfl

@[simp]
theorem baseZero_comp_baseTransition (f : R →+* S) (n : ℕ) :
    baseZero f n ≫ baseTransition f n = baseZero f (n + 1) := by
  rw [baseZero, baseTransition, baseZero, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

variable (f : R →+* S) (V : (Spec (.of R)).Opens) (P : V.toScheme.FiniteEtale)

/-- Infinitesimal neighbourhoods of the section in the total space of a cover. -/
def cover (n : ℕ) : Scheme.{u} := Limits.pullback (P.obj.hom ≫ V.ι) (baseMap f n)

/-- Projection of an infinitesimal neighbourhood to the total space of the cover. -/
def coverMap (n : ℕ) : cover f V P n ⟶ P.obj.left :=
  pullback.fst (P.obj.hom ≫ V.ι) (baseMap f n)

/-- The cover restricted to the quotient section. -/
def zeroCover : Scheme.{u} :=
  Limits.pullback P.obj.hom ((Spec.map (CommRingCat.ofHom f)) ∣_ V)

/-- Inclusion of the restricted cover in its infinitesimal neighbourhood. -/
noncomputable def zeroMap (n : ℕ) : zeroCover f V P ⟶ cover f V P n :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ ((Spec.map (CommRingCat.ofHom f)) ⁻¹ᵁ V).ι ≫ baseZero f n)
    (by
      simp only [Category.assoc, baseZero_comp_baseMap]
      rw [← morphismRestrict_ι, ← Category.assoc, pullback.condition]
      exact Category.assoc _ _ _)

@[simp]
theorem zeroMap_coverMap (n : ℕ) :
    zeroMap f V P n ≫ coverMap f V P n = pullback.fst _ _ := by
  simp [zeroMap, coverMap]

/-- Inclusion of successive infinitesimal neighbourhoods of a cover. -/
noncomputable def coverTransition (n : ℕ) : cover f V P n ⟶ cover f V P (n + 1) :=
  pullback.lift (coverMap f V P n) (pullback.snd _ _ ≫ baseTransition f n)
    (by rw [Category.assoc, baseTransition_comp_baseMap]; exact pullback.condition)

@[simp]
theorem coverTransition_coverMap (n : ℕ) :
    coverTransition f V P n ≫ coverMap f V P (n + 1) = coverMap f V P n := by
  simp [coverTransition, coverMap]

@[simp]
theorem zeroMap_coverTransition (n : ℕ) :
    zeroMap f V P n ≫ coverTransition f V P n = zeroMap f V P (n + 1) := by
  apply pullback.hom_ext
  · simp [zeroMap, coverTransition, coverMap, Category.assoc]
  · simp [zeroMap, coverTransition, Category.assoc]

end AlgebraicGeometry.Scheme.FiniteEtale.Adic

namespace AlgebraicGeometry.Scheme

private theorem etaleUniversalHomeomorphismLift
    {X Y Z' Z : Scheme.{u}} (i : Z' ⟶ Z) [IsUniversalHomeomorphism i] (p : X ⟶ Y) [Etale p]
    (a : Z' ⟶ X) (b : Z ⟶ Y) (h : a ≫ p = i ≫ b) :
    ∃ g : Z ⟶ X, g ≫ p = b ∧ i ≫ g = a  := by
  let v := pullback.snd p b
  let a₀ : Z' ⟶ pullback p b := pullback.lift a i h
  let a' : Z' ⟶ pullback v i := pullback.lift a₀ (𝟙 Z') (by simp [a₀, v])
  obtain ⟨g, hg, _⟩ := Scheme.Hom.existsUnique_of_isPullback i (𝟙 Z) v
    IsPullback.of_id_snd (IsPullback.of_hasPullback v i) a' (by simp [a'])
  refine ⟨g ≫ pullback.fst p b, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hg.1]
    simp
  · have hga : i ≫ g = a₀ := by simpa [a'] using hg.2
    rw [← Category.assoc, hga]
    simp [a₀]


/-- A map of finite étale covers on a quotient section lifts uniquely to each
quotient-power thickening. -/
theorem finiteEtale_adic_unique_lift
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (V : (Spec (.of R)).Opens)
    (P Q : V.toScheme.FiniteEtale)
    (φ : (FiniteEtale.pullback ((Spec.map (CommRingCat.ofHom f)) ∣_ V)).obj P ⟶
      (FiniteEtale.pullback ((Spec.map (CommRingCat.ofHom f)) ∣_ V)).obj Q)
    (n : ℕ) :
    ∃! g : FiniteEtale.Adic.cover f V P n ⟶ Q.obj.left,
      g ≫ Q.obj.hom = FiniteEtale.Adic.coverMap f V P n ≫ P.obj.hom ∧
      FiniteEtale.Adic.zeroMap f V P n ≫ g =
        φ.hom.left ≫ pullback.fst Q.obj.hom
          ((Spec.map (CommRingCat.ofHom f)) ∣_ V) := by
  let q := Ideal.Quotient.lift (FiniteEtale.Adic.ideal f n) f
    (fun _a ha ↦ (Ideal.pow_le_self (Nat.succ_ne_zero n)) ha)
  have hq : Function.Surjective q := by
    intro s
    obtain ⟨r, rfl⟩ := hf s
    exact ⟨Ideal.Quotient.mk _ r, rfl⟩
  have hker : IsNilpotent (RingHom.ker q) := by
    refine ⟨n + 1, ?_⟩
    rw [show RingHom.ker q = (RingHom.ker f).map
      (Ideal.Quotient.mk (FiniteEtale.Adic.ideal f n)) from
        Ideal.ker_quotient_lift f _]
    rw [← Ideal.map_pow, Ideal.map_quotient_self]
    rfl
  have hpull : IsPullback (FiniteEtale.Adic.zeroMap f V P n)
      (pullback.snd P.obj.hom ((Spec.map (CommRingCat.ofHom f)) ∣_ V) ≫
        ((Spec.map (CommRingCat.ofHom f)) ⁻¹ᵁ V).ι)
      (pullback.snd (P.obj.hom ≫ V.ι) (FiniteEtale.Adic.baseMap f n))
      (FiniteEtale.Adic.baseZero f n) := by
    have houter := ((IsPullback.of_hasPullback P.obj.hom
      ((Spec.map (CommRingCat.ofHom f)) ∣_ V)).flip.paste_horiz
        (isPullback_morphismRestrict (Spec.map (CommRingCat.ofHom f)) V).flip).flip
    refine IsPullback.of_right ?_ ?_
      (IsPullback.of_hasPullback (P.obj.hom ≫ V.ι) (FiniteEtale.Adic.baseMap f n))
    · change IsPullback (FiniteEtale.Adic.zeroMap f V P n ≫
        FiniteEtale.Adic.coverMap f V P n) _ _ _
      rw [FiniteEtale.Adic.zeroMap_coverMap, FiniteEtale.Adic.baseZero_comp_baseMap]
      exact houter
    · simp [FiniteEtale.Adic.zeroMap, Category.assoc]
  have : IsClosedImmersion (FiniteEtale.Adic.baseZero f n) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom q) hq
  have : Surjective (FiniteEtale.Adic.baseZero f n) := by
    constructor
    intro x
    change ∃ y : PrimeSpectrum S, PrimeSpectrum.comap q y = x
    rw [← Set.mem_range, range_comap_of_surjective S q hq]
    change RingHom.ker q ≤ x.asIdeal
    obtain ⟨m, hm⟩ := hker
    intro r hr
    apply x.isPrime.mem_of_pow_mem m
    have hzero : r ^ m = 0 := by
      have hh := Ideal.pow_mem_pow hr m
      rwa [hm, Ideal.zero_eq_bot, Ideal.mem_bot] at hh
    rw [hzero]
    exact Ideal.zero_mem _
  have : IsUniversalHomeomorphism (FiniteEtale.Adic.baseZero f n) := inferInstance
  have : IsUniversalHomeomorphism (FiniteEtale.Adic.zeroMap f V P n) :=
    MorphismProperty.of_isPullback hpull.flip inferInstance
  have : Etale Q.obj.hom := Q.obj.prop
  have hφ : (φ.hom.left ≫ pullback.fst Q.obj.hom
      ((Spec.map (CommRingCat.ofHom f)) ∣_ V)) ≫ Q.obj.hom =
      FiniteEtale.Adic.zeroMap f V P n ≫
        (FiniteEtale.Adic.coverMap f V P n ≫ P.obj.hom) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc,
      ← FiniteEtale.pullback_obj_obj_hom, FiniteEtale.hom_left_comp]
    rw [← Category.assoc, FiniteEtale.Adic.zeroMap_coverMap]
    exact pullback.condition.symm
  obtain ⟨g, hg, hg₀⟩ := etaleUniversalHomeomorphismLift
    (FiniteEtale.Adic.zeroMap f V P n) Q.obj.hom _ _ hφ
  refine ⟨g, ⟨hg, hg₀⟩, ?_⟩
  intro g' hg'
  exact Scheme.Hom.ext_of_surjective_of_formallyUnramified
    (FiniteEtale.Adic.zeroMap f V P n) Q.obj.hom
    (hg'.1.trans hg.symm) (hg'.2.trans hg₀.symm)


end AlgebraicGeometry.Scheme
