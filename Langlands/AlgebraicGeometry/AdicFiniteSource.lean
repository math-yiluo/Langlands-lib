import Langlands.AlgebraicGeometry.AdicQuotientBaseChange
import Langlands.AlgebraicGeometry.AdicAffinePoints
import Langlands.AlgebraicGeometry.AffineQuotientPullback
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompletePunctured
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Ring

/-! # Adic effectivity for maps from spectra of finite algebras -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open Langlands.AlgebraicGeometry.AdicAffinePoints
open Langlands.AlgebraicGeometry.UnramifiedFunctor.CompleteLocal (isAdicComplete_map_of_finite)

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.AdicFiniteSource

open Langlands.GroupScheme.HomScheme.Adic (quotientSpecMap quotientSpecMap_quotientMap quotientSpecMap_transition isPullback_quotientSpecMap)

variable {B : Type u} [CommRing B] (I : Ideal B)

private theorem exists_idempotent_lift [IsAdicComplete I B]
    (e : B ⧸ I) (he : IsIdempotentElem e) :
    ∃ b : B, IsIdempotentElem b ∧ Ideal.Quotient.mk I b = e := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective e
  rcases subsingleton_or_nontrivial B with h | h
  · exact ⟨a, h.elim _ _, ha⟩
  let p : B[X] := X ^ 2 - X
  have hp : p.Monic := Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; norm_num)
  have hroot : p.eval a ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simp [p, pow_two, ha, he.eq]
  have hderiv : IsUnit (Ideal.Quotient.mk I (p.derivative.eval a)) := by
    have h : (e + e - 1) * (e + e - 1) = 1 := by
      calc
        _ = 1 + 4 * (e * e - e) := by ring
        _ = 1 := by rw [he.eq, sub_self, mul_zero, add_zero]
    have hunit : IsUnit (e + e - 1) := isUnit_iff_exists.mpr ⟨_, h, h⟩
    simpa [p, pow_two, ha] using hunit
  obtain ⟨b, hb, hcongr⟩ := HenselianRing.is_henselian p hp a hroot hderiv
  have hb' : b * b = b := sub_eq_zero.mp (by simpa [p, pow_two] using hb)
  have hba : Ideal.Quotient.mk I b = Ideal.Quotient.mk I a :=
    Ideal.Quotient.eq.mpr hcongr
  exact ⟨b, hb', hba.trans ha⟩

private theorem exists_closedQuotient_specialization [IsAdicComplete I B]
    (x : Spec (CommRingCat.of B)) :
    ∃ y : quotientSpec I 0, x ⤳ quotientMap I 0 y := by
  obtain ⟨m, hm, hxm⟩ := x.asIdeal.exists_le_maximal x.isPrime.ne_top
  let z : Spec (CommRingCat.of B) := ⟨m, hm.isPrime⟩
  have hIm : I ≤ m := (IsAdicComplete.le_jacobson_bot I).trans
    (sInf_le (show m ∈ {J : Ideal B | ⊥ ≤ J ∧ J.IsMaximal} from ⟨bot_le, hm⟩))
  have hz : z ∈ Set.range (quotientMap I 0) :=
    (mem_range_SpecMap_quotient_iff _ _).mpr (by simpa using hIm)
  obtain ⟨y, hy⟩ := hz
  exact ⟨y, hy.symm ▸ (PrimeSpectrum.le_iff_specializes _ _).mp hxm⟩

private theorem exists_closedQuotient_clopen [IsAdicComplete I B]
    [IsArtinianRing (B ⧸ I ^ (0 + 1))] (y : quotientSpec I 0) :
    ∃ e : B, IsIdempotentElem e ∧
      (quotientMap I 0) ⁻¹' (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum B)) = {y} := by
  obtain ⟨e, he, hopen⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen
    (isClopen_discrete ({y} : Set (quotientSpec I 0)))
  have : IsAdicComplete (I ^ (0 + 1)) B := by simpa using ‹IsAdicComplete I B›
  obtain ⟨b, hb, hbe⟩ := exists_idempotent_lift (I ^ (0 + 1)) e he
  refine ⟨b, hb, ?_⟩
  rw [hopen]
  ext z
  change Ideal.Quotient.mk (I ^ (0 + 1)) b ∉ z.asIdeal ↔ e ∉ z.asIdeal
  rw [hbe]

private theorem transition_surjective (n : ℕ) : Function.Surjective (transition I n) := by
  let f := Ideal.Quotient.factorPow I (n + 1).le_succ
  have hker : RingHom.ker f ^ 2 = ⊥ := by
    dsimp only [f]
    rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, ← pow_mul]
    exact Ideal.map_mk_eq_bot_of_le (Ideal.pow_le_pow_right (by omega))
  intro x
  change x ∈ Set.range (PrimeSpectrum.comap f)
  rw [range_comap_of_surjective _ _ (Ideal.Quotient.factor_surjective _),
    PrimeSpectrum.mem_zeroLocus]
  apply x.isPrime.le_of_pow_le (n := 2)
  rw [hker]
  exact bot_le

private abbrev chartMap (e : B) : Spec (CommRingCat.of (Localization.Away e)) ⟶
    Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away e)))

private theorem range_chartMap (e : B) :
    Set.range (chartMap e) = (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum B)) :=
  PrimeSpectrum.localization_away_comap_range _ _

private theorem eq_of_specializes_into_chart
    {e : B} (he : IsIdempotentElem e) {y w : quotientSpec I 0}
    (hchart : (quotientMap I 0) ⁻¹' (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum B)) = {y})
    {x : Spec (CommRingCat.of B)} (hx : x ∈ Set.range (chartMap e))
    (hxw : x ⤳ quotientMap I 0 w) : w = y := by
  have hs := (PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩).1
  rw [range_chartMap] at hx
  have hw : w ∈ (quotientMap I 0) ⁻¹' (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum B)) :=
    hxw.mem_closed hs hx
  rw [hchart] at hw
  exact hw

section Charts

variable [IsNoetherianRing B] [IsAdicComplete I B] {X : Scheme.{u}}
  (f : ∀ n : ℕ, quotientSpec I n ⟶ X)
  (hf : ∀ n : ℕ, transition I n ≫ f (n + 1) = f n)

include hf in
set_option maxHeartbeats 500000 in
private theorem lift_on_chart {e : B} (he : IsIdempotentElem e) {y : quotientSpec I 0}
    (hchart : (quotientMap I 0) ⁻¹' (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum B)) = {y}) :
    ∃! g : Spec (CommRingCat.of (Localization.Away e)) ⟶ X,
      ∀ n : ℕ, quotientMap (I.map (algebraMap B (Localization.Away e))) n ≫ g =
        quotientSpecMap (algebraMap B (Localization.Away e)) I n ≫ f n := by
  let C := Localization.Away e
  let φ := algebraMap B C
  let J := I.map φ
  let k (n : ℕ) := quotientSpecMap φ I n
  have : Module.Finite B C := RingHom.finite_algebraMap.mp
    (RingHom.Finite.of_surjective φ (IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem e he))
  have : IsAdicComplete J C := isAdicComplete_map_of_finite I
  obtain ⟨D, i, hi, hmem, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (X := X) (x := f 0 y) (U := ⊤) trivial
  have hzero (w : quotientSpec J 0) : k 0 w = y := by
    have hw : quotientMap I 0 (k 0 w) ∈ Set.range (chartMap e) := by
      refine ⟨quotientMap J 0 w, ?_⟩
      exact congrArg (fun d => d w) (quotientSpecMap_quotientMap φ I 0).symm
    exact eq_of_specializes_into_chart I he hchart hw specializes_rfl
  have hcompat (n : ℕ) : transition J n ≫ k (n + 1) ≫ f (n + 1) = k n ≫ f n := by
    rw [← Category.assoc, quotientSpecMap_transition, Category.assoc, hf n]
  have hrange (n : ℕ) : Set.range (k n ≫ f n) ⊆ Set.range i := by
    induction n with
    | zero =>
      rintro _ ⟨w, rfl⟩
      change f 0 (k 0 w) ∈ Set.range i
      rwa [hzero w]
    | succ n ih =>
      rintro _ ⟨w, rfl⟩
      obtain ⟨w', rfl⟩ := transition_surjective J n w
      have h := congrArg (fun d => d w') (hcompat n)
      exact h.symm ▸ ih (Set.mem_range_self w')
  let p (n : ℕ) := IsOpenImmersion.lift i (k n ≫ f n) (hrange n)
  have hp (n : ℕ) : transition J n ≫ p (n + 1) = p n := by
    apply (cancel_mono i).mp
    simpa only [Category.assoc, p, IsOpenImmersion.lift_fac] using hcompat n
  obtain ⟨q, hq, hqu⟩ := existsUnique_adic_lift J p hp
  have hq' (n : ℕ) : quotientMap J n ≫ q ≫ i = k n ≫ f n := by
    rw [← Category.assoc, hq n, IsOpenImmersion.lift_fac]
  refine ⟨q ≫ i, hq', fun g hg => ?_⟩
  have hgr : Set.range g ⊆ Set.range i := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨w₀, hw₀⟩ := exists_closedQuotient_specialization J w
    have h : g (quotientMap J 0 w₀) ∈ Set.range i := by
      change (quotientMap J 0 ≫ g) w₀ ∈ Set.range i
      rw [hg 0]
      exact hrange 0 (Set.mem_range_self w₀)
    exact (hw₀.map g.continuous).mem_open i.isOpenEmbedding.isOpen_range h
  let g' := IsOpenImmersion.lift i g hgr
  have hg' : g' ≫ i = g := IsOpenImmersion.lift_fac _ _ _
  rw [← hg']
  congr 1
  apply hqu
  intro n
  apply (cancel_mono i).mp
  rw [Category.assoc, hg', hg n, IsOpenImmersion.lift_fac]

end Charts

set_option maxHeartbeats 1000000 in
/-- Over an adically complete noetherian ring with Artinian first quotient,
compatible maps to any scheme have a unique actual lift. -/
theorem existsUnique_adic_lift_of_artinianQuotient
    [IsNoetherianRing B] [IsAdicComplete I B] [IsArtinianRing (B ⧸ I)]
    {X : Scheme.{u}} (f : ∀ n : ℕ, quotientSpec I n ⟶ X)
    (hf : ∀ n : ℕ, transition I n ≫ f (n + 1) = f n) :
    ∃! g : Spec (CommRingCat.of B) ⟶ X, ∀ n : ℕ, quotientMap I n ≫ g = f n := by
  classical
  have : IsArtinianRing (B ⧸ I ^ (0 + 1)) := by
    rw [show 0 + 1 = 1 from rfl, pow_one]
    infer_instance
  choose e he hchart using fun y : quotientSpec I 0 => exists_closedQuotient_clopen I y
  let C (y : quotientSpec I 0) := Localization.Away (e y)
  let φ (y : quotientSpec I 0) := algebraMap B (C y)
  let p (y : quotientSpec I 0) := chartMap (e y)
  let J (y : quotientSpec I 0) := I.map (φ y)
  let k (y : quotientSpec I 0) (n : ℕ) := quotientSpecMap (φ y) I n
  have hcover (x : Spec (CommRingCat.of B)) : ∃ y, x ∈ Set.range (p y) := by
    obtain ⟨y, hy⟩ := exists_closedQuotient_specialization I x
    have hmem : y ∈ (quotientMap I 0) ⁻¹'
        (PrimeSpectrum.basicOpen (e y) : Set (PrimeSpectrum B)) := by
      rw [hchart y]
      exact Set.mem_singleton y
    have hopen : IsOpen (PrimeSpectrum.basicOpen (e y) : Set (PrimeSpectrum B)) :=
      (PrimeSpectrum.basicOpen _).isOpen
    exact ⟨y, (range_chartMap (e y)).symm ▸ hy.mem_open hopen hmem⟩
  let 𝒰 : (Spec (CommRingCat.of B)).OpenCover := {
    I₀ := quotientSpec I 0,
    X y := Spec (CommRingCat.of (C y)),
    f := p,
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨hcover, fun _ => inferInstance⟩ }
  choose g hg hgu using fun y => lift_on_chart I f hf (he y) (hchart y)
  have hcompat (y z : 𝒰.I₀) :
      pullback.fst (𝒰.f y) (𝒰.f z) ≫ g y = pullback.snd _ _ ≫ g z := by
    by_cases hyz : y = z
    · subst z
      have : IsOpenImmersion (𝒰.f y) := 𝒰.map_prop y
      have h : pullback.fst (𝒰.f y) (𝒰.f y) = pullback.snd _ _ :=
        (cancel_mono (𝒰.f y)).mp pullback.condition
      rw [h]
    · have : IsEmpty (pullback (C := Scheme.{u}) (𝒰.f y) (𝒰.f z)) := ⟨fun w => by
        let x := p y (pullback.fst (𝒰.f y) (𝒰.f z) w)
        have hxy : x ∈ Set.range (p y) := Set.mem_range_self _
        have hxz : x ∈ Set.range (p z) :=
          ⟨pullback.snd (𝒰.f y) (𝒰.f z) w, by
            exact congrArg (fun d => d w)
              (pullback.condition (f := 𝒰.f y) (g := 𝒰.f z)).symm⟩
        obtain ⟨w₀, hw₀⟩ := exists_closedQuotient_specialization I x
        exact hyz ((eq_of_specializes_into_chart I (he y) (hchart y) hxy hw₀).symm.trans
          (eq_of_specializes_into_chart I (he z) (hchart z) hxz hw₀))⟩
      exact isInitialOfIsEmpty.hom_ext _ _
  let q := 𝒰.glueMorphisms g hcompat
  have hq (y : quotientSpec I 0) : p y ≫ q = g y := 𝒰.ι_glueMorphisms g hcompat y
  have hpb (y : quotientSpec I 0) (n : ℕ) :
      IsPullback (k y n) (quotientMap (J y) n) (quotientMap I n) (p y) :=
    isPullback_quotientSpecMap (φ y) I n
  refine ⟨q, fun n => ?_, fun q' hq' => ?_⟩
  · let 𝒱 : (quotientSpec I n).OpenCover := {
      I₀ := quotientSpec I 0,
      X y := quotientSpec (J y) n,
      f y := k y n,
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun x => ?_, fun y => ?_⟩
        · obtain ⟨y, z, hz⟩ := hcover (quotientMap I n x)
          obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback (hpb y n) x z hz.symm
          exact ⟨y, w, hw⟩
        · exact MorphismProperty.of_isPullback (hpb y n).flip (𝒰.map_prop y) }
    apply 𝒱.hom_ext
    intro y
    change k y n ≫ quotientMap I n ≫ q = k y n ≫ f n
    rw [← Category.assoc, (hpb y n).w, Category.assoc, hq y, hg y n]
  · apply 𝒰.hom_ext
    intro y
    change p y ≫ q' = p y ≫ q
    rw [hq]
    apply hgu
    intro n
    change quotientMap (J y) n ≫ p y ≫ q' = k y n ≫ f n
    rw [← Category.assoc, ← (hpb y n).w, Category.assoc, hq' n]

/-- Adic effectivity for maps from spectra of algebras finite over a complete
noetherian local ring, with its maximal-ideal filtration. -/
def AdicFiniteAlgebraSourceStatement : Prop :=
  ∀ (A B : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CommRing B] [Algebra A B] [Module.Finite A B] (X : Scheme.{u}),
    let J := (IsLocalRing.maximalIdeal A).map (algebraMap A B)
    ∀ (f : ∀ n : ℕ, quotientSpec J n ⟶ X),
      (∀ n : ℕ, transition J n ≫ f (n + 1) = f n) →
      ∃! g : Spec (CommRingCat.of B) ⟶ X, ∀ n : ℕ, quotientMap J n ≫ g = f n

/-- A compatible system of maps from thickenings of a finite affine scheme
over a complete noetherian local ring algebraizes uniquely. -/
theorem adicFiniteAlgebraSource : AdicFiniteAlgebraSourceStatement.{u} := by
  intro A B _ _ _ _ _ _ _ X J f hf
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have : IsAdicComplete J B := isAdicComplete_map_of_finite (IsLocalRing.maximalIdeal A)
  let : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  have : Module.Finite (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ J) :=
    Module.Finite.of_restrictScalars_finite A _ _
  have : IsArtinianRing (B ⧸ J) := IsArtinianRing.of_finite (A ⧸ IsLocalRing.maximalIdeal A) _
  exact existsUnique_adic_lift_of_artinianQuotient J f hf

end Langlands.AlgebraicGeometry.AdicFiniteSource
