import Langlands.AlgebraicGeometry.AdicDetectionStatement
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.AdicCompletion.Noetherian

/-! # Adic detection of an immersed subscheme of a finite scheme -/

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AdicDetection

/-- The base-changed map commutes with the projection to the original ambient scheme. -/
@[reassoc (attr := simp)]
theorem baseChange_fst {S X Z T : Scheme.{u}}
    (p : X ⟶ S) (i : Z ⟶ X) (r : T ⟶ S) :
    baseChange p i r ≫ pullback.fst p r =
      pullback.fst (i ≫ p) r ≫ i := by
  exact pullback.lift_fst _ _ _

/-- An invertible base change gives a factorization for every test scheme over that base. -/
theorem factors_of_baseChange_isIso {S X Z T W : Scheme.{u}}
    (p : X ⟶ S) (i : Z ⟶ X) (r : T ⟶ S)
    [IsIso (baseChange p i r)] (t : W ⟶ X) (s : W ⟶ T)
    (h : t ≫ p = s ≫ r) : ∃ l : W ⟶ Z, l ≫ i = t := by
  refine ⟨pullback.lift t s h ≫ inv (baseChange p i r) ≫
    pullback.fst (i ≫ p) r, ?_⟩
  rw [Category.assoc, Category.assoc, ← baseChange_fst, IsIso.inv_hom_id_assoc,
    pullback.lift_fst]

/-- The image of the base-change projection lies in the image of the original map. -/
theorem range_fst_subset_of_baseChange_isIso {S X Z T : Scheme.{u}}
    (p : X ⟶ S) (i : Z ⟶ X) (r : T ⟶ S)
    [IsIso (baseChange p i r)] :
    Set.range (pullback.fst p r) ⊆ Set.range i := by
  obtain ⟨l, hl⟩ := factors_of_baseChange_isIso p i r
    (pullback.fst p r) (pullback.snd p r) pullback.condition
  rw [← hl, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  exact Set.image_subset_range _ _

/-- The zeroth positive adic thickening contains the closed point of the local base. -/
theorem closedPoint_mem_range_adicBase_zero
    (A : Type u) [CommRing A] [IsLocalRing A] :
    IsLocalRing.closedPoint A ∈ Set.range (adicBase A 0) := by
  change IsLocalRing.closedPoint A ∈
    Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk _))
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
  change RingHom.ker (Ideal.Quotient.mk _) ≤ IsLocalRing.maximalIdeal A
  simp

/-- An open of a finite scheme over a local ring containing the closed fibre is the whole scheme. -/
theorem open_eq_top_of_closed_fiber_subset
    (A : Type u) [CommRing A] [IsLocalRing A]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A)) [IsFinite p]
    (U : X.Opens) (hU : p ⁻¹' {IsLocalRing.closedPoint A} ⊆ U) : U = ⊤ := by
  apply top_le_iff.mp
  intro x _
  by_contra hx
  have hC := p.isClosedMap _ U.isOpen.isClosed_compl
  have hs : IsLocalRing.closedPoint A ∈ p '' (U : Set X)ᶜ :=
    (IsLocalRing.specializes_closedPoint (p x)).mem_closed hC ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hpy⟩ := hs
  exact hy (hU hpy)

/-- The closed-fibre test makes an arbitrary immersion into a finite scheme globally closed. -/
theorem isClosedImmersion_of_closed_fiber
    (A : Type u) [CommRing A] [IsLocalRing A]
    {X Z : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A)) (i : Z ⟶ X)
    [IsFinite p] [IsImmersion i] [IsIso (baseChange p i (adicBase A 0))] :
    IsClosedImmersion i := by
  have hU : i.coborderRange = ⊤ := by
    apply open_eq_top_of_closed_fiber_subset A p
    intro x hx
    have hx' : x ∈ Set.range (pullback.fst p (adicBase A 0)) := by
      rw [Scheme.Pullback.range_fst]
      change p x ∈ Set.range (adicBase A 0)
      rw [show p x = IsLocalRing.closedPoint A from hx]
      exact closedPoint_mem_range_adicBase_zero A
    have hxi := range_fst_subset_of_baseChange_isIso p i (adicBase A 0) hx'
    exact subset_coborder hxi
  have : IsIso i.coborderRange.ι := by
    rw [hU]
    change IsIso X.topIso.hom
    infer_instance
  rw [← i.liftCoborder_ι]
  infer_instance

/-- Finite-module Krull intersection detects zero in all positive extended-ideal quotients. -/
theorem finite_algebra_eq_zero
    (A B : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing B] (a : A →+* B) (ha : a.Finite) (b : B)
    (hb : ∀ n : ℕ, Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal A ^ (n + 1)).map a) b = 0) : b = 0 := by
  let := a.toAlgebra
  have : Module.Finite A B := ha
  apply IsHausdorff.haus (inferInstance : IsHausdorff (IsLocalRing.maximalIdeal A) B)
  intro n
  rw [SModEq.zero, Ideal.smul_top_eq_map]
  cases n with
  | zero => simp [Ideal.map_top]
  | succ n => exact Ideal.Quotient.eq_zero_iff_mem.mp (hb n)

set_option backward.isDefEq.respectTransparency false in
/-- The global-sections map of the inverse affine comparison is the canonical ring comparison. -/
theorem isoSpec_inv_appTop (X : Scheme.{u}) [IsAffine X] :
    X.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).inv := by
  change (inv X.toSpecΓ).appTop = _
  rw [Scheme.Hom.inv_appTop]
  simp [Scheme.toSpecΓ_appTop]

set_option backward.isDefEq.respectTransparency false in
/-- A section killed by `i` vanishes in every quotient whose spectrum factors through `i`. -/
theorem quotient_eq_zero_of_factors
    {X Z : Scheme.{u}} [IsAffine X] (i : Z ⟶ X)
    (J : Ideal Γ(X, ⊤)) (b : Γ(X, ⊤)) (hb : i.appTop b = 0)
    (hf : ∃ l : Spec (CommRingCat.of (Γ(X, ⊤) ⧸ J)) ⟶ Z,
      l ≫ i = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ X.isoSpec.inv) :
    Ideal.Quotient.mk J b = 0 := by
  obtain ⟨l, hl⟩ := hf
  have ht : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫
      X.isoSpec.inv).appTop b = 0 := by
    rw [← hl, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hb, map_zero]
  rw [Scheme.Hom.comp_appTop, isoSpec_inv_appTop,
    ← Scheme.ΓSpecIso_inv_naturality] at ht
  change (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, ⊤) ⧸ J))).inv
    (Ideal.Quotient.mk J b) = 0 at ht
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, ⊤) ⧸ J))).inv).1
  rw [map_zero]
  exact ht

/-- All positive adic base changes detect injectivity on global sections of the finite scheme. -/
theorem appTop_injective_of_adic_baseChange
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {X Z : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A)) (i : Z ⟶ X)
    [IsFinite p] (h : ∀ n : ℕ, IsIso (baseChange p i (adicBase A n))) :
    Function.Injective i.appTop := by
  have : IsAffine X := isAffine_of_isAffineHom p
  obtain ⟨a, ha⟩ := Spec.map_surjective (X.isoSpec.inv ≫ p)
  have hfin : a.hom.Finite := by
    apply (IsFinite.SpecMap_iff a).mp
    rw [ha]
    infer_instance
  apply (RingHom.injective_iff_ker_eq_bot i.appTop.hom).mpr
  apply eq_bot_iff.mpr
  intro b hb
  apply Ideal.mem_bot.mpr
  apply finite_algebra_eq_zero A Γ(X, ⊤) a.hom hfin b
  intro n
  let J : Ideal Γ(X, ⊤) := (IsLocalRing.maximalIdeal A ^ (n + 1)).map a.hom
  apply quotient_eq_zero_of_factors i J b (RingHom.mem_ker.mp hb)
  have := h n
  apply factors_of_baseChange_isIso p i (adicBase A n)
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ X.isoSpec.inv)
    (Spec.map (CommRingCat.ofHom (Ideal.quotientMap J a.hom Ideal.le_comap_map)))
  rw [Category.assoc, ← ha, ← Spec.map_comp, adicBase, ← Spec.map_comp]
  congr 1

/-- SGA 3, Exposé IX, Lemme 5.0, for arbitrary finite schemes and actual immersions. -/
theorem adicImmersionIsIso : AdicImmersionIsIsoStatement.{u} := by
  intro A _ _ _ X Z p i hp hi h
  let := hp
  let := hi
  have := h 0
  have : IsClosedImmersion i := isClosedImmersion_of_closed_fiber A p i
  have : IsAffine X := isAffine_of_isAffineHom p
  exact IsClosedImmersion.isIso_of_injective_of_isAffine (f := i)
    (appTop_injective_of_adic_baseChange A p i h)

end Langlands.AlgebraicGeometry.AdicDetection
