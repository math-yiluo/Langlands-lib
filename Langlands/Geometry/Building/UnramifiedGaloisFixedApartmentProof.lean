import Langlands.Geometry.Building.UnramifiedSpecialApartmentStatement
import Langlands.Geometry.Building.SplitApartmentGaloisFixedPoint
import Langlands.GroupScheme.ComponentGaloisContinuityProof
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-! # Galois-fixed points of stable apartments over algebraic coefficient extensions -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

section Barycenter

/-- A group acting by affine equivalences on a real affine space fixes the barycenter of
every finite orbit. -/
theorem exists_fixed_of_finite_orbit {M V P : Type*} [Group M]
    [AddCommGroup V] [Module ℝ V] [AddTorsor V P]
    (ρ : M →* (P ≃ᵃ[ℝ] P)) (p : P) (h : (Set.range fun m => ρ m p).Finite) :
    ∃ x : P, ∀ m, ρ m x = x := by
  classical
  set O : Finset P := h.toFinset with hO
  have hmem : ∀ q, q ∈ O ↔ ∃ m, ρ m p = q := fun q => by
    rw [hO, Set.Finite.mem_toFinset, Set.mem_range]
  have hp : p ∈ O := (hmem p).2 ⟨1, by rw [map_one]; rfl⟩
  set N : ℝ := (O.card : ℝ)
  have hN : N ≠ 0 := by
    simp only [N, ne_eq, Nat.cast_eq_zero, Finset.card_eq_zero]
    exact Finset.ne_empty_of_mem hp
  let c : V := N⁻¹ • ∑ q ∈ O, (q -ᵥ p)
  refine ⟨c +ᵥ p, fun m => ?_⟩
  have hlin : (ρ m).linear c = N⁻¹ • ∑ q ∈ O, (ρ m q -ᵥ ρ m p) := by
    simp only [c, map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    exact (ρ m).toAffineMap.linearMap_vsub q p
  have hperm : ∑ q ∈ O, (ρ m q -ᵥ p) = ∑ q ∈ O, (q -ᵥ p) := by
    refine Finset.sum_nbij' (ρ m) (ρ m⁻¹) ?_ ?_ ?_ ?_ (fun q _ => rfl)
    · intro q hq
      obtain ⟨n, rfl⟩ := (hmem q).1 hq
      refine (hmem _).2 ⟨m * n, ?_⟩
      rw [map_mul]
      rfl
    · intro q hq
      obtain ⟨n, rfl⟩ := (hmem q).1 hq
      refine (hmem _).2 ⟨m⁻¹ * n, ?_⟩
      rw [map_mul]
      rfl
    · intro q _
      change (ρ m⁻¹ * ρ m) q = q
      rw [← map_mul, inv_mul_cancel, map_one]
      rfl
    · intro q _
      change (ρ m * ρ m⁻¹) q = q
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
  have hsum : ∑ q ∈ O, (ρ m q -ᵥ ρ m p) =
      (∑ q ∈ O, (q -ᵥ p)) - N • (ρ m p -ᵥ p) := by
    have hsplit : ∀ q : P, ρ m q -ᵥ ρ m p = (ρ m q -ᵥ p) - (ρ m p -ᵥ p) :=
      fun q => (vsub_sub_vsub_cancel_right _ _ p).symm
    rw [Finset.sum_congr rfl fun q _ => hsplit q, Finset.sum_sub_distrib, hperm,
      Finset.sum_const]
    simp only [N, Nat.cast_smul_eq_nsmul]
  rw [AffineEquiv.map_vadd, hlin, hsum, smul_sub, smul_smul, inv_mul_cancel₀ hN, one_smul]
  have hq : ρ m p = (ρ m p -ᵥ p) +ᵥ p := (vsub_vadd _ _).symm
  calc (N⁻¹ • ∑ q ∈ O, (q -ᵥ p) - (ρ m p -ᵥ p)) +ᵥ ρ m p
      = (N⁻¹ • ∑ q ∈ O, (q -ᵥ p) - (ρ m p -ᵥ p)) +ᵥ ((ρ m p -ᵥ p) +ᵥ p) := by
        rw [← hq]
    _ = c +ᵥ p := by rw [vadd_vadd, sub_add_cancel]

end Barycenter

namespace KPApartmentData

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

variable [Mono (CategoryTheory.Functor.map
    (GroupScheme.baseChange (algebraBaseMap k K)) i).hom.hom.left] {ω : Kˣ → ℝ}

/-- **Open fixers on a stable apartment.** For an algebraic coefficient extension, a group
of finite type and finitely many upstairs relative roots, there is a finite intermediate
field `E` such that every coefficient automorphism fixing `E` pointwise and every root
fixes the chosen point `x`. -/
theorem exists_finite_fixing_field [Algebra.IsAlgebraic k K] [LocallyOfFiniteType G.X.hom]
    (D : KPApartmentData (S := T_K) i_K ω) (hD : GaloisStable k K i D)
    (hΦ : (relativeRoots (T := T_K) i_K).Finite) (x : D.Apartment) :
    ∃ E : IntermediateField k K, FiniteDimensional k E ∧
      ∀ σ ∈ E.fixingSubgroup, galoisRootAction k K i σ = 1 →
        galoisAction k K i D hD σ x = x := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Finite (relativeRoots (T := T_K) i_K) := hΦ.to_subtype
  have hu : ∀ a : relativeRoots (T := T_K) i_K, ∃ u ∈ rootGroupPoints (S := T_K) i_K a.val,
      x.val a.val u ≠ ⊤ := fun a => x.isValuation.exists_ne_top a.2
  choose u _ hne using hu
  obtain ⟨E, hE, hfix⟩ := IdentityComponent.exists_finite_fixing_algHoms k K
    (fun a : relativeRoots (T := T_K) i_K =>
      GaloisPoint.coordinates k G K (baseChangeCoeffEquiv k K G (u a)))
  refine ⟨E, hE, fun σ hσ hroot => ?_⟩
  have hσ' : σ⁻¹ ∈ E.fixingSubgroup := E.fixingSubgroup.inv_mem hσ
  have hroot' : galoisRootAction k K i σ⁻¹ = 1 := by rw [map_inv, hroot, inv_one]
  have hpt : ∀ a : relativeRoots (T := T_K) i_K, rationalConjugate k K G σ⁻¹ (u a) = u a := by
    intro a
    apply (baseChangeCoeffEquiv k K G).injective
    rw [baseChangeCoeffEquiv_rationalConjugate]
    apply (GaloisPoint.coordinates k G K).injective
    ext c
    rw [GaloisPoint.coordinates_conjugate]
    exact DFunLike.congr_fun (hfix σ⁻¹ hσ' a) c
  have hchar : ∀ a : relativeRoots (T := T_K) i_K,
      characterLattice.galoisRepresentation k K T σ⁻¹ a.val = a.val := by
    intro a
    have h := congrArg (fun π : Equiv.Perm (relativeRoots (T := T_K) i_K) => (π a).val) hroot'
    simpa only [galoisRootAction_val, Equiv.Perm.coe_one, id_eq] using h
  obtain ⟨v, hv⟩ := (galoisStable_iff_equipollent k K i D x).1 hD σ
  have hann : v ∈ rootAnnihilator (S := T_K) i_K := by
    rw [mem_rootAnnihilator]
    intro a ha
    have h1 := congrArg (fun φ : RootFunctionFamily T_K G_K => φ a (u ⟨a, ha⟩)) hv
    simp only [RootFunctionFamily.galoisAction_apply, RootFunctionFamily.vadd_apply] at h1
    rw [hchar ⟨a, ha⟩, hpt ⟨a, ha⟩] at h1
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 (hne ⟨a, ha⟩)
    rw [← ht, ← WithTop.coe_add, WithTop.coe_inj] at h1
    linarith
  apply Apartment.ext
  rw [galoisAction_val, hv]
  exact x.isValuation.vadd_eq_self_iff.2 hann

/-- **Galois-fixed points over algebraic extensions.** A Galois-stable apartment class over an
algebraic coefficient extension, for a group of finite type with finitely many upstairs
relative roots, has a point fixed by every coefficient automorphism. -/
theorem exists_galoisFixed_of_isAlgebraic [Algebra.IsAlgebraic k K]
    [LocallyOfFiniteType G.X.hom]
    (D : KPApartmentData (S := T_K) i_K ω) (hD : GaloisStable k K i D)
    (hΦ : (relativeRoots (T := T_K) i_K).Finite) :
    ∃ x : D.Apartment, ∀ σ : K ≃ₐ[k] K,
      RootFunctionFamily.galoisAction k K T G σ x.val = x.val := by
  classical
  obtain ⟨x₀⟩ : Nonempty D.Apartment := inferInstance
  let ρ := galoisAffineAction k K i D hD
  obtain ⟨E, hE, hfix⟩ := exists_finite_fixing_field k K i D hD hΦ x₀
  have : FiniteDimensional k E := hE
  have : Finite (relativeRoots (T := T_K) i_K) := hΦ.to_subtype
  let q : (K ≃ₐ[k] K) → Equiv.Perm (relativeRoots (T := T_K) i_K) × (E →ₐ[k] K) :=
    fun σ => (galoisRootAction k K i σ, σ.toAlgHom.comp E.val)
  have hq : ∀ σ τ, q σ = q τ → ρ σ x₀ = ρ τ x₀ := by
    intro σ τ h
    have h1 : τ⁻¹ * σ ∈ E.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      have h2 := DFunLike.congr_fun (congrArg Prod.snd h) ⟨y, hy⟩
      change σ y = τ y at h2
      rw [AlgEquiv.mul_apply, h2, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    have hfst : galoisRootAction k K i σ = galoisRootAction k K i τ := congrArg Prod.fst h
    have h2 : galoisRootAction k K i (τ⁻¹ * σ) = 1 := by
      rw [map_mul, map_inv, hfst]
      exact inv_mul_cancel _
    calc ρ σ x₀ = ρ (τ * (τ⁻¹ * σ)) x₀ := by rw [mul_inv_cancel_left]
      _ = ρ τ (ρ (τ⁻¹ * σ) x₀) := by rw [map_mul]; rfl
      _ = ρ τ x₀ := by rw [galoisAffineAction_apply k K i D hD (τ⁻¹ * σ), hfix _ h1 h2]
  have hfin : (Set.range fun σ => ρ σ x₀).Finite := by
    let g : Set.range q → D.Apartment := fun y => ρ y.2.choose x₀
    refine (Set.finite_range g).subset ?_
    rintro _ ⟨σ, rfl⟩
    refine ⟨⟨q σ, σ, rfl⟩, ?_⟩
    exact hq _ _ (⟨q σ, σ, rfl⟩ : Set.range q).2.choose_spec
  obtain ⟨x, hx⟩ := exists_fixed_of_finite_orbit ρ x₀ hfin
  exact ⟨x, fun σ => congrArg Apartment.val (hx σ)⟩

end KPApartmentData

/-- **Galois-fixed points of stable special apartments** (KP §9.2.1, as corrected). -/
theorem unramifiedGaloisFixedApartment : UnramifiedGaloisFixedApartmentStatement.{u} := by
  intro F _ _ _ _ G hG T i hi D hD
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Mono ((GroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).map i).hom.hom.left :=
    mono_of_isMaximalSplitTorus hi
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
    change IsAffineHom
      (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
    infer_instance
  have : LocallyOfFiniteType (baseChanged F (inertiaFixedField F) G).X.hom := by
    change LocallyOfFiniteType
      (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
    infer_instance
  exact KPApartmentData.exists_galoisFixed_of_isAlgebraic F (inertiaFixedField F) i D hD
    (hi.isSplitSubtorus.1.finite_relativeRoots _)

end Langlands.Geometry.Building
