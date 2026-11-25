/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
public import WeilConjectures.RingTheory.Etale.Coordinates

/-!
# Étale charts adapted to a regular immersion

Let `i : Z ⟶ X` be a regular immersion of pure codimension `c` between schemes smooth over a
perfect field `k` (with `Z` regular). Near every point of `Z` there is an affine open `U` of `X`
with functions `f₁, …, f_c` generating the ideal of `Z ∩ U`, and an étale morphism
`v : U ⟶ 𝔸^c_{𝔸^m_k}` whose `c` fibre coordinates pull back to the `fᵢ`.

## Main results

- `AlgebraicGeometry.locally_isStandardSmoothOfRelativeDimension_appLE`: the ring-theoretic
  meaning of smoothness of relative dimension `n` of `U ⟶ X ⟶ Spec k` for an affine open `U`.
- `AlgebraicGeometry.IsRegularImmersion.exists_etale_affineSpace`: the étale chart.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

set_option backward.isDefEq.respectTransparency false in
/-- If `U` is an affine open of `X` on which `aX : X ⟶ Spec k` is smooth of relative dimension
`n`, then `k → Γ(X, U)` is locally standard smooth of relative dimension `n`. -/
theorem locally_isStandardSmoothOfRelativeDimension_appLE {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) {U : X.Opens} (hU : IsAffineOpen U) (n : ℕ)
    [SmoothOfRelativeDimension n (U.ι ≫ aX)] :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      ((aX.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom) := by
  have : IsAffine U.toScheme := hU
  have H := (HasRingHomProperty.iff_of_isAffine
    (P := @SmoothOfRelativeDimension n) (f := U.ι ≫ aX)).mp inferInstance
  have key : (U.ι ≫ aX).appTop = aX.appLE ⊤ U le_top ≫ U.topIso.inv := by
    simp only [Scheme.Hom.comp_appTop, Scheme.Opens.ι_appTop, Scheme.Hom.appLE,
      Scheme.Opens.topIso, Functor.mapIso_inv, Iso.op_inv, eqToIso.inv, Category.assoc,
      ← Functor.map_comp]
    rfl
  have hQ := RingHom.locally_respectsIso
    (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n))
  rw [key, CommRingCat.hom_comp, hQ.cancel_right_isIso] at H
  rw [← CommRingCat.hom_comp]
  exact (hQ.cancel_left_isIso _ _).mpr H

open IsRegularImmersion in
set_option backward.isDefEq.respectTransparency false in
/-- **Étale charts adapted to a regular immersion.** Let `i : Z ⟶ X` be a regular immersion of
pure codimension `c`, with `X` smooth over a perfect field `k` and `Z` regular. Then every point
`z` of `Z` has an affine open neighbourhood `U` in `X` with functions `f₁, …, f_c` on `U`
generating the ideal of `Z ∩ U`, together with an étale morphism `v : U ⟶ 𝔸^c_{𝔸^m_k}` whose
`c` fibre coordinates pull back to the `fᵢ`. -/
theorem IsRegularImmersion.exists_etale_affineSpace [PerfectField k] {X Z : Scheme.{u}}
    (c : ℕ) (i : Z ⟶ X) [IsRegularImmersion c i] (aX : X ⟶ Spec (.of k)) [Smooth aX]
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) (z : Z) :
    ∃ (U : X.affineOpens) (_ : i.base z ∈ U.1) (f : Fin c → Γ(X, U.1)) (m : ℕ)
      (v : U.1.toScheme ⟶ 𝔸(ULift.{u} (Fin c); 𝔸(ULift.{u} (Fin m); Spec (.of k)))),
      Ideal.span (Set.range f) = (Scheme.Hom.ker i).ideal U ∧ Etale v ∧
        ∀ a, v.appTop (AffineSpace.coord _ (ULift.up a)) = U.1.topIso.inv (f a) := by
  classical
  obtain ⟨W, hW, hzW, n, m, hmn, hXW, hZW⟩ :=
    exists_isAffineOpen_smoothOfRelativeDimension c i aX hZ z
  obtain ⟨U₀, hzU₀, r, hr, hreg, hI⟩ :=
    exists_isWeaklyRegular_generators (c := c) (i := i) (i z)
  obtain ⟨_, ⟨U', hU, rfl⟩, hzU, hUle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show i z ∈ (W ⊓ U₀.1 : X.Opens) from ⟨hzW, hzU₀⟩) (W ⊓ U₀.1).isOpen
  let U : X.Opens := U'
  replace hU : IsAffineOpen U := hU
  replace hzU : i z ∈ U := hzU
  have hUW : U ≤ W := fun x hx ↦ (hUle hx).1
  have hUU₀ : U ≤ U₀.1 := fun x hx ↦ (hUle hx).2
  -- smoothness on `U`
  have hXU : SmoothOfRelativeDimension n (U.ι ≫ aX) := by
    rw [← X.homOfLE_ι hUW, Category.assoc]
    have : SmoothOfRelativeDimension (0 + n) (X.homOfLE hUW ≫ W.ι ≫ aX) := inferInstance
    simpa using this
  have hiUW : i ⁻¹ᵁ U ≤ i ⁻¹ᵁ W := fun x hx ↦ hUW hx
  have hZU : SmoothOfRelativeDimension m ((i ⁻¹ᵁ U).ι ≫ i ≫ aX) := by
    rw [← Z.homOfLE_ι hiUW, Category.assoc]
    have : SmoothOfRelativeDimension (0 + m) (Z.homOfLE hiUW ≫ (i ⁻¹ᵁ W).ι ≫ i ≫ aX) :=
      inferInstance
    simpa using this
  -- generators on `U`
  obtain ⟨-, hIU⟩ := isWeaklyRegular_ofList_restrict (U₀ := ⟨U, hU⟩) hUU₀ hreg hI
  set r₀ := r.map (X.presheaf.map (homOfLE hUU₀).op).hom
  have hr₀ : r₀.length = c := by simp [r₀, hr]
  let f : Fin c → Γ(X, U) := r₀.get ∘ Fin.cast hr₀.symm
  have hf : Ideal.span (Set.range f) = i.ker.ideal ⟨U, hU⟩ := by
    have : Set.range f = {x | x ∈ r₀} := by
      rw [← Set.range_list_get]
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨_, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨Fin.cast hr₀ j, by simp [f]⟩
    rw [← hIU, Ideal.ofList, this]
  -- the rings
  let A := Γ(X, U)
  let B := Γ(Z, i ⁻¹ᵁ U)
  let : Algebra A B := (i.app U).hom.toAlgebra
  let : Algebra k A :=
    ((aX.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  let : Algebra k B := ((algebraMap A B).comp (algebraMap k A)).toAlgebra
  have : IsScalarTower k A B := .of_algebraMap_eq fun _ ↦ rfl
  have hsurj : Function.Surjective (algebraMap A B) := i.app_surjective U hU
  have hker : RingHom.ker (algebraMap A B) = i.ker.ideal ⟨U, hU⟩ :=
    (Scheme.Hom.ker_apply i ⟨U, hU⟩).symm
  obtain ⟨hsmA, hrkA⟩ := (Algebra.locally_isStandardSmoothOfRelativeDimension_iff
    (R := k) (S := A) n).mp (locally_isStandardSmoothOfRelativeDimension_appLE aX hU n)
  have hBloc : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension m)
      (algebraMap k B) := by
    have := locally_isStandardSmoothOfRelativeDimension_appLE (i ≫ aX) (hU.preimage i) m
    convert this using 2
    have e : aX.appLE ⊤ U le_top ≫ i.app U = (i ≫ aX).appLE ⊤ (i ⁻¹ᵁ U) le_top := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    rw [← e]
    rfl
  obtain ⟨hsmB, hrkB⟩ := (Algebra.locally_isStandardSmoothOfRelativeDimension_iff
    (R := k) (S := B) m).mp hBloc
  -- the prime of `i z`
  let p : Ideal A :=
    Ideal.comap (X.presheaf.germ U (i z) hzU).hom (IsLocalRing.maximalIdeal _)
  have hmemp : ∀ s, s ∈ p ↔ i z ∉ X.basicOpen s := fun s ↦ by
    rw [X.mem_basicOpen _ _ hzU, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hkp : RingHom.ker (algebraMap A B) ≤ p := by
    have hsupp : i z ∈ X.zeroLocus (U := U) (i.ker.ideal ⟨U, hU⟩) :=
      (Scheme.IdealSheafData.mem_support_iff_of_mem hzU).mp
        (i.range_subset_ker_support ⟨z, rfl⟩)
    intro s hs
    rw [hker] at hs
    exact (hmemp s).mpr ((X.mem_zeroLocus_iff _ _).mp hsupp s hs)
  obtain ⟨a, g, hap, hψ⟩ := Algebra.exists_etale_aeval_sumElim_of_ker hsurj f
    (hf.trans hker.symm) hrkA hrkB hmn p hkp
  -- the basic open `D(a)` and the generators on it
  have hzU' : i z ∈ X.basicOpen a := by
    by_contra h
    exact hap ((hmemp a).mpr h)
  let U' : X.affineOpens := X.affineBasicOpen (U := ⟨U, hU⟩) a
  have hU'le : U'.1 ≤ U := X.basicOpen_le a
  let ρ := (X.presheaf.map (homOfLE hU'le).op).hom
  let f' : Fin c → Γ(X, U'.1) := ρ ∘ f
  have hf' : Ideal.span (Set.range f') = i.ker.ideal U' := by
    rw [Set.range_comp, ← Ideal.map_span, hf]
    exact Scheme.IdealSheafData.map_ideal _ (U := U') (V := ⟨U, hU⟩) hU'le
  -- the étale ring map
  have := hU.isLocalization_basicOpen a
  let T := Localization.Away a
  let eT : T ≃ₐ[A] Γ(X, X.basicOpen a) := IsLocalization.algEquiv (Submonoid.powers a) T _
  let ψ := (MvPolynomial.aeval (algebraMap A T ∘ Sum.elim f g) :
    MvPolynomial (Fin c ⊕ Fin m) k →ₐ[k] T).toRingHom
  let ε : MvPolynomial (ULift.{u} (Fin c)) (MvPolynomial (ULift.{u} (Fin m)) k) ≃+*
      MvPolynomial (Fin c ⊕ Fin m) k :=
    ((MvPolynomial.renameEquiv _ Equiv.ulift).toRingEquiv.trans
      (MvPolynomial.mapEquiv (Fin c) (MvPolynomial.renameEquiv k Equiv.ulift).toRingEquiv)).trans
      (MvPolynomial.sumRingEquiv k (Fin c) (Fin m)).symm
  have hε : ∀ j, ε (MvPolynomial.X (ULift.up j)) = MvPolynomial.X (Sum.inl j) := by
    intro j
    simp [ε, MvPolynomial.sumRingEquiv_symm_X]
  let e₁ := U'.1.topIso.symm.commRingCatIsoToRingEquiv
  let φ := (e₁.toRingHom.comp eT.toRingEquiv.toRingHom).comp (ψ.comp ε.toRingHom)
  have hφ : φ.Etale := RingHom.Etale.respectsIso.1 _ e₁
    (RingHom.Etale.respectsIso.1 _ eT.toRingEquiv (RingHom.Etale.respectsIso.2 ψ ε hψ))
  have hφX : ∀ j, φ (MvPolynomial.X (ULift.up j)) = U'.1.topIso.inv (f' j) := by
    intro j
    change e₁ (eT (ψ (ε (MvPolynomial.X (ULift.up j))))) = _
    rw [hε]
    simp only [ψ, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.aeval_X,
      Function.comp_apply, Sum.elim_inl, AlgEquiv.commutes]
    rfl
  -- the étale morphism
  have : IsAffine U'.1.toScheme := U'.2
  let eA := AffineSpace.SpecIso (ULift.{u} (Fin m)) (.of k)
  have : IsIso (AffineSpace.map (ULift.{u} (Fin c)) eA.inv) :=
    ⟨⟨AffineSpace.map _ eA.hom, by rw [← AffineSpace.map_comp, eA.inv_hom_id, AffineSpace.map_id],
      by rw [← AffineSpace.map_comp, eA.hom_inv_id, AffineSpace.map_id]⟩⟩
  let E := (AffineSpace.SpecIso (ULift.{u} (Fin c))
      (.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv ≫
    AffineSpace.map (ULift.{u} (Fin c)) eA.inv
  let v := U'.1.toScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ E
  refine ⟨U', hzU', f', m, v, hf', ?_, fun j ↦ ?_⟩
  · have : Etale (Spec.map (CommRingCat.ofHom φ)) := HasRingHomProperty.Spec_iff.mpr hφ
    infer_instance
  · simp only [v, E, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.map_appTop_coord]
    rw [AffineSpace.SpecIso_inv_appTop_coord]
    have key : (Spec.map (CommRingCat.ofHom φ)).appTop ((Scheme.ΓSpecIso _).inv
        (MvPolynomial.X (ULift.up j))) =
        (Scheme.ΓSpecIso Γ(U'.1.toScheme, ⊤)).inv (φ (MvPolynomial.X (ULift.up j))) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
      rfl
    erw [key]
    rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop, Iso.inv_hom_id_apply, hφX]

end AlgebraicGeometry
