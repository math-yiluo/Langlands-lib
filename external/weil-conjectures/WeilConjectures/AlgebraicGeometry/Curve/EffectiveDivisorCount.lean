/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf
public import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
public import WeilConjectures.ZetaSeries
public import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
public import WeilConjectures.AlgebraicGeometry.Modules.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.Endomorphism
public import WeilConjectures.AlgebraicGeometry.Modules.HomObjSections
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus

/-!
# Effective divisors in a divisor class on a curve over a finite field

Let `C` be a smooth proper curve over a field `k` with `H⁰(C, 𝒪_C) = k`, and `ℳ` an invertible
`𝒪_C`-module. The effective divisors `E` whose ideal sheaf `𝒪_C(-E)` is isomorphic to `ℳ` are
the zero schemes of the nonzero morphisms `φ : ℳ ⟶ 𝒪_C`, and two such morphisms have the same
zero scheme if and only if they differ by a nonzero scalar. Hence, when `k` has `q` elements,
the number of these divisors is `(q^{h⁰(ℳᵛ)} - 1) / (q - 1)`, where `h⁰(ℳᵛ)` is the dimension of
`H⁰(C, ℳᵛ) = Hom(ℳ, 𝒪_C)`.

This is the count of the points of the complete linear system `|ℳᵛ|`, the input from
Riemann–Roch into the computation of the zeta function of a curve.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.Hom.exists_eq_comp_smulHom_of_zeroLocus_eq`: two morphisms
  `ℳ ⟶ 𝒪_C` with the same zero scheme differ by a scalar.
- `AlgebraicGeometry.Scheme.Divisor.sub_one_mul_card_idealSheaf_iso`: the count
  `(q - 1) · #{E | 𝒪_C(-E) ≅ ℳ} = q^{h⁰(ℳᵛ)} - 1`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

namespace Modules

variable {X : Scheme.{u}}

/-- **Morphisms to `𝒪_X` with the same zero scheme differ by a function.** If `φ, ψ : M ⟶ 𝒪_X`
from an invertible module have the same zero scheme, which is an effective Cartier divisor, then
`ψ = φ ≫ c` for a global function `c`: both identify `M` with the ideal sheaf of the divisor, and
an automorphism of `M` is multiplication by a function
(`AlgebraicGeometry.Scheme.Modules.exists_eq_smulHom`). -/
theorem Hom.exists_eq_comp_smulHom_of_zeroLocus_eq {M : X.Modules} [M.IsInvertible]
    {φ ψ : M ⟶ Modules.unit X} (hφ : φ.zeroLocus.IsInvertible)
    (h : φ.zeroLocus = ψ.zeroLocus) :
    ∃ c : Γ(X, ⊤), ψ = φ ≫ (Modules.unit X).smulHom c := by
  have := IsInvertible.sheafOfModules_isInvertible M
  obtain ⟨κφ, hκφ⟩ := φ.exists_iso_toModules_zeroLocus hφ
  obtain ⟨κψ, hκψ⟩ : ∃ κ : M ≅ φ.zeroLocus.toModules, κ.hom ≫ φ.zeroLocus.toModulesι = ψ := by
    rw [h]
    exact ψ.exists_iso_toModules_zeroLocus (h ▸ hφ)
  obtain ⟨c, hc⟩ := exists_eq_smulHom M (κψ.hom ≫ κφ.inv)
  refine ⟨c, ?_⟩
  calc ψ = (κψ.hom ≫ κφ.inv) ≫ φ := by
        rw [Category.assoc, (Iso.inv_comp_eq κφ).2 hκφ.symm, hκψ]
    _ = M.smulHom c ≫ φ := by rw [hc]
    _ = φ ≫ (Modules.unit X).smulHom c := smulHom_naturality φ c

end Modules

section Curve

variable {k : Type u} [Field k] {C : Scheme.{u}} [C.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))] [IsIntegral C] [IsNoetherian C]

include k in
/-- The ideal sheaf `𝒪_C(-E)` determines the effective divisor `E`. -/
lemma Divisor.idealSheaf_injective :
    Function.Injective (Divisor.idealSheaf (X := C)) := by
  intro E E' h
  ext P
  have h₁ := Divisor.ordAt_idealSheaf (C ↘ Spec (.of k)) E P
  have h₂ := Divisor.ordAt_idealSheaf (C ↘ Spec (.of k)) E' P
  rw [h] at h₁
  exact_mod_cast h₁.symm.trans h₂

include k in
/-- The zero scheme of a nonzero morphism `M ⟶ 𝒪_C` from an invertible module on a smooth
integral curve is the ideal sheaf of a unique effective divisor. -/
lemma Modules.Hom.existsUnique_zeroLocus_eq_idealSheaf {M : C.Modules} [M.IsInvertible]
    {φ : M ⟶ Modules.unit C} (hφ : φ ≠ 0) :
    ∃! E : closedPoints C →₀ ℕ, φ.zeroLocus = Divisor.idealSheaf E := by
  have := Modules.IsInvertible.sheafOfModules_isInvertible M
  have : SheafOfModules.IsInvertible.{u, u, u} (Modules.unit C) :=
    Modules.IsInvertible.sheafOfModules_isInvertible (𝟙_ C.Modules)
  obtain ⟨E, hE⟩ := (Modules.Hom.isInvertible_zeroLocus hφ).exists_eq_idealSheaf
    (C ↘ Spec (.of k))
  exact ⟨E, hE, fun E' hE' ↦ Divisor.idealSheaf_injective (k := k) (hE'.symm.trans hE)⟩

/-- A nonzero morphism `M ⟶ 𝒪_X` composed with multiplication by a unit `c` of `Γ(X, 𝒪_X)` has
the same zero scheme. -/
lemma Modules.Hom.zeroLocus_comp_smulHom {X : Scheme.{u}} {M : X.Modules}
    (φ : M ⟶ Modules.unit X) {c : Γ(X, ⊤)} (hc : IsUnit c) :
    (φ ≫ (Modules.unit X).smulHom c).zeroLocus = φ.zeroLocus := by
  obtain ⟨c, rfl⟩ := hc
  let e : Modules.unit X ≅ Modules.unit X :=
    { hom := (Modules.unit X).smulHom c
      inv := (Modules.unit X).smulHom ↑c⁻¹
      hom_inv_id := by rw [← Modules.smulHom_mul, Units.inv_mul, Modules.smulHom_one]
      inv_hom_id := by rw [← Modules.smulHom_mul, Units.mul_inv, Modules.smulHom_one] }
  exact (Modules.Hom.zeroLocus_eq_of_arrowIso φ (φ ≫ e.hom)
    (Arrow.isoMk (Iso.refl _) e (by simp))).symm

/-- **The effective divisors in a divisor class.** Let `C` be a smooth proper integral curve
over a finite field `k` with `q` elements and `H⁰(C, 𝒪_C) = k`, and let `ℳ` be an invertible
module. The effective divisors `E` with `𝒪_C(-E) ≅ ℳ` are the zero schemes of the nonzero
morphisms `ℳ ⟶ 𝒪_C`, two of which have the same zero scheme exactly when they differ by a
nonzero scalar; so there are `(q^{h⁰(ℳᵛ)} - 1) / (q - 1)` of them, where
`H⁰(C, ℳᵛ) = Hom(ℳ, 𝒪_C)`. -/
theorem Divisor.sub_one_mul_card_idealSheaf_iso [Finite k] [IsProper (C ↘ Spec (.of k))]
    [GlobalSectionsBijective k C] (M : C.Modules) [M.IsInvertible] :
    (Nat.card k - 1) * Nat.card {E : closedPoints C →₀ ℕ //
      Nonempty ((Divisor.idealSheaf E).toModules ≅ M)} = Nat.card k ^ Mᵛ.finrankH k 0 - 1 := by
  classical
  have := Modules.IsInvertible.sheafOfModules_isInvertible M
  have : SheafOfModules.IsInvertible.{u, u, u} (Modules.unit C) :=
    Modules.IsInvertible.sheafOfModules_isInvertible (𝟙_ C.Modules)
  let V := Mᵛ.H 0
  have : Finite V := Module.finite_of_finite k
  let Φ : V ≃+ (M ⟶ Modules.unit C) := Modules.homObjHZeroAddEquiv M _
  have hΦsmul (a : k) (v : V) :
      Φ (a • v) = Φ v ≫ (Modules.unit C).smulHom (globalSectionsRingHom k a) := by
    rw [Modules.smul_H_eq_globalSectionsRingHom_smul]
    exact Modules.homObjHZeroAddEquiv_smul _ _
  let T := {E : closedPoints C →₀ ℕ // Nonempty ((Divisor.idealSheaf E).toModules ≅ M)}
  have hne (v : {v : V // v ≠ 0}) : Φ v.1 ≠ 0 := fun h ↦ v.2 (Φ.map_eq_zero_iff.1 h)
  have hinv (v : {v : V // v ≠ 0}) := Modules.Hom.isInvertible_zeroLocus (hne v)
  have hex (v : {v : V // v ≠ 0}) :=
    (Modules.Hom.existsUnique_zeroLocus_eq_idealSheaf (k := k) (hne v)).exists
  choose E hE using hex
  have hET (v : {v : V // v ≠ 0}) : Nonempty ((Divisor.idealSheaf (E v)).toModules ≅ M) := by
    obtain ⟨κ, -⟩ := (Φ v.1).exists_iso_toModules_zeroLocus (hinv v)
    exact ⟨eqToIso (by rw [hE v]) ≪≫ κ.symm⟩
  let ε : {v : V // v ≠ 0} → T := fun v ↦ ⟨E v, hET v⟩
  have hεE (v w : {v : V // v ≠ 0}) :
      ε v = ε w ↔ (Φ v.1).zeroLocus = (Φ w.1).zeroLocus := by
    rw [hE, hE]
    refine ⟨fun h ↦ by rw [show E v = E w from congrArg Subtype.val h], fun h ↦ ?_⟩
    exact Subtype.ext (Divisor.idealSheaf_injective (k := k) h)
  -- two nonzero vectors with the same divisor differ by a nonzero scalar
  have hfib (v w : {v : V // v ≠ 0}) (h : ε v = ε w) : ∃ a : kˣ, w.1 = (a : k) • v.1 := by
    obtain ⟨c, hc⟩ :=
      Modules.Hom.exists_eq_comp_smulHom_of_zeroLocus_eq (hinv v) ((hεE v w).1 h)
    obtain ⟨a, rfl⟩ :=
      (GlobalSectionsBijective.bijective_globalSectionsRingHom (k := k) (X := C)).2 c
    have ha : a ≠ 0 := by
      rintro rfl
      apply hne w
      rw [hc, map_zero, Modules.smulHom_zero, Limits.comp_zero]
    exact ⟨Units.mk0 a ha, Φ.injective (by rw [Units.val_mk0, hΦsmul, ← hc])⟩
  have hsmul (v : {v : V // v ≠ 0}) (a : kˣ) :
      ε ⟨(a : k) • v.1, smul_ne_zero a.ne_zero v.2⟩ = ε v := by
    rw [hεE]
    change (Φ ((a : k) • v.1)).zeroLocus = _
    rw [hΦsmul]
    exact Modules.Hom.zeroLocus_comp_smulHom _ (a.isUnit.map _)
  have hsurj : Function.Surjective ε := by
    rintro ⟨E₀, ⟨e⟩⟩
    have hJ := Divisor.isInvertible_idealSheaf (C ↘ Spec (.of k)) E₀
    let φ : M ⟶ Modules.unit C := e.inv ≫ (Divisor.idealSheaf E₀).toModulesι
    have hφz : φ.zeroLocus = Divisor.idealSheaf E₀ := by
      rw [Modules.Hom.zeroLocus_eq_of_arrowIso φ (Divisor.idealSheaf E₀).toModulesι
        (Arrow.isoMk e.symm (Iso.refl _) (by simp [φ])), hJ.zeroLocus_toModulesι]
    have hφ0 : φ ≠ 0 := by
      intro h0
      have hι : (Divisor.idealSheaf E₀).toModulesι = 0 := by
        rw [← Iso.hom_inv_id_assoc e (Divisor.idealSheaf E₀).toModulesι]
        exact (congrArg (e.hom ≫ ·) h0).trans Limits.comp_zero
      have hz : IsZero (Divisor.idealSheaf E₀).toModules := by
        have : Mono (0 : (Divisor.idealSheaf E₀).toModules ⟶ Modules.unit C) := by
          rw [← hι]
          exact inferInstanceAs (Mono (kernel.ι _))
        exact IsZero.of_mono_zero _ (Modules.unit C)
      exact Modules.IsInvertible.not_isZero M (hz.of_iso e.symm)
    refine ⟨⟨Φ.symm φ, fun h ↦ hφ0 (by simpa using congrArg Φ h)⟩, Subtype.ext ?_⟩
    apply Divisor.idealSheaf_injective (k := k)
    rw [← hE]
    simpa using hφz
  -- counting
  let s := Function.surjInv hsurj
  have hs (t : T) : ε (s t) = t := Function.surjInv_eq hsurj t
  have hex' (v : {v : V // v ≠ 0}) := hfib (s (ε v)) v (hs (ε v))
  choose a ha using hex'
  have huniq {x : {v : V // v ≠ 0}} {b b' : kˣ} (h : (b : k) • x.1 = (b' : k) • x.1) :
      b = b' :=
    Units.ext (smul_left_injective k x.2 h)
  let e : {v : V // v ≠ 0} ≃ T × kˣ :=
    { toFun v := (ε v, a v)
      invFun p := ⟨(p.2 : k) • (s p.1).1, smul_ne_zero p.2.ne_zero (s p.1).2⟩
      left_inv v := Subtype.ext (ha v).symm
      right_inv p := by
        obtain ⟨t, b⟩ := p
        set w : {v : V // v ≠ 0} := ⟨(b : k) • (s t).1, smul_ne_zero b.ne_zero (s t).2⟩ with hw
        have hεw : ε w = t := (hsmul (s t) b).trans (hs t)
        refine Prod.ext hεw ?_
        have h1 := ha w
        change (b : k) • (s t).1 = (a w : k) • (s (ε w)).1 at h1
        rw [hεw] at h1
        exact (huniq h1).symm }
  have hcard := Nat.card_congr e
  rw [Nat.card_prod, Nat.card_units] at hcard
  have hV : Nat.card {v : V // v ≠ 0} + 1 = Nat.card V := by
    rw [← Nat.card_congr (Equiv.sumCompl (fun v : V ↦ v = 0)), Nat.card_sum,
      Nat.card_unique (α := {v : V // v = 0}), add_comm]
  have := Fintype.ofFinite k
  have := Fintype.ofFinite V
  have hVq : Nat.card V = Nat.card k ^ Mᵛ.finrankH k 0 := by
    rw [Nat.card_eq_fintype_card (α := V), Nat.card_eq_fintype_card (α := k),
      Module.card_eq_pow_finrank (K := k) (V := V)]
    rfl
  rw [mul_comm, ← hcard, ← hVq, ← hV, Nat.add_sub_cancel]

end Curve

section Degree

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- **The degree of a closed point.** The reduced closed subscheme on a closed point `P` of a
`k`-scheme is `Spec κ(P)`, so `dim_k Γ(P, 𝒪_P) = [κ(P) : k]`. -/
theorem finrankΓ_subschemeι_vanishingIdeal_singleton {P : X} (hP : IsClosed {P}) :
    ((IdealSheafData.vanishingIdeal ⟨{P}, hP⟩).subschemeι ≫ X ↘ Spec (.of k)).finrankΓ =
      (X ↘ Spec (.of k)).degreeOver P := by
  have := isClosed_singleton_iff_isClosedImmersion.1 hP
  set g := X.fromSpecResidueField P with hg
  have hker : g.ker = IdealSheafData.vanishingIdeal ⟨{P}, hP⟩ := by
    rw [← IdealSheafData.map_bot, ← nilradical_eq_bot, ← IdealSheafData.vanishingIdeal_top,
      IdealSheafData.map_vanishingIdeal]
    congr 1
    ext1
    rw [TopologicalSpace.Closeds.coe_closure, TopologicalSpace.Closeds.coe_top, Set.image_univ,
      hg, Scheme.range_fromSpecResidueField]
    exact hP.closure_eq
  rw [← hker, Scheme.Hom.finrankΓ_eq_of_iso (g.ker.subschemeι ≫ X ↘ Spec (.of k))
    (g ≫ X ↘ Spec (.of k)) (asIso g.toImage).symm (Iso.refl _) ?_]
  · rw [hg, ← Hom.specMap_residueFieldAlgebraMap]
    let := ((X ↘ Spec (.of k)).residueFieldAlgebraMap P).toAlgebra
    exact Scheme.Hom.finrankΓ_SpecMap k (X.residueField P)
  · rw [Iso.refl_hom, Spec.map_id, Category.comp_id, Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq,
      Hom.toImage_imageι_assoc]

variable [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]

/-- **The degree of an effective divisor.** For an effective divisor `E = ∑_P n_P [P]` on a
smooth proper curve over `k`, `dim_k Γ(E, 𝒪_E) = ∑_P n_P [κ(P) : k]`. -/
theorem Divisor.finrankΓ_subschemeι_idealSheaf (E : closedPoints X →₀ ℕ) :
    ((Divisor.idealSheaf E).subschemeι ≫ X ↘ Spec (.of k)).finrankΓ =
      E.sum fun P n ↦ n * (X ↘ Spec (.of k)).degreeOver P.1 := by
  induction E using Finsupp.induction_linear with
  | zero =>
    rw [Divisor.idealSheaf_zero, Finsupp.sum_zero_index]
    let := ((⊤ : X.IdealSheafData).subschemeι ≫ X ↘ Spec (.of k)).ΓAlgebra
    exact Module.finrank_zero_of_subsingleton
  | add E E' hE hE' =>
    have h₁ := Divisor.isInvertible_idealSheaf (X ↘ Spec (.of k)) E
    have h₂ := Divisor.isInvertible_idealSheaf (X ↘ Spec (.of k)) E'
    have := h₁.isFinite_subschemeι_comp (k := k)
    have := h₂.isFinite_subschemeι_comp (k := k)
    have := (h₁.mul h₂).isFinite_subschemeι_comp (k := k)
    rw [Divisor.idealSheaf_add, IdealSheafData.finrankΓ_subschemeι_mul_comp _ h₁ h₂, hE, hE',
      Finsupp.sum_add_index' (fun _ ↦ zero_mul _) fun _ _ _ ↦ add_mul _ _ _]
  | single P n =>
    have hP := isInvertible_vanishingIdeal_of_smoothOfRelativeDimension_one
      (X ↘ Spec (.of k)) P.2
    rw [Divisor.idealSheaf_single, hP.finrankΓ_subschemeι_pow_comp,
      finrankΓ_subschemeι_vanishingIdeal_singleton, Finsupp.sum_single_index (zero_mul _)]

end Degree

end AlgebraicGeometry.Scheme
