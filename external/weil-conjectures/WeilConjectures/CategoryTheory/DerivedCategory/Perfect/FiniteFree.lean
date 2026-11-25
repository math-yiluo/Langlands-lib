/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Free
public import Mathlib.RingTheory.LocalRing.Module
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.BaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.OfFlat

/-!
# Finite free models of perfect complexes

Let `K` be a complex of flat modules over a commutative ring `A`, concentrated in degrees
`[a, b]`, which is perfect in `D(A)`. We realise `K` at the chain level by finite free complexes,
locally on `Spec A`:

* `DerivedCategory.exists_quasiIso_of_isStrictlyLE_of_projective`: an isomorphism `Q P ≅ Q K`
  in the derived category with `P` a bounded above complex of projectives comes from a
  quasi-isomorphism `P ⟶ K` (`P` is K-projective).
* `CochainComplex.exists_free_away_tensor_X`: a bounded complex of finitely generated projective
  modules becomes a complex of finite free modules after inverting some `s ∉ p`.
* `DerivedCategory.exists_quasiIso_projective_finite_of_isPerfect`: there is a quasi-isomorphism
  `P ⟶ K` from a complex `P` of finitely generated projective modules in degrees `[a, b]`
  (Stacks 0658, 066N): truncate a projective model above at `b` (the cycles are projective since
  the complex is exact above `b`) and below at `a` (the cokernel in degree `a` is finitely
  presented, and flat because `K` is a complex of flat modules in degrees `[a, b]`).
* `DerivedCategory.exists_quasiIso_free_away_of_isPerfect`: for every prime `p` there are
  `s ∉ p`, a complex `P` of finite free `A_s`-modules in degrees `[a, b]` and a
  quasi-isomorphism `P ⟶ A_s ⊗[A] K`. Over a Noetherian ring it suffices that `K` has finitely
  generated cohomology (`DerivedCategory.exists_quasiIso_free_away_of_finite_homology`).

This is the chain-level input for blueprint `lemma-coherent-base-change-invertible-sheaves` (a)
(Mumford's complex).
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace CochainComplex

variable {A : Type u} [CommRing A]

/-- Let `C` be a bounded above complex of finitely generated projective modules, exact in
degrees `> n`. Then the cycles `Zᵏ` are finitely generated projective for `k ≥ n`: the
surjections `Cᵏ ⟶ Zᵏ⁺¹` split, by downward induction. -/
lemma projective_finite_ker_d_of_exactAt (C : CochainComplex (ModuleCat.{u} A) ℤ) (N : ℤ)
    [C.IsStrictlyLE N] (hC : ∀ k, Module.Projective A (C.X k) ∧ Module.Finite A (C.X k))
    {n : ℤ} (hex : ∀ k, n < k → C.ExactAt k) (k : ℤ) (hk : n ≤ k) :
    Module.Projective A (LinearMap.ker (C.d k (k + 1)).hom) ∧
      Module.Finite A (LinearMap.ker (C.d k (k + 1)).hom) := by
  suffices h : ∀ t : ℕ, ∀ k : ℤ, n ≤ k → N < k + t →
      Module.Projective A (LinearMap.ker (C.d k (k + 1)).hom) ∧
        Module.Finite A (LinearMap.ker (C.d k (k + 1)).hom) from
    h (N + 1 - k).toNat k hk (by lia)
  intro t
  induction t with
  | zero =>
    intro k _ hk
    have : Subsingleton (C.X k) :=
      ModuleCat.subsingleton_of_isZero (C.isZero_of_isStrictlyLE N k (by simpa using hk))
    exact ⟨inferInstance, inferInstance⟩
  | succ t ih =>
    intro k hk hkt
    obtain ⟨h₁, -⟩ := ih (k + 1) (by lia) (by lia)
    obtain ⟨hP, hF⟩ := hC k
    obtain ⟨σ, hσ⟩ := (C.dToKer k).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.2 (C.surjective_dToKer k (hex _ (by lia))))
    let ρ : C.X k →ₗ[A] LinearMap.ker (C.d k (k + 1)).hom :=
      (LinearMap.id - σ ∘ₗ C.dToKer k).codRestrict _ fun x ↦ by
        have h := congrArg Subtype.val (LinearMap.congr_fun hσ (C.dToKer k x))
        simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
        rw [LinearMap.mem_ker, LinearMap.sub_apply, map_sub, LinearMap.id_apply,
          LinearMap.comp_apply, ← C.subtype_comp_dToKer k, LinearMap.comp_apply,
          LinearMap.comp_apply, Submodule.subtype_apply, Submodule.subtype_apply, h, sub_self]
    have hρ : ρ ∘ₗ (LinearMap.ker (C.d k (k + 1)).hom).subtype = LinearMap.id := by
      ext ⟨x, hx⟩
      have : C.dToKer k x = 0 := Subtype.ext hx
      simp [ρ, this]
    exact ⟨Module.Projective.of_split _ _ hρ,
      Module.Finite.of_surjective ρ fun y ↦ ⟨y, LinearMap.congr_fun hρ y⟩⟩

/-- The terms of the truncation `τ^{≤ n} C` of a complex of finitely generated projective modules
whose cycles in degree `n` are finitely generated projective are finitely generated projective. -/
lemma projective_finite_truncLE_X (C : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (hC : ∀ k, Module.Projective A (C.X k) ∧ Module.Finite A (C.X k))
    (hZ : Module.Projective A (LinearMap.ker (C.d n (n + 1)).hom) ∧
      Module.Finite A (LinearMap.ker (C.d n (n + 1)).hom))
    (i : ℤ) : Module.Projective A ((C.truncLE n).X i) ∧ Module.Finite A ((C.truncLE n).X i) := by
  rcases lt_trichotomy i n with h | rfl | h
  · obtain ⟨_, _⟩ := hC i
    let e := (C.truncLEXIso n i h).toLinearEquiv
    exact ⟨Module.Projective.of_equiv e.symm, Module.Finite.equiv e.symm⟩
  · have hZ' : Module.Projective A (C.sc i).moduleCatLeftHomologyData.K ∧
        Module.Finite A (C.sc i).moduleCatLeftHomologyData.K := by
      change Module.Projective A (LinearMap.ker (C.d i ((ComplexShape.up ℤ).next i)).hom) ∧
        Module.Finite A (LinearMap.ker (C.d i ((ComplexShape.up ℤ).next i)).hom)
      rw [CochainComplex.next]
      exact hZ
    obtain ⟨_, _⟩ := hZ'
    let e := (C.truncLEXIsoCycles i ≪≫ (C.sc i).moduleCatCyclesIso).toLinearEquiv
    exact ⟨Module.Projective.of_equiv e.symm, Module.Finite.equiv e.symm⟩
  · have : Subsingleton ((C.truncLE n).X i) :=
      ModuleCat.subsingleton_of_isZero ((C.truncLE n).isZero_of_isStrictlyLE n i h)
    exact ⟨inferInstance, inferInstance⟩

/-- The opcycles `Cⁱ / d(Cⁱ⁻¹)` of a complex of finitely presented modules are finitely
presented. -/
lemma finitePresentation_opcycles (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (hC : ∀ k, Module.FinitePresentation A (C.X k)) (i : ℤ) :
    Module.FinitePresentation A (C.opcycles i) := by
  let S := C.sc i
  have : Module.FinitePresentation A S.X₂ := hC i
  have : Module.FinitePresentation A S.X₁ := hC _
  have : Module.FinitePresentation A (S.X₂ ⧸ LinearMap.range S.f.hom) :=
    Module.finitePresentation_of_surjective (LinearMap.range S.f.hom).mkQ
      (Submodule.mkQ_surjective _) (by
        rw [Submodule.ker_mkQ, LinearMap.range_eq_map]
        exact (Module.Finite.fg_top).map _)
  exact Module.FinitePresentation.of_equiv S.moduleCatOpcyclesIso.toLinearEquiv.symm

/-- Let `β : X ⟶ Y` be a quasi-isomorphism between complexes concentrated in degrees `[a, b]`,
where `Y` consists of flat modules and `Xᵏ` is flat for `k > a`. Then `Xᵃ` is flat as well.

The mapping cone `M` of `β` is acyclic, with `Mᵏ = Xᵏ⁺¹ ⊕ Yᵏ` flat for `k ≥ a`, so its cycles
are flat in degrees `≥ a`; and `Xᵃ = Mᵃ⁻¹` is isomorphic to the cycles `Zᵃ(M)`. -/
lemma flat_X_of_quasiIso {X Y : CochainComplex (ModuleCat.{u} A) ℤ} (β : X ⟶ Y) [QuasiIso β]
    (a b : ℤ) [X.IsStrictlyGE a] [X.IsStrictlyLE b] [Y.IsStrictlyGE a] [Y.IsStrictlyLE b]
    (hX : ∀ k, a < k → Module.Flat A (X.X k)) (hY : ∀ k, Module.Flat A (Y.X k)) :
    Module.Flat A (X.X a) := by
  let M := mappingCone β
  have hex (k : ℤ) : M.ExactAt k := (mappingCone.quasiIso_iff_acyclic β).1 inferInstance k
  let eM (k : ℤ) : M.X k ≅ ModuleCat.of A (X.X (k + 1) × Y.X k) :=
    HomologicalComplex.homotopyCofiber.XIsoBiprod β k (k + 1) rfl ≪≫
      ModuleCat.biprodIsoProd (X.X (k + 1)) (Y.X k)
  have hM (k : ℤ) (hk : a ≤ k) : Module.Flat A (M.X k) := by
    have := hX (k + 1) (by lia)
    have := hY k
    exact Module.Flat.of_linearEquiv (eM k).toLinearEquiv
  have hZ : ∀ t : ℕ, ∀ k : ℤ, a ≤ k → b < k + t →
      Module.Flat A (LinearMap.ker (M.d k (k + 1)).hom) := by
    intro t
    induction t with
    | zero =>
      intro k _ hk
      have : Subsingleton (M.X k) := ModuleCat.subsingleton_of_isZero
        ((mappingCone.isZero_X_iff β k).2 ⟨X.isZero_of_isStrictlyLE b (k + 1) (by lia),
          Y.isZero_of_isStrictlyLE b k (by simpa using hk)⟩)
      infer_instance
    | succ t ih =>
      intro k hk hkt
      have := hM k hk
      exact flat_ker_d_of_flat_ker_d_succ k (hex _) (ih (k + 1) (by lia) (by lia))
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 + 1 := ⟨a - 2, by lia⟩
  have hZa := hZ (b - c).toNat (c + 1 + 1) le_rfl (by lia)
  have hzero : Subsingleton (M.X c) := ModuleCat.subsingleton_of_isZero
    ((mappingCone.isZero_X_iff β c).2 ⟨X.isZero_of_isStrictlyGE (c + 1 + 1) (c + 1) (by lia),
      Y.isZero_of_isStrictlyGE (c + 1 + 1) c (by lia)⟩)
  have hinj : Function.Injective (M.dToKer (c + 1)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨y, hy⟩ := ((M.exactAt_iff_exact c).1 (hex _) x).1 (congrArg Subtype.val hx)
    rw [← hy, Subsingleton.elim y 0, map_zero]
  have : Module.Flat A (M.X (c + 1)) := Module.Flat.of_linearEquiv
    (LinearEquiv.ofBijective _ ⟨hinj, M.surjective_dToKer (c + 1) (hex _)⟩)
  have : Module.Flat A (X.X (c + 1 + 1) × Y.X (c + 1)) :=
    Module.Flat.of_linearEquiv (eM (c + 1)).toLinearEquiv.symm
  exact Module.Flat.of_retract (LinearMap.inl A (X.X (c + 1 + 1)) (Y.X (c + 1)))
    (LinearMap.fst A _ _) (by ext; simp)

end CochainComplex

namespace Module

variable {A : Type u} [CommRing A]

/-- If `A_r ⊗[A] M` is free over `A_r` and `r ∣ s`, then `A_s ⊗[A] M` is free over `A_s`. -/
lemma free_away_tensor_of_dvd (M : Type u) [AddCommGroup M] [Module A M] {r s : A} (h : r ∣ s)
    [Module.Free (Localization.Away r) (Localization.Away r ⊗[A] M)] :
    Module.Free (Localization.Away s) (Localization.Away s ⊗[A] M) := by
  obtain ⟨t, rfl⟩ := h
  let : Algebra (Localization.Away r) (Localization.Away (r * t)) :=
    (IsLocalization.Away.awayToAwayRight (S := Localization.Away r) r t).toAlgebra
  have : IsScalarTower A (Localization.Away r) (Localization.Away (r * t)) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (IsLocalization.Away.awayToAwayRight_eq r t x).symm
  exact Module.Free.of_equiv (AlgebraTensorModule.cancelBaseChange A (Localization.Away r)
    (Localization.Away (r * t)) (Localization.Away (r * t)) M)

/-- A finitely generated projective module is locally free: for every prime `p` there is
`r ∉ p` such that `A_r ⊗[A] M` is free over `A_r`. -/
lemma exists_free_away_tensor (M : Type u) [AddCommGroup M] [Module A M] [Module.Projective A M]
    [Module.Finite A M] (p : Ideal A) [p.IsPrime] :
    ∃ r ∉ p, Module.Free (Localization.Away r) (Localization.Away r ⊗[A] M) := by
  have := Module.finitePresentation_of_projective A M
  have : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M) (Localization.AtPrime p)
  exact ⟨r, hr, Module.Free.of_equiv (LocalizedModule.equivTensorProduct (.powers r) M)⟩

end Module

namespace CochainComplex

variable {A : Type u} [CommRing A]

/-- **Localising a perfect complex to a finite free one.** Let `P` be a bounded complex of
finitely generated projective `A`-modules and `p` a prime of `A`. There is `s ∉ p` such that
every term `A_s ⊗[A] Pⁿ` is a free `A_s`-module of finite rank. -/
theorem exists_free_away_tensor_X (P : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (hP : ∀ n, Module.Projective A (P.X n) ∧ Module.Finite A (P.X n))
    (p : Ideal A) [p.IsPrime] :
    ∃ s ∉ p, ∀ n, Module.Free (Localization.Away s) (Localization.Away s ⊗[A] P.X n) ∧
      Module.Finite (Localization.Away s) (Localization.Away s ⊗[A] P.X n) := by
  classical
  have h (n : ℤ) : ∃ r ∉ p,
      Module.Free (Localization.Away r) (Localization.Away r ⊗[A] P.X n) := by
    obtain ⟨_, _⟩ := hP n
    exact Module.exists_free_away_tensor _ p
  choose r hr hfree using h
  refine ⟨∏ n ∈ Finset.Icc a b, r n, fun hmem ↦ ?_, fun n ↦ ⟨?_, ?_⟩⟩
  · obtain ⟨n, -, hn⟩ := Ideal.IsPrime.prod_mem_iff.1 hmem
    exact hr n hn
  · by_cases hn : n ∈ Finset.Icc a b
    · have := hfree n
      exact Module.free_away_tensor_of_dvd _ (Finset.dvd_prod_of_mem r hn)
    · have hz : IsZero (P.X n) := by
        rcases (show n < a ∨ b < n by simp only [Finset.mem_Icc, not_and_or, not_le] at hn; lia)
          with h | h
        · exact P.isZero_of_isStrictlyGE a n h
        · exact P.isZero_of_isStrictlyLE b n h
      have : Subsingleton (P.X n) := ModuleCat.subsingleton_of_isZero hz
      infer_instance
  · have := (hP n).2
    infer_instance

end CochainComplex

namespace DerivedCategory

section KProjective

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- **Chain-level realisation of isomorphisms out of bounded above complexes of projectives.**
Let `P` be a bounded above complex of projective objects. Every isomorphism `Q P ≅ Q K` in the
derived category is induced by a quasi-isomorphism of complexes `P ⟶ K`, as `P` is
K-projective. -/
theorem exists_quasiIso_of_isStrictlyLE_of_projective {P K : CochainComplex C ℤ} (b : ℤ)
    [P.IsStrictlyLE b] [∀ n, Projective (P.X n)] (e : Q.obj P ≅ Q.obj K) :
    ∃ φ : P ⟶ K, QuasiIso φ := by
  have := CochainComplex.isKProjective_of_projective P b
  exact exists_quasiIso_of_isKProjective e

end KProjective

variable {A : Type u} [CommRing A] [HasDerivedCategory.{u} (ModuleCat.{u} A)]

/-- **A perfect complex of flat modules in degrees `[a, b]` has a finite projective model in
degrees `[a, b]`.** Let `K` be a complex of flat `A`-modules concentrated in degrees `[a, b]`
which is perfect in `D(A)`. Then there is a quasi-isomorphism `P ⟶ K` from a complex `P` of
finitely generated projective `A`-modules, also concentrated in degrees `[a, b]`.

Represent `K` by a bounded complex `P₀` of finitely generated projective modules; the isomorphism
lifts to a quasi-isomorphism `P₀ ⟶ K`. The cycles of `P₀` in degree `b` are finitely generated
projective, as `P₀` is exact above `b`, so the truncation `P₁ = τ^{≤ b} P₀` is a complex of
finitely generated projective modules. Its truncation `P = τ^{≥ a} P₁` has
`Pᵃ = P₁ᵃ / d(P₁ᵃ⁻¹)`, which is finitely presented, and flat because `P ⟶ K` is a
quasi-isomorphism into a complex of flat modules in degrees `[a, b]` (Stacks 0658, 066N); hence
`Pᵃ` is projective. -/
theorem exists_quasiIso_projective_finite_of_isPerfect (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b] (hK : ∀ n, Module.Flat A (K.X n))
    (hKP : (Q.obj K).IsPerfect) :
    ∃ (P : CochainComplex (ModuleCat.{u} A) ℤ) (_ : P.IsStrictlyGE a) (_ : P.IsStrictlyLE b),
      (∀ n, Module.Projective A (P.X n) ∧ Module.Finite A (P.X n)) ∧
        ∃ φ : P ⟶ K, QuasiIso φ := by
  obtain ⟨P₀, a', b', _, _, hP₀, ⟨e⟩⟩ := hKP
  have : ∀ n, Projective (P₀.X n) := fun n ↦ (IsProjective.iff_projective (P₀.X n)).1 (hP₀ n).1
  obtain ⟨α, _⟩ := exists_quasiIso_of_isStrictlyLE_of_projective b' e.symm
  -- `P₀` is exact in degrees `> b`, so its truncation `P₁ = τ^{≤ b} P₀` is quasi-isomorphic
  have hex₀ (k : ℤ) (hk : b < k) : P₀.ExactAt k :=
    (exactAt_iff_of_quasiIsoAt α k).2 (K.exactAt_of_isLE b k hk)
  have : P₀.IsLE b := (P₀.isLE_iff b).2 hex₀
  let P₁ := P₀.truncLE b
  have hP₁ : ∀ n, Module.Projective A (P₁.X n) ∧ Module.Finite A (P₁.X n) :=
    CochainComplex.projective_finite_truncLE_X P₀ b hP₀
      (CochainComplex.projective_finite_ker_d_of_exactAt P₀ b' hP₀ hex₀ b le_rfl)
  let α₁ : P₁ ⟶ K := P₀.ιTruncLE b ≫ α
  -- `P₁` is exact in degrees `< a`, so its truncation `P = τ^{≥ a} P₁` is quasi-isomorphic
  have hex₁ (k : ℤ) (hk : k < a) : P₁.ExactAt k :=
    (exactAt_iff_of_quasiIsoAt α₁ k).2 (K.exactAt_of_isGE a k hk)
  have : P₁.IsGE a := (P₁.isGE_iff a).2 hex₁
  let P := P₁.truncGE a
  have : QuasiIso (CochainComplex.truncGEMap α₁ a) :=
    (CochainComplex.quasiIso_truncGEMap_iff _ _).2 fun i _ ↦ inferInstance
  let β : P ⟶ K := CochainComplex.truncGEMap α₁ a ≫ inv (K.πTruncGE a)
  have : P.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rcases lt_trichotomy i a with h | rfl | h
    · exact P.isZero_of_isStrictlyGE a i h
    · exact (IsZero.of_epi (P₁.pOpcycles i) (P₁.isZero_of_isStrictlyLE b i hi)).of_iso
        (P₁.truncGEXIsoOpcycles i)
    · exact (P₁.isZero_of_isStrictlyLE b i hi).of_iso (P₁.truncGEXIso a i h)
  have hPgt (i : ℤ) (h : a < i) :
      Module.Projective A (P.X i) ∧ Module.Finite A (P.X i) := by
    obtain ⟨_, _⟩ := hP₁ i
    let e := (P₁.truncGEXIso a i h).toLinearEquiv
    exact ⟨Module.Projective.of_equiv e.symm, Module.Finite.equiv e.symm⟩
  have hPa : Module.Projective A (P.X a) ∧ Module.Finite A (P.X a) := by
    have : Module.Flat A (P.X a) := CochainComplex.flat_X_of_quasiIso β a b
      (fun k hk ↦ have := (hPgt k hk).1; inferInstance) hK
    have : Module.FinitePresentation A (P₁.opcycles a) :=
      CochainComplex.finitePresentation_opcycles P₁ (fun k ↦ by
        obtain ⟨_, _⟩ := hP₁ k
        exact Module.finitePresentation_of_projective _ _) a
    have : Module.FinitePresentation A (P.X a) :=
      Module.FinitePresentation.of_equiv (P₁.truncGEXIsoOpcycles a).toLinearEquiv.symm
    exact ⟨Module.Flat.projective_of_finitePresentation, inferInstance⟩
  refine ⟨P, inferInstance, inferInstance, fun i ↦ ?_, β, inferInstance⟩
  rcases lt_trichotomy i a with h | rfl | h
  · have : Subsingleton (P.X i) :=
      ModuleCat.subsingleton_of_isZero (P.isZero_of_isStrictlyGE a i h)
    exact ⟨inferInstance, inferInstance⟩
  · exact hPa
  · exact hPgt i h

/-- **Finite free local models of perfect complexes of flat modules.** Let `K` be a complex of flat
`A`-modules concentrated in degrees `[a, b]` which is perfect in `D(A)`, and `p` a prime of `A`.
Then there are `s ∉ p` and a complex `P` of free `A_s`-modules of finite rank, concentrated in
degrees `[a, b]`, with a quasi-isomorphism `P ⟶ A_s ⊗[A] K`.

This is the chain-level input for the perfectness of higher direct images, towards blueprint
`lemma-coherent-base-change-invertible-sheaves` (a) (Mumford's complex). -/
theorem exists_quasiIso_free_away_of_isPerfect (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b] (hK : ∀ n, Module.Flat A (K.X n))
    (hKP : (Q.obj K).IsPerfect) (p : Ideal A) [p.IsPrime] :
    ∃ s ∉ p, ∃ (P : CochainComplex (ModuleCat.{u} (Localization.Away s)) ℤ)
      (_ : P.IsStrictlyGE a) (_ : P.IsStrictlyLE b),
      (∀ n, Module.Free (Localization.Away s) (P.X n) ∧
        Module.Finite (Localization.Away s) (P.X n)) ∧
      ∃ φ : P ⟶ ((ModuleCat.baseChange A (Localization.Away s)).mapHomologicalComplex _).obj K,
        QuasiIso φ := by
  obtain ⟨P, _, _, hP, φ, _⟩ := exists_quasiIso_projective_finite_of_isPerfect K a b hK hKP
  obtain ⟨s, hs, hfree⟩ := CochainComplex.exists_free_away_tensor_X P a b hP p
  let F := (ModuleCat.baseChange A (Localization.Away s)).mapHomologicalComplex
    (ComplexShape.up ℤ)
  have hPflat (i : ℤ) : Module.Flat A (P.X i) := by
    have := (hP i).1
    infer_instance
  -- the mapping cone of `φ` vanishes in high degrees
  have hcone (k : ℤ) (hk : b + 1 ≤ k) :
      Module.Flat A (LinearMap.ker ((CochainComplex.mappingCone φ).d k (k + 1)).hom) := by
    have hz : IsZero ((CochainComplex.mappingCone φ).X k) :=
      (CochainComplex.mappingCone.isZero_X_iff φ k).2
        ⟨P.isZero_of_isStrictlyLE b (k + 1) (by lia), K.isZero_of_isStrictlyLE b k (by lia)⟩
    have : Subsingleton ((CochainComplex.mappingCone φ).X k) :=
      ModuleCat.subsingleton_of_isZero hz
    infer_instance
  have : CochainComplex.IsStrictlyGE (F.obj P) a :=
    (CochainComplex.isStrictlyGE_iff _ a).2 fun i hi ↦
      (ModuleCat.baseChange A _).map_isZero (P.isZero_of_isStrictlyGE a i hi)
  have : CochainComplex.IsStrictlyLE (F.obj P) b :=
    (CochainComplex.isStrictlyLE_iff _ b).2 fun i hi ↦
      (ModuleCat.baseChange A _).map_isZero (P.isZero_of_isStrictlyLE b i hi)
  exact ⟨s, hs, F.obj P, inferInstance, inferInstance, hfree, F.map φ,
    CochainComplex.quasiIso_map_baseChange _ φ hPflat hK hcone⟩

/-- **Finite free local models over a Noetherian ring.** Let `A` be Noetherian and `K` a complex
of flat `A`-modules concentrated in degrees `[a, b]` with finitely generated cohomology. Then for
every prime `p` of `A` there are `s ∉ p` and a complex `P` of free `A_s`-modules of finite rank,
concentrated in degrees `[a, b]`, with a quasi-isomorphism `P ⟶ A_s ⊗[A] K`. -/
theorem exists_quasiIso_free_away_of_finite_homology [IsNoetherianRing A]
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    (hK : ∀ n, Module.Flat A (K.X n)) (hfin : ∀ i, Module.Finite A (K.homology i))
    (p : Ideal A) [p.IsPrime] :
    ∃ s ∉ p, ∃ (P : CochainComplex (ModuleCat.{u} (Localization.Away s)) ℤ)
      (_ : P.IsStrictlyGE a) (_ : P.IsStrictlyLE b),
      (∀ n, Module.Free (Localization.Away s) (P.X n) ∧
        Module.Finite (Localization.Away s) (P.X n)) ∧
      ∃ φ : P ⟶ ((ModuleCat.baseChange A (Localization.Away s)).mapHomologicalComplex _).obj K,
        QuasiIso φ :=
  exists_quasiIso_free_away_of_isPerfect K a b hK
    (isPerfect_of_flat_of_finite_homology K a b hK (Iso.refl _) fun i ↦
      have : Module.Finite A
          ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.up ℤ) i).obj K) := hfin i
      Module.Finite.equiv ((homologyFunctorFactors _ i).app K).toLinearEquiv.symm) p

end DerivedCategory
