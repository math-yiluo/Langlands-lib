/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
public import WeilConjectures.AlgebraicGeometry.Cohomology.Serre
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray

/-!
# Coherent cohomology of projective schemes over a noetherian ring

Let `A` be a noetherian ring. The cohomology of a coherent sheaf on a closed subscheme `X` of
`ℙⁿ_A` consists of finite `A`-modules, and Serre's vanishing theorem holds: the higher
cohomology of `ℱ ⊗ 𝒪_X(m)` vanishes for `m ≫ 0`.

The cohomology `ℱ.H q` of a sheaf on a scheme `X` over `Spec A` is an `A`-module through the
structure morphism; this is `AlgebraicGeometry.Scheme.Modules.moduleHOfSpec`.

Both statements are proved first on `ℙⁿ_A` by descending induction on the degree, for all
coherent modules at once: a coherent module `ℱ` is a quotient of a finite sum `ℰ` of twists
`𝒪(-mⱼ)` with coherent kernel `𝒦` (`AlgebraicGeometry.ProjectiveSpace.exists_epi_sigma_twist`),
and the long exact sequence `H^q(ℰ) ⟶ H^q(ℱ) ⟶ H^{q+1}(𝒦)` reduces the claims to the
cohomology of the twisting sheaves `𝒪(m)`, computed over `A` by the monomial Čech complex. A
closed subscheme reduces to `ℙⁿ_A` by pushing forward along the closed immersion, which is
affine.

## Main statements

- `AlgebraicGeometry.ProjectiveSpace.subsingleton_H_twist_of_pos_of_lt` and
  `AlgebraicGeometry.ProjectiveSpace.subsingleton_H_zero_twist_of_neg`: vanishing of
  `H^q(ℙⁿ_A, 𝒪(m))` for `0 < q < n`, and of `H^0(ℙⁿ_A, 𝒪(m))` for `m < 0`, over any ring `A`.
- `AlgebraicGeometry.ProjectiveSpace.finite_H`: the cohomology of a coherent sheaf on `ℙⁿ_A` is
  finite over `A`.
- `AlgebraicGeometry.Scheme.Modules.finite_H_of_isClosedImmersion`: the same for a closed
  subscheme of `ℙⁿ_A`.
- `AlgebraicGeometry.ProjectiveSpace.exists_subsingleton_H_tensor_twist_of_isNoetherianRing` and
  `AlgebraicGeometry.Scheme.Modules.exists_subsingleton_H_tensor_twist_of_isNoetherianRing`:
  Serre vanishing on `ℙⁿ_A` and on a closed subscheme of `ℙⁿ_A`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {X : Scheme.{u}} {A : Type u} [CommRing A]

/-- The cohomology of a sheaf of modules on a scheme `X` with a morphism `f : X ⟶ Spec A` is an
`A`-module, by restriction of scalars of the `Γ(X, ⊤)`-module structure along
`A ≅ Γ(Spec A, ⊤) ⟶ Γ(X, ⊤)`.

This is not an instance, since `f` cannot be inferred. -/
abbrev moduleHOfSpec (f : X ⟶ Spec (.of A)) (M : X.Modules) (q : ℕ) : Module A (M.H q) :=
  Module.compHom (M.H q) ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom

variable (f : X ⟶ Spec (.of A))

/-- Finiteness over `A` of `H^q` is invariant under isomorphism. -/
lemma finite_H_of_iso {M N : X.Modules} (e : M ≅ N) (q : ℕ)
    (h : letI := moduleHOfSpec f M q; Module.Finite A (M.H q)) :
    letI := moduleHOfSpec f N q; Module.Finite A (N.H q) := by
  let := moduleHOfSpec f M q
  let := moduleHOfSpec f N q
  let e' : M.H q ≃ₗ[A] N.H q :=
    { (H.mapLinearEquiv e q).toAddEquiv with
      map_smul' := fun a x ↦ (H.mapLinearEquiv e q).map_smul _ x }
  exact Module.Finite.equiv e'

/-- **Finiteness along a short exact sequence.** For `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` short exact and
`A` noetherian, if `H^q(M₂)` and `H^{q+1}(M₁)` are finite `A`-modules, then so is `H^q(M₃)`, by
exactness of `H^q(M₂) ⟶ H^q(M₃) ⟶ H^{q+1}(M₁)`. -/
lemma finite_H_of_shortExact [IsNoetherianRing A] {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (q : ℕ)
    (h₂ : letI := moduleHOfSpec f S.X₂ q; Module.Finite A (S.X₂.H q))
    (h₁ : letI := moduleHOfSpec f S.X₁ (q + 1); Module.Finite A (S.X₁.H (q + 1))) :
    letI := moduleHOfSpec f S.X₃ q; Module.Finite A (S.X₃.H q) := by
  let := moduleHOfSpec f S.X₁ (q + 1)
  let := moduleHOfSpec f S.X₂ q
  let := moduleHOfSpec f S.X₃ q
  let g : S.X₂.H q →ₗ[A] S.X₃.H q :=
    { toFun := H.map S.g q
      map_add' := map_add _
      map_smul' := fun a x ↦ H.map_smul S.g q _ x }
  let δ : S.X₃.H q →ₗ[A] S.X₁.H (q + 1) :=
    { toFun := H.δ hS q
      map_add' := map_add _
      map_smul' := fun a x ↦ H.δ_smul hS q _ x }
  have hker : LinearMap.ker δ = LinearMap.range g := by
    ext x
    exact SetLike.ext_iff.1 (H.ker_δ_eq_range_map_g hS q) x
  have : _root_.IsNoetherian A (S.X₁.H (q + 1)) := isNoetherian_of_isNoetherianRing_of_finite _ _
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker δ (IsNoetherian.noetherian _) ?_⟩
  rw [top_inf_eq, hker, LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map g

/-- **Finiteness for a finite coproduct.** If every `H^q(G i)` is a finite `A`-module, so is
`H^q(∐ G)`: the identity of the coproduct, which is a biproduct, is the sum of the projections
followed by the inclusions. -/
lemma finite_H_sigma {ι : Type u} [Finite ι] (G : ι → X.Modules) (q : ℕ)
    (h : ∀ i, letI := moduleHOfSpec f (G i) q; Module.Finite A ((G i).H q)) :
    letI := moduleHOfSpec f (∐ G) q; Module.Finite A ((∐ G).H q) := by
  -- reindex by `Fin k`, since the biproduct API is stated for index types in `Type`
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  suffices ∀ G' : Fin k → X.Modules,
      (∀ i, letI := moduleHOfSpec f (G' i) q; Module.Finite A ((G' i).H q)) →
      letI := moduleHOfSpec f (∐ G') q; Module.Finite A ((∐ G').H q) from
    finite_H_of_iso f (Sigma.reindex e.symm G) q (this (G ∘ e.symm) fun i ↦ h (e.symm i))
  intro G h
  have : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteCoproducts
  refine finite_H_of_iso f (biproduct.isoCoproduct G) q ?_
  let := moduleHOfSpec f (⨁ G) q
  let inst (i : Fin k) := moduleHOfSpec f (G i) q
  let ι' (i : Fin k) : (G i).H q →ₗ[A] (⨁ G).H q :=
    { toFun := H.map (biproduct.ι G i) q
      map_add' := map_add _
      map_smul' := fun a x ↦ H.map_smul _ q _ x }
  have htop : ⨆ i, Submodule.map (ι' i) ⊤ = ⊤ := by
    refine eq_top_iff.2 fun z _ ↦ ?_
    have h1 : H.map (∑ i, biproduct.π G i ≫ biproduct.ι G i) q z = z := by
      rw [biproduct.total]
      exact H.map_id_apply _ _ z
    rw [← h1, H.map_sum_apply]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.mem_iSup_of_mem i
      ⟨H.map (biproduct.π G i) q z, trivial, (H.map_comp_apply _ _ q z).symm⟩
  exact ⟨htop ▸ Submodule.fg_iSup _ fun i ↦ (h i).fg_top.map (ι' i)⟩

/-- **Cohomology along an affine morphism, with its module structure.** For an affine morphism
`g : X ⟶ Y` and a quasi-coherent `𝒪_X`-module `ℱ`, `H^q(X, ℱ) ≅ H^q(Y, g_* ℱ)`, the isomorphism
taking the action of `g^♯ r` to that of `r`, for every global function `r` on `Y`.

(blueprint: `lem-pc-closed-immersion-coherent-cohomology`) -/
theorem exists_H_addEquiv_pushforward_of_isAffineHom {Y : Scheme.{u}} (g : X ⟶ Y)
    [IsAffineHom g] (ℱ : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
    (q : ℕ) : ∃ e : ℱ.H q ≃+ ((pushforward g).obj ℱ).H q,
      ∀ (r : Γ(Y, ⊤)) (x : ℱ.H q), e (g.appTop r • x) = r • e x := by
  obtain ⟨e⟩ := nonempty_functorH_iso_pushforwardAb_of_isAffineHom g q
  let F : (cechAcyclicOnAffines X).FullSubcategory :=
    ⟨(SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ, cechAcyclicOnAffines_of_isQuasicoherent ℱ⟩
  refine ⟨(e.app F).addCommGroupIsoToAddEquiv, fun r x ↦ ?_⟩
  have h := NatTrans.naturality_apply e.hom (ObjectProperty.homMk
    ((SheafOfModules.toSheaf X.ringCatSheaf).map (ℱ.smulHom (g.appTop r))) : F ⟶ F) x
  change e.hom.app F (H.map (ℱ.smulHom (g.appTop r)) q x) =
    H.map (((pushforward g).obj ℱ).smulHom r) q (e.hom.app F x)
  rw [← pushforward_map_smulHom]
  exact h

end Scheme.Modules

open Scheme.Modules

namespace ProjectiveSpace

variable {n : Type u}

/-- **The cohomology of `𝒪(m)` on `ℙ(n; Spec A)` is that of the monomial Čech complex**, as
`A`-modules, for any commutative ring `A`: Leray's theorem for the standard affine covering of
the separated scheme `ℙ(n; Spec A)`, combined with the identification of the Čech complex of
`𝒪(m)` with the monomial Čech complex.

(blueprint: `lem-pc-projective-space-twist-cohomology`) -/
theorem nonempty_H_twist_linearEquiv_monomialCechComplex_homology (A : Type u) [CommRing A]
    [Fintype n] (m : ℤ) (q : ℕ) :
    letI := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) (twist n (Spec (.of A)) m) q
    Nonempty ((twist n (Spec (.of A)) m).H q ≃ₗ[A] (monomialCechComplex n A m).homology q) := by
  let := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) (twist n (Spec (.of A)) m) q
  let φ := ((Scheme.ΓSpecIso (.of A)).inv ≫ (ℙ(n; Spec (.of A)) ↘ Spec (.of A)).appTop).hom
  let K := (cechComplexFunctor (standardOpen n (Spec (.of A)))).obj
    (twist n (Spec (.of A)) m).presheafModuleCat
  obtain ⟨e₁⟩ := Scheme.Modules.nonempty_cechComplex_linearEquiv_H_of_isSeparated
    (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) (standardOpen n (Spec (.of A)))
    (fun i ↦ isAffineOpen_standardOpen n _ i) (iSup_standardOpen n _)
    (twist n (Spec (.of A)) m) q
  let e₃ : (twist n (Spec (.of A)) m).H q ≃ₗ[A] (ModuleCat.restrictScalars φ).obj (K.homology q) :=
    { e₁.symm.toAddEquiv with map_smul' := fun c x ↦ e₁.symm.map_smul (φ c) x }
  exact ⟨e₃ ≪≫ₗ ((ModuleCat.restrictScalarsHomologyIso φ K q).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ q).mapIso
      (cechComplexTwistIso n A m)).toLinearEquiv⟩

/-- There are finitely many strictly negative exponent vectors of a given sum. -/
lemma finite_negativeExponents [Fintype n] (m : ℤ) : Finite (negativeExponents n m) := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, Fintype.card n = d + 1 ∨ IsEmpty n := by
    rcases isEmpty_or_nonempty n with h | h
    · exact ⟨0, .inr h⟩
    · exact ⟨Fintype.card n - 1, .inl (by have := Fintype.card_pos (α := n); omega)⟩
  rcases hd with hd | hd
  · by_cases hm : m ≤ -(d : ℤ) - 1
    · have : Finite {s : n →₀ ℕ | s.degree = (-m - d - 1).toNat} :=
        (Finsupp.finite_of_degree_eq _).to_subtype
      exact Finite.of_equiv _ (negativeExponentsEquiv n m hd hm).symm
    · have := isEmpty_negativeExponents (n := n) hd (m := m) (by omega)
      infer_instance
  · exact Finite.of_injective (fun e : negativeExponents n m ↦ (e : n → ℤ))
      Subtype.val_injective

/-- **The homology of the monomial Čech complex is finite**, in the degrees `q ≤ d` where it can
compute cohomology: `H⁰` is a module of homogeneous polynomials (or zero), the middle degrees
vanish and the top degree is free on the finitely many strictly negative exponent vectors. -/
lemma finite_monomialCechComplex_homology (A : Type u) [CommRing A] [Fintype n] {d : ℕ}
    (hn : Fintype.card n = d + 1) (m : ℤ) {q : ℕ} (hq : q ≤ d) :
    Module.Finite A ((monomialCechComplex n A m).homology q) := by
  have := finite_negativeExponents (n := n) m
  have hnonempty : Nonempty n := Fintype.card_pos_iff.1 (by omega)
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · rcases le_or_gt 0 m with hm | hm
    · obtain ⟨D, rfl⟩ := Int.eq_ofNat_of_zero_le hm
      have : Finite {s : n →₀ ℕ | s.degree = D} := (Finsupp.finite_of_degree_eq _).to_subtype
      have := Module.Finite.of_basis (homogeneousSubmoduleBasis n A D)
      exact Module.Finite.equiv (monomialCechComplexHomologyZeroLinearEquiv n A D).symm
    · rcases Nat.eq_zero_or_pos d with rfl | hd
      · exact Module.Finite.equiv (monomialCechComplexHomologyTopLinearEquiv n A m hn
          (Fintype.equivFinOfCardEq hn).symm (.inr hm)).symm
      · have : Nontrivial n := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
        have := subsingleton_monomialCechComplex_homology_zero n A hm
        infer_instance
  · rcases hq.lt_or_eq with hlt | rfl
    · obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0.ne'
      have := ModuleCat.isZero_iff_subsingleton.1
        (exactAt_monomialCechComplex n A m hn q hlt).isZero_homology
      infer_instance
    · exact Module.Finite.equiv (monomialCechComplexHomologyTopLinearEquiv n A m hn
        (Fintype.equivFinOfCardEq hn).symm (.inl hq0.ne')).symm

/-- **The cohomology of the twisting sheaves over a ring is finite**: each `H^q(ℙⁿ_A, 𝒪(m))` is
a finite `A`-module, for any commutative ring `A`.

(blueprint: `lem-pc-projective-space-twist-cohomology`) -/
theorem finite_H_twist (A : Type u) [CommRing A] [Finite n] (m : ℤ) (q : ℕ) :
    letI := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) (twist n (Spec (.of A)) m) q
    Module.Finite A ((twist n (Spec (.of A)) m).H q) := by
  let := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) (twist n (Spec (.of A)) m) q
  have := Fintype.ofFinite n
  rcases isEmpty_or_nonempty n with hn | hn
  · have := subsingleton_H_of_isEmpty (Spec (.of A)) (twist n (Spec (.of A)) m) q
    infer_instance
  obtain ⟨d, hd⟩ : ∃ d : ℕ, Fintype.card n = d + 1 :=
    ⟨Fintype.card n - 1, by have := Fintype.card_pos (α := n); omega⟩
  rcases le_or_gt q d with hq | hq
  · obtain ⟨e⟩ := nonempty_H_twist_linearEquiv_monomialCechComplex_homology (n := n) A m q
    have := finite_monomialCechComplex_homology A hd m hq
    exact Module.Finite.equiv e.symm
  · have := subsingleton_H_of_lt n A (by rwa [Nat.card_eq_fintype_card])
      (twist n (Spec (.of A)) m) hq
    infer_instance

/-- `H^q(ℙⁿ_A, 𝒪(e)) = 0` for `q > 0` and `e ≥ 0`, over any commutative ring `A`.

(blueprint: `lem-pc-projective-space-twist-cohomology`) -/
lemma subsingleton_H_twist_of_pos_of_commRing (A : Type u) [CommRing A] [Finite n] {q : ℕ}
    (hq : 0 < q) {e : ℤ} (he : 0 ≤ e) : Subsingleton ((twist n (Spec (.of A)) e).H q) := by
  have := Fintype.ofFinite n
  rcases isEmpty_or_nonempty n with hn | hn
  · exact subsingleton_H_of_isEmpty _ _ q
  obtain ⟨d, hd⟩ : ∃ d : ℕ, Fintype.card n = d + 1 :=
    ⟨Fintype.card n - 1, by have := Fintype.card_pos (α := n); omega⟩
  rcases lt_trichotomy q d with hlt | rfl | hgt
  · obtain ⟨e'⟩ := nonempty_H_twist_linearEquiv_monomialCechComplex_homology (n := n) A e q
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
    have := ModuleCat.isZero_iff_subsingleton.1
      (exactAt_monomialCechComplex n A e hd q hlt).isZero_homology
    exact e'.toEquiv.subsingleton
  · obtain ⟨e'⟩ := nonempty_H_twist_linearEquiv_monomialCechComplex_homology (n := n) A e q
    have := subsingleton_monomialCechComplex_homology_top (A := A) hd hq.ne' (m := e) (by omega)
    exact e'.toEquiv.subsingleton
  · exact subsingleton_H_of_lt n A (by rwa [Nat.card_eq_fintype_card]) _ hgt

/-- `H^q(ℙᵈ_A, 𝒪(m)) = 0` for `0 < q < d` and every `m`, over any commutative ring `A`, where
`ℙᵈ_A = ℙ(n; Spec A)` with `n` of cardinality `d + 1`: the middle homology of the monomial Čech
complex vanishes.

(blueprint: `lem-pc-projective-space-twist-cohomology`) -/
lemma subsingleton_H_twist_of_pos_of_lt (A : Type u) [CommRing A] [Fintype n] {d : ℕ}
    (hn : Fintype.card n = d + 1) (m : ℤ) {q : ℕ} (hq : 0 < q) (hqd : q < d) :
    Subsingleton ((twist n (Spec (.of A)) m).H q) := by
  obtain ⟨e⟩ := nonempty_H_twist_linearEquiv_monomialCechComplex_homology (n := n) A m q
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  have := ModuleCat.isZero_iff_subsingleton.1
    (exactAt_monomialCechComplex n A m hn q hqd).isZero_homology
  exact e.toEquiv.subsingleton

/-- `H^0(ℙⁿ_A, 𝒪(m)) = 0` for `m < 0` and `n ≥ 1`, over any commutative ring `A`: a global
section of `𝒪(m)` is a combination of monomials of degree `m` with nonnegative exponents.

(blueprint: `lem-pc-projective-space-twist-cohomology`) -/
lemma subsingleton_H_zero_twist_of_neg (A : Type u) [CommRing A] [Finite n] [Nontrivial n]
    {m : ℤ} (hm : m < 0) : Subsingleton ((twist n (Spec (.of A)) m).H 0) := by
  have := Fintype.ofFinite n
  obtain ⟨e⟩ := nonempty_H_twist_linearEquiv_monomialCechComplex_homology (n := n) A m 0
  have := subsingleton_monomialCechComplex_homology_zero n A hm
  exact e.toEquiv.subsingleton

end ProjectiveSpace

variable {n : Type u} [Finite n]

/-- **Coherent cohomology of projective space over a noetherian ring.** Let `A` be noetherian
and `ℱ` a coherent module on `ℙⁿ_A`. Then each `H^q(ℙⁿ_A, ℱ)` is a finite `A`-module.

By descending induction on `q`, for all coherent modules at once: for `q > n` the cohomology
vanishes; in general, a surjection `ℰ ⟶ ℱ` from a finite sum `ℰ` of twists `𝒪(m)` with coherent
kernel `𝒦` gives an exact sequence `H^q(ℰ) ⟶ H^q(ℱ) ⟶ H^{q+1}(𝒦)` whose outer terms are finite.

(blueprint: `lem-pc-projective-space-coherent-finiteness`) -/
theorem ProjectiveSpace.finite_H (A : Type u) [CommRing A] [IsNoetherianRing A]
    (ℱ : (ℙ(n; Spec (.of A))).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ℙ(n; Spec (.of A))).ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := (ℙ(n; Spec (.of A))).ringCatSheaf) ℱ] (q : ℕ) :
    letI := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) ℱ q
    Module.Finite A (ℱ.H q) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · let := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) ℱ q
    have := ProjectiveSpace.subsingleton_H_of_isEmpty (Spec (.of A)) ℱ q
    infer_instance
  obtain ⟨D, hD⟩ : ∃ D : ℕ, Nat.card n = D + 1 :=
    ⟨Nat.card n - 1, by have := Nat.card_pos (α := n); omega⟩
  suffices key : ∀ j : ℕ, ∀ (𝒢 : (ℙ(n; Spec (.of A))).Modules)
      [SheafOfModules.IsQuasicoherent (R := (ℙ(n; Spec (.of A))).ringCatSheaf) 𝒢]
      [SheafOfModules.IsFinitePresentation (R := (ℙ(n; Spec (.of A))).ringCatSheaf) 𝒢],
      ∀ q : ℕ, D < q + j →
        letI := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) 𝒢 q
        Module.Finite A (𝒢.H q) from key (q + D + 1) ℱ q (by omega)
  intro j
  induction j with
  | zero =>
    intro 𝒢 _ _ q hq
    let := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) 𝒢 q
    have := ProjectiveSpace.subsingleton_H_of_lt n A hD 𝒢 (q := q) (by omega)
    infer_instance
  | succ j ih =>
    intro 𝒢 _ _ q hq
    by_cases hqj : D < q + j
    · exact ih 𝒢 q hqj
    obtain ⟨ι, _, m, p, hp, hK₁, hK₂⟩ := ProjectiveSpace.exists_epi_sigma_twist A 𝒢
    have hS : (ShortComplex.kernelSequence p).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact p) inferInstance hp
    exact finite_H_of_shortExact _ hS q
      (finite_H_sigma _ _ q fun i ↦ ProjectiveSpace.finite_H_twist A _ q)
      (ih (kernel p) (q + 1) (by omega))

variable {X : Scheme.{u}}

/-- **Coherent cohomology of a projective scheme over a noetherian ring.** Let `A` be
noetherian, `i : X ⟶ ℙⁿ_A` a closed immersion and `ℱ` a coherent `𝒪_X`-module. Then each
`H^q(X, ℱ)` is a finite `A`-module: `i_* ℱ` is coherent with the same cohomology as `ℱ`, and
`AlgebraicGeometry.ProjectiveSpace.finite_H` applies to it.

(blueprint: `lem-pc-projective-coherent-finiteness`) -/
theorem Scheme.Modules.finite_H_of_isClosedImmersion (A : Type u) [CommRing A]
    [IsNoetherianRing A] (i : X ⟶ ℙ(n; Spec (.of A))) [IsClosedImmersion i] (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    letI := moduleHOfSpec (i ≫ ℙ(n; Spec (.of A)) ↘ Spec (.of A)) ℱ q
    Module.Finite A (ℱ.H q) := by
  have := LocallyOfFiniteType.isLocallyNoetherian (ℙ(n; Spec (.of A)) ↘ Spec (.of A))
  have := isQuasicoherent_pushforward_of_isClosedImmersion i ℱ
  have := isFinitePresentation_pushforward_of_isClosedImmersion i ℱ
  have h := ProjectiveSpace.finite_H A ((pushforward i).obj ℱ) q
  obtain ⟨e, he⟩ := exists_H_addEquiv_pushforward_of_isAffineHom i ℱ q
  let := moduleHOfSpec (i ≫ ℙ(n; Spec (.of A)) ↘ Spec (.of A)) ℱ q
  let := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) ((pushforward i).obj ℱ) q
  let e' : ℱ.H q ≃ₗ[A] ((pushforward i).obj ℱ).H q :=
    { e with
      map_smul' := fun a x ↦ by
        change e ((((Scheme.ΓSpecIso (.of A)).inv ≫
          (i ≫ ℙ(n; Spec (.of A)) ↘ Spec (.of A)).appTop).hom a) • x) = _
        rw [Scheme.Hom.comp_appTop, ← Category.assoc, CommRingCat.hom_comp,
          RingHom.comp_apply]
        exact he _ x }
  exact Module.Finite.equiv e'.symm

/-- **Serre vanishing on projective space over a noetherian ring.** Let `A` be noetherian and
`ℱ` a coherent module on `ℙⁿ_A`. There is `d₀` such that `H^q(ℙⁿ_A, ℱ(d)) = 0` for all
`d ≥ d₀` and all `q > 0`.

The proof is that of the field case
`AlgebraicGeometry.ProjectiveSpace.exists_subsingleton_H_tensor_twist`, with the vanishing of
`H^q(ℙⁿ_A, 𝒪(e))` for `q > 0`, `e ≥ 0` computed over `A` by the monomial Čech complex.

(blueprint: `lemma-coherent-base-change-invertible-sheaves--1`) -/
theorem ProjectiveSpace.exists_subsingleton_H_tensor_twist_of_isNoetherianRing (A : Type u)
    [CommRing A] [IsNoetherianRing A] (ℱ : (ℙ(n; Spec (.of A))).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ℙ(n; Spec (.of A))).ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := (ℙ(n; Spec (.of A))).ringCatSheaf) ℱ] :
    ∃ d₀ : ℤ, ∀ d ≥ d₀, ∀ q : ℕ, 0 < q →
      Subsingleton ((ℱ ⊗ ProjectiveSpace.twist n (Spec (.of A)) d).H q) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨0, fun d _ q _ ↦ ProjectiveSpace.subsingleton_H_of_isEmpty _ _ q⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ, Nat.card n = D + 1 :=
    ⟨Nat.card n - 1, by have := Nat.card_pos (α := n); omega⟩
  suffices key : ∀ j : ℕ, ∀ (𝒢 : (ℙ(n; Spec (.of A))).Modules)
      [SheafOfModules.IsQuasicoherent (R := (ℙ(n; Spec (.of A))).ringCatSheaf) 𝒢]
      [SheafOfModules.IsFinitePresentation (R := (ℙ(n; Spec (.of A))).ringCatSheaf) 𝒢],
      ∃ d₀ : ℤ, ∀ d ≥ d₀, ∀ q : ℕ, D < q + j → 0 < q →
        Subsingleton ((𝒢 ⊗ ProjectiveSpace.twist n (Spec (.of A)) d).H q) by
    obtain ⟨d₀, h⟩ := key (D + 1) ℱ
    exact ⟨d₀, fun d hd q hq ↦ h d hd q (by omega) hq⟩
  intro j
  induction j with
  | zero =>
    intro 𝒢 _ _
    refine ⟨0, fun d _ q hq _ ↦ ?_⟩
    have := isQuasicoherent_tensorObj 𝒢 (ProjectiveSpace.twist n (Spec (.of A)) d)
    exact ProjectiveSpace.subsingleton_H_of_lt n A hD _ (by omega)
  | succ j ih =>
    intro 𝒢 _ _
    obtain ⟨ι, _, m, p, hp, hK₁, hK₂⟩ := ProjectiveSpace.exists_epi_sigma_twist A 𝒢
    obtain ⟨M, hM⟩ := (Set.finite_range m).bddAbove
    obtain ⟨d₁, h₁⟩ := ih 𝒢
    obtain ⟨d₂, h₂⟩ := ih (kernel p)
    refine ⟨max (max d₁ d₂) (M : ℤ), fun d hd q hq hq0 ↦ ?_⟩
    have hd₁ : d₁ ≤ d := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hd
    have hd₂ : d₂ ≤ d := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hd
    have hdm : ∀ i, (m i : ℤ) ≤ d := fun i ↦
      le_trans (Nat.cast_le.2 (hM ⟨i, rfl⟩)) (le_trans (le_max_right _ _) hd)
    by_cases hqj : D < q + j
    · exact h₁ d hd₁ q hqj hq0
    -- twisting by `𝒪(d)` is an equivalence, with inverse twisting by `𝒪(-d)`
    let T := ProjectiveSpace.twist n (Spec (.of A)) d
    obtain ⟨e₁⟩ := ProjectiveSpace.nonempty_tensorObj_twist_iso n (Spec (.of A)) d (-d)
    let E := BraidedCategory.tensorRightEquivalence T (ProjectiveSpace.twist n (Spec (.of A)) (-d))
      (e₁ ≪≫ eqToIso (congrArg _ (add_neg_cancel d)) ≪≫
        (ProjectiveSpace.unitIsoTwistZero n (Spec (.of A))).symm)
    have : (tensorRight T).IsEquivalence := E.isEquivalence_functor
    have hS : (ShortComplex.kernelSequence p).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact p) inferInstance hp
    have hS' := hS.map_of_exact (tensorRight T)
    let G := fun i ↦ ProjectiveSpace.twist n (Spec (.of A)) (-(m i : ℤ))
    have : ∀ i, Subsingleton ((G i ⊗ T).H q) := fun i ↦ by
      obtain ⟨e⟩ := ProjectiveSpace.nonempty_tensorObj_twist_iso n (Spec (.of A)) (-(m i : ℤ)) d
      have := ProjectiveSpace.subsingleton_H_twist_of_pos_of_commRing (n := n) A hq0
        (e := -(m i : ℤ) + d) (by have := hdm i; omega)
      exact subsingleton_H_of_iso e.symm q
    have hsum : Subsingleton ((∐ fun i ↦ G i ⊗ T).H q) := subsingleton_H_sigma (fun i ↦ G i ⊗ T) q
    have h₂' : Subsingleton (((tensorRight T).obj (kernel p)).H (q + 1)) :=
      h₂ d hd₂ (q + 1) (by omega) (by omega)
    have h₃ : Subsingleton (((tensorRight T).obj (∐ G)).H q) :=
      @subsingleton_H_of_iso _ _ _ (PreservesCoproduct.iso (tensorRight T) G).symm q hsum
    exact @subsingleton_H_of_shortExact _ _ hS' q h₃ h₂'

open scoped AlgebraicGeometry.Scheme.Modules in
/-- **Serre's theorem B over a noetherian ring.** Let `A` be noetherian, `X ⊆ ℙⁿ_A` a closed
subscheme, i.e. a closed immersion `i : X ⟶ ℙ(n; Spec A)`, and `ℱ` a coherent sheaf on `X`.
Then `H^q(X, ℱ ⊗ 𝒪_X(m)) = 0` for all `q > 0` and all `m ≫ 0`, where `𝒪_X(m)` is the pullback
along `i` of the twisting sheaf `𝒪(m)`. This extends
`AlgebraicGeometry.Scheme.Modules.exists_subsingleton_H_tensor_twist`
(`lemma-coherent-base-change-invertible-sheaves--1`) from a field to a noetherian ring.

As in the field case, `H^q(X, ℱ ⊗ 𝒪_X(m)) ≅ H^q(ℙⁿ_A, (i_* ℱ)(m))` by the projection formula
and the affineness of `i`, and Serre vanishing on `ℙⁿ_A`
(`AlgebraicGeometry.ProjectiveSpace.exists_subsingleton_H_tensor_twist_of_isNoetherianRing`)
applies to the coherent module `i_* ℱ`.

(blueprint: `lem-pc-serre-vanishing`, `lemma-coherent-base-change-invertible-sheaves--1`) -/
theorem Scheme.Modules.exists_subsingleton_H_tensor_twist_of_isNoetherianRing (A : Type u)
    [CommRing A] [IsNoetherianRing A] (i : X ⟶ ℙ(n; Spec (.of A))) [IsClosedImmersion i]
    (F : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) F] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q : ℕ, 0 < q →
      Subsingleton ((F ⊗ₘ ProjectiveSpace.twistRestrict i m).H q) := by
  have := LocallyOfFiniteType.isLocallyNoetherian (ℙ(n; Spec (.of A)) ↘ Spec (.of A))
  have := isQuasicoherent_pushforward_of_isClosedImmersion i F
  have := isFinitePresentation_pushforward_of_isClosedImmersion i F
  obtain ⟨m₀, h⟩ :=
    ProjectiveSpace.exists_subsingleton_H_tensor_twist_of_isNoetherianRing A ((pushforward i).obj F)
  refine ⟨m₀, fun m hm q hq ↦ ?_⟩
  have := h m hm q hq
  obtain ⟨e⟩ := nonempty_pushforward_tensorObj_pullback_iso i F
    (ProjectiveSpace.twist n (Spec (.of A)) m)
  have := isQuasicoherent_tensorObj F (ProjectiveSpace.twistRestrict i m)
  obtain ⟨e', -⟩ := exists_H_addEquiv_pushforward_of_isAffineHom i
    (F ⊗ₘ ProjectiveSpace.twistRestrict i m) q
  have := subsingleton_H_of_iso e.symm q
  exact e'.toEquiv.subsingleton

end AlgebraicGeometry
