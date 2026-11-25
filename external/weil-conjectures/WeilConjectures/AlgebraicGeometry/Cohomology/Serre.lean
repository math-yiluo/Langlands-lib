/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Vanishing
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSection
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.MonomialCech
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistSections
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray
import Mathlib.Order.Int.ConditionallyCompleteOrder

/-!
# Serre's theorems on the cohomology of projective schemes

This file states, for the Picard-framework block of the blueprint, the three results of
Serre's *Faisceaux algébriques cohérents* that the rest of the block uses: the computation of
the cohomology of the twisting sheaves on projective space, and Serre's theorems A and B for a
coherent sheaf on a closed subscheme of projective space.

Theorem B is proved from the cohomology of the twisting sheaves: a coherent module on `ℙᵈ_k`
is a quotient of a finite sum of twists `𝒪(-m)` with coherent kernel, and descending induction
on the degree in the long exact cohomology sequence gives Serre vanishing on `ℙᵈ_k`; a closed
subscheme reduces to `ℙᵈ_k` by pushing forward. Serre vanishing for an ample invertible module
follows.

Projective space is the project's relative projective space `ℙ(n; S)`, whose index type `n` is
the index type of the *homogeneous* coordinates, so that `ℙᵈ_k` is `ℙ(n; Spec k)` for a type
`n` with `Nat.card n = d + 1`.

The twisting sheaf `AlgebraicGeometry.ProjectiveSpace.twist` is the pullback along
`AlgebraicGeometry.ProjectiveSpace.toProjInt` of `AlgebraicGeometry.Proj.twist` of the integral
model `Proj ℤ[Tᵢ]`, and `AlgebraicGeometry.ProjectiveSpace.twistRestrict` is its pullback to a
closed subscheme.

## Implementation notes

The symmetric power `Sᵐ(V)` of `V = k^{d+1}` is realised as the degree-`m` homogeneous part
`MvPolynomial.homogeneousSubmodule n k m` of the polynomial ring in the homogeneous
coordinates. Mathlib's `SymmetricPower R ι M` forces the index type `ι` to lie in the same
universe as the ring `R`, which does not fit `Sym^m` for a field in an arbitrary universe, and
the homogeneous part is anyway the object Serre's theorem produces.

Mathlib has no `IsCoherent` predicate for sheaves of modules; "coherent" is spelled here as
`SheafOfModules.IsFinitePresentation` together with `SheafOfModules.IsQuasicoherent`, which
agrees with coherence on a noetherian scheme such as a closed subscheme of `ℙᵈ_k`.

## Main statements

- `AlgebraicGeometry.ProjectiveSpace.subsingleton_H_twist_of_ne` and `subsingleton_H_twist_top`
  — the vanishing of the cohomology of `𝒪(m)` on `ℙᵈ_k`. The canonical isomorphisms
  `H⁰(ℙᵈ_k, 𝒪(m)) ≅ Sᵐ(V)` and `Hᵈ(ℙᵈ_k, 𝒪(m)) ≅ S^{-m-d-1}(V)^∨` are in
  `WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveSpaceOverField`.
- `AlgebraicGeometry.ProjectiveSpace.exists_epi_sigma_twist` — a coherent module on `ℙⁿ_A` is a
  quotient of a finite sum of twists `𝒪(-mⱼ)`.
- `AlgebraicGeometry.ProjectiveSpace.exists_subsingleton_H_tensor_twist` — Serre vanishing on
  `ℙᵈ_k`: `H^q(ℙᵈ_k, ℱ(d)) = 0` for `q > 0` and `d ≫ 0`.
- `AlgebraicGeometry.Scheme.Modules.exists_subsingleton_H_tensor_twist` — Serre's theorem B.
- `AlgebraicGeometry.Scheme.Modules.exists_subsingleton_H_tensorObj_tensorPow` — Serre vanishing
  for an ample invertible module.
- `AlgebraicGeometry.Scheme.Modules.exists_generatingSections_tensor_twist` — Serre's
  theorem A.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry.Scheme.Modules

noncomputable section

namespace AlgebraicGeometry

variable (n : Type u)

section Pn

/-- **The Čech complex of `𝒪(m)` on the standard covering is the monomial Čech complex.** Let
`k` be a field and `Uᵢ = D₊(xᵢ)` the standard opens of `ℙ(n; Spec k)`. The sections of `𝒪(m)`
over `U_J = ⋂_{j ∈ J} U_j` are the degree-`m` part of `k[xᵢ, x_j⁻¹ : j ∈ J]`, the restriction
maps being the inclusions; so the Čech complex of `𝒪(m)` on the covering `(Uᵢ)ᵢ`, as a complex
of `k`-vector spaces, is `ProjectiveSpace.monomialCechComplex n k m`.

This is the first step of the proof of `lem-pc-projective-space-twist-cohomology`: the
transition rule `e_i^{(m)} = (x_i/x_j)^m e_j^{(m)}` of `def-pc-projective-space-twist`, a
well-defined gluing by `lem-pc-twist-cocycle`, identifies the section `(x^e / x_i^m) e_i^{(m)}`
on `U_J ⊆ U_i` with the Laurent monomial `xᵉ`.

(blueprint: `lem-pc-projective-space-twist-cohomology`, `def-pc-projective-space-twist`) -/
theorem ProjectiveSpace.nonempty_cechComplex_twist_iso_monomialCechComplex (k : Type u)
    [Field k] [Fintype n] (m : ℤ) :
    Nonempty (((ModuleCat.restrictScalars
        (Scheme.globalSectionsRingHom k (X := ℙ(n; Spec (.of k))))).mapHomologicalComplex _).obj
      ((cechComplexFunctor (ProjectiveSpace.standardOpen n (Spec (.of k)))).obj
        (ProjectiveSpace.twist n (Spec (.of k)) m).presheafModuleCat) ≅
      ProjectiveSpace.monomialCechComplex n k m) :=
  ⟨ProjectiveSpace.cechComplexTwistIso n k m⟩

/-- **Cohomology vanishes above the number of projective coordinates.** For a commutative
ring `A`, `n` with `Nat.card n = d + 1` and a quasi-coherent module `ℱ` on `ℙᵈ_A = ℙ(n; Spec A)`,
`H^q(ℙᵈ_A, ℱ) = 0` for `q > d`: `ℙᵈ_A` is separated and covered by the `d + 1` affine standard
opens, so this is `AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_card_le` (a
Mayer-Vietoris induction on the number of affine opens).

(blueprint: `lem-pc-projective-space-cohomology-bound`) -/
theorem ProjectiveSpace.subsingleton_H_of_lt (A : Type u) [CommRing A] [Finite n] {d : ℕ}
    (hn : Nat.card n = d + 1) (ℱ : (ℙ(n; Spec (.of A))).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ℙ(n; Spec (.of A))).ringCatSheaf) ℱ] {q : ℕ}
    (hq : d < q) : Subsingleton (ℱ.H q) := by
  classical
  have := Fintype.ofFinite n
  have : IsSeparated (terminal.from ℙ(n; Spec (.of A))) := by
    rw [← terminal.comp_from (ℙ(n; Spec (.of A)) ↘ Spec (.of A))]
    infer_instance
  have hcard : (Finset.univ : Finset n).card = d + 1 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hn]
  exact subsingleton_H_of_card_le Finset.univ (Finset.card_pos.1 (by omega))
    (ProjectiveSpace.standardOpen n _) (fun i _ ↦ ProjectiveSpace.isAffineOpen_standardOpen n _ i)
    (by rw [Finset.sup_univ_eq_iSup, ProjectiveSpace.iSup_standardOpen]) _
    (cechAcyclicOnAffines_of_isQuasicoherent ℱ) (by omega)

/-- **The cohomology of `𝒪(m)` on `ℙ(n; Spec k)` is that of the monomial Čech complex**,
as `k`-vector spaces: Leray's theorem for the standard affine covering of the separated scheme
`ℙ(n; Spec k)`, combined with `nonempty_cechComplex_twist_iso_monomialCechComplex`.

(blueprint: `lem-pc-projective-space-twist-cohomology`) -/
theorem ProjectiveSpace.nonempty_H_twist_linearEquiv_homology (k : Type u) [Field k]
    [Fintype n] (m : ℤ) (q : ℕ) :
    Nonempty ((ProjectiveSpace.twist n (Spec (.of k)) m).H q ≃ₗ[k]
      (ProjectiveSpace.monomialCechComplex n k m).homology q) := by
  let φ := Scheme.globalSectionsRingHom k (X := ℙ(n; Spec (.of k)))
  let K := (cechComplexFunctor (ProjectiveSpace.standardOpen n (Spec (.of k)))).obj
    (ProjectiveSpace.twist n (Spec (.of k)) m).presheafModuleCat
  obtain ⟨e₁⟩ := Scheme.Modules.nonempty_cechComplex_linearEquiv_H_of_isSeparated
    (ℙ(n; Spec (.of k)) ↘ Spec (.of k)) (ProjectiveSpace.standardOpen n (Spec (.of k)))
    (fun i ↦ ProjectiveSpace.isAffineOpen_standardOpen n _ i)
    (ProjectiveSpace.iSup_standardOpen n _)
    (ProjectiveSpace.twist n (Spec (.of k)) m) q
  obtain ⟨e₂⟩ := ProjectiveSpace.nonempty_cechComplex_twist_iso_monomialCechComplex n k m
  let e₃ : (ProjectiveSpace.twist n (Spec (.of k)) m).H q ≃ₗ[k]
      (ModuleCat.restrictScalars φ).obj (K.homology q) :=
    { e₁.symm.toAddEquiv with map_smul' := fun c x ↦ e₁.symm.map_smul (φ c) x }
  exact ⟨e₃ ≪≫ₗ ((ModuleCat.restrictScalarsHomologyIso φ K q).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ q).mapIso e₂).toLinearEquiv⟩

/-- **Vanishing of the cohomology of the twisting sheaves in middle degrees.**
`H^q(ℙᵈ_k, 𝒪(m)) = 0` for every `m` and every `q ∉ {0, d}`.

(blueprint: `lemma-coherent-base-change-invertible-sheaves--1`,
`lem-pc-projective-space-twist-cohomology`) -/
theorem ProjectiveSpace.subsingleton_H_twist_of_ne (k : Type u) [Field k] [Finite n] (d : ℕ)
    (hn : Nat.card n = d + 1) (q : ℕ) (m : ℤ) (hq0 : q ≠ 0) (hqd : q ≠ d) :
    Subsingleton ((ProjectiveSpace.twist n (Spec (.of k)) m).H q) := by
  have := Fintype.ofFinite n
  rcases lt_or_gt_of_ne hqd with hlt | hlt
  · obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
    obtain ⟨e⟩ := ProjectiveSpace.nonempty_H_twist_linearEquiv_homology n k m (q + 1)
    have h := (ProjectiveSpace.exactAt_monomialCechComplex n k m
      (by rwa [← Nat.card_eq_fintype_card]) q hlt).isZero_homology
    have : Subsingleton ((ProjectiveSpace.monomialCechComplex n k m).homology (q + 1)) :=
      (ModuleCat.isZero_iff_subsingleton).1 h
    exact e.toEquiv.subsingleton
  · exact ProjectiveSpace.subsingleton_H_of_lt n k hn _ hlt

/-- **Vanishing of the top cohomology of the twisting sheaves.**
`H^d(ℙᵈ_k, 𝒪(m)) = 0` for `m ≥ -d`, when `d ≠ 0`. For `d = 0` the statement is false, since
`H⁰(Spec k, 𝒪) = k`; that case is `nonempty_H_zero_twist_equiv` with `d = 0`.

(blueprint: `lemma-coherent-base-change-invertible-sheaves--1`,
`lem-pc-projective-space-twist-cohomology` (ii)) -/
theorem ProjectiveSpace.subsingleton_H_twist_top (k : Type u) [Field k] [Finite n] (d : ℕ)
    (hd : d ≠ 0) (hn : Nat.card n = d + 1) (m : ℤ) (hm : -(d : ℤ) ≤ m) :
    Subsingleton ((ProjectiveSpace.twist n (Spec (.of k)) m).H d) := by
  have := Fintype.ofFinite n
  obtain ⟨e⟩ := ProjectiveSpace.nonempty_H_twist_linearEquiv_homology n k m d
  have := ProjectiveSpace.subsingleton_monomialCechComplex_homology_top (n := n) (A := k)
    (by rwa [← Nat.card_eq_fintype_card]) hd hm
  exact e.toEquiv.subsingleton

end Pn

section TwistQuotient

variable {n}

/-- **A coherent module is a quotient of a finite sum of twists.** Let `A` be noetherian and
`ℱ` a coherent module on `ℙⁿ_A = ℙ(n; Spec A)`. There are `m₁, …, m_r ≥ 0` and an epimorphism
`⨁ⱼ 𝒪(-mⱼ) ⟶ ℱ`, whose kernel is coherent.

On each standard chart `D₊(Tᵢ)` choose finitely many generators `tᵢₐ` of `ℱ`. Clearing
denominators (`lem-pc-section-clearing-denominators`, applied to the section `Tᵢ` of `𝒪(1)`,
`ℙⁿ_A` being separated over `Spec A`) extends `tᵢₐ ⊗ Tᵢ^{mᵢₐ}` to a global section of
`ℱ(mᵢₐ)`, i.e. to a map `𝒪(-mᵢₐ) ⟶ ℱ` whose image contains `tᵢₐ` on `D₊(Tᵢ)`. The
sum of these maps is surjective on every chart, hence surjective. Its kernel is coherent, the
charts being spectra of noetherian rings.

(blueprint: `lem-pc-projective-space-twist-quotient`) -/
theorem ProjectiveSpace.exists_epi_sigma_twist (A : Type u) [CommRing A] [IsNoetherianRing A]
    [Finite n] (F : (ℙ(n; Spec (.of A))).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ℙ(n; Spec (.of A))).ringCatSheaf) F]
    [SheafOfModules.IsFinitePresentation (R := (ℙ(n; Spec (.of A))).ringCatSheaf) F] :
    ∃ (ι : Type u) (_ : Finite ι) (e : ι → ℕ)
      (φ : (∐ fun a ↦ ProjectiveSpace.twist n (Spec (.of A)) (-(e a : ℤ))) ⟶ F), Epi φ ∧
        SheafOfModules.IsQuasicoherent (R := (ℙ(n; Spec (.of A))).ringCatSheaf) (kernel φ) ∧
        SheafOfModules.IsFinitePresentation (R := (ℙ(n; Spec (.of A))).ringCatSheaf)
          (kernel φ) := by
  -- every section over `D₊(Tᵢ)` is hit by a map from a twist `𝒪(-m)`, by clearing denominators
  have key (i : n) : ∀ (V : (ℙ(n; Spec (.of A))).Opens)
      (_ : (Hom.zeroLocus (ProjectiveSpace.coordinateSection n (Spec (.of A)) i)).support.compl
        = V) (t : Γ(F, V)), ∃ (m : ℕ) (φ : ProjectiveSpace.twist n (Spec (.of A)) (-(m : ℤ)) ⟶ F)
        (w : Γ(ProjectiveSpace.twist n (Spec (.of A)) (-(m : ℤ)), V)), φ.app V w = t := by
    rintro V rfl t
    have : CompactSpace ℙ(n; Spec (.of A)) :=
      QuasiCompact.compactSpace_of_compactSpace (ℙ(n; Spec (.of A)) ↘ Spec (.of A))
    obtain ⟨m, u, hu⟩ := exists_tensorPowSection_eq_restrict (ℙ(n; Spec (.of A)) ↘ Spec (.of A))
      _ (ProjectiveSpace.coordinateSection n (Spec (.of A)) i) F t
    obtain ⟨e₁⟩ := ProjectiveSpace.nonempty_tensorPow_twist_one_iso n (Spec (.of A)) m
    obtain ⟨e₂⟩ := ProjectiveSpace.nonempty_tensorObj_twist_iso n (Spec (.of A)) m (-m)
    let c : (ProjectiveSpace.twist n (Spec (.of A)) 1).tensorPow m ⊗
        ProjectiveSpace.twist n (Spec (.of A)) (-(m : ℤ)) ≅ 𝟙_ _ :=
      (e₁ ⊗ᵢ Iso.refl _) ≪≫ e₂ ≪≫ eqToIso (by rw [add_neg_cancel]) ≪≫
        (ProjectiveSpace.unitIsoTwistZero n _).symm
    exact ⟨m, exists_hom_app_eq_of_tensorPowSection _ (isFreeGenerator_app_one_of_le _ le_rfl)
      m c t u hu⟩
  -- finitely many generators of `Γ(D₊(Tᵢ), ℱ)` for each `i`
  have := Fintype.ofFinite n
  have hfin (i : n) : Module.Finite Γ(ℙ(n; Spec (.of A)), ProjectiveSpace.standardOpen n _ i)
      Γ(F, ProjectiveSpace.standardOpen n _ i) :=
    finite_sections_of_isFinitePresentation F (ProjectiveSpace.isAffineOpen_standardOpen _ _ i)
  choose r t ht using fun i ↦ (hfin i).exists_fin
  choose m φ w hw using fun (a : Σ i : n, ULift.{u} (Fin (r i))) ↦ key a.1 _
    (ProjectiveSpace.compl_support_zeroLocus_coordinateSection n _ a.1) (t a.1 a.2.down)
  refine ⟨Σ i : n, ULift.{u} (Fin (r i)), inferInstance, m, Sigma.desc φ, ?_, ?_, ?_⟩
  · -- the sum of these maps is surjective on every `D₊(Tᵢ)`
    refine epi_of_surjective_app _ (ProjectiveSpace.standardOpen n (Spec (.of A)))
      (fun i ↦ ProjectiveSpace.isAffineOpen_standardOpen _ _ i)
      (ProjectiveSpace.iSup_standardOpen n _) fun i y ↦ ?_
    have hy : y ∈ Submodule.span Γ(ℙ(n; Spec (.of A)), ProjectiveSpace.standardOpen n _ i)
        (Set.range (t i)) := by
      rw [ht i]
      trivial
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hy
    refine ⟨∑ a, c a • (Sigma.ι (fun b ↦ ProjectiveSpace.twist n (Spec (.of A)) (-(m b : ℤ)))
      ⟨i, ⟨a⟩⟩).app _ (w ⟨i, ⟨a⟩⟩), ?_⟩
    simp only [map_sum, Hom.app_smul]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Sigma.ι_comp_desc, hw]
  · have := isQuasicoherent_sigma
      (fun a ↦ ProjectiveSpace.twist n (Spec (.of A)) (-(m a : ℤ)))
    exact isQuasicoherent_kernel _
  · have : IsLocallyNoetherian ℙ(n; Spec (.of A)) :=
      LocallyOfFiniteType.isLocallyNoetherian (ℙ(n; Spec (.of A)) ↘ Spec (.of A))
    have := isFinitePresentation_sigma
      (fun a ↦ ProjectiveSpace.twist n (Spec (.of A)) (-(m a : ℤ)))
    exact isFinitePresentation_kernel _

end TwistQuotient

section SerreVanishing

variable {n} (k : Type u) [Field k]

/-- On a projective space without homogeneous coordinates, which is empty, all cohomology
vanishes. -/
lemma ProjectiveSpace.subsingleton_H_of_isEmpty [IsEmpty n] (S : Scheme.{u})
    (ℱ : (ℙ(n; S)).Modules) (q : ℕ) : Subsingleton (ℱ.H q) :=
  subsingleton_H_of_isZero (isZero_of_isEmpty ℱ) q

/-- `H^q(ℙᵈ_k, 𝒪(e)) = 0` for `q > 0` and `e ≥ 0`, from `subsingleton_H_twist_of_ne` and
`subsingleton_H_twist_top`. -/
lemma ProjectiveSpace.subsingleton_H_twist_of_pos [Finite n] {d : ℕ} (hn : Nat.card n = d + 1)
    {q : ℕ} (hq : 0 < q) {e : ℤ} (he : 0 ≤ e) :
    Subsingleton ((ProjectiveSpace.twist n (Spec (.of k)) e).H q) := by
  by_cases hqd : q = d
  · subst hqd
    exact ProjectiveSpace.subsingleton_H_twist_top n k q hq.ne' hn e (by omega)
  · exact ProjectiveSpace.subsingleton_H_twist_of_ne n k d hn q e hq.ne' hqd

/-- **Serre vanishing on projective space.** Let `ℱ` be a coherent module on `ℙᵈ_k`. There is
`d₀` such that `H^q(ℙᵈ_k, ℱ(d)) = 0` for all `d ≥ d₀` and all `q > 0`.

By descending induction on `q`, for all coherent modules at once. For `q > d` the cohomology
vanishes (`AlgebraicGeometry.ProjectiveSpace.subsingleton_H_of_lt`). In general,
`AlgebraicGeometry.ProjectiveSpace.exists_epi_sigma_twist` gives `0 ⟶ 𝒦 ⟶ ⨁ⱼ 𝒪(-mⱼ) ⟶ ℱ ⟶ 0`
with `𝒦` coherent; twisting by the invertible `𝒪(d)` keeps it exact, and in its long exact
sequence `⨁ⱼ H^q(𝒪(d - mⱼ)) ⟶ H^q(ℱ(d)) ⟶ H^{q+1}(𝒦(d))` the left term vanishes for
`d ≥ maxⱼ mⱼ` and the right one for `d ≫ 0` by induction.

The blueprint states this over a noetherian ring `A`; it is stated here over a field, where
the cohomology of the twisting sheaves
(`AlgebraicGeometry.ProjectiveSpace.subsingleton_H_twist_of_ne` and `subsingleton_H_twist_top`)
is available.

(blueprint: `lemma-coherent-base-change-invertible-sheaves--1`) -/
theorem ProjectiveSpace.exists_subsingleton_H_tensor_twist [Finite n]
    (ℱ : (ℙ(n; Spec (.of k))).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ℙ(n; Spec (.of k))).ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := (ℙ(n; Spec (.of k))).ringCatSheaf) ℱ] :
    ∃ d₀ : ℤ, ∀ d ≥ d₀, ∀ q : ℕ, 0 < q →
      Subsingleton ((ℱ ⊗ ProjectiveSpace.twist n (Spec (.of k)) d).H q) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨0, fun d _ q _ ↦ ProjectiveSpace.subsingleton_H_of_isEmpty _ _ q⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ, Nat.card n = D + 1 :=
    ⟨Nat.card n - 1, by have := Nat.card_pos (α := n); omega⟩
  suffices key : ∀ j : ℕ, ∀ (𝒢 : (ℙ(n; Spec (.of k))).Modules)
      [SheafOfModules.IsQuasicoherent (R := (ℙ(n; Spec (.of k))).ringCatSheaf) 𝒢]
      [SheafOfModules.IsFinitePresentation (R := (ℙ(n; Spec (.of k))).ringCatSheaf) 𝒢],
      ∃ d₀ : ℤ, ∀ d ≥ d₀, ∀ q : ℕ, D < q + j → 0 < q →
        Subsingleton ((𝒢 ⊗ ProjectiveSpace.twist n (Spec (.of k)) d).H q) by
    obtain ⟨d₀, h⟩ := key (D + 1) ℱ
    exact ⟨d₀, fun d hd q hq ↦ h d hd q (by omega) hq⟩
  intro j
  induction j with
  | zero =>
    intro 𝒢 _ _
    refine ⟨0, fun d _ q hq _ ↦ ?_⟩
    have := isQuasicoherent_tensorObj 𝒢 (ProjectiveSpace.twist n (Spec (.of k)) d)
    exact ProjectiveSpace.subsingleton_H_of_lt n k hD _ (by omega)
  | succ j ih =>
    intro 𝒢 _ _
    obtain ⟨ι, _, m, p, hp, hK₁, hK₂⟩ := ProjectiveSpace.exists_epi_sigma_twist k 𝒢
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
    let T := ProjectiveSpace.twist n (Spec (.of k)) d
    obtain ⟨e₁⟩ := ProjectiveSpace.nonempty_tensorObj_twist_iso n (Spec (.of k)) d (-d)
    let E := BraidedCategory.tensorRightEquivalence T (ProjectiveSpace.twist n (Spec (.of k)) (-d))
      (e₁ ≪≫ eqToIso (congrArg _ (add_neg_cancel d)) ≪≫
        (ProjectiveSpace.unitIsoTwistZero n (Spec (.of k))).symm)
    have : (tensorRight T).IsEquivalence := E.isEquivalence_functor
    have hS : (ShortComplex.kernelSequence p).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact p) inferInstance hp
    have hS' := hS.map_of_exact (tensorRight T)
    let G := fun i ↦ ProjectiveSpace.twist n (Spec (.of k)) (-(m i : ℤ))
    have : ∀ i, Subsingleton ((G i ⊗ T).H q) := fun i ↦ by
      obtain ⟨e⟩ := ProjectiveSpace.nonempty_tensorObj_twist_iso n (Spec (.of k)) (-(m i : ℤ)) d
      have := ProjectiveSpace.subsingleton_H_twist_of_pos k hD hq0 (e := -(m i : ℤ) + d)
        (by have := hdm i; omega)
      exact subsingleton_H_of_iso e.symm q
    have hsum : Subsingleton ((∐ fun i ↦ G i ⊗ T).H q) := subsingleton_H_sigma (fun i ↦ G i ⊗ T) q
    have h₂' : Subsingleton (((tensorRight T).obj (kernel p)).H (q + 1)) :=
      h₂ d hd₂ (q + 1) (by omega) (by omega)
    have h₃ : Subsingleton (((tensorRight T).obj (∐ G)).H q) :=
      @subsingleton_H_of_iso _ _ _ (PreservesCoproduct.iso (tensorRight T) G).symm q hsum
    exact @subsingleton_H_of_shortExact _ _ hS' q h₃ h₂'

end SerreVanishing

variable {n} {X : Scheme.{u}} (k : Type u) [Field k]

open scoped AlgebraicGeometry.Scheme.Modules in
/-- **Serre's theorem B: vanishing after a twist.** Let `X ⊆ ℙᵈ_k` be a closed subscheme, i.e. a
closed immersion `i : X ⟶ ℙ(n; Spec k)`, and let `ℱ` be a coherent sheaf on `X`. Then
`H^q(X, ℱ ⊗ 𝒪_X(m)) = 0` for all `q > 0` and all `m ≫ 0`, where `𝒪_X(m)` is the pullback along
`i` of the twisting sheaf `𝒪(m)`.

Mathlib has no `IsCoherent` predicate, so "coherent" is spelled as
`SheafOfModules.IsFinitePresentation` together with `SheafOfModules.IsQuasicoherent`; on the
noetherian scheme `X` these two conditions together are coherence.

The pushforward `i_* ℱ` is coherent
(`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_pushforward_of_isClosedImmersion`), with
`i_* (ℱ ⊗ 𝒪_X(m)) ≅ (i_* ℱ)(m)` by the projection formula and
`H^q(X, ℱ ⊗ 𝒪_X(m)) ≅ H^q(ℙᵈ_k, i_* (ℱ ⊗ 𝒪_X(m)))` since a closed immersion is affine
(`AlgebraicGeometry.Scheme.Modules.nonempty_cohomologyFunctor_iso_pushforward_of_isAffineHom`),
so this is Serre vanishing on `ℙᵈ_k`,
`AlgebraicGeometry.ProjectiveSpace.exists_subsingleton_H_tensor_twist`, for `i_* ℱ`.

(blueprint: `lemma-coherent-base-change-invertible-sheaves--1`) -/
theorem Scheme.Modules.exists_subsingleton_H_tensor_twist [Finite n]
    (i : X ⟶ ℙ(n; Spec (.of k))) [IsClosedImmersion i] (F : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) F] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q : ℕ, 0 < q →
      Subsingleton ((F ⊗ₘ ProjectiveSpace.twistRestrict i m).H q) := by
  have := LocallyOfFiniteType.isLocallyNoetherian (ℙ(n; Spec (.of k)) ↘ Spec (.of k))
  have := isQuasicoherent_pushforward_of_isClosedImmersion i F
  have := isFinitePresentation_pushforward_of_isClosedImmersion i F
  obtain ⟨m₀, h⟩ := ProjectiveSpace.exists_subsingleton_H_tensor_twist k ((pushforward i).obj F)
  refine ⟨m₀, fun m hm q hq ↦ ?_⟩
  have := h m hm q hq
  obtain ⟨e⟩ := nonempty_pushforward_tensorObj_pullback_iso i F
    (ProjectiveSpace.twist n (Spec (.of k)) m)
  let : X.Over (Spec (.of k)) := ⟨i ≫ ℙ(n; Spec (.of k)) ↘ Spec (.of k)⟩
  have : i.IsOver (Spec (.of k)) := ⟨rfl⟩
  have := isQuasicoherent_tensorObj F (ProjectiveSpace.twistRestrict i m)
  obtain ⟨e'⟩ := nonempty_cohomologyFunctor_iso_pushforward_of_isAffineHom k i q
  have := subsingleton_H_of_iso e.symm q
  exact Equiv.subsingleton (β := ((pushforward i).obj (F ⊗ₘ ProjectiveSpace.twistRestrict i m)).H q)
    (e'.app ⟨F ⊗ₘ ProjectiveSpace.twistRestrict i m, inferInstance⟩).toLinearEquiv.toEquiv

open scoped AlgebraicGeometry.Scheme.Modules in
open ProjectiveSpace in
/-- **Serre's theorem A: global generation after a twist.** Let `X ⊆ ℙᵈ_k` be a closed
subscheme, i.e. a closed immersion `i : X ⟶ ℙ(n; Spec k)`, and let `ℱ` be a coherent sheaf on
`X`. Then `ℱ ⊗ 𝒪_X(m)` is generated by its global sections for all `m ≫ 0`.

"Generated by its global sections" is `Nonempty (SheafOfModules.GeneratingSections _)`: the
sections `σ.s : σ.I → M.sections` of a `GeneratingSections` are by construction global
sections of `M`, and `σ.π : free σ.I ⟶ M` being an epimorphism is exactly the statement that
the map from the free module on those global sections is surjective as a map of sheaves.

As for theorem B, "coherent" is `SheafOfModules.IsFinitePresentation` together with
`SheafOfModules.IsQuasicoherent`.

The proof follows Hartshorne: `𝒢 = i_* ℱ` is coherent on `P = ℙ(n; Spec k)`, and is a
quotient `⊕ₐ 𝒪(-mₐ) ⟶ 𝒢` of a finite sum of twists (`ProjectiveSpace.exists_epi_sigma_twist`).
For `m ≥ max mₐ`, tensoring with the invertible module `𝒪(m)` gives a surjection
`⊕ₐ 𝒪(m - mₐ) ⟶ 𝒢(m)` from a sum of twists of non-negative degree, each generated by global
sections (`ProjectiveSpace.generatingSectionsTwist`). Finally `𝒢(m) ≅ i_* (ℱ(m))` by the
projection formula, and global generation descends along `i` because `i_*` is faithful
(`Scheme.Modules.GeneratingSections.ofPushforward`).

(blueprint: `lemma-coherent-base-change-invertible-sheaves--1`, `thm-picard-serre-a`) -/
theorem Scheme.Modules.exists_generatingSections_tensor_twist [Finite n]
    (i : X ⟶ ℙ(n; Spec (.of k))) [IsClosedImmersion i] (F : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) F] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀,
      Nonempty (SheafOfModules.GeneratingSections (F ⊗ₘ ProjectiveSpace.twistRestrict i m)) := by
  -- Step 1: `𝒢 = i_* ℱ` is coherent on `P`, and a quotient of a finite sum of twists.
  have : IsLocallyNoetherian ℙ(n; Spec (.of k)) :=
    LocallyOfFiniteType.isLocallyNoetherian (ℙ(n; Spec (.of k)) ↘ Spec (.of k))
  have := isQuasicoherent_pushforward_of_isClosedImmersion i F
  have := isFinitePresentation_pushforward_of_isClosedImmersion i F
  obtain ⟨ι, _, e, φ, hφ, -, -⟩ := exists_epi_sigma_twist k ((pushforward i).obj F)
  obtain ⟨M, hM⟩ := (Set.finite_range e).bddAbove
  refine ⟨M, fun m hm ↦ ?_⟩
  -- Step 2: each `𝒪(-mₐ) ⊗ 𝒪(m) ≅ 𝒪(m - mₐ)` is generated by global sections.
  have hgen (a : ι) : Nonempty (SheafOfModules.GeneratingSections
      (twist n (Spec (.of k)) (-(e a : ℤ)) ⊗ₘ twist n (Spec (.of k)) m)) := by
    obtain ⟨t⟩ := nonempty_tensorObj_twist_iso n (Spec (.of k)) (-(e a : ℤ)) m
    have hd : -(e a : ℤ) + m = ((m - e a).toNat : ℕ) := by
      have := hM ⟨a, rfl⟩
      omega
    exact ⟨(SheafOfModules.GeneratingSections.equivOfIso (t ≪≫ eqToIso (by rw [hd]))).symm
      (generatingSectionsTwist n _ _)⟩
  -- Step 3: `- ⊗ 𝒪(m)` is an autoequivalence, so `φ ⊗ 𝒪(m)` is an epimorphism out of
  -- `(⊕ₐ 𝒪(-mₐ)) ⊗ 𝒪(m) ≅ ⊕ₐ (𝒪(-mₐ) ⊗ 𝒪(m))`.
  obtain ⟨t⟩ := nonempty_tensorObj_twist_iso n (Spec (.of k)) m (-m)
  have : (tensorRight (twist n (Spec (.of k)) m)).IsEquivalence :=
    (BraidedCategory.tensorRightEquivalence (twist n (Spec (.of k)) m)
      (twist n (Spec (.of k)) (-m))
        (t ≪≫ eqToIso (by simp) ≪≫ (unitIsoTwistZero n _).symm)).isEquivalence_functor
  have : Epi (φ ▷ twist n (Spec (.of k)) m) := (tensorRight _).map_epi φ
  let σ := ((SheafOfModules.GeneratingSections.equivOfIso
    (PreservesCoproduct.iso (tensorRight (twist n (Spec (.of k)) m)) _).symm)
      (SheafOfModules.GeneratingSections.sigma _ fun a ↦ (hgen a).some)).ofEpi
        (φ ▷ twist n (Spec (.of k)) m)
  -- Step 4: `𝒢 ⊗ 𝒪(m) ≅ i_* (ℱ ⊗ i^* 𝒪(m))`, and generation descends along `i`.
  obtain ⟨pf⟩ := nonempty_pushforward_tensorObj_pullback_iso i F (twist n (Spec (.of k)) m)
  exact ⟨GeneratingSections.ofPushforward i
    (SheafOfModules.GeneratingSections.equivOfIso pf.symm σ)⟩

/-- **Serre vanishing for an ample module.** Let `X` be a scheme over a field `k`, `ℒ` an ample
invertible `𝒪_X`-module and `ℱ` a coherent `𝒪_X`-module. Then there is `n₀` with
`H^p(X, ℱ ⊗ ℒ^{⊗ n}) = 0` for all `n ≥ n₀` and all `p > 0`.

Some power `ℒ^{⊗ m}`, `m ≥ 1`, is `i^* 𝒪(1)` for a closed immersion `i : X ⟶ ℙᴺ_k`. For each of
the finitely many `0 ≤ r < m`, Serre's theorem B
(`AlgebraicGeometry.Scheme.Modules.exists_subsingleton_H_tensor_twist`) applied to
`ℱ ⊗ ℒ^{⊗ r}` gives `t_r` with `H^q(X, ℱ ⊗ ℒ^{⊗ (m t + r)}) = H^q(X, ℱ ⊗ ℒ^{⊗ r} ⊗ 𝒪_X(t)) = 0`
for `t ≥ t_r` and `q > 0`; take `n₀ = m · maxᵣ t_r` and write `n = m t + r`.

The blueprint asks `X` to be proper over `k`; this is not needed here, since
`AlgebraicGeometry.IsVeryAmple` already provides a closed immersion into projective space.

(blueprint: `lem-pc-serre-vanishing`) -/
@[stacks 0B5U]
theorem Scheme.Modules.exists_subsingleton_H_tensorObj_tensorPow (f : X ⟶ Spec (.of k))
    (ℒ : X.Modules) (hℒ : IsAmple f ℒ) (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) ℱ] :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ p : ℕ, 0 < p → Subsingleton ((ℱ ⊗ ℒ.tensorPow n).H p) := by
  obtain ⟨hinv, m, hm, N, i, hN, hi, -, ⟨e⟩⟩ := hℒ
  have key (r : Fin m) : ∃ t₀ : ℕ, ∀ t ≥ t₀, ∀ p : ℕ, 0 < p →
      Subsingleton (((ℱ ⊗ ℒ.tensorPow r) ⊗ ProjectiveSpace.twistRestrict i t).H p) := by
    have := isQuasicoherent_tensorObj ℱ (ℒ.tensorPow r)
    have := isFinitePresentation_tensorObj ℱ (ℒ.tensorPow r)
    obtain ⟨m₀, h⟩ := exists_subsingleton_H_tensor_twist k i (ℱ ⊗ ℒ.tensorPow r)
    exact ⟨m₀.toNat, fun t ht p hp ↦ h t (by omega) p hp⟩
  choose t₀ ht₀ using key
  refine ⟨m * ∑ r, t₀ r, fun n hn p hp ↦ ?_⟩
  -- write `n = r + m t` with `r < m`
  set r : Fin m := ⟨n % m, Nat.mod_lt n hm⟩
  set t := n / m
  have hn' : n = r + m * t := (Nat.mod_add_div n m).symm
  have ht : t₀ r ≤ t := by
    refine le_trans (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ r)) ?_
    exact (Nat.le_div_iff_mul_le hm).2 (by rw [mul_comm]; exact hn)
  -- `ℒ^{⊗ m t} ≅ 𝒪_X(t)`
  have hpow : ∀ s : ℕ, Nonempty ((ℒ.tensorPow m).tensorPow s ≅
      (ProjectiveSpace.twistRestrict i 1).tensorPow s) := by
    intro s
    induction s with
    | zero => exact ⟨Iso.refl _⟩
    | succ s ih => exact ⟨e.symm ⊗ᵢ ih.some⟩
  obtain ⟨e₁⟩ := Scheme.Modules.nonempty_pullback_tensorPow_iso i
    (ProjectiveSpace.twist N (Spec (.of k)) 1) t
  obtain ⟨e₂⟩ := ProjectiveSpace.nonempty_tensorPow_twist_one_iso N (Spec (.of k)) t
  let e₃ : ℒ.tensorPow n ≅ ℒ.tensorPow r ⊗ ProjectiveSpace.twistRestrict i t :=
    eqToIso (congrArg ℒ.tensorPow hn') ≪≫ ℒ.tensorPowAddIso r (m * t) ≪≫
      (Iso.refl _ ⊗ᵢ (ℒ.tensorPowMulIso m t ≪≫ (hpow t).some ≪≫ e₁.symm ≪≫
        (Scheme.Modules.pullback i).mapIso e₂))
  have := ht₀ r t ht p hp
  exact subsingleton_H_of_iso ((α_ _ _ _) ≪≫ (Iso.refl ℱ ⊗ᵢ e₃.symm)) p

end AlgebraicGeometry
