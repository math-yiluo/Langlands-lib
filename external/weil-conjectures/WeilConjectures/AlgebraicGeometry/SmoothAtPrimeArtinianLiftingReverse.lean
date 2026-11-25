/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.Basic

import Mathlib.LinearAlgebra.TensorProduct.Quotient
import WeilConjectures.AlgebraicGeometry.ArtinianLiftingConormalModMaximal

/-!
# Reverse Artinian lifting criterion

The proof uses the localized polynomial presentation, conormal splitting modulo the maximal ideal,
and the residue-field splitting criterion. Mathlib then gives formal smoothness of the
localization and a smooth principal open neighbourhood.
Source: Stacks Project, Algebra, Lemma 02HT.

The declaration's docstring records the original source argument. Its completion step
is replaced here by Mathlib's local finite-free residue-field criterion: the private
helper transports the quotient retraction through the tensor/quotient equivalences.
Only reduction modulo the maximal ideal is needed. The new conormal lemma isolates
steps 7--11 of that argument, with N chosen so that N-c = 1.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem residue_injective_of_split_quot
    {S : Type u} [CommRing S] [IsLocalRing S]
    {N : Type v} [AddCommGroup N] [Module S N]
    {M : Type*} [AddCommGroup M] [Module S M]
    (u : N →ₗ[S] M)
    (v : (M ⧸ (IsLocalRing.maximalIdeal S • (⊤ : Submodule S M))) →ₗ[S]
      (N ⧸ (IsLocalRing.maximalIdeal S • (⊤ : Submodule S N))))
    (hv : v.comp ((IsLocalRing.maximalIdeal S • (⊤ : Submodule S M)).mkQ.comp u) =
      (IsLocalRing.maximalIdeal S • (⊤ : Submodule S N)).mkQ) :
    Function.Injective (u.lTensor (IsLocalRing.ResidueField S)) := by
  change Function.Injective (u.lTensor (S ⧸ IsLocalRing.maximalIdeal S))
  let eN := TensorProduct.quotTensorEquivQuotSMul N (IsLocalRing.maximalIdeal S)
  let eM := TensorProduct.quotTensorEquivQuotSMul M (IsLocalRing.maximalIdeal S)
  have h : (eN.symm.toLinearMap.comp (v.comp eM.toLinearMap)).comp
      (u.lTensor (S ⧸ IsLocalRing.maximalIdeal S)) = LinearMap.id := by
    apply TensorProduct.ext'
    intro c x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe,
      LinearMap.id_apply]
    change eN.symm (v (eM (TensorProduct.tmul S (Ideal.Quotient.mk _ r) (u x)))) = _
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
    have hvr : v (Submodule.Quotient.mk (r • u x)) =
        Submodule.Quotient.mk (r • x) := by
      simpa only [LinearMap.comp_apply, u.map_smul, Submodule.mkQ_apply] using
        LinearMap.congr_fun hv (r • x)
    rw [hvr]
    exact (TensorProduct.quotTensorEquivQuotSMul_mk_tmul _ r x).symm
      |> eN.symm_apply_eq.mpr
  exact Function.HasLeftInverse.injective
    ⟨eN.symm.toLinearMap.comp (v.comp eM.toLinearMap), LinearMap.congr_fun h⟩

set_option backward.isDefEq.respectTransparency false in
/-- Source: Stacks Project, Algebra, Lemma 02HT, (3) implies (1); Definition 02HS.
(blueprint: lem-weil-pbc-smooth-at-prime-artinian-lifting-reverse).

Proof in words, with step numbers inherited from the parent plan:
1. Principal opens form a basis of Spec A (def-weil-affine-spectrum). The localization
   map identifies Spec A_g with D(g) (lem-weil-pbc-principal-localization-open-immersion,
   def-weil-open-immersion). Smoothness is unchanged by that isomorphism and by restriction
   (lem-weil-pbc-smooth-restrict-open-subschemes,
   lem-weil-pbc-morphism-factors-through-open-subscheme). Thus an open smooth neighbourhood
   exists iff some g outside q makes R -> A_g smooth
   (lem-weil-pbc-smooth-ring-map-iff-smooth-affine, def-weil-pbc-smooth-ring-map).
2. The kernel I of a small extension is a simple module. Its annihilator is the unique
   maximal ideal m' of B', so m'I = 0. Since B is nonzero, I is proper and contained in m',
   hence I squared is zero. Surjectivity also gives preimage(m_B) = m' and B'/I = B.
4. Finite type over Noetherian gives a finite presentation A = P/I with P a finite polynomial
   ring (lem-weil-pbc-finite-type-noetherian-finite-presentation). Differentials of P are free
   on the coordinate differentials (lem-weil-pbc-polynomial-ring-kahler-basis,
   def-weil-pbc-kahler-differentials), and its first cotangent homology vanishes
   (lem-weil-pbc-polynomial-ring-h1-cotangent-vanishing). Jacobi-Zariski gives the exact
   sequence from first cotangent homology through I/I squared and the free differential
   module to Omega A/R (lem-weil-pbc-jacobi-zariski-quotient-smooth).
5. If the conormal map splits at q, exactness gives vanishing first cotangent homology there
   and makes the differentials a finite flat direct summand of a finite free module.
   Finite flat over local is free (lem-weil-pbc-finite-flat-local-free), so the criterion
   lem-weil-pbc-smooth-at-prime-naive-cotangent-criterion and step 1 give smoothness near q.
6. Localize P at the preimage q' of q, obtaining C with maximal ideal m and ideal J = IC.
   Noetherianity follows from lem-weil-pbc-finite-type-algebra-noetherian and
   lem-weil-pbc-localization-noetherian. Exact localization identifies C/J with A_q and
   J/J squared with the localized conormal module. Differential localization identifies
   the target with A_q tensor Omega C/R (lem-weil-pbc-kahler-differentials-localization).
7. For N >= 1 take B'_N = C/(J squared + m^N), B_N = C/(J + m^N), and their quotient map.
   Both are Artinian local with maximal ideals having N-th power zero
   (lem-weil-pbc-noetherian-local-quotient-artinian-local). The kernel has square zero.
   The natural maps from R and A give a compatible diagram with preimage maximal ideal q.
8. Filter the kernel by length-one factors (lem-weil-pbc-artinian-ideal-length-one-filtration).
   All intermediate quotients remain Artinian local by the quotient lemma in step 7.
   Apply the lifting hypothesis successively to these small extensions. At each step the
   preimage maximal ideal stays q by step 2. This produces s_N : A -> B'_N over R.
9. Elements outside q map to units, so s_N factors through A_q. The N-th power of q maps
   to zero, so it factors further through B_N. The resulting R-algebra map sigma_N is a
   section of B'_N -> B_N, by the universal properties of localization and quotient.
10. The square-zero conormal retraction lemma
    (lem-weil-pbc-square-zero-section-conormal-retraction) applied to this section makes
    the conormal map of B'_N -> B_N a split injection.
11. Artin-Rees (lem-weil-pbc-artin-rees) supplies c >= 1 such that m^N intersect J is
    contained in m^(N-c) J. Put k = N-c >= 1. Tensor step 10 with A_q/q^k. The modular law
    identifies its source with (J/J squared)/q^k. Apply the differential power-ideal lemma first to
    C and J with n = 1, then to C/J squared and its maximal ideal with n = N-1. This identifies the
    target with (A_q tensor Omega C/R)/q^k. Both maps send x to dx, so the localized conormal map
    modulo q^k is split for every k >= 1; tensoring preserves the given left inverse.
12. The source and target of the localized conormal map are finitely generated over the
    Noetherian local ring A_q. Its maximal ideal is its Jacobson radical. Apply
    lem-weil-pbc-split-injection-after-completion to the split maps modulo q^k from step 11.
    The conormal map itself splits, and step 5 finishes the reverse implication.
The rings in the test construction can be transported to Type (max u v) by ULift;
the algebra structures, module lengths and lifting equations are preserved.
-/
theorem artinian_lifting_smooth_on_open_reverse
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R]
    (φ₀ : R →+* A) (hfinite : φ₀.FiniteType) (q : Ideal A) [q.IsPrime] :
    (∀ (B' B : Type (max u v)) [CommRing B'] [CommRing B]
      [IsArtinianRing B'] [IsArtinianRing B] [IsLocalRing B'] [IsLocalRing B]
      (φ : B' →+* B), Function.Surjective φ → Module.length B' (RingHom.ker φ) = 1 →
      ∀ (ρ : R →+* B') (a : A →+* B),
        a.comp φ₀ = φ.comp ρ → Ideal.comap a (IsLocalRing.maximalIdeal B) = q →
        ∃ a' : A →+* B', φ.comp a' = a ∧ a'.comp φ₀ = ρ) →
    (∃ W : (Spec (CommRingCat.of A)).Opens,
      (⟨q, inferInstance⟩ : PrimeSpectrum A) ∈ W ∧
        Smooth (W.ι ≫ Spec.map (CommRingCat.ofHom φ₀))) := by
  classical
  intro hlift
  let := φ₀.toAlgebra
  have : Algebra.FiniteType R A := hfinite
  have : Algebra.FinitePresentation R A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  obtain ⟨n, π, hπ⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := A)).mp
    (inferInstanceAs (Algebra.FiniteType R A))
  let C₀ := MvPolynomial (Fin n) R
  let := π.toRingHom.toAlgebra
  have : IsScalarTower R C₀ A := IsScalarTower.of_algebraMap_eq' π.comp_algebraMap.symm
  let Q := q.comap (algebraMap C₀ A)
  have : Q.IsPrime := Ideal.comap_isPrime _ q
  have : q.LiesOver Q := ⟨rfl⟩
  let := Localization.AtPrime.algebraOfLiesOver Q q
  let C := Localization.AtPrime Q
  let S := Localization.AtPrime q
  have hsurj : Function.Surjective (algebraMap C S) := by
    intro x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl x
    obtain ⟨a', rfl⟩ := hπ a
    obtain ⟨s', hs'⟩ := hπ (s : A)
    have hs'Q : s' ∈ Q.primeCompl := by
      change algebraMap C₀ A s' ∉ q
      exact hs' ▸ s.2
    refine ⟨IsLocalization.mk' C a' ⟨s', hs'Q⟩, ?_⟩
    rw [Localization.AtPrime.algebraMap_eq, Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hs'
  let P : Algebra.Extension R S :=
    { Ring := C, σ := Function.surjInv hsurj, algebraMap_σ := Function.surjInv_eq hsurj }
  have : Algebra.FormallySmooth C₀ C := .of_isLocalization Q.primeCompl
  have : Algebra.FormallySmooth R C := .comp R C₀ C
  have : Algebra.EssFiniteType C₀ C := .of_isLocalization C Q.primeCompl
  have : Algebra.EssFiniteType R C := .comp R C₀ C
  have : Module.Finite S P.Cotangent := Algebra.Extension.Cotangent.finite
    (IsNoetherian.noetherian P.ker)
  have : Module.Finite S P.CotangentSpace := inferInstance
  have : Module.Free S P.CotangentSpace := Module.free_of_flat_of_isLocalRing
  obtain ⟨v, hv⟩ := Algebra.artinian_lifting_conormal_split_mod_maximal.{u, v} q P hlift
  obtain ⟨l, hl⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective
    P.cotangentComplex).mpr (residue_injective_of_split_quot P.cotangentComplex v hv)
  have : Algebra.IsSmoothAt R q := P.formallySmooth_iff_split_injection.mpr ⟨l, hl⟩
  obtain ⟨g, hg, hsmooth⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R q
  let j := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away g)))
  have : Smooth (Spec.map (CommRingCat.ofHom
      ((algebraMap A (Localization.Away g)).comp φ₀))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    change ((algebraMap A (Localization.Away g)).comp (algebraMap R A)).Smooth
    rw [← IsScalarTower.algebraMap_eq R A (Localization.Away g)]
    exact RingHom.smooth_algebraMap.mpr hsmooth
  have : Smooth (j ≫ Spec.map (CommRingCat.ofHom φ₀)) := by
    change Smooth (Spec.map _ ≫ Spec.map _)
    rw [← Spec.map_comp]
    exact this
  refine ⟨j.opensRange, ?_, ?_⟩
  · change (⟨q, inferInstance⟩ : (Spec (CommRingCat.of A))) ∈ j.opensRange
    rw [Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of A) g]
    exact hg
  · rw [← j.isoOpensRange_inv_comp, Category.assoc]
    infer_instance

end AlgebraicGeometry
