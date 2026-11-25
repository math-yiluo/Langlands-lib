/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.Algebra.TrivSqZeroExt.Basic
import WeilConjectures.RingTheory.SymmetricAlgebraQuotientModule

/-!
# Naive cotangent complex of a symmetric algebra

Source: literature/stacks-project/more-algebra.tex, Lemma Tag 07EV (corrected: the
conormal map is only surjective)
(blueprint: lem-weil-pbc-cotangent-complex-symmetric-algebra)
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace AlgebraicGeometry

open Algebra

private local instance cotangentOppositeModule (S : Type*) (N : Type*)
    [CommRing S] [AddCommGroup N] [Module S N] : Module Sᵐᵒᵖ N :=
  Module.compHom N ((RingHom.id S).fromOpposite fun a b ↦ mul_comm a b)

private local instance cotangentCentralModule (S : Type*) (N : Type*)
    [CommRing S] [AddCommGroup N] [Module S N] : IsCentralScalar S N := ⟨fun _ _ ↦ rfl⟩

private local instance cotangentOppositeTower (R : Type u) (S : Type*) (N : Type*)
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup N]
    [Module R N] [Module S N] [IsScalarTower R S N] : IsScalarTower R Sᵐᵒᵖ N :=
  ⟨fun r s n ↦ smul_assoc r (MulOpposite.unop s) n⟩

-- Universal-property construction from Stacks 00DM and 00RO. The private helpers
-- adapt the proof in WeilConjectures.RingTheory.SymmetricAlgebraDifferentials to independent
-- universes for the coefficient ring, generator module, and derivation target.
private noncomputable def cotangentSymmetricDerivation
    (R : Type u) (K : Type v) (N : Type*) [CommRing R] [AddCommGroup K] [Module R K]
    [AddCommGroup N] [Module R N] [Module (SymmetricAlgebra R K) N]
    [IsScalarTower R (SymmetricAlgebra R K) N] (v : K →ₗ[R] N) :
    Derivation R (SymmetricAlgebra R K) N := by
  let S := SymmetricAlgebra R K
  let f : S →ₐ[R] TrivSqZeroExt S N := SymmetricAlgebra.lift
    ((TrivSqZeroExt.inlAlgHom R S N).toLinearMap.comp (SymmetricAlgebra.ι R K) +
      ((TrivSqZeroExt.inrHom S N).restrictScalars R).comp v)
  have hf : (TrivSqZeroExt.fstHom R S N).comp f = AlgHom.id R S := by
    ext k
    simp [f]
    rfl
  have hf' (s : S) : (f s).fst = s := DFunLike.congr_fun hf s
  refine
    { toLinearMap := ((TrivSqZeroExt.sndHom S N).restrictScalars R).comp f.toLinearMap
      map_one_eq_zero' := by simp
      leibniz' := ?_ }
  intro a b
  change (f (a * b)).snd = a • (f b).snd + b • (f a).snd
  rw [map_mul, TrivSqZeroExt.snd_mul, hf', hf']
  simp

private theorem cotangentSymmetricDerivation_ι
    (R : Type u) (K : Type v) (N : Type*) [CommRing R] [AddCommGroup K] [Module R K]
    [AddCommGroup N] [Module R N] [Module (SymmetricAlgebra R K) N]
    [IsScalarTower R (SymmetricAlgebra R K) N] (v : K →ₗ[R] N) (k : K) :
    cotangentSymmetricDerivation R K N v (SymmetricAlgebra.ι R K k) = v k := by
  simp [cotangentSymmetricDerivation]

private theorem cotangentSymmetricDerivation_ext
    (R : Type u) (K : Type v) (N : Type*) [CommRing R] [AddCommGroup K] [Module R K]
    [AddCommGroup N] [Module R N] [Module (SymmetricAlgebra R K) N]
    [IsScalarTower R (SymmetricAlgebra R K) N]
    (d e : Derivation R (SymmetricAlgebra R K) N)
    (h : ∀ k, d (SymmetricAlgebra.ι R K k) = e (SymmetricAlgebra.ι R K k)) : d = e := by
  ext s
  induction s using SymmetricAlgebra.induction with
  | algebraMap r => simp
  | ι k => exact h k
  | mul a b ha hb => simp only [Derivation.leibniz, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

private theorem cotangentSymmetricDifferentials
    (R : Type u) (K : Type v) [CommRing R] [AddCommGroup K] [Module R K] :
    ∃ e : KaehlerDifferential R (SymmetricAlgebra R K) ≃ₗ[SymmetricAlgebra R K]
        (SymmetricAlgebra R K ⊗[R] K),
      ∀ k : K, e (KaehlerDifferential.D R (SymmetricAlgebra R K)
        (SymmetricAlgebra.ι R K k)) = 1 ⊗ₜ[R] k := by
  let S := SymmetricAlgebra R K
  let v : K →ₗ[R] S ⊗[R] K := TensorProduct.mk R S K 1
  let d := cotangentSymmetricDerivation R K (S ⊗[R] K) v
  let f := d.liftKaehlerDifferential
  let g : S ⊗[R] K →ₗ[S] KaehlerDifferential R S :=
    ((KaehlerDifferential.D R S).toLinearMap.comp (SymmetricAlgebra.ι R K)).liftBaseChange S
  have hd (k : K) : d (SymmetricAlgebra.ι R K k) = 1 ⊗ₜ[R] k :=
    cotangentSymmetricDerivation_ι R K _ v k
  have hgf : g.comp f = LinearMap.id := by
    apply Derivation.liftKaehlerDifferential_unique
    apply cotangentSymmetricDerivation_ext R K _
    intro k
    simp [f, g, hd]
    rfl
  have hfg : f.comp g = LinearMap.id := by
    ext k
    change f (g (1 ⊗ₜ[R] k)) = 1 ⊗ₜ[R] k
    simp only [g, LinearMap.liftBaseChange_tmul, one_smul, LinearMap.comp_apply]
    change f (KaehlerDifferential.D R S (SymmetricAlgebra.ι R K k)) = _
    exact (Derivation.liftKaehlerDifferential_comp_D d _).trans (hd k)
  let e : KaehlerDifferential R S ≃ₗ[S] S ⊗[R] K :=
    { f with
      invFun := g
      left_inv := fun x ↦ DFunLike.congr_fun hgf x
      right_inv := fun x ↦ DFunLike.congr_fun hfg x }
  refine ⟨e, ?_⟩
  intro k
  exact (Derivation.liftKaehlerDifferential_comp_D d _).trans (hd k)

private theorem symmetricPresentation
    {A : Type u} [CommRing A]
    {M : Type v} [AddCommGroup M] [Module A M] {m : ℕ}
    (K : Submodule A (Fin m → A)) (π : (Fin m → A) →ₗ[A] M)
    (hπ : Function.Surjective π) (hK : LinearMap.ker π = K) :
    let a := fun j ↦ SymmetricAlgebra.ι A M (π (Pi.single j 1))
    let ℓ := fun k : Fin m → A ↦ ∑ j, MvPolynomial.C (k j) * MvPolynomial.X j
    Function.Surjective (MvPolynomial.aeval (R := A) a) ∧
      RingHom.ker (MvPolynomial.aeval (R := A) a) = Ideal.span (ℓ '' (K : Set _)) := by
  classical
  let b := Pi.basisFun A (Fin m)
  let e := SymmetricAlgebra.equivMvPolynomial b
  let φ := SymmetricAlgebra.lift ((SymmetricAlgebra.ι A M).comp π)
  obtain ⟨hφ, hker, _⟩ := symmetricAlgebra_quotient_module A (Fin m → A) M π hπ
  let f := φ.comp e.symm.toAlgHom
  have heval : MvPolynomial.aeval (R := A)
      (fun j ↦ SymmetricAlgebra.ι A M (π (Pi.single j 1))) = f := by
    ext j
    simp [f, φ, e, b, Pi.basisFun_apply]
  have hlin (k : Fin m → A) : e (SymmetricAlgebra.ι A (Fin m → A) k) =
      ∑ j, MvPolynomial.C (k j) * MvPolynomial.X j := by
    calc
      e (SymmetricAlgebra.ι A (Fin m → A) k) =
          e (SymmetricAlgebra.ι A (Fin m → A) (∑ j, b.repr k j • b j)) :=
        congrArg (fun z ↦ e (SymmetricAlgebra.ι A (Fin m → A) z)) (b.sum_repr k).symm
      _ = _ := by
        rw [map_sum, map_sum]
        simp only [map_smul, e, SymmetricAlgebra.equivMvPolynomial_ι_apply]
        simp [b, Algebra.smul_def]
  dsimp only
  rw [heval]
  refine ⟨hφ.comp e.symm.surjective, ?_⟩
  have himage : (fun k : Fin m → A ↦ ∑ j, MvPolynomial.C (k j) * MvPolynomial.X j) ''
      (K : Set _) = e '' (SymmetricAlgebra.ι A (Fin m → A) '' (K : Set _)) := by
    rw [← Set.image_comp]
    congr 1
    funext k
    exact (hlin k).symm
  rw [himage, ← Ideal.map_span, ← hK, ← hker]
  change RingHom.ker f.toRingHom = Ideal.map (e.toRingEquiv : _ →+* _) (RingHom.ker φ.toRingHom)
  rw [Ideal.map_comap_of_equiv e.toRingEquiv]
  exact (RingHom.comap_ker φ.toRingHom e.symm.toAlgHom.toRingHom).symm

/-- The true part of Stacks Tag 07EV.  For an exact sequence `0 → K → A^m → M → 0`
(`K` a submodule of `Fin m → A` equal to `ker π`), the presentation
`α : A[y₁,…,yₘ] → Sym_A(M)`, `yⱼ ↦ ι(π eⱼ)` (Mathlib `Algebra.Generators.ofSurjective`),
is surjective with kernel generated by the linear forms `ℓ(k) = ∑ kⱼ yⱼ`, `k ∈ K`; the
`C`-linear map `λ : C ⊗_A K → J/J²`, `c ⊗ k ↦ c · [ℓ(k)]`, is well defined and surjective;
its composite with the differential `δ` of the naive cotangent complex
(`Algebra.Extension.cotangentComplex`, `J/J² → C ⊗_P Ω_{P/A}`) is
`c ⊗ k ↦ ∑ⱼ c kⱼ (1 ⊗ dyⱼ)` and `im δ = im (δ ∘ λ)`; and `Ω_{C/A} ≅ C ⊗_A M` as
`C`-modules with `d(ι x) ↦ 1 ⊗ x`.  (`K ⊗_A C` of the node is written `C ⊗[A] K`, the
Mathlib form carrying the `C`-module structure.)
(blueprint: lem-weil-pbc-cotangent-complex-symmetric-algebra)

Proof, following Stacks 07EV/00DO: `α` is surjective since `C` is generated by `ι(M)` and
`π` is surjective.  The ideal `(ℓ(K))` is in `J`, and `P/(ℓ(K))` satisfies the universal
property of `Sym_A(M)` (lem-weil-pbc-symmetric-algebra-universal-property), so it is `J`.
Hence `J/J²` is generated as a `C`-module by the classes of `ℓ(k)`, and `k ↦ [ℓ(k)]` is
`A`-linear, giving `λ` by extension of scalars, surjective.  With the basis `dyⱼ`
(lem-weil-pbc-polynomial-ring-kahler-basis), `d ℓ(k) = ∑ kⱼ dyⱼ`, which is the formula;
surjectivity of `λ` gives the equality of images.  Finally `Ω_{C/A} = coker δ`, and the
cokernel of `C ⊗ K → C^m` is `C ⊗_A M` by right exactness of `C ⊗_A −`. -/
theorem cotangentComplex_symmetricAlgebra
    {A : Type u} [CommRing A]
    {M : Type v} [AddCommGroup M] [Module A M]
    {m : ℕ}
    (K : Submodule A (Fin m → A))
    (π : (Fin m → A) →ₗ[A] M)
    (hπ : Function.Surjective π)
    (hK : LinearMap.ker π = K) :
    let a : Fin m → SymmetricAlgebra A M := fun j => SymmetricAlgebra.ι A M (π (Pi.single j 1))
    let ℓ : (Fin m → A) → MvPolynomial (Fin m) A := fun k =>
      ∑ j, MvPolynomial.C (k j) * MvPolynomial.X j
    (∃ hα : Function.Surjective (MvPolynomial.aeval (R := A) a),
      RingHom.ker (MvPolynomial.aeval (R := A) a) = Ideal.span (ℓ '' (K : Set (Fin m → A))) ∧
      let G := Generators.ofSurjective a hα
      ∃ lam : SymmetricAlgebra A M ⊗[A] K →ₗ[SymmetricAlgebra A M] G.toExtension.Cotangent,
        (∀ (c : SymmetricAlgebra A M) (k : K) (x : G.toExtension.ker),
          (x.1 : G.toExtension.Ring) = ℓ k →
            lam (c ⊗ₜ k) = c • Extension.Cotangent.mk x) ∧
        Function.Surjective lam ∧
        (∀ (c : SymmetricAlgebra A M) (k : K),
          G.toExtension.cotangentComplex (lam (c ⊗ₜ k)) =
            ∑ j, (c * algebraMap A (SymmetricAlgebra A M) (k.1 j)) •
              ((1 : SymmetricAlgebra A M) ⊗ₜ[G.toExtension.Ring]
                KaehlerDifferential.D A G.toExtension.Ring (MvPolynomial.X j) :
                G.toExtension.CotangentSpace)) ∧
        LinearMap.range G.toExtension.cotangentComplex =
          LinearMap.range (G.toExtension.cotangentComplex ∘ₗ lam)) ∧
    ∃ e : Ω[SymmetricAlgebra A M⁄A] ≃ₗ[SymmetricAlgebra A M] SymmetricAlgebra A M ⊗[A] M,
      ∀ x : M, e (KaehlerDifferential.D A (SymmetricAlgebra A M) (SymmetricAlgebra.ι A M x)) =
        1 ⊗ₜ x := by
  classical
  dsimp only
  obtain ⟨hα, hker⟩ := symmetricPresentation K π hπ hK
  constructor
  · refine ⟨hα, hker, ?_⟩
    let G := Generators.ofSurjective
      (fun j ↦ SymmetricAlgebra.ι A M (π (Pi.single j 1))) hα
    let ℓ : (Fin m → A) →ₗ[A] MvPolynomial (Fin m) A :=
      (Pi.basisFun A (Fin m)).constr A (fun j ↦ MvPolynomial.X j)
    have hℓ (k : Fin m → A) : ℓ k =
        ∑ j, MvPolynomial.C (k j) * MvPolynomial.X j := by
      simp [ℓ, Algebra.smul_def]
    have hmem (k : K) : ℓ k ∈ G.toExtension.ker := by
      change ℓ k ∈ RingHom.ker (MvPolynomial.aeval (R := A) G.val)
      change ℓ k ∈ RingHom.ker (MvPolynomial.aeval (R := A)
        (fun j ↦ SymmetricAlgebra.ι A M (π (Pi.single j 1))))
      rw [hker, hℓ]
      exact Ideal.subset_span ⟨k, k.2, rfl⟩
    let l : K →ₗ[A] G.toExtension.ker :=
      { toFun := fun k ↦ ⟨ℓ k, hmem k⟩
        map_add' := fun x y ↦ Subtype.ext (ℓ.map_add x y)
        map_smul' := fun r x ↦ Subtype.ext (ℓ.map_smul r x) }
    let q : K →ₗ[A] G.toExtension.Cotangent :=
      ((Extension.Cotangent.mk (P := G.toExtension)).restrictScalars A).comp l
    let lam := q.liftBaseChange (SymmetricAlgebra A M)
    have hlam (c : SymmetricAlgebra A M) (k : K) :
        lam (c ⊗ₜ[A] k) = c • Extension.Cotangent.mk (l k) := by
      simp [lam, q]
    have hsurj : Function.Surjective lam := by
      apply LinearMap.range_eq_top.mp
      change LinearMap.range (q.liftBaseChange (SymmetricAlgebra A M)) = ⊤
      rw [LinearMap.range_liftBaseChange]
      have hs : Ideal.span (Set.range (fun k : K ↦ ℓ k)) = G.toExtension.ker := by
        change Ideal.span (Set.range (fun k : K ↦ ℓ k)) =
          RingHom.ker (MvPolynomial.aeval (R := A)
            (fun j ↦ SymmetricAlgebra.ι A M (π (Pi.single j 1))))
        rw [hker]
        congr 1
        ext z
        constructor
        · rintro ⟨k, rfl⟩
          exact ⟨k, k.2, (hℓ k).symm⟩
        · rintro ⟨k, hk, rfl⟩
          exact ⟨⟨k, hk⟩, hℓ k⟩
      have ht := Extension.Cotangent.span_eq_top_of_span_eq_ker
        (P := G.toExtension) (fun k : K ↦ ℓ k) hs
      convert ht using 1
      congr 1
    refine ⟨lam, ?_, hsurj, ?_, ?_⟩
    · intro c k x hx
      rw [hlam]
      congr 2
      apply Subtype.ext
      exact (hℓ k).trans hx.symm
    · intro c k
      let : Algebra (MvPolynomial (Fin m) A) (SymmetricAlgebra A M) :=
        G.toExtension.algebra₂
      let : IsScalarTower A (MvPolynomial (Fin m) A) (SymmetricAlgebra A M) :=
        G.toExtension.isScalarTower
      rw [hlam, map_smul, Extension.cotangentComplex_mk]
      change c • ((1 : SymmetricAlgebra A M) ⊗ₜ[G.toExtension.Ring]
        KaehlerDifferential.D A G.toExtension.Ring (ℓ k)) = _
      change c • ((1 : SymmetricAlgebra A M) ⊗ₜ[MvPolynomial (Fin m) A]
        KaehlerDifferential.D A (MvPolynomial (Fin m) A) (ℓ k)) =
          ∑ j, (c * algebraMap A (SymmetricAlgebra A M) (k.1 j)) •
            ((1 : SymmetricAlgebra A M) ⊗ₜ[MvPolynomial (Fin m) A]
              KaehlerDifferential.D A (MvPolynomial (Fin m) A) (MvPolynomial.X j))
      rw [hℓ, map_sum, TensorProduct.tmul_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [← MvPolynomial.smul_eq_C_mul, Derivation.map_smul]
      rw [TensorProduct.tmul_smul]
      rw [← IsScalarTower.algebraMap_smul (SymmetricAlgebra A M) (k.1 j), smul_smul]
    · exact (LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hsurj)).symm
  · exact cotangentSymmetricDifferentials A M

end AlgebraicGeometry
