/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.Data.Fintype.Order
import WeilConjectures.FieldTheory.SeparableSplitPurelyInseparableResidueFields

/-!
# Splitting the reduction of a finite algebra after a separable extension

Source: blueprint, `sec-smooth-purity/sk-prop-sf-cbc`, proof of
`lem-weil-pbc-finite-pushforward-generic-constructible`; Stacks Project, More on Morphisms,
proof of Tag 02LM (blueprint: lem-weil-pbc-generic-separable-algebra-splitting).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

namespace Algebra

/-- The reduction of a finite-dimensional commutative algebra over a field is a finite product
of finite field extensions.  This is the Artinian nilradical/Chinese-remainder part of the
finite-algebra calculation in the proof of Tag 02LM. -/
private theorem exists_reduction_equiv_pi_of_finite_dimensional
    (K : Type u) [Field K] (C : Type v) [CommRing C] [Algebra K C]
    [FiniteDimensional K C] :
    ∃ (n : ℕ) (E : Fin n → Type v) (hE : ∀ j, Field (E j))
      (aE : ∀ j, Algebra K (E j)),
      let := hE
      let := aE
      (∀ j, Module.Finite K (E j)) ∧
      Nonempty ((C ⧸ nilradical C) ≃ₐ[K] (∀ j, E j)) := by
  classical
  have : IsArtinianRing C := isArtinian_of_tower K (inferInstance : IsArtinian K C)
  let := Fintype.ofFinite (MaximalSpectrum C)
  let e := (Fintype.equivFin (MaximalSpectrum C)).symm
  let E := fun j : Fin (Fintype.card (MaximalSpectrum C)) ↦ C ⧸ (e j).asIdeal
  let hE := fun j ↦ Ideal.Quotient.field (e j).asIdeal
  let := hE
  refine ⟨_, E, hE, (fun j ↦ inferInstance), (fun j ↦ inferInstance), ?_⟩
  exact ⟨((IsArtinianRing.quotNilradicalEquivPi C).restrictScalars K).trans
    (AlgEquiv.piCongrLeft' K (fun I : MaximalSpectrum C ↦ C ⧸ I.asIdeal)
      (Fintype.equivFin (MaximalSpectrum C)))⟩

private theorem reductionEquivOfSurjective
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B)
    (hs : Function.Surjective f) (hk : RingHom.ker f ≤ nilradical A) :
    Nonempty ((A ⧸ nilradical A) ≃ₐ[R] (B ⧸ nilradical B)) := by
  have hmap : nilradical A ≤ (nilradical B).comap f := by
    intro x hx
    exact mem_nilradical.mpr ((mem_nilradical.mp hx).map f)
  have hback : (nilradical B).comap f ≤ nilradical A := by
    intro x hx
    obtain ⟨n, hn⟩ := mem_nilradical.mp hx
    have hxpow : x ^ n ∈ RingHom.ker f := by
      change f (x ^ n) = 0
      rwa [map_pow]
    exact mem_nilradical.mpr (IsNilpotent.of_pow (mem_nilradical.mp (hk hxpow)))
  exact ⟨AlgEquiv.ofBijective (Ideal.quotientMapₐ (nilradical B) f hmap)
    ⟨Ideal.quotientMap_injective' (H := hmap) hback,
      Ideal.quotientMap_surjective (H := hmap) hs⟩⟩

private theorem reductionEquivOfEquiv
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) :
    Nonempty ((A ⧸ nilradical A) ≃ₐ[R] (B ⧸ nilradical B)) := by
  apply reductionEquivOfSurjective R A B e.toAlgHom e.surjective
  intro x hx
  have hx0 : e x = 0 := hx
  have : x = 0 := e.injective (hx0.trans (map_zero e).symm)
  simp [this]

private theorem tensorReductionEquiv
    (K F C : Type*) [Field K] [CommRing F] [Algebra K F]
    [CommRing C] [Algebra K C] :
    Nonempty (((F ⊗[K] C) ⧸ nilradical (F ⊗[K] C)) ≃ₐ[F]
      ((F ⊗[K] (C ⧸ nilradical C)) ⧸ nilradical (F ⊗[K] (C ⧸ nilradical C)))) := by
  let I : Ideal (F ⊗[K] C) :=
    (nilradical C).map (Algebra.TensorProduct.includeRight (R := K) (A := F))
  have hI : I ≤ nilradical (F ⊗[K] C) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    exact mem_nilradical.mpr ((mem_nilradical.mp hx).map
      (Algebra.TensorProduct.includeRight (R := K) (A := F)))
  obtain ⟨e₁⟩ := reductionEquivOfSurjective F (F ⊗[K] C) ((F ⊗[K] C) ⧸ I)
    (Ideal.Quotient.mkₐ F I) Ideal.Quotient.mk_surjective (by
      intro x hx
      exact hI (Ideal.Quotient.eq_zero_iff_mem.mp hx))
  obtain ⟨e₂⟩ := reductionEquivOfEquiv F ((F ⊗[K] C) ⧸ I)
    (F ⊗[K] (C ⧸ nilradical C))
    (Algebra.TensorProduct.tensorQuotientEquiv (R := K) F C F (nilradical C)).symm
  exact ⟨e₁.trans e₂⟩

private theorem piReductionEquiv
    (F : Type*) [CommRing F] (ι : Type*) [Finite ι] (B : ι → Type*)
    [∀ i, CommRing (B i)] [∀ i, Algebra F (B i)] :
    Nonempty (((∀ i, B i) ⧸ nilradical (∀ i, B i)) ≃ₐ[F]
      (∀ i, B i ⧸ nilradical (B i))) := by
  classical
  have : ∀ i, IsReduced (B i ⧸ nilradical (B i)) := fun i ↦
    (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
  let f := AlgHom.pi (fun i ↦
    (Ideal.Quotient.mkₐ F (nilradical (B i))).comp (Pi.evalAlgHom F B i))
  have hs : Function.Surjective f := by
    intro x
    choose y hy using (fun i ↦ Ideal.Quotient.mk_surjective (x i))
    exact ⟨y, funext hy⟩
  have hk : RingHom.ker f = nilradical (∀ i, B i) := by
    apply le_antisymm
    · intro x hx
      have hxnil : ∀ i, IsNilpotent (x i) := by
        intro i
        apply mem_nilradical.mp
        exact Ideal.Quotient.eq_zero_iff_mem.mp (congrFun hx i)
      choose n hn using hxnil
      obtain ⟨N, hN⟩ := Finite.exists_le n
      apply mem_nilradical.mpr
      refine ⟨N, funext (fun i ↦ ?_)⟩
      exact pow_eq_zero_of_le (hN i) (hn i)
    · intro x hx
      exact (mem_nilradical.mp hx).map f |>.eq_zero
  exact ⟨(Ideal.quotientEquivAlgOfEq F hk.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hs)⟩

/-- Given the Artinian product decomposition and a separable extension splitting all its field
factors, the tensor-product reduction is the corresponding product of purely inseparable fields.
This is the tensor/base-change and reassembly part of the finite-algebra calculation in Tag 02LM. -/
private theorem exists_tensor_reduction_equiv_pi_of_reduction_equiv_pi
    (K : Type u) [Field K] (C : Type v) [CommRing C] [Algebra K C]
    [FiniteDimensional K C] (n : ℕ) (E : Fin n → Type v)
    (hE : ∀ j, Field (E j)) (aE : ∀ j, Algebra K (E j))
    (K' : Type (max u v)) (hK' : Field K') (aK' : Algebra K K')
    (hEfin : ∀ j, Module.Finite K (E j))
    (hred : Nonempty ((C ⧸ nilradical C) ≃ₐ[K] (∀ j, E j)))
    (hprime : ∀ j, Finite (PrimeSpectrum (K' ⊗[K] E j)) ∧
      ∀ p : Ideal (K' ⊗[K] E j), p.IsPrime →
        IsField ((K' ⊗[K] E j) ⧸ p) ∧
          Module.Finite K' ((K' ⊗[K] E j) ⧸ p) ∧
          IsPurelyInseparable K' ((K' ⊗[K] E j) ⧸ p)) :
    let := hK'
    let := aK'
    let := Algebra.TensorProduct.rightAlgebra (R := K) (A := C) (B := K')
    ∃ (m : ℕ) (L : Fin m → Type (max u v))
      (hL : ∀ i, Field (L i)) (aL : ∀ i, Algebra K' (L i)),
      let := hL
      let := aL
      (∀ i, FiniteDimensional K' (L i) ∧ IsPurelyInseparable K' (L i)) ∧
        Nonempty (((C ⊗[K] K') ⧸ nilradical (C ⊗[K] K')) ≃ₐ[K'] (∀ i, L i)) := by
  classical
  let : Algebra K' (C ⊗[K] K') :=
    Algebra.TensorProduct.rightAlgebra (R := K) (A := C) (B := K')
  let := hEfin
  obtain ⟨ered⟩ := hred
  let swap : (C ⊗[K] K') ≃ₐ[K'] (K' ⊗[K] C) :=
    { __ := (Algebra.TensorProduct.comm K C K').toRingEquiv
      commutes' _ := rfl }
  obtain ⟨e₁⟩ := reductionEquivOfEquiv K' _ _ swap
  obtain ⟨e₂⟩ := tensorReductionEquiv K K' C
  let eprod := (Algebra.TensorProduct.congr (AlgEquiv.refl : K' ≃ₐ[K'] K') ered).trans
    (Algebra.TensorProduct.piRight K K' K' E)
  obtain ⟨e₃⟩ := reductionEquivOfEquiv K' _ _ eprod
  obtain ⟨e₄⟩ := piReductionEquiv K' (Fin n) (fun j ↦ K' ⊗[K] E j)
  have hart : ∀ j, IsArtinianRing (K' ⊗[K] E j) := fun j ↦
    isArtinian_of_tower K' (inferInstance : IsArtinian K' (K' ⊗[K] E j))
  let I := (j : Fin n) × MaximalSpectrum (K' ⊗[K] E j)
  let Q := fun x : I ↦ (K' ⊗[K] E x.1) ⧸ x.2.asIdeal
  let hQ : ∀ x : I, Field (Q x) := fun x ↦ Ideal.Quotient.field x.2.asIdeal
  let := hQ
  let ec : (∀ j, (K' ⊗[K] E j) ⧸ nilradical (K' ⊗[K] E j)) ≃ₐ[K']
      (∀ x : I, Q x) :=
    (AlgEquiv.piCongrRight (fun j ↦
      (IsArtinianRing.quotNilradicalEquivPi (K' ⊗[K] E j)).restrictScalars K')).trans
      { toFun := fun f x ↦ f x.1 x.2
        invFun := fun f j p ↦ f ⟨j, p⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_mul' := fun _ _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        commutes' := fun _ ↦ rfl }
  let := Fintype.ofFinite I
  let ef := Fintype.equivFin I
  let L := fun j : Fin (Fintype.card I) ↦ Q (ef.symm j)
  let hL := fun j ↦ hQ (ef.symm j)
  refine ⟨Fintype.card I, L, hL, (fun _ ↦ inferInstance), ?_, ?_⟩
  · intro j
    exact (hprime (ef.symm j).1).2 _ (ef.symm j).2.isMaximal.isPrime |>.2
  · exact ⟨e₁.trans (e₂.trans (e₃.trans (e₄.trans (ec.trans
      (AlgEquiv.piCongrLeft' K' Q ef)))))⟩

/-- The reduction of a finite-dimensional commutative algebra over a field becomes a finite
product of finite purely inseparable fields after a finite separable extension.
Source: blueprint, proof of `lem-weil-pbc-finite-pushforward-generic-constructible`, generic
finite-algebra calculation; Stacks Project, proof of Tag 02LM.
(blueprint: lem-weil-pbc-generic-separable-algebra-splitting)

Proof:
1. By `lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum`, applied over the field K,
   C has finitely many prime ideals, all maximal, with intersection its nilradical N.
   The Chinese remainder theorem (`lem-pc-crt-ideal-quotient-product`) identifies C/N with
   the product of the finite residue fields E_i. For C = 0 the product is empty.
   N is nilpotent. Its image after tensoring with K' is nilpotent too; right exactness of
   tensor product identifies the quotient by that image with (C/N) tensor K'. Thus reducing
   C tensor K' gives the product of the reductions of E_i tensor K'.
2. Apply `lem-weil-pbc-separable-split-purely-inseparable-residue-fields` to the finite family
   E_i/K. It supplies a finite separable extension K'/K such that every prime of
   K' tensor E_i has a residue field finite purely inseparable over K'. Swap tensor factors
   to use the right-factor K'-algebra structure in the statement.
3. Apply `lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum` over K' to each tensor
   factor. Its finitely many primes are maximal and intersect in the nilradical. Apply
   `lem-pc-crt-ideal-quotient-product` to identify its reduction with their residue fields.
   By step 2 each of those fields is finite purely inseparable over K'.
4. Assemble these finite products over i to obtain the asserted K'-algebra isomorphism.
   The extension K'/K retains the finiteness and separability supplied in step 2.
-/
theorem exists_separable_extension_reduction_tensorProduct_equiv_pi
    (K : Type u) [Field K] (C : Type v) [CommRing C] [Algebra K C]
    [FiniteDimensional K C] :
    ∃ (K' : Type (max u v)) (hK' : Field K') (aK' : Algebra K K'),
      letI := hK'
      letI := aK'
      FiniteDimensional K K' ∧ Algebra.IsSeparable K K' ∧
        ∃ (n : ℕ) (L : Fin n → Type (max u v))
          (hL : ∀ j, Field (L j)) (aL : ∀ j, Algebra K' (L j)),
          letI := hL
          letI := aL
          letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := C) (B := K')
          (∀ j, FiniteDimensional K' (L j) ∧ IsPurelyInseparable K' (L j)) ∧
            Nonempty (((C ⊗[K] K') ⧸ nilradical (C ⊗[K] K')) ≃ₐ[K'] (∀ j, L j)) := by
  obtain ⟨n, E, hE, aE, hEfin, hred⟩ :=
    exists_reduction_equiv_pi_of_finite_dimensional K C
  let := hE
  let := aE
  have := hEfin
  obtain ⟨K', hK', aK', hfin, hsep, hgal, hemb, hprime⟩ :=
    exists_separable_split_purelyInseparable_prime_quotients K n E
  let := hK'
  let := aK'
  obtain ⟨m, L, hL, aL, hfinite, hequiv⟩ :=
    exists_tensor_reduction_equiv_pi_of_reduction_equiv_pi K C n E hE aE K' hK' aK'
      hEfin hred hprime
  exact ⟨K', hK', aK', hfin, hsep, m, L, hL, aL, hfinite, hequiv⟩

end Algebra
