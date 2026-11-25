/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

import Mathlib.Algebra.Homology.Embedding.HomEquiv

/-!
# Assembling an ascending cokernel and pushout system

Source: Stacks Project, Tag 05T6(1), the ascending recursion dual to Tag 05T7(1).
(blueprint: lem-weil-pbc-subcategory-right-resolution-assembly).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject

namespace CochainComplex

/-- Assemble a supplied sequence of terms, cokernels, augmentation components and local
pushout factorizations into an integer-indexed complex. This is only the assembly step:
the sequence, all its monomorphisms, and its pushouts are inputs; no quasi-isomorphism
is asserted. Source: Stacks Project, Tag 05T6(1), the recursion in the dual of Tag 05T7(1).
(blueprint: lem-weil-pbc-subcategory-right-resolution-assembly).

Proof: Put `I.X (a + m) = X m` for `m : ℕ`, and put the chosen zero object in every
smaller degree. Use the supplied `d m` as the differential in degree `a + m`; all other
differentials are zero. Successive differentials compose to zero because `d m` factors
through `p m` and `d (m - 1) ≫ p m = 0`; at the lower boundary the first map is zero.
Set the augmentation equal to `α m` in degree `a + m`, and zero below `a`. The identity
`K.pOpcycles ≫ β = α ≫ p` followed by the pushout identity proves commutation in each
nonzero degree. Below `a`, commutation holds since the source term of `K` is zero.
The initial `p 0` is an isomorphism, so it is a cokernel of the zero incoming differential.
For later degrees, `hcoker` identifies `Q m` with the opcycles of `I`. Under these
canonical identifications the induced map on opcycles is `β m`, by its characterization
after precomposition with the epimorphism `K.pOpcycles`. Thus it is mono. Transport the
supplied pushout squares along these identifications; the induced map out of opcycles
is `v ≫ j` by the differential factorization and cancellation of `p m`. In degree
`a - 1`, the opcycles on both sides are zero: take pushout object `K.X a`, maps the
identity and zero, and embedding `α 0`. In smaller degrees take the zero pushout.
Every augmentation component is mono, either by `hmono` or because its source is zero.
Membership follows from `hmem` and `hzero`; the lower bound follows from the construction.
-/
theorem exists_complex_of_cokernel_pushout_system
    (C : Type u) [Category.{v} C] [Abelian C]
    (𝓘 : Set C) (hzero : (0 : C) ∈ 𝓘)
    (a : ℤ) (K : CochainComplex C ℤ)
    (hK : ∀ n : ℤ, n < a → IsZero (K.X n))
    (X Q : ℕ → C) (p : ∀ m : ℕ, X m ⟶ Q m)
    (α : ∀ m : ℕ, K.X (a + m) ⟶ X m)
    (β : ∀ m : ℕ, K.opcycles (a + m) ⟶ Q m)
    (hmem : ∀ m : ℕ, X m ∈ 𝓘) (hepi : ∀ m : ℕ, Epi (p m))
    (hmono : ∀ m : ℕ, Mono (α m)) (hβ : ∀ m : ℕ, Mono (β m))
    (hcomm : ∀ m : ℕ, K.pOpcycles (a + m) ≫ β m = α m ≫ p m)
    (hinit : IsIso (p 0))
    (d : ∀ m : ℕ, X m ⟶ X (m + 1))
    (hzero_d : ∀ m : ℕ, d m ≫ p (m + 1) = 0)
    (hcoker : ∀ m : ℕ, IsColimit (CokernelCofork.ofπ (p (m + 1)) (hzero_d m)))
    (hsq : ∀ m : ℕ, ∃ (P : C) (u : K.X (a + (m + 1 : ℕ)) ⟶ P) (v : Q m ⟶ P)
      (j : P ⟶ X (m + 1)), Mono j ∧
      IsPushout (K.fromOpcycles (a + m) (a + (m + 1 : ℕ))) (β m) u v ∧
      u ≫ j = α (m + 1) ∧ p m ≫ v ≫ j = d m) :
    ∃ (I : CochainComplex C ℤ) (ι : K ⟶ I),
      (∀ n : ℤ, Mono (ι.f n)) ∧ (∀ n : ℤ, I.X n ∈ 𝓘) ∧
      (∀ n : ℤ, n < a → IsZero (I.X n)) ∧
      (∀ n : ℤ, Mono (opcyclesMap ι n)) ∧
      (∀ n : ℤ, ∃ (P : C) (u : K.X (n + 1) ⟶ P) (v : I.opcycles n ⟶ P)
        (j : P ⟶ I.X (n + 1)), Mono j ∧
        IsPushout (K.fromOpcycles n (n + 1)) (opcyclesMap ι n) u v ∧
        u ≫ j = ι.f (n + 1) ∧ v ≫ j = I.fromOpcycles n (n + 1)) := by
  classical
  have hd : ∀ m, d m ≫ d (m + 1) = 0 := by
    intro m
    obtain ⟨P, u, v, j, _, _, _, hj⟩ := hsq (m + 1)
    rw [← hj, ← Category.assoc, hzero_d, zero_comp]
  have hα : ∀ m, α m ≫ d m =
      K.d (a + m) (a + (m + 1 : ℕ)) ≫ α (m + 1) := by
    intro m
    obtain ⟨P, u, v, j, _, hpo, hu, hv⟩ := hsq m
    rw [← hv, ← Category.assoc, ← hcomm, Category.assoc, ← hpo.w_assoc, hu,
      p_fromOpcycles_assoc]
  let L : CochainComplex C ℕ := CochainComplex.of X d hd
  let e := ComplexShape.embeddingUpIntGE a
  let ψ : K.restriction e ⟶ L :=
    CochainComplex.ofHom α (fun m ↦ by
      change α m ≫ CochainComplex.of.d X d m (m + 1) = _
      rw [CochainComplex.of_d]
      exact hα m)
  have hψ : e.HasLift ψ := by
    intro m hm n hn
    have hm0 : m = 0 :=
      (ComplexShape.boundaryGE_embeddingUpIntGE_iff a m).mp hm
    subst m
    have hn' : n < a := by
      have : n + 1 = a := by simpa [e, ComplexShape.up_Rel] using hn
      omega
    exact (hK n hn').eq_of_src _ _
  let I := L.extend e
  let ι : K ⟶ I := e.liftExtend ψ hψ
  have he (m : ℕ) : e.f m = a + m := rfl
  let E : ∀ m : ℕ, I.X (a + m) ≅ X m := fun m ↦ L.extendXIso e (he m)
  have hf (m : ℕ) : ι.f (a + m) ≫ (E m).hom = α m := by
    dsimp [ι, E]
    rw [e.liftExtend_f ψ hψ (he m)]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact Category.id_comp _
  have hI : ∀ n, n < a → IsZero (I.X n) := by
    intro n hn
    exact L.isZero_extend_X e n
      ((ComplexShape.notMem_range_embeddingUpIntGE_iff a n).mpr hn)
  have hι : ∀ n, Mono (ι.f n) := by
    intro n
    by_cases hn : n < a
    · exact (hK n hn).mono _
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = a + m := by
        refine ⟨(n - a).toNat, ?_⟩
        omega
      have := hmono m
      exact mono_of_mono_fac (hf m)
  have h𝓘 : ∀ n, I.X n ∈ 𝓘 := by
    intro n
    obtain hn | ⟨m, hm⟩ := (e.r n).eq_none_or_eq_some
    · change HomologicalComplex.extend.X L (e.r n) ∈ 𝓘
      rw [hn]
      exact hzero
    · change HomologicalComplex.extend.X L (e.r n) ∈ 𝓘
      rw [hm]
      exact hmem m
  have hdI (m : ℕ) : I.d (a + m) (a + (m + 1 : ℕ)) =
      (E m).hom ≫ d m ≫ (E (m + 1)).inv := by
    exact (L.extend_d_eq e (he m) (he (m + 1))).trans (by simp [L, E])
  have hF : ∀ m : ℕ, ∃ F : I.opcycles (a + m) ≅ Q m,
      I.pOpcycles (a + m) ≫ F.hom = (E m).hom ≫ p m := by
    intro m
    let n := a + (m : ℤ)
    let q : I.X n ⟶ Q m := (E m).hom ≫ p m
    have : Epi q := by
      have := hepi m
      dsimp [q]
      infer_instance
    have hq : I.d (n - 1) n ≫ q = 0 := by
      cases m with
      | zero =>
        have hz : IsZero (I.X (n - 1)) := hI _ (by dsimp [n]; omega)
        exact hz.eq_of_src _ _
      | succ m =>
        have hn : n - 1 = a + m := by dsimp [n]; omega
        dsimp [q]
        rw [hn, hdI m]
        simp [hzero_d, Category.assoc]
    have hcol : IsColimit (CokernelCofork.ofπ q hq) := by
      cases m with
      | zero =>
        have := hinit
        have : IsIso q := by dsimp [q]; infer_instance
        exact CokernelCofork.IsColimit.ofπ q hq
          (fun k _ ↦ inv q ≫ k) (fun k _ ↦ by simp)
          (fun k _ l hl ↦ by rw [← hl]; simp)
      | succ m =>
        have hn : n - 1 = a + m := by dsimp [n]; omega
        exact CokernelCofork.isColimitOfIsColimitOfIff (hcoker m)
          (I.d (n - 1) n) (E (m + 1)) (by
            intro W k
            rw [hn, hdI m]
            simp only [Category.assoc, Iso.inv_hom_id_assoc]
            exact ⟨fun h ↦ by rw [h, comp_zero], fun h ↦ by
              simpa only [← Category.assoc, ← cancel_epi (E m).hom,
                comp_zero] using h⟩)
    have hn : (ComplexShape.up ℤ).prev n = n - 1 := by simp
    let hcan := I.opcyclesIsCokernel (n - 1) n hn
    refine ⟨hcan.coconePointUniqueUpToIso hcol, ?_⟩
    exact hcan.comp_coconePointUniqueUpToIso_hom hcol WalkingParallelPair.one
  choose F hFp using hF
  have hmap (m : ℕ) : opcyclesMap ι (a + m) ≫ (F m).hom = β m := by
    rw [← cancel_epi (K.pOpcycles (a + m))]
    calc
      K.pOpcycles (a + m) ≫ (opcyclesMap ι (a + m) ≫ (F m).hom) =
          ι.f (a + m) ≫ (I.pOpcycles (a + m) ≫ (F m).hom) := by
            rw [← Category.assoc, p_opcyclesMap, Category.assoc]
      _ = ι.f (a + m) ≫ ((E m).hom ≫ p m) := by rw [hFp]
      _ = α m ≫ p m := by rw [← Category.assoc, hf]
      _ = K.pOpcycles (a + m) ≫ β m := (hcomm m).symm
  have hKIzero (n : ℤ) (hn : n < a) :
      IsZero (K.opcycles n) ∧ IsZero (I.opcycles n) :=
    ⟨IsZero.of_epi (K.pOpcycles n) (hK n hn),
      IsZero.of_epi (I.pOpcycles n) (hI n hn)⟩
  have hpos (m : ℕ) :
      ∃ (P : C) (u : K.X (a + (m + 1 : ℕ)) ⟶ P)
        (v : I.opcycles (a + m) ⟶ P) (j : P ⟶ I.X (a + (m + 1 : ℕ))),
        Mono j ∧ IsPushout
          (K.fromOpcycles (a + m) (a + (m + 1 : ℕ))) (opcyclesMap ι (a + m)) u v ∧
        u ≫ j = ι.f (a + (m + 1 : ℕ)) ∧
        v ≫ j = I.fromOpcycles (a + m) (a + (m + 1 : ℕ)) := by
    obtain ⟨P, u, v, j, hj, hpo, hu, hv⟩ := hsq m
    have := hj
    refine ⟨P, u, (F m).hom ≫ v, j ≫ (E (m + 1)).inv, inferInstance, ?_, ?_, ?_⟩
    · exact hpo.of_iso' (Iso.refl _) (Iso.refl _) (F m) (Iso.refl _)
        (by simp) (by simpa using (hmap m).symm) (by simp) (by simp)
    · rw [← Category.assoc, hu]
      rw [← hf, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · rw [← cancel_epi (I.pOpcycles (a + m))]
      simp only [Category.assoc, p_fromOpcycles]
      rw [← Category.assoc, hFp]
      simp only [Category.assoc]
      rw [hdI]
      simpa only [Category.assoc] using
        congrArg (fun k ↦ (E m).hom ≫ k ≫ (E (m + 1)).inv) hv
  refine ⟨I, ι, hι, h𝓘, hI, ?_, ?_⟩
  · intro n
    by_cases hn : n < a
    · exact ((hKIzero n hn).1).mono _
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = a + m := by
        refine ⟨(n - a).toNat, ?_⟩
        omega
      have := hβ m
      exact mono_of_mono_fac (hmap m)
  · intro n
    by_cases hn : n < a
    · have hKz := (hKIzero n hn).1
      have hIz := (hKIzero n hn).2
      have : Epi (opcyclesMap ι n) := hIz.epi _
      have := hι (n + 1)
      refine ⟨K.X (n + 1), 𝟙 _, 0, ι.f (n + 1), inferInstance, ?_, by simp, ?_⟩
      · apply IsPushout.of_vert_isIso_epi
        exact ⟨hKz.eq_of_src _ _⟩
      · rw [zero_comp]
        exact hIz.eq_of_src _ _
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = a + m := by
        refine ⟨(n - a).toNat, ?_⟩
        omega
      have hm : a + (m : ℤ) + 1 = a + (m + 1 : ℕ) := by omega
      rw [hm]
      exact hpos m

end CochainComplex
