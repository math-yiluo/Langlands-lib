/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Ideal.Operations
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAnnihilatedLimit
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAnnihilatedFormalCover
import Mathlib.Tactic.TFAE
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAnnihilatedDoubleKernel
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAnnihilatedDoubleCokernel
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAbelian
import WeilConjectures.RingTheory.KernelCokernelAnnihilatedModIdeal

/-! # Annihilation of kernels and cokernels of coherent formal module maps

Source: Stacks Project, Cohomology of Schemes, Remark 0888; Lemmas 087W and 087X
(blueprint: lem-weil-pbc-formal-systems-annihilated-by-power).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The four annihilation conditions are equivalent. The affine map is the limit of
section maps, regarded as linear over Γ(U, O_X); Lemma 087W identifies this with the
underlying map of finite modules over the completion. `op n` denotes level `n+1`.
Kernel forks and cokernel coforks express condition (4) without choosing an abelian
structure or particular representatives of the kernel and cokernel.
Source: Stacks, Remark 0888 and Lemmas 087W, 087X
(blueprint: lem-weil-pbc-formal-systems-annihilated-by-power).
Proof:
1. The fixed-exponent affine-limit lemma gives (1) implies (2), with exponent 2t.
2. Quasi-compactness gives a finite affine subcover. The maximum of its finitely many
   exponents, bounded below by 1, proves (2) implies (3), including the empty scheme.
3. The existing double-exponent kernel and cokernel lemmas give (3) implies (1).
4. Abelianness supplies canonical formal kernel and cokernel forks. The fixed-exponent
   formal-cover criterion on the finite cover gives (3) implies (4).
5. Apply that criterion on the cover of all affine opens to give (4) implies (2).
These five implications assemble the TFAE. The two geometric criteria remain named
open theorems in their own modules; this is a decomposition of the equivalence.
-/
theorem coherentFormalModule_annihilated_iff (X : Scheme.{u}) [IsNoetherian X]
    (I K : X.IdealSheafData) (F G : CoherentFormalModule X I) (α : F ⟶ G) :
    List.TFAE
      [(∃ t : ℕ, 1 ≤ t ∧ ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (kernel (α.hom.app (op n)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (cokernel (α.hom.app (op n))))),
       (∀ U : X.affineOpens, ∃ t : ℕ, 1 ≤ t ∧
      K.ideal U ^ t ≤ Module.annihilator Γ(X, U.1) (LinearMap.ker
        (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op U.1)))).hom) ∧
      K.ideal U ^ t ≤ Module.annihilator Γ(X, U.1)
        (↥(limit (G.obj ⋙
          SheafOfModules.evaluation X.ringCatSheaf (op U.1)) :
          ModuleCat Γ(X, U.1)) ⧸ LinearMap.range
          (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op U.1)))).hom)),
       (∃ (r : ℕ) (U : Fin r → X.affineOpens) (t : ℕ),
      (⨆ i, (U i).1) = ⊤ ∧ 1 ≤ t ∧ ∀ i : Fin r,
      K.ideal (U i) ^ t ≤ Module.annihilator Γ(X, (U i).1) (LinearMap.ker
        (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op (U i).1)))).hom) ∧
      K.ideal (U i) ^ t ≤ Module.annihilator Γ(X, (U i).1)
        (↥(limit (G.obj ⋙
          SheafOfModules.evaluation X.ringCatSheaf (op (U i).1)) :
          ModuleCat Γ(X, (U i).1)) ⧸ LinearMap.range
          (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op (U i).1)))).hom)),
       (∃ (k : KernelFork α) (c : CokernelCofork α),
      Nonempty (IsLimit k) ∧ Nonempty (IsColimit c) ∧
      ∃ t : ℕ, 1 ≤ t ∧ ∀ n : ℕ,
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
          (k.pt.obj.obj (op n))) ∧
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
          (c.pt.obj.obj (op n))))] := by
  classical
  tfae_have 1 → 2 := by
    rintro ⟨t, ht, h⟩ U
    refine ⟨2 * t, by omega, ?_⟩
    exact coherentFormalModule_annihilated_affine_limit X I K F G α t ht h U
  tfae_have 2 → 3 := by
    intro h
    obtain ⟨s, hs, hcover⟩ :=
      (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : X.Opens))).mp
        (by simpa using (isCompact_univ (X := X)))
    let S := hs.toFinset
    let e := S.equivFin
    let U : Fin S.card → X.affineOpens := fun i ↦ (e.symm i).1
    choose t ht hkill using h
    let b := max 1 (S.sup t)
    refine ⟨S.card, U, b, ?_, le_max_left _ _, ?_⟩
    · apply le_antisymm le_top
      rw [hcover]
      refine iSup_le fun V ↦ iSup_le fun hV ↦ ?_
      have hVS : V ∈ S := hs.mem_toFinset.mpr hV
      exact le_iSup_of_le (e ⟨V, hVS⟩) (by simp [U])
    · intro i
      have hle : t (U i) ≤ b :=
        (Finset.le_sup (e.symm i).2).trans (le_max_right _ _)
      exact ⟨(Ideal.pow_le_pow_right hle).trans (hkill (U i)).1,
        (Ideal.pow_le_pow_right hle).trans (hkill (U i)).2⟩
  tfae_have 3 → 1 := by
    rintro ⟨r, U, t, hcover, ht, h⟩
    refine ⟨2 * t, by omega, ?_⟩
    intro n
    exact ⟨coherentFormalModule_annihilated_double_kernel X I K F G α r U t hcover ht h n,
      coherentFormalModule_annihilated_double_cokernel X I K F G α r U t hcover ht h n⟩
  tfae_have 3 → 4 := by
    rintro ⟨r, U, t, hcover, ht, h⟩
    have : Abelian (CoherentFormalModule X I) :=
      (coherentFormalModule_abelian X I).1.some
    let k := KernelFork.ofι (kernel.ι α) (kernel.condition α)
    let c := CokernelCofork.ofπ (cokernel.π α) (cokernel.condition α)
    refine ⟨k, c, ⟨kernelIsKernel α⟩, ⟨cokernelIsCokernel α⟩, t, ht, ?_⟩
    exact (coherentFormalModule_annihilated_formal_cover X I K F G α k c
      (kernelIsKernel α) (cokernelIsCokernel α) (Fin r) U hcover t ht).mpr h
  tfae_have 4 → 2 := by
    rintro ⟨k, c, ⟨hk⟩, ⟨hc⟩, t, ht, h⟩ U
    refine ⟨t, ht, ?_⟩
    exact (coherentFormalModule_annihilated_formal_cover X I K F G α k c hk hc
      X.affineOpens id (iSup_affineOpens_eq_top X) t ht).mp h U
  tfae_finish

/-- The exponent t on a finite affine cover gives exponent 2t for every component.
Source: Stacks, Remark 0888 (blueprint: lem-weil-pbc-formal-systems-annihilated-by-power).
Proof: pair the existing double-exponent kernel and cokernel conclusions at each level
(node step 3). Those lemmas apply reduction modulo the adic ideal powers on affines
and glue the resulting ideal-product vanishing over the cover.
-/
theorem coherentFormalModule_annihilated_double (X : Scheme.{u}) [IsNoetherian X]
    (I K : X.IdealSheafData) (F G : CoherentFormalModule X I) (α : F ⟶ G)
    (r : ℕ) (U : Fin r → X.affineOpens) (t : ℕ)
    (hcover : (⨆ i, (U i).1) = ⊤) (ht : 1 ≤ t)
    (h : ∀ i : Fin r,
      K.ideal (U i) ^ t ≤ Module.annihilator Γ(X, (U i).1) (LinearMap.ker
        (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op (U i).1)))).hom) ∧
      K.ideal (U i) ^ t ≤ Module.annihilator Γ(X, (U i).1)
        (↥(limit (G.obj ⋙
          SheafOfModules.evaluation X.ringCatSheaf (op (U i).1)) :
          ModuleCat Γ(X, (U i).1)) ⧸ LinearMap.range
          (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op (U i).1)))).hom)) :
    ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (2 * t)).2
        (kernel (α.hom.app (op n)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (2 * t)).2
        (cokernel (α.hom.app (op n)))) := by
  intro n
  exact ⟨coherentFormalModule_annihilated_double_kernel X I K F G α r U t hcover ht h n,
    coherentFormalModule_annihilated_double_cokernel X I K F G α r U t hcover ht h n⟩


end AlgebraicGeometry

namespace LinearMap

/-- The commutative algebra fact underlying the four-way equivalence: reduce modulo
any ideal J. The kernel/cokernel hypothesis is the intrinsic form of the exact sequence
0 → T → M → N → Q → 0, which identifies T with ker u and Q with N/range u.
Source: Stacks, Remark 0888 (blueprint: lem-weil-pbc-formal-systems-annihilated-by-power).
Proof (node step 3): for f,g in K^t, lift fy to x and set h(y)=gx. The kernel
hypothesis makes this independent of x, and linearity gives a linear map. The two
composites with u are multiplication by fg. Reduce these identities modulo J; every
product fg kills the reduced kernel and cokernel. Such products generate K^(2t).
-/
theorem ker_coker_reduction_annihilated_double
    {A : Type u} [CommRing A] {M : Type v} {N : Type w}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (K J : Ideal A) (t : ℕ) (ht : 1 ≤ t) (u : M →ₗ[A] N)
    (hker : K ^ t ≤ Module.annihilator A (ker u))
    (hcoker : K ^ t ≤ Module.annihilator A (N ⧸ range u)) :
    K ^ (2 * t) ≤ Module.annihilator A
      (ker ((J • ⊤ : Submodule A M).mapQ (J • ⊤ : Submodule A N) u
        (Submodule.smul_top_le_comap_smul_top J u))) ∧
    K ^ (2 * t) ≤ Module.annihilator A
      ((N ⧸ (J • ⊤ : Submodule A N)) ⧸
        range ((J • ⊤ : Submodule A M).mapQ (J • ⊤ : Submodule A N) u
          (Submodule.smul_top_le_comap_smul_top J u))) := by
  exact (ker_coker_annihilated_mod_ideal.{u, v, w, v, w, v, w} K t ht u hker hcoker).2.1 J


end LinearMap
