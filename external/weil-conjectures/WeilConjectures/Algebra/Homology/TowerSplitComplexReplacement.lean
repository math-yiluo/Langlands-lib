/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import WeilConjectures.CategoryTheory.TowerSplitEnvelope
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone

/-! # Replacing a tower complex by a complex with split terms

Source: Stacks Project, Derived Categories, Tag 070M, and the split-envelope
extension recorded in lem-weil-derived-limit-roos-complex.
(blueprint: lem-weil-tower-split-complex-replacement).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem tower_split_of_iso
    {A : Type u} [Category.{v} A] [Abelian A]
    {T S : ℕᵒᵖ ⥤ A} (e : T ≅ S) (n : ℕ)
    [IsSplitEpi (S.map (homOfLE (Nat.le_succ n)).op)] :
    IsSplitEpi (T.map (homOfLE (Nat.le_succ n)).op) := by
  refine IsSplitEpi.mk' ⟨e.hom.app (Opposite.op n) ≫
    section_ (S.map (homOfLE (Nat.le_succ n)).op) ≫
    e.inv.app (Opposite.op (n + 1)), ?_⟩
  simp only [Category.assoc]
  rw [← e.inv.naturality (homOfLE (Nat.le_succ n)).op]
  simp only [IsSplitEpi.id_assoc]
  exact congrArg (fun a : T ⟶ T ↦ a.app (Opposite.op n)) e.hom_inv_id

private theorem tower_split_biprod
    {A : Type u} [Category.{v} A] [Abelian A]
    (T S : ℕᵒᵖ ⥤ A) (n : ℕ)
    [IsSplitEpi (T.map (homOfLE (Nat.le_succ n)).op)]
    [IsSplitEpi (S.map (homOfLE (Nat.le_succ n)).op)] :
    IsSplitEpi ((T ⊞ S).map (homOfLE (Nat.le_succ n)).op) := by
  let f := (homOfLE (Nat.le_succ n)).op
  refine IsSplitEpi.mk' ⟨
    (biprod.fst : T ⊞ S ⟶ T).app (Opposite.op n) ≫ section_ (T.map f) ≫
      (biprod.inl : T ⟶ T ⊞ S).app (Opposite.op (n + 1)) +
    (biprod.snd : T ⊞ S ⟶ S).app (Opposite.op n) ≫ section_ (S.map f) ≫
      (biprod.inr : S ⟶ T ⊞ S).app (Opposite.op (n + 1)), ?_⟩
  simp only [Preadditive.add_comp, Category.assoc]
  rw [← (biprod.inl : T ⟶ T ⊞ S).naturality f,
    ← (biprod.inr : S ⟶ T ⊞ S).naturality f]
  simp only [IsSplitEpi.id_assoc]
  exact congrArg (fun a : T ⊞ S ⟶ T ⊞ S ↦ a.app (Opposite.op n)) (biprod.total (X := T) (Y := S))

/-- Every tower complex has a quasi-isomorphic replacement with split transitions.
No K-injectivity assumption or choice of product and limit complexes is involved.

Proof: Apply the additive split-envelope functor E and its natural monomorphism j
termwise. Let q be the cokernel chain map of j. The sequence 0 → I → E(I) → coker(j)
→ 0 is degreewise short exact, and both E(I) and coker(j) have split transitions.
The degreewise-epi kernel/cone comparison applied to q, followed by the canonical
isomorphism I ≅ ker(q), gives u : I → Cone(q)[-1], a quasi-isomorphism. Each term
of this shifted cone is a binary biproduct of two split towers. Biproducts of
sections are sections, so all transitions of this replacement split.

Source: Stacks Project, Derived Categories, Tag 070M; the explicit extension
in lem-weil-derived-limit-roos-complex.
(blueprint: lem-weil-tower-split-complex-replacement). -/
theorem tower_split_complex_replacement
    (A : Type u) [Category.{v} A] [Abelian A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ∃ (J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (u : I ⟶ J),
      QuasiIso u ∧ ∀ (p : ℤ) (n : ℕ),
        IsSplitEpi ((J.X p).map (homOfLE (Nat.le_succ n)).op) := by
  obtain ⟨E, j, e, he, hmap, hj, hsplitE, hmono, hadd, hsplitC⟩ := tower_split_envelope (C := A)
  have : E.Additive := ⟨hadd _ _ _ _⟩
  let EI := (E.mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  let ji : I ⟶ EI :=
    (Functor.mapHomologicalComplexIdIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ)).inv.app I ≫
      (j.mapHomologicalComplex (ComplexShape.up ℤ)).app I
  have hji (p : ℤ) : ji.f p = j.app (I.X p) := by
    change 𝟙 (I.X p) ≫ j.app (I.X p) = j.app (I.X p)
    rw [Category.id_comp]
  have : Mono ji := HomologicalComplex.mono_of_mono_f ji (fun p ↦ by
    rw [hji]
    exact (NatTrans.mono_iff_mono_app _).2 (fun n ↦ by
      obtain ⟨n⟩ := n
      exact hmono (I.X p) n))
  let q := cokernel.π ji
  have hq (p : ℤ) : Epi (q.f p) := by
    change Epi ((HomologicalComplex.eval _ _ p).map q)
    infer_instance
  let _ := HasDerivedCategory.standard (ℕᵒᵖ ⥤ A)
  obtain ⟨κ, hκ, hqκ, _⟩ :=
    CochainComplex.exists_kernel_to_shifted_mappingCone_of_degreewise_epi q hq
  let eK := IsLimit.conePointUniqueUpToIso
    (s := KernelFork.ofι ji (cokernel.condition ji))
    (t := KernelFork.ofι (kernel.ι q) (kernel.condition q))
    (Abelian.monoIsKernelOfCokernel
      (CokernelCofork.ofπ (cokernel.π ji) (cokernel.condition ji))
      (cokernelIsCokernel ji))
    (kernelIsKernel q)
  have : QuasiIso κ := hqκ
  refine ⟨(CochainComplex.mappingCone q)⟦(-1 : ℤ)⟧, eK.hom ≫ κ, inferInstance, ?_⟩
  intro p n
  let ec : ∀ p : ℤ, (cokernel ji).X p ≅ cokernel (j.app (I.X p)) := fun p ↦
    PreservesCokernel.iso (HomologicalComplex.eval _ _ p) ji ≪≫
      cokernelIsoOfEq (hji p)
  have hc (p : ℤ) :
      IsSplitEpi (((cokernel ji).X p).map (homOfLE (Nat.le_succ n)).op) := by
    have := hsplitC (I.X p) n
    exact tower_split_of_iso (ec p) n
  have he (p : ℤ) : IsSplitEpi ((EI.X p).map (homOfLE (Nat.le_succ n)).op) :=
    hsplitE (I.X p) n
  let eJ := ((CochainComplex.mappingCone q).shiftFunctorObjXIso (-1) p (p - 1) (by omega)) ≪≫
    HomologicalComplex.homotopyCofiber.XIsoBiprod q (p - 1) p (by
      change p - 1 + 1 = p
      omega)
  have : IsSplitEpi (((EI.X p) ⊞ (cokernel ji).X (p - 1)).map
      (homOfLE (Nat.le_succ n)).op) := tower_split_biprod _ _ n
  exact tower_split_of_iso eJ n

end CategoryTheory
