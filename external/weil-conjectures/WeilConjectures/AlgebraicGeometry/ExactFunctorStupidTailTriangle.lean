/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! # The kernel triangle of an exact restricted stupid tail

Source: Stacks Project, Tag 08EG, stupid truncation step, and Tag 0152.
(blueprint: lem-sc-exact-functor-stupid-tail-triangle).
-/

@[expose] public section

set_option autoImplicit false

universe u₁ v₁ u₂ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

private noncomputable def stupidTailι
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    (K : CochainComplex C ℤ) (r : ℤ) :
    K.stupidTrunc (ComplexShape.embeddingUpIntGE r) ⟶ K := by
  classical
  let e := ComplexShape.embeddingUpIntGE r
  have he (i : ℤ) (hi : r ≤ i) : e.f (i - r).toNat = i := by
    change r + ((i - r).toNat : ℤ) = i
    omega
  refine { f := fun i ↦ if hi : r ≤ i then (K.stupidTruncXIso e (he i hi)).hom else 0
           comm' := ?_ }
  intro i j hij
  have hij' : i + 1 = j := hij
  by_cases hi : r ≤ i
  · have hj : r ≤ j := by omega
    simp only [dite_eq_left hi, dite_eq_left hj]
    dsimp only [HomologicalComplex.stupidTrunc]
    rw [HomologicalComplex.extend_d_eq _ e (he i hi) (he j hj)]
    rw [HomologicalComplex.restriction_d_eq K e (he i hi) (he j hj)]
    simp [HomologicalComplex.stupidTruncXIso, HomologicalComplex.restrictionXIso,
      e, Category.assoc]
  · have hz : IsZero ((K.stupidTrunc e).X i) :=
      K.isZero_stupidTrunc_X e i
        ((ComplexShape.notMem_range_embeddingUpIntGE_iff r i).mpr (by omega))
    exact hz.eq_of_src _ _

private theorem stupidTailι_isIso_f
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    (K : CochainComplex C ℤ) (r i : ℤ) (hi : r ≤ i) :
    IsIso ((stupidTailι K r).f i) := by
  classical
  dsimp only [stupidTailι]
  simp only [dite_eq_left hi]
  infer_instance

/-- If the image complex is exact through r, its stupid tail fits into the triangle
whose first term is the outgoing kernel placed in degree r. This is solely a
homological-algebra statement: no finiteness, boundedness or perfectness is assumed.
Source: Stacks Project, Tag 08EG, stupid truncations; Tag 0152, SES triangle.
(blueprint: lem-sc-exact-functor-stupid-tail-triangle).

Proof: Map the inclusion of K's stupid tail into K termwise by R, giving j : S → L.
The complex S is strictly zero below r and j is an isomorphism in each degree ≥ r.
The canonical truncation sequence S.truncLE r → S → B is short exact, so its derived
triangle is distinguished. The first complex is concentrated in degree r, where
its term is cycles(S,r); its kernel universal property and the isomorphisms j^r
and j^(r+1) identify this term with ker(L.d r (r+1)). The quotient B maps by a
quasi-isomorphism to S.truncGE(r+1). The map induced by j from this truncation to
L.truncGE(r+1) is a quasi-isomorphism since all three adjacent components computing
homology above r are isomorphisms. Exactness of L through r makes its projection
to L.truncGE(r+1) a quasi-isomorphism as well. Thus B represents L. Transport the
SES triangle along these identifications and the derived restriction comparisons.
This construction has the single kernel in degree r directly and needs no choice
of a splitting. Zero kernels and zero complexes require no separate argument.
-/
theorem exactFunctor_stupidTail_triangle
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (K : CochainComplex C ℤ) (r : ℤ)
    (hexact : ∀ i : ℤ, i ≤ r →
      ((R.mapHomologicalComplex (.up ℤ)).obj K).ExactAt i) :
    ∃ (i : (singleFunctor D r).obj (kernel (R.map (K.d r (r + 1)))) ⟶
          R.mapDerivedCategory.obj (Q.obj (K.stupidTrunc (ComplexShape.embeddingUpIntGE r))))
      (p : R.mapDerivedCategory.obj (Q.obj
          (K.stupidTrunc (ComplexShape.embeddingUpIntGE r))) ⟶ R.mapDerivedCategory.obj (Q.obj K))
      (δ : R.mapDerivedCategory.obj (Q.obj K) ⟶
          ((singleFunctor D r).obj (kernel (R.map (K.d r (r + 1)))))⟦(1 : ℤ)⟧),
      Triangle.mk i p δ ∈ distTriang (DerivedCategory D) := by
  classical
  let T : CochainComplex C ℤ := K.stupidTrunc (ComplexShape.embeddingUpIntGE r)
  let S : CochainComplex D ℤ := (R.mapHomologicalComplex (.up ℤ)).obj T
  let L : CochainComplex D ℤ := (R.mapHomologicalComplex (.up ℤ)).obj K
  let j : S ⟶ L := (R.mapHomologicalComplex (.up ℤ)).map (stupidTailι K r)
  have hj (n : ℤ) (hn : r ≤ n) : IsIso (j.f n) := by
    let := stupidTailι_isIso_f K r n hn
    exact R.map_isIso ((stupidTailι K r).f n)
  let : S.IsStrictlyGE r := inferInstance
  let : L.IsGE (r + 1) := by
    rw [CochainComplex.isGE_iff]
    intro n hn
    exact hexact n (by omega)
  let A : CochainComplex D ℤ := S.truncLE r
  let B := (S.shortComplexTruncLE r).X₃
  let : A.IsStrictlyGE r := inferInstance
  let : A.IsStrictlyLE r := inferInstance
  have hq : QuasiIso (CochainComplex.truncGEMap j (r + 1)) := by
    rw [CochainComplex.quasiIso_truncGEMap_iff]
    intro n hn
    rw [quasiIsoAt_iff' j (n - 1) n (n + 1) (by simp) (by simp)]
    let f := (HomologicalComplex.shortComplexFunctor' D (.up ℤ) (n - 1) n (n + 1)).map j
    let : IsIso f.τ₁ := hj (n - 1) (by omega)
    let : IsIso f.τ₂ := hj n (by omega)
    let : IsIso f.τ₃ := hj (n + 1) (by omega)
    let : IsIso f := ShortComplex.isIso_of_isIso f
    exact ShortComplex.quasiIso_of_isIso f
  let e₃ : Q.obj B ≅ R.mapDerivedCategory.obj (Q.obj K) :=
    asIso (Q.map (S.shortComplexTruncLEX₃ToTruncGE r (r + 1))) ≪≫
      asIso (Q.map (CochainComplex.truncGEMap j (r + 1))) ≪≫
      (asIso (Q.map (L.πTruncGE (r + 1)))).symm ≪≫
      (R.mapDerivedCategoryFactors.app K).symm
  let e₂ : Q.obj S ≅ R.mapDerivedCategory.obj (Q.obj T) :=
    (R.mapDerivedCategoryFactors.app T).symm
  obtain ⟨M, ⟨e⟩⟩ := CochainComplex.exists_iso_single A r
  let hM : M ≅ A.X r :=
    (HomologicalComplex.singleObjXSelf (.up ℤ) r M).symm ≪≫
      (HomologicalComplex.eval D (.up ℤ) r).mapIso e.symm
  let k : S.cycles r ≅ kernel (S.d r (r + 1)) :=
    (S.cyclesIsKernel r (r + 1) (by simp)).conePointUniqueUpToIso
      (limit.isLimit _)
  let : IsIso (j.f r) := hj r le_rfl
  let : IsIso (j.f (r + 1)) := hj (r + 1) (by omega)
  let hk : kernel (S.d r (r + 1)) ≅ kernel (L.d r (r + 1)) :=
    kernel.mapIso (S.d r (r + 1)) (L.d r (r + 1))
      (asIso (j.f r)) (asIso (j.f (r + 1))) (j.comm r (r + 1)).symm
  let hMk : M ≅ kernel (R.map (K.d r (r + 1))) :=
    hM ≪≫ S.truncLEXIsoCycles r ≪≫ k ≪≫ hk
  let e₁ : Q.obj A ≅ (singleFunctor D r).obj (kernel (R.map (K.d r (r + 1)))) :=
    Q.mapIso e ≪≫ (singleFunctor D r).mapIso hMk
  let t := triangleOfSES (S.shortComplexTruncLE_shortExact r)
  let i := e₁.inv ≫ t.mor₁ ≫ e₂.hom
  let p := e₂.inv ≫ t.mor₂ ≫ e₃.hom
  let δ := e₃.inv ≫ t.mor₃ ≫ (shiftFunctor (DerivedCategory D) (1 : ℤ)).map e₁.hom
  refine ⟨i, p, δ, ?_⟩
  apply isomorphic_distinguished t
    (triangleOfSES_distinguished (S.shortComplexTruncLE_shortExact r)) _
  refine Triangle.isoMk _ _ e₁.symm e₂.symm e₃.symm ?_ ?_ ?_
  · simp [i, Category.assoc]
  · simp [p, Category.assoc]
  · simp [δ, Category.assoc, ← Functor.map_comp]

end DerivedCategory
