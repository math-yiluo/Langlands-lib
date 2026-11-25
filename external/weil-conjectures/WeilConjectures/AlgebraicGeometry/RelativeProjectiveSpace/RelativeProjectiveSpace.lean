/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.SymmetricAlgebraSheafConstruction
public import WeilConjectures.AlgebraicGeometry.RelativeProjAlgebra.RelativeProjAffineRestriction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.Data.Finsupp.Multiset
import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
import Mathlib.LinearAlgebra.DirectSum.Basis
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.QuasiCoherentSymmetricAlgebraAffine

/-! # Relative projective space with its relative-Proj charts

The algebra is the constructed symmetric algebra of the free module. Its grading is fixed
by the monomial inclusions. Only uniquely specified algebra data and the universal relative
Proj realization are selected; no chart isomorphisms are selected separately.

## Main definitions

* `RelativeProjectiveSpace.algebra`: the symmetric algebra with symmetric-degree grading.
* `RelativeProjectiveSpace.construction`: its relative-Proj realization.
* `RelativeProjectiveSpace.scheme`, `RelativeProjectiveSpace.π`: the scheme over the base.
* `RelativeProjectiveSpace.standardOpen`: its standard homogeneous-coordinate opens.

## References

* Nagata compactification, Conrad sketch
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry.RelativeProjectiveSpace

variable (X : Scheme.{u}) (r : ℕ)

/-- The free module with ordered basis indexed by `0, ..., r`. -/
def freeModule : X.Modules :=
  SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (r + 1)))

/-- The degree-one generator `j_F(e_i)` on an arbitrary open. -/
def generator (U : X.Opens) (i : Fin (r + 1)) :
    (SymmetricAlgebraSheaf.algebra (freeModule X r)).right.obj.obj (op U) :=
  (SymmetricAlgebraSheaf.inclusion (freeModule X r)).val.app (op U)
    ((SheafOfModules.ιFree (R := X.ringCatSheaf) (ULift.up i)).val.app (op U)
      (1 : X.ringCatSheaf.obj.obj (op U)))

/-- The indexing set of monomials of symmetric degree `n`. -/
def monomials (n : ℕ) := ULift.{u} {a : Fin (r + 1) → ℕ // ∑ i, a i = n}

/-- The degree-`n` monomial evaluated in the constructed symmetric algebra. -/
def monomial (n : ℕ) (a : monomials.{u} r n) (U : X.Opens) :
    (SymmetricAlgebraSheaf.algebra (freeModule X r)).right.obj.obj (op U) :=
  ∏ i : Fin (r + 1), generator X r U i ^ a.down.val i

private theorem generator_restriction {U V : X.Opensᵒᵖ} (f : U ⟶ V)
    (i : Fin (r + 1)) :
    (SymmetricAlgebraSheaf.algebra (freeModule X r)).right.obj.map f
      (generator X r U.unop i) = generator X r V.unop i := by
  have h := PresheafOfModules.naturality_apply
    ((SheafOfModules.ιFree (R := X.ringCatSheaf) (ULift.up i)) ≫
      SymmetricAlgebraSheaf.inclusion (freeModule X r)).val f
    (1 : X.ringCatSheaf.obj.obj U)
  have hunit : (SheafOfModules.unit X.ringCatSheaf).val.map f
      (1 : X.ringCatSheaf.obj.obj U) = (1 : X.ringCatSheaf.obj.obj V) :=
    (X.ringCatSheaf.obj.map f).hom.map_one
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply, hunit] at h
  change generator X r V.unop i =
    (SymmetricAlgebraSheaf.algebra (freeModule X r)).right.obj.map f
      (generator X r U.unop i) at h
  exact h.symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The linear maps sending 1 to a fixed monomial commute with restriction. -/
theorem monomial_naturality (n : ℕ) (a : monomials.{u} r n)
    {U V : X.Opensᵒᵖ} (f : U ⟶ V) :
    (SheafOfModules.unit X.ringCatSheaf).val.map f ≫
        (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map f).hom).map
          (ModuleCat.ofHom (LinearMap.toSpanSingleton (X.ringCatSheaf.obj.obj V)
            ((SymmetricAlgebraSheaf.algebra (freeModule X r)).toModule.val.obj V)
            (monomial X r n a V.unop))) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton (X.ringCatSheaf.obj.obj U)
          ((SymmetricAlgebraSheaf.algebra (freeModule X r)).toModule.val.obj U)
          (monomial X r n a U.unop)) ≫
        (SymmetricAlgebraSheaf.algebra (freeModule X r)).toModule.val.map f := by
  have hm :
      (SymmetricAlgebraSheaf.algebra (freeModule X r)).right.obj.map f
        (monomial X r n a U.unop) = monomial X r n a V.unop := by
    simp only [monomial, map_prod, map_pow, generator_restriction]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (SymmetricAlgebraSheaf.algebra (freeModule X r)).hom.hom.app V
      ((X.presheaf.map f) x) * monomial X r n a V.unop =
    (SymmetricAlgebraSheaf.algebra (freeModule X r)).right.obj.map f
      ((SymmetricAlgebraSheaf.algebra (freeModule X r)).hom.hom.app U x *
        monomial X r n a U.unop)
  rw [map_mul, hm]
  exact congrArg (· * monomial X r n a V.unop)
    (CategoryTheory.congr_fun
      ((SymmetricAlgebraSheaf.algebra (freeModule X r)).hom.hom.naturality f) x)

/-- The monomial map from a copy of the structure module into the symmetric algebra. -/
def monomialUnit (n : ℕ) (a : monomials.{u} r n) :
    SheafOfModules.unit X.ringCatSheaf ⟶
      (SymmetricAlgebraSheaf.algebra (freeModule X r)).toModule where
  val :=
    { app U := ModuleCat.ofHom
        (Y := (SymmetricAlgebraSheaf.algebra (freeModule X r)).toModule.val.obj U)
        (LinearMap.toSpanSingleton (X.ringCatSheaf.obj.obj U)
        ((SymmetricAlgebraSheaf.algebra (freeModule X r)).toModule.val.obj U)
        (monomial X r n a U.unop))
      naturality f := monomial_naturality X r n a f }

/-- The homogeneous monomial inclusion, extended from the free monomial basis. -/
def monomialMap (n : ℕ) :
    SheafOfModules.free (R := X.ringCatSheaf) (monomials.{u} r n) ⟶
      (SymmetricAlgebraSheaf.algebra (freeModule X r)).toModule :=
  Sigma.desc (fun a ↦ monomialUnit X r n a)

/-- The exact characterization of the symmetric-degree relative-Proj input. The pieces
are the free monomial sheaves and their inclusions are evaluation of those monomials.
`HEq` compares maps whose endpoints are identified by the preceding equalities. -/
def IsSymmetricInput (A : RelativeProjAlgebra X) : Prop :=
  A.algebra.obj = SymmetricAlgebraSheaf.algebra (freeModule X r) ∧
    A.piece = (fun n ↦ SheafOfModules.free (R := X.ringCatSheaf) (monomials.{u} r n)) ∧
    ∀ n : ℕ, HEq (Sigma.ι A.piece n ≫ A.decomposition.hom) (monomialMap X r n)

private def freeSectionEquiv (I : Type u) [Fintype I] [DecidableEq I] (U : X.Opens) :
    (SheafOfModules.free (R := X.ringCatSheaf) I).val.obj (op U) ≃ₗ[Γ(X, U)]
      (I → Γ(X, U)) where
  toFun x i := (Scheme.Modules.freeπ i).val.app (op U) x
  map_add' x y := by ext i; exact map_add _ _ _
  map_smul' a x := by ext i; exact (Scheme.Modules.freeπ i).val.app (op U) |>.hom.map_smul a x
  invFun c := ∑ i, (SheafOfModules.ιFree (R := X.ringCatSheaf) i).val.app (op U) (c i)
  left_inv x := by
    change ∑ i : I, (Scheme.Modules.Hom.app
      (Scheme.Modules.freeπ i ≫ SheafOfModules.ιFree i) U) x = x
    rw [← Scheme.Modules.Hom.sum_app_apply, Scheme.Modules.sum_freeπ_ιFree]
    rfl
  right_inv c := by
    ext j
    change (Scheme.Modules.freeπ j).val.app (op U) (∑ i,
      (SheafOfModules.ιFree (R := X.ringCatSheaf) i).val.app (op U) (c i)) = c j
    rw [map_sum, Finset.sum_eq_single j _ (by simp)]
    · have h := congrArg (fun f ↦ f.val.app (op U) (c j))
        (Scheme.Modules.ιFree_freeπ (X := X) j j)
      rw [ite_eq_left rfl] at h
      exact h
    · intro i _ hij
      have h := congrArg (fun f ↦ f.val.app (op U) (c i))
        (Scheme.Modules.ιFree_freeπ (X := X) i j)
      rw [ite_eq_right hij] at h
      exact h

set_option backward.isDefEq.respectTransparency.types false in
private theorem freeMap_range (I : Type u) [Finite I]
    (U : X.Opens) (M : X.Modules)
    (f : SheafOfModules.free (R := X.ringCatSheaf) I ⟶ M) :
    LinearMap.range (f.val.app (op U)).hom = Submodule.span Γ(X, U)
      (Set.range fun i ↦ (f.val.app (op U))
        ((SheafOfModules.ιFree (R := X.ringCatSheaf) i).val.app (op U)
          (1 : X.ringCatSheaf.obj.obj (op U)))) := by
  classical
  let _ := Fintype.ofFinite I
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    have hx := (freeSectionEquiv X I U).symm_apply_apply x
    change (∑ i : I, (SheafOfModules.ιFree (R := X.ringCatSheaf) i).val.app (op U)
      (freeSectionEquiv X I U x i)) = x at hx
    rw [← hx, map_sum]
    apply Submodule.sum_mem
    intro i _
    have hi : (SheafOfModules.ιFree (R := X.ringCatSheaf) i).val.app (op U)
        (freeSectionEquiv X I U x i) =
      freeSectionEquiv X I U x i •
        ((SheafOfModules.ιFree (R := X.ringCatSheaf) i).val.app (op U)
          (1 : X.ringCatSheaf.obj.obj (op U))) := by
      rw [← map_smul]
      congr 1
      change _ = (freeSectionEquiv X I U x i : Γ(X, U)) * 1
      exact (mul_one _).symm
    rw [hi, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact LinearMap.mem_range_self _ _

private def freeSectionBasis (U : X.Opens) :
    Module.Basis (Fin (r + 1)) Γ(X, U) ((freeModule X r).val.obj (op U)) :=
  ((Pi.basisFun Γ(X, U) (ULift.{u} (Fin (r + 1)))).map
    (freeSectionEquiv X (ULift.{u} (Fin (r + 1))) U).symm).reindex Equiv.ulift

set_option backward.isDefEq.respectTransparency.types false in
private theorem freeSectionBasis_apply (U : X.Opens) (i : Fin (r + 1)) :
    freeSectionBasis X r U i =
      (SheafOfModules.ιFree (R := X.ringCatSheaf) (ULift.up i)).val.app (op U)
        (1 : X.ringCatSheaf.obj.obj (op U)) := by
  classical
  unfold freeSectionBasis
  erw [Module.Basis.reindex_apply, Module.Basis.map_apply, Pi.basisFun_apply]
  change (∑ j : ULift.{u} (Fin (r + 1)),
    (SheafOfModules.ιFree (R := X.ringCatSheaf) j).val.app (op U)
      ((Pi.single (ULift.up i) 1 : ULift.{u} (Fin (r + 1)) → Γ(X, U)) j)) = _
  simp only [Pi.single_apply]
  rw [Finset.sum_eq_single (ULift.up i)]
  · simp only [↓reduceIte]
  · intro j _ hj
    simp only [hj, ↓reduceIte, map_zero]
  · simp

private theorem affinePolynomialEquiv_exists_aux (V : X.affineOpens)
    (B : X.CommAlgebraSheaf) (hB : B = SymmetricAlgebraSheaf.algebra (freeModule X r)) :
    ∃ e : MvPolynomial (Fin (r + 1)) Γ(X, V.1) ≃+* B.right.obj.obj (op V.1),
      (∀ a : Γ(X, V.1), e (MvPolynomial.C a) = B.hom.hom.app (op V.1) a) ∧
      (∀ i : Fin (r + 1), e (MvPolynomial.X i) =
        (eqToHom hB.symm).right.hom.app (op V.1) (generator X r V.1 i)) := by
  subst B
  have : (freeModule X r).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_free.{u, u, u} (R := X.ringCatSheaf) _
  let e := (SymmetricAlgebra.equivMvPolynomial (freeSectionBasis X r V.1)).symm
  let t := RingEquiv.ofBijective (SymmetricAlgebraSheaf.sectionMap (freeModule X r) (op V.1))
    ((quasiCoherentSymmetricAlgebra_affine_comparison X (freeModule X r)).2 V)
  refine ⟨e.toRingEquiv.trans t, ?_, ?_⟩
  · intro a
    change SymmetricAlgebraSheaf.sectionMap (freeModule X r) (op V.1)
      (e (algebraMap Γ(X, V.1) (MvPolynomial (Fin (r + 1)) Γ(X, V.1)) a)) = _
    rw [e.commutes]
    rfl
  · intro i
    change SymmetricAlgebraSheaf.sectionMap (freeModule X r) (op V.1)
      ((SymmetricAlgebra.equivMvPolynomial (freeSectionBasis X r V.1)).symm
        (MvPolynomial.X i)) = generator X r V.1 i
    rw [SymmetricAlgebra.equivMvPolynomial_symm_X, freeSectionBasis_apply]
    rfl

private abbrev monomialFintype (n : ℕ) : Fintype (monomials.{u} r n) := by
  classical
  exact Fintype.ofEquiv (Sym (Fin (r + 1)) n)
    ((Sym.equivNatSumOfFintype (Fin (r + 1)) n).trans Equiv.ulift.symm)

private def monomialIndexEquiv : (Σ n, monomials.{u} r n) ≃ (Fin (r + 1) →₀ ℕ) where
  toFun a := Finsupp.equivFunOnFinite.symm a.2.down.val
  invFun d := ⟨d.degree, ⟨⟨d, (Finsupp.degree_eq_sum d).symm⟩⟩⟩
  left_inv a := by
    obtain ⟨n, ⟨a, ha⟩⟩ := a
    have hd : (Finsupp.equivFunOnFinite.symm a).degree = n := by
      rw [Finsupp.degree_eq_sum]
      exact ha
    apply Sigma.ext hd
    cases hd
    rfl
  right_inv d := by
    ext i
    simp

private def monomialSectionBasis (n : ℕ) (U : X.Opens) :
    Module.Basis (monomials.{u} r n) Γ(X, U)
      ((SheafOfModules.free (R := X.ringCatSheaf) (monomials.{u} r n)).val.obj (op U)) := by
  classical
  let _ := monomialFintype r n
  exact (Pi.basisFun Γ(X, U) (monomials.{u} r n)).map
    (freeSectionEquiv X (monomials.{u} r n) U).symm

set_option backward.isDefEq.respectTransparency.types false in
private theorem monomialSectionBasis_apply (n : ℕ) (U : X.Opens)
    (a : monomials.{u} r n) :
    monomialSectionBasis X r n U a =
      (SheafOfModules.ιFree (R := X.ringCatSheaf) a).val.app (op U)
        (1 : X.ringCatSheaf.obj.obj (op U)) := by
  classical
  let _ := monomialFintype r n
  unfold monomialSectionBasis
  erw [Module.Basis.map_apply, Pi.basisFun_apply]
  change (∑ j : monomials.{u} r n,
    (SheafOfModules.ιFree (R := X.ringCatSheaf) j).val.app (op U)
      ((Pi.single a 1 : monomials.{u} r n → Γ(X, U)) j)) = _
  simp only [Pi.single_apply]
  rw [Finset.sum_eq_single a]
  · simp only [↓reduceIte]
  · intro j _ hj
    simp only [hj, ↓reduceIte, map_zero]
  · simp

set_option backward.isDefEq.respectTransparency.types false in
private theorem monomialMap_basis (n : ℕ) (U : X.Opens)
    (a : monomials.{u} r n) :
    (monomialMap X r n).val.app (op U) (monomialSectionBasis X r n U a) =
      monomial X r n a U := by
  rw [monomialSectionBasis_apply]
  have h := congrArg (fun t ↦ t.val.app (op U) (1 : X.ringCatSheaf.obj.obj (op U)))
    (Sigma.ι_comp_desc (fun a ↦ monomialUnit X r n a) a)
  change (monomialMap X r n).val.app (op U)
      ((SheafOfModules.ιFree (R := X.ringCatSheaf) a).val.app (op U)
        (1 : X.ringCatSheaf.obj.obj (op U))) =
    (monomialUnit X r n a).val.app (op U)
      (1 : X.ringCatSheaf.obj.obj (op U)) at h
  exact h.trans (one_smul _ _)

private theorem directSumBasis_apply (U : X.Opens) (a : Σ n, monomials.{u} r n) :
    (DFinsupp.basis (fun n ↦ monomialSectionBasis X r n U)) a =
      DirectSum.of (fun n ↦
        (SheafOfModules.free (R := X.ringCatSheaf) (monomials.{u} r n)).val.obj (op U))
        a.1 (monomialSectionBasis X r a.1 U a.2) := by
  classical
  apply (DFinsupp.basis (fun n ↦ monomialSectionBasis X r n U)).repr.injective
  simp only [DFinsupp.basis, Module.Basis.coe_ofRepr, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, DFinsupp.mapRange.linearEquiv_symm, LinearEquiv.trans_apply,
    sigmaFinsuppLequivDFinsupp_apply, AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe,
    EquivLike.coe_coe, sigmaFinsuppAddEquivDFinsupp_apply, sigmaFinsuppEquivDFinsupp_single,
    DFinsupp.mapRange.linearEquiv_apply, Module.Basis.repr_symm_apply, DFinsupp.mapRange_single,
    Finsupp.linearCombination_single, one_smul, Module.Basis.repr_self,
    sigmaFinsuppLequivDFinsupp_symm_apply, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
    sigmaFinsuppAddEquivDFinsupp_symm_apply, EmbeddingLike.apply_eq_iff_eq]
  change DFinsupp.single a.1 (Finsupp.single a.2 1) =
    DFinsupp.mapRange (fun i x ↦ (monomialSectionBasis X r i U).repr x)
      (fun i ↦ map_zero _) (DFinsupp.single a.1 (monomialSectionBasis X r a.1 U a.2))
  simp

set_option backward.isDefEq.respectTransparency.types false in
private theorem monomialSum_bijective (V : X.affineOpens) :
    Function.Bijective
      (DirectSum.toModule Γ(X, V.1) ℕ
        ((SymmetricAlgebraSheaf.algebra (freeModule X r)).toModule.val.obj (op V.1))
        (fun n ↦ ((monomialMap X r n).val.app (op V.1)).hom)) := by
  classical
  obtain ⟨e, hC, hX⟩ := affinePolynomialEquiv_exists_aux X r V
    (SymmetricAlgebraSheaf.algebra (freeModule X r)) rfl
  let L : MvPolynomial (Fin (r + 1)) Γ(X, V.1) ≃ₗ[Γ(X, V.1)]
      (SymmetricAlgebraSheaf.algebra (freeModule X r)).toModule.val.obj (op V.1) :=
    { toEquiv := e.toEquiv
      map_add' := fun a b ↦ e.map_add a b
      map_smul' := by
        intro a q
        rw [Algebra.smul_def]
        change e (MvPolynomial.C a * q) =
          (SymmetricAlgebraSheaf.algebra (freeModule X r)).hom.hom.app (op V.1) a * e q
        rw [map_mul, hC] }
  let b := DFinsupp.basis (fun n ↦ monomialSectionBasis X r n V.1)
  let c := (MvPolynomial.basisMonomials (Fin (r + 1)) Γ(X, V.1)).map L
  let E := b.equiv c (monomialIndexEquiv r)
  have hE : DirectSum.toModule Γ(X, V.1) ℕ
      ((SymmetricAlgebraSheaf.algebra (freeModule X r)).toModule.val.obj (op V.1))
      (fun n ↦ ((monomialMap X r n).val.app (op V.1)).hom) = E.toLinearMap := by
    apply b.ext
    intro a
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
    change _ = c (monomialIndexEquiv r a)
    rw [directSumBasis_apply]
    rw [← DirectSum.lof_eq_of Γ(X, V.1)]
    erw [DirectSum.toModule_lof, monomialMap_basis]
    change monomial X r a.1 a.2 V.1 =
      e (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm a.2.down.val) 1)
    have hp : (∏ i : Fin (r + 1), (MvPolynomial.X i :
        MvPolynomial (Fin (r + 1)) Γ(X, V.1)) ^ a.2.down.val i) =
        MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm a.2.down.val) 1 := by
      rw [MvPolynomial.prod_X_pow]
      apply congrArg (fun d ↦ MvPolynomial.monomial d (1 : Γ(X, V.1)))
      ext i
      simp
    rw [← hp]
    simp only [map_prod, map_pow, hX, monomial]
    rfl
  rw [hE]
  exact E.bijective

set_option backward.isDefEq.respectTransparency.types false in
private theorem monomialCofan_isColimit : Nonempty (IsColimit (Cofan.mk
    (SymmetricAlgebraSheaf.algebra (freeModule X r)).toModule (monomialMap X r))) := by
  classical
  let P : ℕ → X.Modules := fun n ↦
    SheafOfModules.free (R := X.ringCatSheaf) (monomials.{u} r n)
  let N : X.Modules := (SymmetricAlgebraSheaf.algebra (freeModule X r)).toModule
  let b : ∀ n, P n ⟶ N := monomialMap X r
  let sumB (U : X.affineOpens) := DirectSum.toModule Γ(X, U.1) ℕ
    (N.val.obj (op U.1)) (fun n ↦ ((b n).val.app (op U.1)).hom)
  have hb (U : X.affineOpens) : Function.Bijective (sumB U) :=
    monomialSum_bijective X r U
  let e (U : X.affineOpens) := LinearEquiv.ofBijective (sumB U) (hb U)
  have hext (M : X.Modules) (f g : N ⟶ M)
      (hfg : ∀ d, b d ≫ f = b d ≫ g) : f = g := by
    have haff (U : X.affineOpens) (z : N.val.obj (op U.1)) :
        f.val.app (op U.1) z = g.val.app (op U.1) z := by
      obtain ⟨v, rfl⟩ := (hb U).surjective z
      have h : (f.val.app (op U.1)).hom.comp (sumB U) =
          (g.val.app (op U.1)).hom.comp (sumB U) := by
        apply DirectSum.linearMap_ext
        intro d
        apply LinearMap.ext
        intro a
        simp only [LinearMap.comp_apply, sumB, DirectSum.toModule_lof]
        exact congrArg (fun k ↦ k.val.app (op U.1) a) (hfg d)
      exact LinearMap.congr_fun h v
    refine Scheme.Modules.hom_ext f g fun U ↦ ?_
    ext z
    refine TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩
      (fun i : {V : X.affineOpens // V.1 ≤ U} ↦ i.1.1) U
      (fun i ↦ homOfLE i.2) ?_ _ _ fun i ↦ ?_
    · intro y hy
      obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hy U.2
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hVU⟩, hyV⟩
    · rw [← Scheme.Modules.Hom.app_presheaf_map, ← Scheme.Modules.Hom.app_presheaf_map]
      exact haff i.1 _
  have hexists (M : X.Modules) (c : ∀ d : ℕ, P d ⟶ M) :
      ∃ f : N ⟶ M, ∀ d, b d ≫ f = c d := by
    let localMap (U : X.affineOpens) : N.val.obj (op U.1) →ₗ[Γ(X, U.1)]
        M.val.obj (op U.1) :=
      (DirectSum.toModule Γ(X, U.1) ℕ (M.val.obj (op U.1))
        (fun d ↦ ((c d).val.app (op U.1)).hom)) ∘ₗ (e U).symm.toLinearMap
    have localFac (U : X.affineOpens) (d : ℕ) (a : (P d).val.obj (op U.1)) :
        localMap U ((b d).val.app (op U.1) a) = (c d).val.app (op U.1) a := by
      have he : e U (DirectSum.lof Γ(X, U.1) ℕ
          (fun d ↦ (P d).val.obj (op U.1)) d a) = (b d).val.app (op U.1) a :=
        DirectSum.toModule_lof _ _ _
      rw [← he]
      simp only [localMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply]
      exact DirectSum.toModule_lof _ _ _
    have localNat (U V : X.affineOpens) (i : V.1 ⟶ U.1)
        (z : N.val.obj (op U.1)) :
        M.presheaf.map i.op (localMap U z) =
          localMap V (N.presheaf.map i.op z) := by
      obtain ⟨v, rfl⟩ := (hb U).surjective z
      induction v using DirectSum.induction_on with
      | zero => simp
      | of d a =>
        change M.presheaf.map i.op
            (localMap U (sumB U (DirectSum.lof Γ(X, U.1) ℕ
              (fun d ↦ (P d).val.obj (op U.1)) d a))) =
          localMap V (N.presheaf.map i.op (sumB U (DirectSum.lof Γ(X, U.1) ℕ
            (fun d ↦ (P d).val.obj (op U.1)) d a)))
        have he : sumB U (DirectSum.lof Γ(X, U.1) ℕ
            (fun d ↦ (P d).val.obj (op U.1)) d a) = (b d).val.app (op U.1) a :=
          DirectSum.toModule_lof _ _ _
        simp only [he, localFac]
        have hcn := PresheafOfModules.naturality_apply (c d).val i.op a
        have hbn := PresheafOfModules.naturality_apply (b d).val i.op a
        exact hcn.symm.trans ((localFac V d ((P d).val.map i.op a)).symm.trans
          (congrArg (localMap V) hbn))
      | add v w hv hw => simp only [map_add, hv, hw]
    have hbasis : TopologicalSpace.Opens.IsBasis
        (Set.range (fun U : X.affineOpens ↦ U.1)) := by
      simpa only [Subtype.range_coe] using X.isBasis_affineOpens
    let alpha : (CategoryTheory.inducedFunctor (fun U : X.affineOpens ↦ U.1)).op ⋙
        N.presheaf ⟶
        (CategoryTheory.inducedFunctor (fun U : X.affineOpens ↦ U.1)).op ⋙ M.presheaf :=
      { app := fun U ↦ AddCommGrpCat.ofHom (localMap U.unop).toAddMonoidHom
        naturality := by
          intro U V i
          ext z
          exact (localNat U.unop V.unop
            ((CategoryTheory.inducedFunctor (fun U : X.affineOpens ↦ U.1)).map i.unop) z).symm }
    let f := TopCat.Sheaf.restrictHomEquivHom N.presheaf ⟨M.presheaf, M.isSheaf⟩
      hbasis alpha
    have fAffine (U : X.affineOpens) (z : N.val.obj (op U.1)) :
        f.app (op U.1) z = localMap U z := by
      change (TopCat.Sheaf.restrictHomEquivHom N.presheaf
        ⟨M.presheaf, M.isSheaf⟩ hbasis alpha).app (op U.1) z = _
      rw [TopCat.Sheaf.extend_hom_app]
      rfl
    have fLinear (U : X.Opensᵒᵖ) (a : X.ringCatSheaf.obj.obj U) (z : N.val.obj U) :
        f.app U (a • z) = a • (show M.val.obj U from f.app U z) := by
      refine TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩
        (fun i : {V : X.affineOpens // V.1 ≤ U.unop} ↦ i.1.1) U.unop
        (fun i ↦ homOfLE i.2) ?_ _ _ fun i ↦ ?_
      · intro y hy
        obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
          X.isBasis_affineOpens.exists_subset_of_mem_open hy U.unop.2
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hVU⟩, hyV⟩
      · have hf (z : N.val.obj U) :
            M.presheaf.map (homOfLE i.2).op (f.app U z) =
              f.app (op i.1.1) (N.presheaf.map (homOfLE i.2).op z) :=
          (ConcreteCategory.congr_hom (f.naturality (homOfLE i.2).op) z).symm
        rw [hf]
        change f.app (op i.1.1) (N.val.map (homOfLE i.2).op (a • z)) =
          M.val.map (homOfLE i.2).op (a • (show M.val.obj U from f.app U z))
        have hf' : M.val.map (homOfLE i.2).op
            (show M.val.obj U from f.app U z) =
              f.app (op i.1.1) (N.val.map (homOfLE i.2).op z) := hf z
        rw [N.val.map_smul, M.val.map_smul, hf', fAffine, fAffine]
        exact (localMap i.1).map_smul _ _
    let fm : N ⟶ M := ⟨PresheafOfModules.homMk f fLinear⟩
    refine ⟨fm, ?_⟩
    intro d
    refine Scheme.Modules.hom_ext (b d ≫ fm) (c d) fun U ↦ ?_
    ext z
    refine TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩
      (fun i : {V : X.affineOpens // V.1 ≤ U} ↦ i.1.1) U
      (fun i ↦ homOfLE i.2) ?_ _ _ fun i ↦ ?_
    · intro y hy
      obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hy U.2
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hVU⟩, hyV⟩
    · rw [← Scheme.Modules.Hom.app_presheaf_map, ← Scheme.Modules.Hom.app_presheaf_map]
      change f.app (op i.1.1) ((b d).val.app (op i.1.1) _) = (c d).val.app (op i.1.1) _
      rw [fAffine, localFac]
  let desc (t : Cofan P) := Classical.choose (hexists t.pt t.inj)
  have hfac (t : Cofan P) (d : ℕ) : (Cofan.mk N b).inj d ≫ desc t = t.inj d :=
    Classical.choose_spec (hexists t.pt t.inj) d
  refine ⟨Cofan.IsColimit.mk _ desc hfac ?_⟩
  intro t m hm
  apply hext t.pt m (desc t)
  intro d
  exact (hm d).trans (hfac t d).symm

private def monomialDecomposition :
    (∐ fun n ↦ SheafOfModules.free (R := X.ringCatSheaf) (monomials.{u} r n)) ≅
      (SymmetricAlgebraSheaf.algebra (freeModule X r)).toModule :=
  (coproductIsCoproduct _).coconePointUniqueUpToIso (monomialCofan_isColimit X r).some

private theorem monomialDecomposition_ι (n : ℕ) :
    Sigma.ι (fun n ↦ SheafOfModules.free (R := X.ringCatSheaf) (monomials.{u} r n)) n ≫
      (monomialDecomposition X r).hom = monomialMap X r n := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct _)
    (monomialCofan_isColimit X r).some (Discrete.mk n)

private theorem monomialMap_injective (n : ℕ) (U : X.Opens) :
    Function.Injective ((monomialMap X r n).val.app (op U)) := by
  rw [← monomialDecomposition_ι]
  let E := SheafOfModules.evaluation X.ringCatSheaf (op U)
  have : IsSplitMono (E.map (Sigma.ι
      (fun n ↦ SheafOfModules.free (R := X.ringCatSheaf) (monomials.{u} r n)) n)) :=
    inferInstance
  have : IsSplitMono (E.map (monomialDecomposition X r).hom) := inferInstance
  have : Mono (E.map (Sigma.ι
      (fun n ↦ SheafOfModules.free (R := X.ringCatSheaf) (monomials.{u} r n)) n ≫
      (monomialDecomposition X r).hom)) := by
    rw [Functor.map_comp]
    infer_instance
  exact (ModuleCat.mono_iff_injective _).mp this

private def monomialAdd {m n : ℕ} (a : monomials.{u} r m) (b : monomials.{u} r n) :
    monomials.{u} r (m + n) :=
  ⟨⟨fun i ↦ a.down.val i + b.down.val i, by
    rw [Finset.sum_add_distrib, a.down.property, b.down.property]⟩⟩

private def monomialMul (m n : ℕ) (U : X.Opens) :
    (SheafOfModules.free (R := X.ringCatSheaf) (monomials.{u} r m)).val.obj (op U) →ₗ[Γ(X, U)]
      (SheafOfModules.free (R := X.ringCatSheaf) (monomials.{u} r n)).val.obj (op U) →ₗ[Γ(X, U)]
      (SheafOfModules.free (R := X.ringCatSheaf) (monomials.{u} r (m + n))).val.obj (op U) :=
  (monomialSectionBasis X r m U).constr Γ(X, U) (fun a ↦
    (monomialSectionBasis X r n U).constr Γ(X, U) (fun b ↦
      monomialSectionBasis X r (m + n) U (monomialAdd r a b)))

private def zeroMonomial : monomials.{u} r 0 := ⟨⟨fun _ ↦ 0, by simp⟩⟩

private def monomialUnitMap : SheafOfModules.unit X.ringCatSheaf ⟶
    SheafOfModules.free (R := X.ringCatSheaf) (monomials.{u} r 0) :=
  SheafOfModules.ιFree (zeroMonomial r)

set_option backward.isDefEq.respectTransparency.types false in
private theorem monomialMul_eq (U : X.Opens) (m n : ℕ)
    (a : (SheafOfModules.free (R := X.ringCatSheaf) (monomials.{u} r m)).val.obj (op U))
    (b : (SheafOfModules.free (R := X.ringCatSheaf) (monomials.{u} r n)).val.obj (op U)) :
    (monomialMap X r (m + n)).val.app (op U) (monomialMul X r m n U a b) =
      (show (SymmetricAlgebraSheaf.algebra (freeModule X r)).right.obj.obj (op U) from
        (monomialMap X r m).val.app (op U) a) *
      (show (SymmetricAlgebraSheaf.algebra (freeModule X r)).right.obj.obj (op U) from
        (monomialMap X r n).val.app (op U) b) := by
  let : Algebra Γ(X, U) ((SymmetricAlgebraSheaf.algebra (freeModule X r)).right.obj.obj (op U)) :=
    ((SymmetricAlgebraSheaf.algebra (freeModule X r)).hom.hom.app (op U)).hom.toAlgebra
  let f := ((monomialMap X r (m + n)).val.app (op U)).hom
  let g := ((monomialMap X r m).val.app (op U)).hom
  let h := ((monomialMap X r n).val.app (op U)).hom
  have he : (monomialMul X r m n U).compr₂ f =
      (LinearMap.mul Γ(X, U)
        ((SymmetricAlgebraSheaf.algebra (freeModule X r)).right.obj.obj (op U))).compl₁₂ g h := by
    apply (monomialSectionBasis X r m U).ext
    intro i
    apply (monomialSectionBasis X r n U).ext
    intro j
    change f (monomialMul X r m n U _ _) = _
    simp only [monomialMul, Module.Basis.constr_basis]
    change (monomialMap X r (m + n)).val.app (op U)
      (monomialSectionBasis X r (m + n) U (monomialAdd r i j)) =
        (show (SymmetricAlgebraSheaf.algebra (freeModule X r)).right.obj.obj (op U) from
          (monomialMap X r m).val.app (op U)
          (monomialSectionBasis X r m U i)) *
        (show (SymmetricAlgebraSheaf.algebra (freeModule X r)).right.obj.obj (op U) from
          (monomialMap X r n).val.app (op U)
          (monomialSectionBasis X r n U j))
    rw [monomialMap_basis, monomialMap_basis, monomialMap_basis]
    change (∏ k, generator X r U k ^ (i.down.val k + j.down.val k)) =
      (∏ k, generator X r U k ^ i.down.val k) * ∏ k, generator X r U k ^ j.down.val k
    simp only [pow_add, Finset.prod_mul_distrib]
  exact LinearMap.congr_fun (LinearMap.congr_fun he a) b

set_option backward.isDefEq.respectTransparency.types false in
private theorem monomialUnit_eq (U : X.Opens) (a : Γ(X, U)) :
    (monomialMap X r 0).val.app (op U) ((monomialUnitMap X r).val.app (op U) a) =
      (SymmetricAlgebraSheaf.algebra (freeModule X r)).hom.hom.app (op U) a := by
  have h := congrArg (fun t ↦ t.val.app (op U) a)
    (Sigma.ι_comp_desc (fun a ↦ monomialUnit X r 0 a) (zeroMonomial r))
  change (monomialMap X r 0).val.app (op U) ((monomialUnitMap X r).val.app (op U) a) =
    (monomialUnit X r 0 (zeroMonomial r)).val.app (op U) a at h
  rw [h]
  change _ * (∏ i : Fin (r + 1), generator X r U i ^ 0) = _
  simp
  rfl

set_option backward.isDefEq.respectTransparency.types false in
private theorem monomialMap_restrict (n : ℕ) {U V : X.Opens} (i : V ⟶ U)
    (a : (SheafOfModules.free (R := X.ringCatSheaf) (monomials.{u} r n)).val.obj (op U)) :
    (monomialMap X r n).val.app (op V)
        ((SheafOfModules.free (R := X.ringCatSheaf) (monomials.{u} r n)).val.map i.op a) =
      (SymmetricAlgebraSheaf.algebra (freeModule X r)).right.obj.map i.op
        ((monomialMap X r n).val.app (op U) a) :=
  PresheafOfModules.naturality_apply (monomialMap X r n).val i.op a

private theorem monomialMap_heq {m n : ℕ} (h : m = n) (U : X.Opens)
    (a : (SheafOfModules.free (R := X.ringCatSheaf) (monomials.{u} r m)).val.obj (op U))
    (b : (SheafOfModules.free (R := X.ringCatSheaf) (monomials.{u} r n)).val.obj (op U))
    (hab : (show (SymmetricAlgebraSheaf.algebra (freeModule X r)).right.obj.obj (op U) from
        (monomialMap X r m).val.app (op U) a) =
      (show (SymmetricAlgebraSheaf.algebra (freeModule X r)).right.obj.obj (op U) from
        (monomialMap X r n).val.app (op U) b)) : HEq a b := by
  subst n
  exact heq_of_eq (monomialMap_injective X r m U hab)

set_option backward.isDefEq.respectTransparency.types false in
private def monomialGraded : GradedSheafAlgebra
    (fun n ↦ SheafOfModules.free (R := X.ringCatSheaf) (monomials.{u} r n)) where
  mul := monomialMul X r
  unit := monomialUnitMap X r
  naturality := by
    intro m n U V h a b
    apply monomialMap_injective X r (m + n) V
    rw [monomialMap_restrict, monomialMul_eq, monomialMul_eq, map_mul,
      monomialMap_restrict, monomialMap_restrict]
  assoc := by
    intro l m n U a b c
    apply monomialMap_heq X r (Nat.add_assoc l m n) U
    rw [monomialMul_eq, monomialMul_eq, monomialMul_eq, monomialMul_eq]
    exact mul_assoc _ _ _
  comm := by
    intro m n U a b
    apply monomialMap_heq X r (Nat.add_comm m n) U
    rw [monomialMul_eq, monomialMul_eq]
    exact mul_comm _ _
  one_mul := by
    intro n U a
    apply monomialMap_heq X r (Nat.zero_add n) U
    rw [monomialMul_eq, monomialUnit_eq, map_one, one_mul]
  mul_one := by
    intro n U a
    apply monomialMap_heq X r (Nat.add_zero n) U
    rw [monomialMul_eq, monomialUnit_eq, map_one, mul_one]

private theorem input_inclusion_injective (A : RelativeProjAlgebra X)
    (n : ℕ) (U : X.Opens) :
    Function.Injective ((Sigma.ι A.piece n ≫ A.decomposition.hom).val.app (op U)) := by
  let E := SheafOfModules.evaluation X.ringCatSheaf (op U)
  have : IsSplitMono (E.map (Sigma.ι A.piece n)) := inferInstance
  have : IsSplitMono (E.map A.decomposition.hom) := inferInstance
  have : Mono (E.map (Sigma.ι A.piece n ≫ A.decomposition.hom)) := by
    rw [Functor.map_comp]
    infer_instance
  exact (ModuleCat.mono_iff_injective _).mp this

private theorem input_eq_of_inclusions (A B : RelativeProjAlgebra X)
    (hA : A.algebra = B.algebra) (hP : A.piece = B.piece)
    (hI : ∀ n : ℕ, HEq (Sigma.ι A.piece n ≫ A.decomposition.hom)
      (Sigma.ι B.piece n ≫ B.decomposition.hom)) : A = B := by
  obtain ⟨A, P, g, d, hm, hu⟩ := A
  obtain ⟨A', P', g', d', hm', hu'⟩ := B
  dsimp only at hA hP hI
  cases hA
  cases hP
  have hd : d = d' := by
    apply Iso.ext
    exact Sigma.hom_ext _ _ (fun n ↦ eq_of_heq (hI n))
  cases hd
  have hi (n : ℕ) (U : X.Opens) :
      Function.Injective ((Sigma.ι P n ≫ d.hom).val.app (op U)) :=
    input_inclusion_injective X ⟨A, P, g, d, hm, hu⟩ n U
  have hmul : g.mul = g'.mul := by
    funext m n U
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    apply hi (m + n) U
    exact (hm U m n a b).trans (hm' U m n a b).symm
  have hunit : g.unit = g'.unit := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply hi 0 U.unop
    exact (hu U.unop a).trans (hu' U.unop a).symm
  have hg : g = g' := by
    cases g
    cases g'
    cases hmul
    cases hunit
    rfl
  cases hg
  rfl

private theorem symmetricInput_unique (A B : RelativeProjAlgebra X)
    (hA : IsSymmetricInput X r A) (hB : IsSymmetricInput X r B) : A = B := by
  apply input_eq_of_inclusions X A B
  · apply CategoryTheory.ObjectProperty.FullSubcategory.ext
    exact hA.1.trans hB.1.symm
  · exact hA.2.1.trans hB.2.1.symm
  · intro n
    exact (hA.2.2 n).trans (hB.2.2 n).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- There is exactly one relative-Proj algebra structure with these fixed pieces,
algebra sheaf and monomial inclusions; thus selecting it does not select unknown data. -/
theorem existsUnique_symmetricInput : ∃! A : RelativeProjAlgebra X, IsSymmetricInput X r A := by
  have : (freeModule X r).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_free.{u, u, u} (R := X.ringCatSheaf) _
  let A : RelativeProjAlgebra X :=
    { algebra := ⟨SymmetricAlgebraSheaf.algebra (freeModule X r),
        (quasiCoherentSymmetricAlgebra_affine_comparison X (freeModule X r)).1⟩
      piece := fun n ↦ SheafOfModules.free (R := X.ringCatSheaf) (monomials.{u} r n)
      graded := monomialGraded X r
      decomposition := monomialDecomposition X r
      mul_eq := by
        intro U m n a b
        simp only [monomialDecomposition_ι X r]
        exact monomialMul_eq X r U m n a b
      unit_eq := by
        intro U a
        simp only [monomialDecomposition_ι X r]
        exact monomialUnit_eq X r U a }
  have hA : IsSymmetricInput X r A :=
    ⟨rfl, rfl, fun n ↦ heq_of_eq (monomialDecomposition_ι X r n)⟩
  exact ⟨A, hA, fun B hB ↦ symmetricInput_unique X r B A hB hA⟩

/-- The uniquely specified symmetric algebra input, with its symmetric-degree grading. -/
def algebra : RelativeProjAlgebra X := (existsUnique_symmetricInput X r).exists.choose

/-- Relative Proj with all its compatible affine restriction isomorphisms. The existence
theorem determines this realization up to the unique chart-preserving isomorphism. -/
def construction : RelativeProjData (algebra X r) := (algebra X r).realization

/-- Relative projective `r`-space over `X`, using symmetric-algebra relative Proj. -/
def scheme : Scheme.{u} := (construction X r).proj

/-- The structural morphism of relative projective space. -/
def π : scheme X r ⟶ X := (construction X r).π

/-- The specified equality with the constructed symmetric algebra sheaf. -/
theorem algebra_eq : (algebra X r).algebra.obj =
    SymmetricAlgebraSheaf.algebra (freeModule X r) := by
  exact (existsUnique_symmetricInput X r).exists.choose_spec.1

/-- The coordinate section in the actual graded section ring used for local Proj. -/
def coordinate (V : X.affineOpens) (i : Fin (r + 1)) : (algebra X r).sections V :=
  (eqToHom (algebra_eq X r).symm).right.hom.app (op V.1) (generator X r V.1 i)

set_option backward.isDefEq.respectTransparency.types false in
/-- On an affine base the polynomial identification is uniquely determined by its
coefficients and its ordered degree-one generators. -/
theorem existsUnique_affinePolynomialEquiv (V : X.affineOpens) :
    ∃! e : MvPolynomial (Fin (r + 1)) (X.presheaf.obj (op V.1)) ≃+*
        (algebra X r).sections V,
      (∀ a : X.presheaf.obj (op V.1),
        e (MvPolynomial.C a) = (algebra X r).algebra.obj.hom.hom.app (op V.1) a) ∧
      (∀ i : Fin (r + 1), e (MvPolynomial.X i) = coordinate X r V i) := by
  obtain ⟨e, he⟩ := affinePolynomialEquiv_exists_aux X r V
    (algebra X r).algebra.obj (algebra_eq X r)
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply RingEquiv.toRingHom_injective
  exact MvPolynomial.ringHom_ext
    (fun a ↦ (he'.1 a).trans (he.1 a).symm)
    (fun i ↦ (he'.2 i).trans (he.2 i).symm)

/-- The canonical polynomial identification, preserving coefficients and coordinates. -/
def affinePolynomialEquiv (V : X.affineOpens) :
    MvPolynomial (Fin (r + 1)) (X.presheaf.obj (op V.1)) ≃+* (algebra X r).sections V :=
  (existsUnique_affinePolynomialEquiv X r V).exists.choose

private theorem affinePolynomialEquiv_C (V : X.affineOpens) (a : Γ(X, V.1)) :
    affinePolynomialEquiv X r V (MvPolynomial.C a) =
      (algebra X r).algebra.obj.hom.hom.app (op V.1) a :=
  (existsUnique_affinePolynomialEquiv X r V).exists.choose_spec.1 a

private theorem affinePolynomialEquiv_X (V : X.affineOpens) (i : Fin (r + 1)) :
    affinePolynomialEquiv X r V (MvPolynomial.X i) = coordinate X r V i :=
  (existsUnique_affinePolynomialEquiv X r V).exists.choose_spec.2 i

set_option backward.isDefEq.respectTransparency.types false in
private theorem homogeneous_range_aux
    (B : X.CommAlgebraSheaf) (M : X.Modules) (f : M ⟶ B.toModule)
    (hB : B = SymmetricAlgebraSheaf.algebra (freeModule X r)) (n : ℕ)
    (hM : M = SheafOfModules.free (R := X.ringCatSheaf) (monomials.{u} r n))
    (hf : HEq f (monomialMap X r n)) (U : X.Opens) :
    LinearMap.range (f.val.app (op U)).hom = Submodule.span Γ(X, U)
      (Set.range fun a : monomials.{u} r n ↦
        (show B.toModule.val.obj (op U) from
          (eqToHom hB.symm).right.hom.app (op U) (monomial X r n a U))) := by
  subst B
  subst M
  cases hf
  let _ := monomialFintype r n
  classical
  rw [freeMap_range]
  apply congrArg (Submodule.span Γ(X, U))
  apply congrArg Set.range
  funext a
  have h := congrArg (fun t ↦ t.val.app (op U) (1 : X.ringCatSheaf.obj.obj (op U)))
    (Sigma.ι_comp_desc (fun a ↦ monomialUnit X r n a) a)
  change (monomialMap X r n).val.app (op U)
      ((SheafOfModules.ιFree (R := X.ringCatSheaf) a).val.app (op U)
        (1 : X.ringCatSheaf.obj.obj (op U))) =
    (monomialUnit X r n a).val.app (op U) (1 : X.ringCatSheaf.obj.obj (op U)) at h
  rw [h]
  exact one_smul _ _

set_option backward.isDefEq.respectTransparency.types false in
private theorem polynomial_monomial_span (V : X.affineOpens) (n : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin (r + 1)) Γ(X, V.1) n =
      Submodule.span Γ(X, V.1) (Set.range fun a : monomials.{u} r n ↦
        ∏ i : Fin (r + 1), (MvPolynomial.X i : MvPolynomial (Fin (r + 1))
          Γ(X, V.1)) ^ a.down.val i) := by
  classical
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
    AddMonoidAlgebra.supported_eq_span_single]
  congr 1
  ext p
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨⟨⟨d, (Finsupp.degree_eq_sum d).symm.trans hd⟩⟩, ?_⟩
    change ∏ i : Fin (r + 1), (MvPolynomial.X i : MvPolynomial (Fin (r + 1))
      Γ(X, V.1)) ^ d i = MvPolynomial.monomial d 1
    rw [MvPolynomial.prod_X_pow]
    apply congrArg (fun d ↦ MvPolynomial.monomial d (1 : Γ(X, V.1)))
    ext i
    simp
  · rintro ⟨a, rfl⟩
    let d : Fin (r + 1) →₀ ℕ := Finsupp.equivFunOnFinite.symm a.down.val
    refine ⟨d, ?_, ?_⟩
    · change d.degree = n
      rw [Finsupp.degree_eq_sum]
      exact a.down.property
    · change MvPolynomial.monomial d 1 = ∏ i : Fin (r + 1),
        (MvPolynomial.X i : MvPolynomial (Fin (r + 1)) Γ(X, V.1)) ^ a.down.val i
      rw [MvPolynomial.prod_X_pow]
      apply congrArg (fun d ↦ MvPolynomial.monomial d (1 : Γ(X, V.1)))
      ext i
      simp [d]

set_option backward.isDefEq.respectTransparency.types false in
/-- Symmetric degree is polynomial total degree in the standard coordinates. -/
theorem affinePolynomial_homogeneous (V : X.affineOpens) (n : ℕ)
    (p : MvPolynomial (Fin (r + 1)) (X.presheaf.obj (op V.1))) :
    affinePolynomialEquiv X r V p ∈ (algebra X r).sectionGrade V n ↔
      p ∈ MvPolynomial.homogeneousSubmodule (Fin (r + 1))
        (X.presheaf.obj (op V.1)) n := by
  classical
  let L : MvPolynomial (Fin (r + 1)) Γ(X, V.1) ≃ₗ[Γ(X, V.1)]
      (algebra X r).algebra.obj.toModule.val.obj (op V.1) :=
    { toEquiv := (affinePolynomialEquiv X r V).toEquiv
      map_add' := fun a b ↦ (affinePolynomialEquiv X r V).map_add a b
      map_smul' := by
        intro a q
        rw [Algebra.smul_def]
        change affinePolynomialEquiv X r V (MvPolynomial.C a * q) =
          (algebra X r).algebra.obj.hom.hom.app (op V.1) a *
            affinePolynomialEquiv X r V q
        rw [map_mul, affinePolynomialEquiv_C] }
  have hs := (existsUnique_symmetricInput X r).exists.choose_spec
  have hr := homogeneous_range_aux X r (algebra X r).algebra.obj
    ((algebra X r).piece n)
    (Sigma.ι (algebra X r).piece n ≫ (algebra X r).decomposition.hom)
    hs.1 n (congrFun hs.2.1 n) (hs.2.2 n) V.1
  have hm (a : monomials.{u} r n) :
      L (∏ i : Fin (r + 1), (MvPolynomial.X i :
        MvPolynomial (Fin (r + 1)) Γ(X, V.1)) ^ a.down.val i) =
      (eqToHom hs.1.symm).right.hom.app (op V.1) (monomial X r n a V.1) := by
    change affinePolynomialEquiv X r V _ = _
    simp only [map_prod, map_pow, affinePolynomialEquiv_X, monomial, coordinate]
    rfl
  have he : LinearMap.range
      ((Sigma.ι (algebra X r).piece n ≫ (algebra X r).decomposition.hom).val.app
        (op V.1)).hom =
      (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) Γ(X, V.1) n).map
        L.toLinearMap := by
    rw [hr, polynomial_monomial_span, Submodule.map_span, ← Set.range_comp]
    apply congrArg (Submodule.span Γ(X, V.1))
    apply congrArg Set.range
    exact funext (fun a ↦ (hm a).symm)
  change L p ∈ LinearMap.range
    ((Sigma.ι (algebra X r).piece n ≫ (algebra X r).decomposition.hom).val.app
      (op V.1)).hom ↔ p ∈ MvPolynomial.homogeneousSubmodule (Fin (r + 1)) Γ(X, V.1) n
  rw [he]
  constructor
  · rintro ⟨q, hq, hqp⟩
    exact L.injective hqp ▸ hq
  · intro hp
    exact ⟨p, hp, rfl⟩

/-- The standard open on an affine local model, using the actual coordinate section. -/
def localStandardOpen (V : X.affineOpens) (i : Fin (r + 1)) :
    ((algebra X r).localProj V).Opens :=
  Proj.basicOpen ((algebra X r).sectionGrade V) (coordinate X r V i)

/-- The global standard open is the union of the specified opens over all affine bases.
There is no independent choice of opens or charts. -/
def standardOpen (i : Fin (r + 1)) : (scheme X r).Opens :=
  ⨆ V : X.affineOpens,
    ((π X r ⁻¹ᵁ V.1).ι.opensFunctor.obj
      ((TopologicalSpace.Opens.map ((construction X r).restrictionIso V).hom.base).obj
        (localStandardOpen X r V i)))

private theorem coordinate_restriction {V W : X.affineOpens} (h : W ≤ V)
    (i : Fin (r + 1)) :
    (algebra X r).restriction h (coordinate X r V i) = coordinate X r W i := by
  let t := (eqToHom (algebra_eq X r).symm).right.hom
  have ht := CategoryTheory.congr_fun (t.naturality (homOfLE (X := X.Opens) h).op)
    (generator X r V.1 i)
  change t.app (op W.1)
      ((SymmetricAlgebraSheaf.algebra (freeModule X r)).right.obj.map (homOfLE (X := X.Opens) h).op
        (generator X r V.1 i)) =
    (algebra X r).restriction h (coordinate X r V i) at ht
  rw [generator_restriction] at ht
  exact ht.symm

private theorem localStandardOpen_compat {V W : X.affineOpens} (h : W ≤ V)
    (i : Fin (r + 1)) :
    (scheme X r).homOfLE ((π X r).preimage_mono h) ⁻¹ᵁ
        (((construction X r).restrictionIso V).hom ⁻¹ᵁ localStandardOpen X r V i) =
      ((construction X r).restrictionIso W).hom ⁻¹ᵁ localStandardOpen X r W i := by
  have hc : (scheme X r).homOfLE ((π X r).preimage_mono h) ≫
      ((construction X r).restrictionIso V).hom =
    ((construction X r).restrictionIso W).hom ≫ (algebra X r).localTransition h := by
    rw [← (construction X r).restriction_compatibility V W h, Iso.hom_inv_id_assoc]
    rfl
  rw [← Scheme.Hom.comp_preimage, hc, Scheme.Hom.comp_preimage]
  congr 1
  change Proj.map _ _ ⁻¹ᵁ Proj.basicOpen _ (coordinate X r V i) = _
  rw [Proj.map_preimage_basicOpen, coordinate_restriction]
  rfl

/-- The global standard open restricts to the specified local standard open on every
affine base. The chart map is therefore the inherited relative-Proj chart map. -/
theorem standardOpen_restrict (V : X.affineOpens) (i : Fin (r + 1)) :
    (TopologicalSpace.Opens.map (π X r ⁻¹ᵁ V.1).ι.base).obj (standardOpen X r i) =
      (TopologicalSpace.Opens.map ((construction X r).restrictionIso V).hom.base).obj
        (localStandardOpen X r V i) := by
  ext x
  change x.1 ∈ standardOpen X r i ↔
    x ∈ ((construction X r).restrictionIso V).hom ⁻¹ᵁ localStandardOpen X r V i
  constructor
  · intro hx
    obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨y, hy, hyx⟩ := hW
    obtain ⟨Z, hZ, hxZ, hZVW⟩ := exists_isAffineOpen_mem_and_subset
      (show (π X r) x.1 ∈ V.1 ⊓ W.1 from ⟨x.2, by
        rw [← hyx]
        exact y.2⟩)
    let Z' : X.affineOpens := ⟨Z, hZ⟩
    have hZV : Z' ≤ V := fun z hz ↦ (hZVW hz).1
    have hZW : Z' ≤ W := fun z hz ↦ (hZVW hz).2
    let z : (π X r ⁻¹ᵁ Z).toScheme := ⟨x.1, hxZ⟩
    have hzy : (scheme X r).homOfLE ((π X r).preimage_mono hZW) z = y := by
      apply Subtype.ext
      rw [Scheme.homOfLE_apply]
      exact hyx.symm
    have hzx : (scheme X r).homOfLE ((π X r).preimage_mono hZV) z = x := by
      apply Subtype.ext
      rw [Scheme.homOfLE_apply]
    have hz : z ∈ ((construction X r).restrictionIso Z').hom ⁻¹ᵁ
        localStandardOpen X r Z' i := by
      rw [← localStandardOpen_compat X r hZW i]
      exact (show (scheme X r).homOfLE ((π X r).preimage_mono hZW) z ∈
        ((construction X r).restrictionIso W).hom ⁻¹ᵁ localStandardOpen X r W i by
          rw [hzy]
          exact hy)
    rw [← localStandardOpen_compat X r hZV i] at hz
    have hz' : (scheme X r).homOfLE ((π X r).preimage_mono hZV) z ∈
        ((construction X r).restrictionIso V).hom ⁻¹ᵁ localStandardOpen X r V i := hz
    rw [hzx] at hz'
    exact hz'
  · intro hx
    apply TopologicalSpace.Opens.mem_iSup.mpr
    exact ⟨V, x, hx, rfl⟩

end AlgebraicGeometry.RelativeProjectiveSpace
