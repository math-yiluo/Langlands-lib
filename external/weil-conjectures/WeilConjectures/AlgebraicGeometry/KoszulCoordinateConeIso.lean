/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import WeilConjectures.RingTheory.KoszulTensorConeCoordinates
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import WeilConjectures.Algebra.Homology.ChainConeCoordinatesIso

/-! # A Koszul coordinate as a scalar mapping cone

Source: Stacks Project, Tag 0629.
(blueprint: lem-pc-koszul-coordinate-cone-iso).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

private theorem contract_reindex (A : Type u) [CommRing A] (r : ℕ)
    (g : Fin r → A) (e : Equiv.Perm (Fin r))
    (x : ExteriorAlgebra A (Fin r →₀ A)) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm A (Fin r →₀ A)))
      (Finsupp.linearCombination A g)
      (ExteriorAlgebra.map (Finsupp.lmapDomain A A e) x) =
    ExteriorAlgebra.map (Finsupp.lmapDomain A A e)
      (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm A (Fin r →₀ A)))
        (Finsupp.linearCombination A (g ∘ e)) x) := by
  have hφ (v : Fin r →₀ A) :
      Finsupp.linearCombination A g (Finsupp.lmapDomain A A e v) =
        Finsupp.linearCombination A (g ∘ e) v :=
    LinearMap.congr_fun (Finsupp.linearCombination_comp_lmapDomain A (v' := g) e) v
  induction x using CliffordAlgebra.left_induction with
  | algebraMap c => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul v x hx =>
    simp only [map_mul, ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul,
      hφ, map_sub, map_smul, hx]

private theorem exterior_map_coe (A : Type u) [CommRing A] (r n : ℕ)
    (l : (Fin r →₀ A) →ₗ[A] (Fin r →₀ A)) (x : ⋀[A]^n (Fin r →₀ A)) :
    (exteriorPower.map n l x : ExteriorAlgebra A (Fin r →₀ A)) =
      ExteriorAlgebra.map l (x : ExteriorAlgebra A (Fin r →₀ A)) := by
  have h : (⋀[A]^n (Fin r →₀ A)).subtype.comp (exteriorPower.map n l) =
      (ExteriorAlgebra.map l).toLinearMap.comp (⋀[A]^n (Fin r →₀ A)).subtype := by
    apply exteriorPower.linearMap_ext
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      exteriorPower.map_apply_ιMulti, AlgHom.toLinearMap_apply]
    exact (ExteriorAlgebra.map_apply_ιMulti l v).symm
  exact LinearMap.congr_fun h x

private theorem koszul_reindex_iso (A : Type u) [CommRing A] (r : ℕ)
    (g : Fin r → A) (e : Equiv.Perm (Fin r)) :
    Nonempty (ExteriorAlgebra.koszulComplex A r (g ∘ e) ≅
      ExteriorAlgebra.koszulComplex A r g) := by
  let l : (Fin r →₀ A) ≃ₗ[A] (Fin r →₀ A) := Finsupp.mapDomain.linearEquiv A A e
  let t (n : ℕ) : (⋀[A]^n (Fin r →₀ A)) ≃ₗ[A] (⋀[A]^n (Fin r →₀ A)) :=
    LinearEquiv.ofLinearMap (exteriorPower.map n l.toLinearMap)
      (exteriorPower.map n l.symm.toLinearMap)
      (by rw [← exteriorPower.map_comp, l.comp_symm, exteriorPower.map_id])
      (by rw [← exteriorPower.map_comp, l.symm_comp, exteriorPower.map_id])
  refine ⟨HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ LinearEquiv.toModuleIso (t n)) ?_⟩
  rintro n m hnm
  have h : m + 1 = n := hnm
  subst n
  dsimp only [ExteriorAlgebra.koszulComplex]
  simp only [ChainComplex.of_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ExteriorAlgebra.koszulBoundary A r g m (exteriorPower.map (m + 1)
      l.toLinearMap x) =
    exteriorPower.map m l.toLinearMap (ExteriorAlgebra.koszulBoundary A r (g ∘ e) m x)
  apply Subtype.ext
  simp only [ExteriorAlgebra.koszulBoundary, LinearMap.codRestrict_apply,
    LinearMap.comp_apply, exterior_map_coe]
  rw [show (⋀[A]^(m + 1) (Fin r →₀ A)).subtype
      (exteriorPower.map (m + 1) l.toLinearMap x) =
      ExteriorAlgebra.map l.toLinearMap (x : ExteriorAlgebra A (Fin r →₀ A)) from
    exterior_map_coe A r (m + 1) l.toLinearMap x]
  exact contract_reindex A r g e x

private theorem rid_naturality (A : Type u) [CommRing A]
    {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (l : M →ₗ[A] N) (x : TensorProduct A M A) :
    TensorProduct.rid A N (l.rTensor A x) = l (TensorProduct.rid A M x) := by
  induction x using TensorProduct.inductionOn with
  | tmul x a => simp
  | add x y hx hy => simp only [map_add, hx, hy]

set_option backward.isDefEq.respectTransparency false in
private theorem koszul_cone_coordinates (A : Type u) [CommRing A] (r : ℕ)
    (f : Fin (r + 1) → A) :
    let L := ExteriorAlgebra.koszulComplex A r (fun j ↦ f j.castSucc)
    let K := ExteriorAlgebra.koszulComplex A (r + 1) f
    ∃ (e₀ : K.X 0 ≃ₗ[A] L.X 0)
      (e : ∀ n : ℕ, K.X (n + 1) ≃ₗ[A] L.X (n + 1) × L.X n),
      (∀ x : K.X 1, e₀ (K.d 1 0 x) =
        L.d 1 0 (e 0 x).1 + f (Fin.last r) • (e 0 x).2) ∧
      (∀ (n : ℕ) (x : K.X (n + 2)), e n (K.d (n + 2) (n + 1) x) =
        (L.d (n + 2) (n + 1) (e (n + 1) x).1 +
          f (Fin.last r) • (e (n + 1) x).2,
          -L.d (n + 1) n (e (n + 1) x).2)) := by
  obtain ⟨t₀, t, h₀, hd⟩ := ExteriorAlgebra.exists_koszulTensorConeCoordinates A f
  let u (n : ℕ) := TensorProduct.rid A (⋀[A]^n (Fin r →₀ A))
  let v (n : ℕ) := TensorProduct.rid A (⋀[A]^n (Fin (r + 1) →₀ A))
  let e₀ := (v 0).symm.trans (t₀.trans (u 0))
  let e (n : ℕ) := (v (n + 1)).symm.trans
    ((t n).trans ((u (n + 1)).prodCongr (u n)))
  refine ⟨e₀, e, ?_, ?_⟩
  · intro x
    have h := congrArg (u 0) (h₀ ((v 1).symm x))
    dsimp only [ExteriorAlgebra.koszulComplexTensor, ExteriorAlgebra.koszulComplex] at h ⊢
    erw [ChainComplex.of_d _ _ 0, ChainComplex.of_d _ _ 0] at h
    erw [ChainComplex.of_d _ _ 0, ChainComplex.of_d _ _ 0]
    simp only [Nat.reduceAdd, ConcreteCategory.hom_ofHom, TensorProduct.rid_symm_apply,
      LinearMap.rTensor_tmul, map_add, rid_naturality, map_smul, LinearEquiv.trans_apply,
      LinearEquiv.prodCongr, AddEquiv.prodCongr, Equiv.prodCongr, AddHom.toFun_eq_coe,
      LinearMap.coe_toAddHom, LinearEquiv.coe_coe, LinearEquiv.invFun_eq_symm, Equiv.coe_fn_mk,
      Equiv.symm_mk, AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
      AddEquiv.coe_mk, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm, AddEquiv.symm_mk,
      LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Prod.map_fst, Prod.map_snd,
      u, v, e₀, e] at h ⊢
    convert h using 1
  · intro n x
    have h := congrArg ((u (n + 1)).prodCongr (u n)) (hd n ((v (n + 2)).symm x))
    dsimp only [ExteriorAlgebra.koszulComplexTensor, ExteriorAlgebra.koszulComplex] at h ⊢
    erw [ChainComplex.of_d _ _ (n + 1), ChainComplex.of_d _ _ (n + 1),
      ChainComplex.of_d _ _ n] at h
    erw [ChainComplex.of_d _ _ (n + 1), ChainComplex.of_d _ _ (n + 1),
      ChainComplex.of_d _ _ n]
    simp only [LinearEquiv.prodCongr, AddEquiv.prodCongr, Equiv.prodCongr,
      AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
      LinearEquiv.invFun_eq_symm, Equiv.coe_fn_mk, Equiv.symm_mk, AddEquiv.toEquiv_eq_coe,
      Equiv.toFun_as_coe, EquivLike.coe_coe, AddEquiv.coe_mk, Equiv.invFun_as_coe,
      AddEquiv.coe_toEquiv_symm, AddEquiv.symm_mk, ConcreteCategory.hom_ofHom,
      TensorProduct.rid_symm_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_mk,
      LinearMap.coe_mk, AddHom.coe_mk, Prod.map_apply, map_add, rid_naturality, map_smul,
      map_neg, LinearEquiv.trans_apply, Prod.map_fst, Prod.map_snd, u, v, e] at h ⊢
    convert h using 1

/-- The sheafified Koszul complex, with one distinguished coordinate, is the
mapping cone of multiplication by that coordinate on the remaining complex.
Source: Stacks Project, More on Algebra, Tags 0628 and 0629.
(blueprint: lem-pc-koszul-coordinate-cone-iso).

Proof: Reindex the standard basis by the equivalence which places `i` last
and sends the preceding coordinates to `i.succAbove`. Exterior powers of this
basis change commute with contraction against the reindexed linear form,
and therefore give an isomorphism of Koszul complexes. For the last coordinate,
split every exterior power according to whether it contains that coordinate.
Writing the last basis vector first, the degree `q` identification is
`wedge^q(prefix) + wedge^(q-1)(prefix)`. Contraction has matrix
`(x,y) |-> (d x + a y, -d y)`, by the graded Leibniz formula. In degree zero
only the first summand remains. These are exactly the mapping-cone terms and
differentials after extending chain degree `q` to cochain degree `-q`.
Termwise sheafification preserves these finite biproducts and the matrix
formulas because it is additive, giving the stated cochain isomorphism.
The construction includes `r = 0`, zero generators and the zero ring. -/
theorem koszul_coordinate_cone_iso
    (A : Type u) [CommRing A] (r : ℕ) (g : Fin (r + 1) → A)
    (i : Fin (r + 1)) (a : A) :
    let T := @Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
      _ _ _ _ (tilde.functor (.of A))
      ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)
    let P := (ExteriorAlgebra.koszulComplex A r (fun j ↦ g (i.succAbove j))).extend
      ComplexShape.embeddingDownNat
    Nonempty (T.obj ((ExteriorAlgebra.koszulComplex A (r + 1)
        (Function.update g i a)).extend ComplexShape.embeddingDownNat) ≅
      CochainComplex.mappingCone (T.map (a • 𝟙 P))) := by
  let : (tilde.functor (.of A)).Additive := ⟨by intros; exact tilde.map_add _ _⟩
  let : (tilde.functor (.of A)).PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  dsimp only
  let p : Equiv.Perm (Fin (r + 1)) :=
    (finSuccEquiv' (Fin.last r)).trans (finSuccEquiv' i).symm
  let f := Function.update g i a ∘ p
  have hp (j : Fin r) : p j.castSucc = i.succAbove j := by
    simp [p, finSuccEquiv'_last_apply_castSucc]
  have hl : p (Fin.last r) = i := by simp [p]
  have hprefix : (fun j : Fin r ↦ f j.castSucc) = (fun j ↦ g (i.succAbove j)) := by
    funext j
    simp [f, hp, Fin.succAbove_ne]
  have hlast : f (Fin.last r) = a := by simp [f, hl]
  obtain ⟨e₀, e, h₀, hd⟩ := koszul_cone_coordinates A r f
  obtain ⟨c⟩ := ChainComplex.scalarCone_iso_of_coordinates A
    (ExteriorAlgebra.koszulComplex A (r + 1) f)
    (ExteriorAlgebra.koszulComplex A r (fun j ↦ f j.castSucc))
    (f (Fin.last r)) e₀ e h₀ hd
  obtain ⟨b⟩ := koszul_reindex_iso A (r + 1) (Function.update g i a) p
  let b' := (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)).mapIso b.symm
  rw [hprefix, hlast] at c
  exact ⟨((tilde.functor (.of A)).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
    (b' ≪≫ c) ≪≫ CochainComplex.mappingCone.mapHomologicalComplexIso
      (a • 𝟙 ((ExteriorAlgebra.koszulComplex A r (fun j ↦ g (i.succAbove j))).extend
        ComplexShape.embeddingDownNat)) (tilde.functor (.of A))⟩

end AlgebraicGeometry
