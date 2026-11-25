/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.RingTheory.FaithfullyFlat.Amitsur
import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorCofaces

/-! # Singleton affine tensor-section Čech complexes
Source: Stacks Project, Tag 03P2, affine tensor-product calculation.
(blueprint: new-etale-affine-singleton-tensor-amitsur).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

/-- The singleton Čech complex of an affine map is its tensor Amitsur complex.
Source: Stacks Project, Tag 03P2, identification before the faithfully-flat exactness argument;
Tag 03OZ, singleton-cover calculation.
(blueprint: new-etale-affine-singleton-tensor-amitsur)

Proof: set A = Γ(U.left, O), B = Γ(W.left, O), M = Γ(U.left, U.hom*F).
Compare tensorPullback with Mathlib pullback by uniqueness of left adjoints to pushforward;
the unit-compatible comparison transports quasi-coherence from the proved pullback instance.
The unit-normalized composition isomorphism identifies
restriction of the tensor-section presheaf from X with sections of the pullback of F to U.
The degree p categorical product is the (p+1)-fold fibre product of W over U. Affine charts
and the affine fibre-product formula identify its ring with the indexed tensor product of
(p+1) copies of B over A, compatibly with projections. The affine pullback-sections formula
then identifies sections with M tensor that ring. On pure tensors, pullback along a projection
omitting factor j inserts 1 in factor j; the unit equation for the composition comparison
ensures this is also the restriction of the original tensor-section presheaf. Pure tensors
generate, so the coface maps agree with the Amitsur cofaces. In each degree the product over
maps Fin (p+1) to Fin 1 is a singleton product; evaluation at its unique index identifies it
with this section group. Apply ULift to the additive isomorphisms and their inverses. They
commute with every coface and hence with the alternating differentials, giving the asserted
complex isomorphism. This calculation uses neither flatness nor surjectivity. For empty W,
B is the zero ring and all terms on both sides vanish. For an identity map it is the usual
A tensor-power identification, with exactly the alternating identity cofaces. -/
theorem nonempty_etale_affine_singleton_tensor_amitsur_iso
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) (hU : IsAffine U.left) (hW : IsAffine W.left) :
    letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
    Nonempty (((cechComplexFunctor fun _ : Fin 1 ↦ Over.mk g).obj
      ((Over.forget U).op ⋙
        ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
          (Modules.etaleTensorSectionsSheaf F)).obj)) ≅
      (((forget₂ (ModuleCat.{u} Γ(U.left, ⊤)) AddCommGrpCat.{u}) ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u}).mapHomologicalComplex (.up ℕ)).obj
          (Algebra.TensorProduct.amitsurComplex Γ(U.left, ⊤) Γ(W.left, ⊤)
            Γ((Modules.tensorPullback U.hom).obj F, ⊤))) := by
  classical
  let : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
  obtain ⟨e, he⟩ := exists_singletonTensorDegreeComparison X F U W g hU hW
  have hc := singletonTensorDegreeComparison_coface X F U W g e he
  refine ⟨(HomologicalComplex.Hom.isoOfComponents e ?_).symm⟩
  intro i j hij
  have hj : i + 1 = j := hij
  subst j
  change (e i).hom ≫ ((AlgebraicTopology.alternatingCofaceMapComplex _).obj
    (singletonTensorCechCosimplicial X F U W g)).d i (i + 1) =
      (singletonTensorForget U.left).map
        ((Algebra.TensorProduct.amitsurComplex Γ(U.left, ⊤) Γ(W.left, ⊤)
          Γ((Modules.tensorPullback U.hom).obj F, ⊤)).d i (i + 1)) ≫ (e (i + 1)).hom
  simp only [Algebra.TensorProduct.amitsurComplex,
    AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d]
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD,
    Functor.map_sum, Functor.map_zsmul, Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  exact Finset.sum_congr rfl (fun k _ ↦ congrArg (fun f ↦ (-1 : ℤ) ^ k.val • f) (hc i k))

end AlgebraicGeometry.Scheme
