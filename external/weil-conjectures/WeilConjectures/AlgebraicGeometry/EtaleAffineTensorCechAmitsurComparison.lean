/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleFiniteAffineCechBasis
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.RingTheory.FaithfullyFlat.Amitsur

import WeilConjectures.AlgebraicGeometry.EtaleOverCoproductCechComparison
import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorAmitsur

/-! # Affine tensor-section Čech complexes as Amitsur complexes
Source: Stacks Project, Tags 03OZ and 03P2, affine-case proof.
(blueprint: new-etale-affine-tensor-cech-amitsur-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

/-- The finite affine tensor-section Čech complex is a lifted Amitsur complex.
Source: Stacks Project, Tag 03OZ and Tag 03P2, proof in the affine case.
(blueprint: new-etale-affine-tensor-cech-amitsur-comparison)

Proof: form W as the finite scheme coproduct of the V i, with its canonical map to U.
The covering sieve makes this map surjective. It is étale by locality at the source,
and W is affine since a finite coproduct of affine schemes is affine. The affine
flat-and-surjective criterion makes g.appTop faithfully flat. Thus B = Γ(W, O_W)
and a = g.appTop are explicit constructions, independent of any existence theorem.
Apply nonempty_etale_over_coproduct_cech_iso to the lifted tensor-section sheaf,
using the coproduct cone and the coprojection factorization equations. Apply
nonempty_etale_affine_singleton_tensor_amitsur_iso to the affine map W → U and
compose the resulting complex isomorphisms. The first comparison uses only the
sheaf property and coproduct distribution; the second uses affine fibre products
and the pure-tensor pullback formula, without faithful flatness. If I is empty,
W is the empty coproduct; surjectivity then forces U empty. The same constructions
and the two comparison theorems apply, without a separate choice of zero rings. -/
theorem exists_etaleTensorSectionsSheaf_ulift_cech_amitsur_iso
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Etale) (I : Type (u + 1)) (V : I → X.Etale) (f : ∀ i : I, V i ⟶ U)
    (hf : finiteAffineEtaleCechCover X U I V f) :
    ∃ (B : CommRingCat.{u}) (a : Γ(U.left, ⊤) →+* B),
      letI : Algebra Γ(U.left, ⊤) B := a.toAlgebra
      Module.FaithfullyFlat Γ(U.left, ⊤) B ∧
        Nonempty (((cechComplexFunctor fun i : I ↦ Over.mk (f i)).obj
          ((Over.forget U).op ⋙
            ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
              (Modules.etaleTensorSectionsSheaf F)).obj)) ≅
          (((forget₂ (ModuleCat.{u} Γ(U.left, ⊤)) AddCommGrpCat.{u}) ⋙
            AddCommGrpCat.uliftFunctor.{u + 1, u}).mapHomologicalComplex (.up ℕ)).obj
              (Algebra.TensorProduct.amitsurComplex Γ(U.left, ⊤) B
                Γ((Modules.tensorPullback U.hom).obj F, ⊤))) := by
  classical
  let : IsAffine U.left := hf.1
  let : Finite I := hf.2.1
  let : ∀ i : I, IsAffine (V i).left := hf.2.2.1
  let v : ∀ i : I, (V i).left ⟶ U.left := fun i ↦ (f i).left
  have hv : Etale (Sigma.desc v) :=
    IsZariskiLocalAtSource.sigmaDesc (fun i ↦ inferInstance)
  let W : X.Etale := Etale.mk (Sigma.desc v ≫ U.hom)
  let g : W ⟶ U := MorphismProperty.Over.homMk (Sigma.desc v)
  let c : ∀ i : I, V i ⟶ W := fun i ↦
    MorphismProperty.Over.homMk (Sigma.ι (fun i ↦ (V i).left) i) (by
      change Sigma.ι (fun i ↦ (V i).left) i ≫ (Sigma.desc v ≫ U.hom) = (V i).hom
      rw [← Category.assoc, Sigma.ι_comp_desc]
      exact MorphismProperty.Over.w (f i))
  have hc : IsColimit (Cofan.mk W.left (fun i ↦ (c i).left)) :=
    coproductIsCoproduct _
  have hw (i : I) : c i ≫ g = f i := by
    apply MorphismProperty.Over.Hom.ext
    exact Sigma.ι_comp_desc v i
  have hs : Surjective (Sigma.desc v) := by
    apply Surjective.sigmaDesc_of_union_range_eq_univ
    exact (ofArrows_mem_smallEtaleTopology_iff f).mp hf.2.2.2
  have hW : IsAffine W.left := by
    change IsAffine (∐ fun i : I ↦ (V i).left)
    infer_instance
  let : IsAffine W.left := hW
  have hff : RingHom.FaithfullyFlat g.left.appTop.hom :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g.left).mp
      ⟨inferInstance, hs⟩
  refine ⟨Γ(W.left, ⊤), g.left.appTop.hom, hff, ?_⟩
  obtain ⟨e₁⟩ := nonempty_etale_over_coproduct_cech_iso X U I V f W g c hc hw
    ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
      (Modules.etaleTensorSectionsSheaf F))
  obtain ⟨e₂⟩ := nonempty_etale_affine_singleton_tensor_amitsur_iso X F U W g hf.1 hW
  exact ⟨e₁ ≪≫ e₂⟩

end AlgebraicGeometry.Scheme
