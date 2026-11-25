/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization
import WeilConjectures.AlgebraicGeometry.EtaleTensorSections

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

noncomputable section


-- Use the predicate's existing limit witnesses: fresh proofs force the kernel
-- to compare large types containing the entire tensor-pullback construction.
-- These generated names must be updated if the normalization file is refactored.
set_option linter.auxLemma false in
attribute [local instance] IsSingletonTensorDegreeComparison._proof_1
  IsSingletonTensorDegreeComparison._proof_2

private def tensorScalarMap {A B C M N : Type u}
    [CommSemiring A] [CommSemiring B] [CommSemiring C] [Algebra A B] [Algebra A C]
    [AddCommMonoid M] [AddCommMonoid N] [Module A M] [Module C N]
    (t : B →ₐ[A] C) (r : M →+ N)
    (hr : ∀ (a : A) (m : M), r (a • m) = algebraMap A C a • r m) : M ⊗[A] B →+ N :=
  (TensorProduct.lift (LinearMap.mk₂'ₛₗ (algebraMap A C) (algebraMap A C) (fun m b ↦ t b • r m)
    (by intros; simp [smul_add])
    (by intro a m b; rw [hr]; exact smul_comm (t b) (algebraMap A C a) (r m))
    (by intros; simp [add_smul])
    (by
      intro a m b
      rw [map_smul, Algebra.smul_def]
      exact mul_smul (algebraMap A C a) (t b) (r m)))).toAddMonoidHom

private theorem tensorScalarMap_tmul {A B C M N : Type u}
    [CommSemiring A] [CommSemiring B] [CommSemiring C] [Algebra A B] [Algebra A C]
    [AddCommMonoid M] [AddCommMonoid N] [Module A M] [Module C N]
    (t : B →ₐ[A] C) (r : M →+ N)
    (hr : ∀ (a : A) (m : M), r (a • m) = algebraMap A C a • r m) (m : M) (b : B) :
    tensorScalarMap t r hr (m ⊗ₜ[A] b) = t b • r m := rfl

private theorem existsTensorSectionHom {ι : Type} [Fintype ι]
    {A B C M N : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module C N]
    (σ : A →+* C) (q : ι → B →+* C)
    (hq : ∀ k a, q k (algebraMap A B a) = σ a)
    (r : M →+ N) (hr : ∀ (a : A) (m : M), r (a • m) = σ a • r m) :
    ∃ c : (M ⊗[A] (⨂[A] _ : ι, B)) →+ N,
      ∀ m b, c (m ⊗ₜ[A] PiTensorProduct.tprod A b) = (∏ k, q k (b k)) • r m := by
  let : Algebra A C := σ.toAlgebra
  let q' (k : ι) : B →ₐ[A] C := ⟨q k, hq k⟩
  let t := PiTensorProduct.liftCommAlgHom q'
  let c := tensorScalarMap t r hr
  refine ⟨c, fun m b ↦ ?_⟩
  exact (tensorScalarMap_tmul t r hr m (PiTensorProduct.tprod A b)).trans
    (congrArg (fun z : C ↦ z • r m) (PiTensorProduct.liftCommAlgHom_tprod q' b))

private def uliftPiHom {I : Type} {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    (c : M →+ N) : AddCommGrpCat.of (ULift.{u + 1} M) ⟶
      ∏ᶜ (fun _ : I ↦ AddCommGrpCat.of (ULift.{u + 1} N)) :=
  Pi.lift fun _ ↦ AddCommGrpCat.uliftFunctor.map (AddCommGrpCat.ofHom c)

private theorem uliftPiHom_apply {I : Type} {M N : Type u}
    [AddCommGroup M] [AddCommGroup N] (c : M →+ N) (i : I) (x : M) :
    ((Pi.π (fun _ : I ↦ AddCommGrpCat.of (ULift.{u + 1} N)) i)
      (uliftPiHom c (ULift.up x))).down = c x := by
  have h := congrArg (fun f ↦ f (ULift.up x))
    (Pi.lift_comp_π (fun _ : I ↦ AddCommGrpCat.uliftFunctor.map (AddCommGrpCat.ofHom c)) i)
  exact congrArg ULift.down h

private theorem semilinearOfSmulHom {A B : Scheme.{u}} (G : A.Modules) (H : B.Modules)
    (r : Γ(G, ⊤) ⟶ Γ(H, ⊤)) (σ : Γ(A, ⊤) →+* Γ(B, ⊤))
    (hr : ∀ a, (G.smul a).asHom ≫ r = r ≫ (H.smul (σ a)).asHom) :
    ∀ (a : Γ(A, ⊤)) (m : Γ(G, ⊤)), r (a • m) = σ a • r m := by
  intro a m
  exact congrArg (fun φ ↦ φ.hom m) (hr a)

private theorem existsSectionsHom (X : Scheme.{u})
    (U W V : X.Etale) (g : W ⟶ U) (h : V ⟶ U) (n : ℕ)
    (p : Fin (n + 1) → (V ⟶ W)) (hp : ∀ k, p k ≫ g = h)
    (G : U.left.Modules) (H : V.left.Modules) (r : Γ(G, ⊤) ⟶ Γ(H, ⊤))
    (hr : ∀ (a : Γ(U.left, ⊤)), (G.smul a).asHom ≫ r = r ≫ (H.smul (h.left.appTop a)).asHom) :
    letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
    ∃ c : (Γ(G, ⊤) ⊗[Γ(U.left, ⊤)]
        (⨂[Γ(U.left, ⊤)] _ : Fin (n + 1), Γ(W.left, ⊤))) →+ Γ(H, ⊤),
      ∀ m b, c (m ⊗ₜ PiTensorProduct.tprod Γ(U.left, ⊤) b) =
        (∏ k, (p k).left.appTop (b k)) • r m := by
  classical
  dsimp only
  let : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
  let q (k : Fin (n + 1)) : Γ(W.left, ⊤) →+* Γ(V.left, ⊤) :=
    (p k).left.appTop.hom
  have hq (k : Fin (n + 1)) (a : Γ(U.left, ⊤)) :
      q k (algebraMap Γ(U.left, ⊤) Γ(W.left, ⊤) a) = h.left.appTop.hom a :=
    congrArg (fun f ↦ f.left.appTop.hom a) (hp k)
  exact existsTensorSectionHom h.left.appTop.hom q hq r.hom
    (semilinearOfSmulHom G H r h.left.appTop.hom hr)

private theorem specialization (X : Scheme.{u}) (F : X.Modules)
    (U W V : X.Etale) (g : W ⟶ U) (h : V ⟶ U) (n : ℕ)
    (p : Fin (n + 1) → (V ⟶ W)) (hp : ∀ k, p k ≫ g = h)
    (r : Γ((Modules.tensorPullback U.hom).obj F, ⊤) ⟶
      Γ((Modules.tensorPullback V.hom).obj F, ⊤))
    (hr : ∀ (a : Γ(U.left, ⊤)),
      (((Modules.tensorPullback U.hom).obj F).smul a).asHom ≫ r =
        r ≫ (((Modules.tensorPullback V.hom).obj F).smul (h.left.appTop a)).asHom) :
    letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
    ∃ c : (Γ((Modules.tensorPullback U.hom).obj F, ⊤) ⊗[Γ(U.left, ⊤)]
        (⨂[Γ(U.left, ⊤)] _ : Fin (n + 1), Γ(W.left, ⊤))) →+
        Γ((Modules.tensorPullback V.hom).obj F, ⊤),
      ∀ m b, c (m ⊗ₜ PiTensorProduct.tprod Γ(U.left, ⊤) b) =
        (∏ k, (p k).left.appTop (b k)) • r m := by
  exact existsSectionsHom X U W V g h n p hp
    ((Modules.tensorPullback U.hom).obj F) ((Modules.tensorPullback V.hom).obj F) r hr

private theorem specializationRestriction (X : Scheme.{u}) (F : X.Modules)
    (U W V : X.Etale) (g : W ⟶ U) (h : V ⟶ U) (n : ℕ)
    (p : Fin (n + 1) → (V ⟶ W)) (hp : ∀ k, p k ≫ g = h) :
    letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
    ∃ c : (Γ((Modules.tensorPullback U.hom).obj F, ⊤) ⊗[Γ(U.left, ⊤)]
        (⨂[Γ(U.left, ⊤)] _ : Fin (n + 1), Γ(W.left, ⊤))) →+
        Γ((Modules.tensorPullback V.hom).obj F, ⊤),
      ∀ m b, c (m ⊗ₜ PiTensorProduct.tprod Γ(U.left, ⊤) b) =
        (∏ k, (p k).left.appTop (b k)) • Modules.etaleTensorSectionsRestriction F h m := by
  exact specialization X F U W V g h n p hp
    (Modules.etaleTensorSectionsRestriction F h)
    (Modules.etaleTensorSectionsRestriction_smul F h)

private theorem specializationDegree (X : Scheme.{u}) (F : X.Modules)
    (U W V : X.Etale) (g : W ⟶ U) (h : V ⟶ U) (n : ℕ)
    (p : Fin (n + 1) → (V ⟶ W)) (hp : ∀ k, p k ≫ g = h) :
    letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
    ∃ f : AddCommGrpCat.of (ULift.{u + 1}
        (Γ((Modules.tensorPullback U.hom).obj F, ⊤) ⊗[Γ(U.left, ⊤)]
        (⨂[Γ(U.left, ⊤)] _ : Fin (n + 1), Γ(W.left, ⊤)))) ⟶
        ∏ᶜ (fun _ : Fin (n + 1) → Fin 1 ↦ AddCommGrpCat.of (ULift.{u + 1}
          Γ((Modules.tensorPullback V.hom).obj F, ⊤))),
      ∀ m b,
        ((Pi.π (fun _ : Fin (n + 1) → Fin 1 ↦ AddCommGrpCat.of (ULift.{u + 1}
          Γ((Modules.tensorPullback V.hom).obj F, ⊤))) (fun _ ↦ 0))
          (f (ULift.up (m ⊗ₜ PiTensorProduct.tprod Γ(U.left, ⊤) b)))).down =
            (∏ k, (p k).left.appTop (b k)) • Modules.etaleTensorSectionsRestriction F h m := by
  classical
  dsimp only
  let : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
  have hh := specializationRestriction X F U W V g h n p hp
  let c := Classical.choose hh
  have hc := Classical.choose_spec hh
  refine ⟨uliftPiHom c, fun m b ↦ ?_⟩
  exact (uliftPiHom_apply c (fun _ : Fin (n + 1) ↦ (0 : Fin 1))
    (m ⊗ₜ PiTensorProduct.tprod Γ(U.left, ⊤) b)).trans (hc m b)

private theorem specializationOver (X : Scheme.{u}) (F : X.Modules)
    (U W : X.Etale) (g : W ⟶ U) (n : ℕ) (P : Over U)
    (p : Fin (n + 1) → (P ⟶ Over.mk g)) :
    letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
    ∃ f : AddCommGrpCat.of (ULift.{u + 1}
        (Γ((Modules.tensorPullback U.hom).obj F, ⊤) ⊗[Γ(U.left, ⊤)]
        (⨂[Γ(U.left, ⊤)] _ : Fin (n + 1), Γ(W.left, ⊤)))) ⟶
        ∏ᶜ (fun _ : Fin (n + 1) → Fin 1 ↦ AddCommGrpCat.of (ULift.{u + 1}
          Γ((Modules.tensorPullback P.left.hom).obj F, ⊤))),
      ∀ m b,
        ((Pi.π (fun _ : Fin (n + 1) → Fin 1 ↦ AddCommGrpCat.of (ULift.{u + 1}
          Γ((Modules.tensorPullback P.left.hom).obj F, ⊤))) (fun _ ↦ 0))
          (f (ULift.up (m ⊗ₜ PiTensorProduct.tprod Γ(U.left, ⊤) b)))).down =
            (∏ k, (p k).left.left.appTop (b k)) •
              Modules.etaleTensorSectionsRestriction F P.hom m := by
  exact specializationDegree X F U W P.left g P.hom n
    (fun k ↦ (p k).left) (fun k ↦ (p k).w)

private theorem specializationProduct (X : Scheme.{u}) (F : X.Modules)
    (U W : X.Etale) (g : W ⟶ U) (n : ℕ) :
    letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
    let P := ∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)
    ∃ f : AddCommGrpCat.of (ULift.{u + 1}
        (Γ((Modules.tensorPullback U.hom).obj F, ⊤) ⊗[Γ(U.left, ⊤)]
        (⨂[Γ(U.left, ⊤)] _ : Fin (n + 1), Γ(W.left, ⊤)))) ⟶
        ∏ᶜ (fun _ : Fin (n + 1) → Fin 1 ↦ AddCommGrpCat.of (ULift.{u + 1}
          Γ((Modules.tensorPullback P.left.hom).obj F, ⊤))),
      ∀ m b,
        ((Pi.π (fun _ : Fin (n + 1) → Fin 1 ↦ AddCommGrpCat.of (ULift.{u + 1}
          Γ((Modules.tensorPullback P.left.hom).obj F, ⊤))) (fun _ ↦ 0))
          (f (ULift.up (m ⊗ₜ PiTensorProduct.tprod Γ(U.left, ⊤) b)))).down =
            (∏ k, (Pi.π (fun _ : Fin (n + 1) ↦ Over.mk g) k).left.left.appTop (b k)) •
              Modules.etaleTensorSectionsRestriction F P.hom m := by
  classical
  exact specializationOver X F U W g n
    (∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g))
    (fun k ↦ Pi.π (fun _ : Fin (n + 1) ↦ Over.mk g) k)

private theorem normalizationOfFormula (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent] (U W : X.Etale) (g : W ⟶ U) (n : ℕ)
    (f : (singletonTensorAmitsur X F U W g).X n ⟶
      (singletonTensorCech X F U W g).X n)
    (hf : letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
      let P := ∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)
      ∀ (m : Γ((Modules.tensorPullback U.hom).obj F, ⊤))
          (b : Fin (n + 1) → Γ(W.left, ⊤)),
        ((Pi.π (fun _ : Fin (n + 1) → Fin 1 ↦ AddCommGrpCat.of (ULift.{u + 1}
          Γ((Modules.tensorPullback P.left.hom).obj F, ⊤))) (fun _ ↦ 0))
          (f (ULift.up (m ⊗ₜ PiTensorProduct.tprod Γ(U.left, ⊤) b)))).down =
            (∏ k, (Pi.π (fun _ : Fin (n + 1) ↦ Over.mk g) k).left.left.appTop (b k)) •
              Modules.etaleTensorSectionsRestriction F P.hom m) :
    IsSingletonTensorDegreeComparisonHom X F U W g n f := by
  exact hf

-- Affineness is only needed for the subsequent invertibility theorem.
set_option linter.unusedVariables false in
/-- A normalized degree comparison homomorphism, without invertibility.
Source: Stacks Project, Tag 03P2, affine calculation; Tag 03DR, equation (35.8.1).
(blueprint: new-etale-affine-singleton-tensor-degree-comparison-hom)

Proof: the product projections induce compatible maps on global functions.
Tensor universality sends tprod(b) to the product of their images. Combine this
map with the additive, semilinear section restriction by the universal property
of the coefficient tensor product. Lift the resulting additive map through ULift
and map it into the outer categorical product. The projection equation for Pi.lift
and the pure-tensor equations for both tensor lifts give the required normalization.
-/
theorem exists_singletonTensorDegreeComparison_hom
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) (hU : IsAffine U.left) (hW : IsAffine W.left)
    (n : ℕ) :
    ∃ f : (singletonTensorAmitsur X F U W g).X n ⟶
      (singletonTensorCech X F U W g).X n,
      IsSingletonTensorDegreeComparisonHom X F U W g n f := by
  classical
  have hh := specializationProduct X F U W g n
  let f := Classical.choose hh
  have hf := Classical.choose_spec hh
  exact ⟨f, normalizationOfFormula X F U W g n f hf⟩

end
end AlgebraicGeometry.Scheme
