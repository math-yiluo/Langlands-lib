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

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

noncomputable section

/-- The singleton tensor-section Čech complex, before identifying its terms. 
(blueprint: new-etale-affine-singleton-tensor-degree-comparison-hom-normalization)
-/
abbrev singletonTensorCech (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) :=
  (cechComplexFunctor fun _ : Fin 1 ↦ Over.mk g).obj
    ((Over.forget U).op ⋙
      ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf F)).obj)

/-- Forget scalars and lift the affine Amitsur complex. 
(blueprint: new-etale-affine-singleton-tensor-degree-comparison-hom-normalization)
-/
abbrev singletonTensorAmitsur (X : Scheme.{u}) (F : X.Modules)
    (U W : X.Etale) (g : W ⟶ U) :=
  letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
  (((forget₂ (ModuleCat.{u} Γ(U.left, ⊤)) AddCommGrpCat.{u}) ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}).mapHomologicalComplex (.up ℕ)).obj
      (Algebra.TensorProduct.amitsurComplex Γ(U.left, ⊤) Γ(W.left, ⊤)
        Γ((Modules.tensorPullback U.hom).obj F, ⊤))

/-- The cosimplicial object underlying the singleton tensor-section Čech complex. 
(blueprint: new-etale-affine-singleton-tensor-degree-comparison-hom-normalization)
-/
abbrev singletonTensorCechCosimplicial (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent] (U W : X.Etale) (g : W ⟶ U) :=
  (FormalCoproduct.cosimplicialObjectFunctor
    (FormalCoproduct.mk _ (fun _ : Fin 1 ↦ Over.mk g)).cech).obj
      ((Over.forget U).op ⋙
        ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
          (Modules.etaleTensorSectionsSheaf F)).obj)

/-- The coefficient-forgetting and universe-lifting functor used by the comparison. 
(blueprint: new-etale-affine-singleton-tensor-degree-comparison-hom-normalization)
-/
abbrev singletonTensorForget (U : Scheme.{u}) :=
  (forget₂ (ModuleCat.{u} Γ(U, ⊤)) AddCommGrpCat.{u}) ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- The pure-tensor equation fixes the degree comparison uniquely: evaluate the singleton
product, multiply the pulled-back functions, and pull back the coefficient section.
This predicate mentions no differential or coface. 
(blueprint: new-etale-affine-singleton-tensor-degree-comparison-hom-normalization)
-/
def IsSingletonTensorDegreeComparison (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent] (U W : X.Etale) (g : W ⟶ U) (n : ℕ)
    (e : (singletonTensorAmitsur X F U W g).X n ≅
      (singletonTensorCech X F U W g).X n) : Prop :=
  letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
  let P := ∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)
  ∀ (m : Γ((Modules.tensorPullback U.hom).obj F, ⊤))
    (b : Fin (n + 1) → Γ(W.left, ⊤)),
    ((Pi.π (fun _ : Fin (n + 1) → Fin 1 ↦
      AddCommGrpCat.of (ULift.{u + 1} Γ((Modules.tensorPullback P.left.hom).obj F, ⊤)))
      (fun _ ↦ 0))
        (e.hom (ULift.up (m ⊗ₜ[Γ(U.left, ⊤)] PiTensorProduct.tprod Γ(U.left, ⊤) b)))).down =
      (∏ k : Fin (n + 1), (Pi.π (fun _ : Fin (n + 1) ↦ Over.mk g) k).left.left.appTop
        (b k)) • Modules.etaleTensorSectionsRestriction F P.hom m

/-- The pure-tensor normalization for a comparison homomorphism.
Source: Stacks Project, Tag 03P2, affine tensor calculation.
(blueprint: new-etale-affine-singleton-tensor-degree-comparison-hom-normalization)
-/
def IsSingletonTensorDegreeComparisonHom (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent] (U W : X.Etale) (g : W ⟶ U) (n : ℕ)
    (f : (singletonTensorAmitsur X F U W g).X n ⟶
      (singletonTensorCech X F U W g).X n) : Prop :=
  letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
  let P := ∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)
  ∀ (m : Γ((Modules.tensorPullback U.hom).obj F, ⊤))
    (b : Fin (n + 1) → Γ(W.left, ⊤)),
    ((Pi.π (fun _ : Fin (n + 1) → Fin 1 ↦
      AddCommGrpCat.of (ULift.{u + 1} Γ((Modules.tensorPullback P.left.hom).obj F, ⊤)))
      (fun _ ↦ 0))
        (f (ULift.up (m ⊗ₜ[Γ(U.left, ⊤)] PiTensorProduct.tprod Γ(U.left, ⊤) b)))).down =
      (∏ k : Fin (n + 1), (Pi.π (fun _ : Fin (n + 1) ↦ Over.mk g) k).left.left.appTop
        (b k)) • Modules.etaleTensorSectionsRestriction F P.hom m

end
end AlgebraicGeometry.Scheme
