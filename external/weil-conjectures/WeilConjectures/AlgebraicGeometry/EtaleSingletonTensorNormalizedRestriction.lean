/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization
import WeilConjectures.AlgebraicGeometry.EtaleTensorSections

/-! # EtaleSingletonTensorNormalizedRestriction
Source: Stacks Project, Tags 03P2 and 03DR.
(blueprint: lem-sc-singleton-tensor-normalized-restriction)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme
noncomputable section

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true


attribute [local irreducible] Modules.tensorPullback Modules.tensorPullbackObj
  Modules.etaleTensorSectionsRestriction


private theorem restriction_smul {A B : Scheme.{u}} (G : A.Modules) (H : B.Modules)
    (r : Γ(G, ⊤) ⟶ Γ(H, ⊤)) (σ : Γ(A, ⊤) →+* Γ(B, ⊤))
    (hr : ∀ a, (G.smul a).asHom ≫ r = r ≫ (H.smul (σ a)).asHom)
    (a : Γ(A, ⊤)) (m : Γ(G, ⊤)) : r (a • m) = σ a • r m := by
  exact congrArg (fun φ ↦ φ.hom m) (hr a)

-- The equality determines the witness completely; no unproved existence is used.
private theorem exists_equal {α : Sort*} (a : α) : ∃ b : α, b = a := ⟨a, rfl⟩

/-- Keep map values out of kernel reduction while retaining their proved equality.
The witness is completely fixed by `exists_equal`, whose proof is complete. -/
private noncomputable def pinnedValue {α : Sort*} (a : α) : α :=
  Classical.choose (exists_equal a)

private theorem seal_eq {α : Sort*} (a : α) : pinnedValue a = a :=
  Classical.choose_spec (exists_equal a)

private theorem comp_sealed {X : Scheme.{u}} (F : X.Modules)
    {U V W : X.Etale} (h : W ⟶ V) (g : V ⟶ U) :
    pinnedValue (Modules.etaleTensorSectionsRestriction F (h ≫ g)) =
      pinnedValue (Modules.etaleTensorSectionsRestriction F g) ≫
        pinnedValue (Modules.etaleTensorSectionsRestriction F h) := by
  exact (seal_eq _).trans ((Modules.etaleTensorSectionsRestriction_comp F h g).trans
    (congrArg₂ (fun r s ↦ r ≫ s) (seal_eq _).symm (seal_eq _).symm))

private theorem comp_over_pinned_apply {X : Scheme.{u}} (F : X.Modules)
    {U : X.Etale} {P Q : Over U} (h : Q ⟶ P)
    (m : Γ((Modules.tensorPullback U.hom).obj F, ⊤)) :
    pinnedValue (Modules.etaleTensorSectionsRestriction F h.left)
      (pinnedValue (Modules.etaleTensorSectionsRestriction F P.hom) m) =
      pinnedValue (Modules.etaleTensorSectionsRestriction F Q.hom) m := by
  have he : pinnedValue (Modules.etaleTensorSectionsRestriction F Q.hom) =
      pinnedValue (Modules.etaleTensorSectionsRestriction F P.hom) ≫
        pinnedValue (Modules.etaleTensorSectionsRestriction F h.left) :=
    (congrArg (fun k : Q.left ⟶ U ↦
      pinnedValue (Modules.etaleTensorSectionsRestriction F k)) h.w).symm.trans
        (comp_sealed F h.left P.hom)
  exact (AddCommGrpCat.comp_apply
    (pinnedValue (Modules.etaleTensorSectionsRestriction F P.hom))
    (pinnedValue (Modules.etaleTensorSectionsRestriction F h.left)) m).symm.trans
      (ConcreteCategory.congr_hom he m).symm

private theorem smul_pinned {A B : Scheme.{u}} (G : A.Modules) (H : B.Modules)
    (r : Γ(G, ⊤) ⟶ Γ(H, ⊤)) (σ : Γ(A, ⊤) →+* Γ(B, ⊤))
    (hr : ∀ a, (G.smul a).asHom ≫ r = r ≫ (H.smul (σ a)).asHom) (a : Γ(A, ⊤)) :
    (G.smul a).asHom ≫ pinnedValue r = pinnedValue r ≫ (H.smul (σ a)).asHom := by
  exact (congrArg (fun r ↦ (G.smul a).asHom ≫ r) (seal_eq r)).trans
    ((hr a).trans (congrArg (fun r ↦ r ≫ (H.smul (σ a)).asHom) (seal_eq r).symm))

/-- The evaluated normalized pure sections agree after omitting a factor.
Source: Stacks Project, Tag 03P2 (tensor Čech identification), Tag 03DR.
(blueprint: lem-sc-singleton-tensor-normalized-restriction)

Proof: apply hf to evaluate the input section as the product of pulled-back
functions times the restriction of m from U. Semilinearity of
etaleTensorSectionsRestriction moves that scalar product outside restriction.
A ring homomorphism preserves finite products. For each k, the product map
omitting j followed by the k-th projection is the j.succAbove(k)-th projection,
by Pi.lift_comp_π. Functoriality of appTop therefore identifies each pulled-back
scalar with the corresponding retained projection function on the larger
product. Composition of etaleTensorSectionsRestriction and the over-U
triangle identify the restricted coefficient with direct restriction from U.
Apply hf' to evaluate the inserted-unit pure section. Its j-th scalar factor
is the pullback of one and equals one. Fin.prod_univ_succAbove, together with
insertNth at j and at j.succAbove(k), identifies its remaining factors with
those just computed. Thus the evaluated sections agree. This argument has
no Čech coface and no injectivity assertion. It works in degree zero, for
both possible omitted factors, and for zero modules and empty schemes.
-/
theorem singletonTensor_normalized_restriction
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) (n : ℕ) (j : Fin (n + 2))
    (f : (singletonTensorAmitsur X F U W g).X n ⟶
      (singletonTensorCech X F U W g).X n)
    (f' : (singletonTensorAmitsur X F U W g).X (n + 1) ⟶
      (singletonTensorCech X F U W g).X (n + 1))
    (hf : IsSingletonTensorDegreeComparisonHom X F U W g n f)
    (hf' : IsSingletonTensorDegreeComparisonHom X F U W g (n + 1) f')
    (m : Γ((Modules.tensorPullback U.hom).obj F, ⊤))
    (b : Fin (n + 1) → Γ(W.left, ⊤)) :
    letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
    Modules.etaleTensorSectionsRestriction F (Pi.lift (fun k : Fin (n + 1) ↦
      Pi.π (fun _ : Fin (n + 2) ↦ Over.mk g) (j.succAbove k))).left
      (((Pi.π (fun _ : Fin (n + 1) → Fin 1 ↦
      AddCommGrpCat.of (ULift.{u + 1}
        Γ((Modules.tensorPullback
          (∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)).left.hom).obj F, ⊤)))
      (fun _ ↦ 0)) (f (ULift.up (m ⊗ₜ[Γ(U.left, ⊤)] PiTensorProduct.tprod Γ(U.left, ⊤) b)))).down) =
    ((Pi.π (fun _ : Fin (n + 2) → Fin 1 ↦
      AddCommGrpCat.of (ULift.{u + 1}
        Γ((Modules.tensorPullback
          (∏ᶜ (fun _ : Fin (n + 2) ↦ Over.mk g)).left.hom).obj F, ⊤)))
      (fun _ ↦ 0)) (f' (ULift.up (m ⊗ₜ[Γ(U.left, ⊤)]
        PiTensorProduct.tprod Γ(U.left, ⊤) (j.insertNth 1 b))))).down := by
  classical
  let : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
  let P := ∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)
  let Q := ∏ᶜ (fun _ : Fin (n + 2) ↦ Over.mk g)
  let h : Q ⟶ P := Pi.lift fun k ↦ Pi.π (fun _ : Fin (n + 2) ↦ Over.mk g)
    (j.succAbove k)
  let a : Γ(P.left.left, ⊤) :=
    ∏ k, (Pi.π (fun _ : Fin (n + 1) ↦ Over.mk g) k).left.left.appTop (b k)
  have hs := restriction_smul ((Modules.tensorPullback P.left.hom).obj F)
    ((Modules.tensorPullback Q.left.hom).obj F)
    (pinnedValue (Modules.etaleTensorSectionsRestriction F h.left))
    h.left.left.appTop.hom
    (smul_pinned _ _ (Modules.etaleTensorSectionsRestriction F h.left)
      h.left.left.appTop.hom (Modules.etaleTensorSectionsRestriction_smul F h.left)) a
    (pinnedValue (Modules.etaleTensorSectionsRestriction F P.hom) m)
  have hc := comp_over_pinned_apply F h m
  have hp (k : Fin (n + 1)) :
      h.left.left ≫ (Pi.π (fun _ : Fin (n + 1) ↦ Over.mk g) k).left.left =
      (Pi.π (fun _ : Fin (n + 2) ↦ Over.mk g) (j.succAbove k)).left.left := by
    exact congrArg (fun q ↦ q.left.left)
      (Pi.lift_comp_π (fun k ↦ Pi.π (fun _ : Fin (n + 2) ↦ Over.mk g)
        (j.succAbove k)) k)
  have ha : h.left.left.appTop a =
      ∏ k, (Pi.π (fun _ : Fin (n + 2) ↦ Over.mk g) k).left.left.appTop
        (Fin.insertNth (α := fun _ ↦ Γ(W.left, ⊤)) j 1 b k) := by
    dsimp only [a]
    rw [map_prod, Fin.prod_univ_succAbove _ j]
    simp only [Fin.insertNth_apply_same, map_one, one_mul,
      Fin.insertNth_apply_succAbove]
    apply Finset.prod_congr rfl
    intro k hk
    have hh := congrArg (fun q : Q.left.left ⟶ W.left ↦ q.appTop.hom (b k)) (hp k)
    exact hh
  have hfp := (hf m b).trans
    (congrArg (fun r : Γ((Modules.tensorPullback U.hom).obj F, ⊤) ⟶
      Γ((Modules.tensorPullback P.left.hom).obj F, ⊤) ↦ a • r m)
      (seal_eq (Modules.etaleTensorSectionsRestriction F P.hom)).symm)
  have hf'p := (hf' m (j.insertNth 1 b)).trans
    (congrArg (fun r : Γ((Modules.tensorPullback U.hom).obj F, ⊤) ⟶
      Γ((Modules.tensorPullback Q.left.hom).obj F, ⊤) ↦
      (∏ k, (Pi.π (fun _ : Fin (n + 2) ↦ Over.mk g) k).left.left.appTop
        (Fin.insertNth (α := fun _ ↦ Γ(W.left, ⊤)) j 1 b k)) • r m)
      (seal_eq (Modules.etaleTensorSectionsRestriction F Q.hom)).symm)
  have he := (congrArg (fun s ↦
    pinnedValue (Modules.etaleTensorSectionsRestriction F h.left) s) hfp).trans
      (hs.trans (congrArg₂ (fun a s ↦ a • s) ha hc))
  exact (ConcreteCategory.congr_hom
    (seal_eq (Modules.etaleTensorSectionsRestriction F h.left)).symm _).trans
      (he.trans hf'p.symm)

end
end AlgebraicGeometry.Scheme
