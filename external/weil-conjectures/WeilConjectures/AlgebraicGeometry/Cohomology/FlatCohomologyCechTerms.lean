/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Topology.Sheaves.CechComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.LinearAlgebra.TensorProduct.Pi
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyAffineSections

/-! # Canonical degree maps for affine Cech base change

Source: Stacks Project, Tags 02KH and 02KG, the separated-case Cech argument.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {X : Scheme.{u}} {ι : Type u}

private noncomputable def coordinateEquiv {T : TopCat.{u}} (U : ι → TopologicalSpace.Opens T)
    {K : Type u} [CommRing K] (P : (TopologicalSpace.Opens T)ᵒᵖ ⥤ ModuleCat.{u} K) (k : ℕ) :
    ((cechComplexFunctor U).obj P).X k ≃ₗ[K]
      (∀ y : Fin (k + 1) → ι, P.obj (op (⨅ l, U (y l)))) where
  toAddEquiv := TopCat.Presheaf.cechComplexFunctorXAddEquiv U P k
  map_smul' b x := by
    funext y
    change P.map _ (TopCat.Presheaf.cechComplexFunctorπ U P k y (b • x)) = _
    rw [(TopCat.Presheaf.cechComplexFunctorπ U P k y).hom.map_smul,
      (P.map (homOfLE (TopCat.Presheaf.iInf_le_piObj U y)).op).hom.map_smul]
    rfl

private noncomputable def scalarTensorEquiv (T : ModuleCat.{u} R) :
    (ModuleCat.extendScalars (algebraMap R S)).obj T ≃ₗ[S] TensorProduct R S T := by
  let e : (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) ≃ₗ[R] S :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r t ↦ (@Algebra.smul_def R S _ _ _ r t).symm }
  let t := TensorProduct.congr e (LinearEquiv.refl R T)
  exact
    { toEquiv := t.toEquiv
      map_add' := t.map_add
      map_smul' := by
        intro b x
        change t (b • x) = b • t x
        induction x using TensorProduct.inductionOn with
        | tmul s a => rfl
        | add x y hx hy => simp only [smul_add, map_add, hx, hy] }

/-- Canonical scalar extension gives isomorphisms of the individual Cech terms.
This assertion concerns only the objects in each degree, not the differentials.

Source: Stacks Project, Tags 02KH (separated-case proof) and 02KG.
(blueprint: lem-pc-flat-cech-base-change-terms)

Proof: A tuple of length k+1 has at least one entry. Induction on its length and
separatedness over the affine base show that its intersection is affine. Its
inverse image is the base change of this affine, hence affine. Apply the affine
pullback section formula to the quasi-coherent module. Transfer from tensorPullback
to the library pullback using uniqueness of left adjoints with their units. The
cartesian affine ring formula and tensor associativity give S tensor_R Gamma(M,W).
These identifications send b tensor s to b times the restricted adjunction unit.
There are finitely many tuples in each degree, so extension of scalars commutes
with their product. Take the product of the section isomorphisms and transport
through the categorical product-open identifications. This gives the displayed
isomorphisms and coordinate equation. With no indices the products are zero;
with an empty intersection its sections are zero. Neither case needs an extra
hypothesis. No flatness or assumption that the family covers X is used. -/
theorem exists_cechBaseChange_term_isos (f : X ⟶ Spec (.of R)) [IsSeparated f]
    [Finite ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (M : X.Modules) [M.IsQuasicoherent]
    (hI : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, baseChangeFst (S := S) f ⁻¹ᵁ U (y l)) ≤
        baseChangeFst (S := S) f ⁻¹ᵁ (⨅ l, U (y l))) :
    let g := baseChangeFst (S := S) f
    let V : ι → (baseChangedScheme (S := S) f).Opens := fun i ↦ g ⁻¹ᵁ U i
    let N := baseChangedModule (S := S) f M
    let P := M.presheafModuleCat ⋙
      ModuleCat.restrictScalars (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom)
    let Q := N.presheafModuleCat ⋙ ModuleCat.restrictScalars
      (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom)
    let C := (cechComplexFunctor U).obj P
    let A := ((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex (.up ℕ)).obj C
    let B := (cechComplexFunctor V).obj Q
    let a := fun (k : ℕ) (y : Fin (k + 1) → ι) (x : C.X k) ↦
      M.presheaf.map (homOfLE (TopCat.Presheaf.iInf_le_piObj U y)).op
        (TopCat.Presheaf.cechComplexFunctorπ U P k y x)
    let z := fun (k : ℕ) (y : Fin (k + 1) → ι) (x : B.X k) ↦
      N.presheaf.map (homOfLE (TopCat.Presheaf.iInf_le_piObj V y)).op
        (TopCat.Presheaf.cechComplexFunctorπ V Q k y x)
    ∃ e : ∀ k, A.X k ≅ B.X k,
      let c := fun k ↦ (e k).hom
      ∀ (k : ℕ) (y : Fin (k + 1) → ι) (b : S) (x : C.X k),
      z k y (c k (b ⊗ₜ[R] x)) =
        ((baseChangedScheme (S := S) f).presheaf.map
          (homOfLE (le_top : (⨅ l, V (y l)) ≤ ⊤)).op).hom
          (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom b) •
          N.presheaf.map (homOfLE (hI k y)).op
            ((baseChangeUnit (S := S) f M).val.app (op (⨅ l, U (y l))) (a k y x)) := by
  classical
  let := Fintype.ofFinite ι
  let g := baseChangeFst (S := S) f
  let V : ι → (baseChangedScheme (S := S) f).Opens := fun i ↦ g ⁻¹ᵁ U i
  let N := baseChangedModule (S := S) f M
  let P := M.presheafModuleCat ⋙
    ModuleCat.restrictScalars (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom)
  let Q := N.presheafModuleCat ⋙ ModuleCat.restrictScalars
    (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom)
  let C := (cechComplexFunctor U).obj P
  let B := (cechComplexFunctor V).obj Q
  have hW (k : ℕ) (y : Fin (k + 1) → ι) : IsAffineOpen (⨅ l, U (y l)) := by
    apply InfClosed.iInf_mem_of_nonempty (s := Set.ofPred IsAffineOpen)
      (fun _ h₁ _ h₂ ↦ isAffineHom_diagonal_iff.mp
        (inferInstance : IsAffineHom (CategoryTheory.Limits.pullback.diagonal f))
        ⊤ (isAffineOpen_top _) _ (by simp) _ (by simp) h₁ h₂)
    exact fun l ↦ hU (y l)
  have hW' (k : ℕ) (y : Fin (k + 1) → ι) :
      (⨅ l, V (y l)) = g ⁻¹ᵁ (⨅ l, U (y l)) := by
    apply le_antisymm (hI k y)
    exact le_iInf fun l ↦ Scheme.Hom.preimage_mono g (iInf_le _ l)
  let hsec (k : ℕ) (y : Fin (k + 1) → ι) :=
    exists_baseChange_affine_section_equiv (S := S)
      f (⨅ l, U (y l)) (hW k y) M (⨅ l, V (y l)) (hW' k y) (hI k y)
  let t (k : ℕ) (y : Fin (k + 1) → ι) := Classical.choose (hsec k y)
  have ht (k : ℕ) (y : Fin (k + 1) → ι) := Classical.choose_spec (hsec k y)
  let E (k : ℕ) :=
    (scalarTensorEquiv (R := R) (S := S) (C.X k)).trans
      ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S)
        (coordinateEquiv U P k)).trans
        ((TensorProduct.piRight R S S (fun y : Fin (k + 1) → ι ↦
          P.obj (op (⨅ l, U (y l))))).trans
          ((LinearEquiv.piCongrRight (fun y ↦ t k y)).trans (coordinateEquiv V Q k).symm)))
  refine ⟨fun k ↦ (E k).toModuleIso, ?_⟩
  dsimp only
  intro k y b x
  change (coordinateEquiv V Q k) (E k (b ⊗ₜ[R] x)) y = _
  simp only [E, LinearEquiv.trans_apply]
  rw [LinearEquiv.apply_symm_apply]
  change t k y (b ⊗ₜ[R] ((coordinateEquiv U P k) x y)) = _
  exact ht k y b ((coordinateEquiv U P k) x y)

end AlgebraicGeometry.Scheme.Modules

