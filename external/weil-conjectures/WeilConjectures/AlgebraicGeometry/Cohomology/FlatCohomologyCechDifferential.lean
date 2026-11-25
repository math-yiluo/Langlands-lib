/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Topology.Sheaves.CechComparison

/-! # Naturality of canonical Cech base-change components

Source: Stacks Project, Tags 02KH and 02KG, the separated-case Cech argument.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {X : Scheme.{u}} {ι : Type u}

-- The coordinate formula after identifying product opens with intersections.
private theorem cechCoordinate_d {Z : Scheme.{u}} {J K : Type u} [CommRing K]
    (W : J → Z.Opens) (T : Z.Opensᵒᵖ ⥤ ModuleCat.{u} K) (k : ℕ)
    (x : ((cechComplexFunctor W).obj T).X k) (y : Fin (k + 2) → J) :
    TopCat.Presheaf.cechComplexFunctorXAddEquiv W T (k + 1)
        (((cechComplexFunctor W).obj T).d k (k + 1) x) y =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        T.map (homOfLE (TopCat.Presheaf.iInf_le_iInf_comp W y i.succAbove)).op
          (TopCat.Presheaf.cechComplexFunctorXAddEquiv W T k x (y ∘ i.succAbove)) := by
  rw [TopCat.Presheaf.cechComplexFunctorXAddEquiv_apply,
    TopCat.Presheaf.cechComplexFunctorπ_d_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_zsmul, TopCat.Presheaf.cechComplexFunctorXAddEquiv_apply]
  congr 1
  have h := (homOfLE ((TopCat.Presheaf.iInf_le_iInf_comp W y i.succAbove).trans
    (TopCat.Presheaf.iInf_le_piObj W (y ∘ i.succAbove)))).op
  rw [TopCat.Presheaf.map_map_apply T _ _ h]
  exact TopCat.Presheaf.map_map_apply T _ _ h _

-- Naturality followed by restriction to arbitrary compatible smaller opens.
private theorem unitRestriction_comm {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (M : Z.Modules) (N : Y.Modules) (η : M ⟶ (pushforward g).obj N)
    {W W' : Z.Opens} {T T' : Y.Opens} (hW : W ≤ W') (hT : T ≤ T')
    (h : T ≤ g ⁻¹ᵁ W) (h' : T' ≤ g ⁻¹ᵁ W') (x : M.presheaf.obj (op W')) :
    N.presheaf.map (homOfLE hT).op
        (N.presheaf.map (homOfLE h').op (η.val.app (op W') x)) =
      N.presheaf.map (homOfLE h).op
        (η.val.app (op W) (M.presheaf.map (homOfLE hW).op x)) := by
  have hn := PresheafOfModules.naturality_apply η.val (homOfLE hW).op x
  change η.val.app (op W) (M.presheaf.map (homOfLE hW).op x) =
    N.presheaf.map ((Opens.map g.base).map (homOfLE hW)).op
      (η.val.app (op W') x) at hn
  rw [hn]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 2

-- Restricting a global scalar commutes with restriction of module sections.
private theorem scalarRestriction_comm {Y : Scheme.{u}} (N : Y.Modules)
    {T T' : Y.Opens} (hT : T ≤ T') (r : Γ(Y, ⊤))
    (x : N.presheaf.obj (op T')) :
    N.presheaf.map (homOfLE hT).op
        ((Y.presheaf.map (homOfLE (le_top : T' ≤ ⊤)).op).hom r • x) =
      (Y.presheaf.map (homOfLE (le_top : T ≤ ⊤)).op).hom r •
        N.presheaf.map (homOfLE hT).op x := by
  rw [map_smul]
  congr 1
  change (Y.presheaf.map (homOfLE hT).op).hom
      ((Y.presheaf.map (homOfLE (le_top : T' ≤ ⊤)).op).hom r) = _
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  congr 2

/-- Canonical component maps commute with the alternating Cech differential.
This is a naturality assertion and does not assert invertibility of any component.

Source: Stacks Project, Tag 02KH, separated-case Cech argument, and the
coordinate differential formula in WeilConjectures.Topology.Sheaves.CechComparison.
(blueprint: lem-pc-flat-cech-base-change-differential)

Proof: Test the equality on pure tensors b tensor x, which span scalar extension.
Then test each target tuple coordinate; product projections and restriction along
an isomorphism of opens are jointly injective. In the coordinate differential
formula, each summand is the restriction of a face coordinate with sign (-1)^i.
Apply the assumed coordinate equation to each face. Naturality of the module
adjunction unit moves restriction across the pulled-back section. Naturality of
the structure-sheaf map moves the image of b across the same restriction. Inverse
image preserves the finite intersections; all maps between these opens agree
because the category of opens is thin. Linearity distributes b over the finite
alternating sum. The two sides therefore have equal coordinates. Tensor induction
and product extensionality finish. The empty index type gives no coordinates and
zero terms; empty opens have zero sections. There is no affine or flat hypothesis:
only naturality of the unit and the assumed pure-tensor formula are used. -/
theorem cechBaseChange_components_comm (f : X ⟶ Spec (.of R))
    (U : ι → X.Opens) (M : X.Modules)
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
    ∀ c : ∀ k, A.X k ⟶ B.X k,
      (∀ (k : ℕ) (y : Fin (k + 1) → ι) (b : S) (x : C.X k),
      z k y (c k (b ⊗ₜ[R] x)) =
        ((baseChangedScheme (S := S) f).presheaf.map
          (homOfLE (le_top : (⨅ l, V (y l)) ≤ ⊤)).op).hom
          (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom b) •
          N.presheaf.map (homOfLE (hI k y)).op
            ((baseChangeUnit (S := S) f M).val.app (op (⨅ l, U (y l))) (a k y x))) →
      ∀ k, c k ≫ B.d k (k + 1) = A.d k (k + 1) ≫ c (k + 1) := by
  intro g V N P Q C A B a z c hc k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul b x =>
    simp only [ModuleCat.comp_apply]
    change B.d k (k + 1) (c k (b ⊗ₜ[R] x)) =
      c (k + 1) (((ModuleCat.extendScalars (algebraMap R S)).map
        (C.d k (k + 1))) (b ⊗ₜ[R] x))
    rw [ModuleCat.ExtendScalars.map_tmul]
    apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv V Q (k + 1)).injective
    funext y
    rw [cechCoordinate_d]
    change (∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
      Q.map (homOfLE (TopCat.Presheaf.iInf_le_iInf_comp V y i.succAbove)).op
        (z k (y ∘ i.succAbove) (c k (b ⊗ₜ[R] x)))) =
      z (k + 1) y (c (k + 1) (b ⊗ₜ[R] C.d k (k + 1) x))
    simp only [hc]
    have ha : a (k + 1) y (C.d k (k + 1) x) =
        ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
          M.presheaf.map
            (homOfLE (TopCat.Presheaf.iInf_le_iInf_comp U y i.succAbove)).op
            (a k (y ∘ i.succAbove) x) := cechCoordinate_d U P k x y
    rw [ha]
    simp only [map_sum, map_zsmul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [smul_comm _ ((-1 : ℤ) ^ (i : ℕ))]
    congr 1
    change N.presheaf.map
        (homOfLE (TopCat.Presheaf.iInf_le_iInf_comp V y i.succAbove)).op
        (_ • N.presheaf.map (homOfLE (hI k (y ∘ i.succAbove))).op
          ((baseChangeUnit (S := S) f M).val.app _ (a k (y ∘ i.succAbove) x))) = _
    rw [scalarRestriction_comm]
    congr 1
    exact unitRestriction_comm g M N (baseChangeUnit (S := S) f M)
      (TopCat.Presheaf.iInf_le_iInf_comp U y i.succAbove)
      (TopCat.Presheaf.iInf_le_iInf_comp V y i.succAbove)
      (hI (k + 1) y) (hI k (y ∘ i.succAbove)) (a k (y ∘ i.succAbove) x)
  | add t t' ht ht' => simpa only [map_add] using congrArg₂ (· + ·) ht ht'

end AlgebraicGeometry.Scheme.Modules
