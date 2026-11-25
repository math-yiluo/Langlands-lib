/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Topology.Sheaves.CechComparison

/-! # Refinement of module Cech complexes along a scheme morphism

Source: Stacks Project, Cohomology, Tag 01FD
(blueprint: def-sc-cech-refinement-cochain-map).
The component formula fixes the map to pullback of sections followed by restriction;
it is not an unconstrained map assumed to commute with cohomology comparisons.
-/

@[expose] public section

universe uR
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The inclusion of a refined intersection in the inverse image of its original
intersection. Covers and index sets need not be finite.
Source: Stacks, Tag 01FD (blueprint: def-sc-cech-refinement-cochain-map). -/
def cechRefinementIntersection {X X' : Scheme.{uR}} (f : X' ⟶ X)
    {ι ι' : Type uR} (U : ι → X.Opens) (U' : ι' → X'.Opens)
    (refine : ι' → ι) (hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i))
    (n : ℕ) (y : Fin (n + 1) → ι') :
    (⨅ j, U' (y j)) ⟶ f ⁻¹ᵁ (⨅ j, U (refine (y j))) :=
  homOfLE (by
    intro x hx
    change f.base x ∈ ⨅ j, U (refine (y j))
    rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    intro j
    exact hrefine (y j) ((iInf_le (fun j ↦ U' (y j)) j) hx))

/-- The prescribed refinement map on cochains, written on every tuple of indices.
The canonical tensor-pullback adjunction unit gives pullback of sections.
Source: Stacks, Tag 01FD (blueprint: def-sc-cech-refinement-cochain-map). -/
def IsCechRefinementMap {X X' : Scheme.{uR}} (f : X' ⟶ X)
    {ι ι' : Type uR} (U : ι → X.Opens) (U' : ι' → X'.Opens)
    (refine : ι' → ι) (hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i)) (F : X.Modules)
    (gamma : ((forget₂ (ModuleCat.{uR} Γ(X, ⊤)) AddCommGrpCat.{uR}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj F.presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{uR} Γ(X', ⊤)) AddCommGrpCat.{uR}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          ((cechComplexFunctor U').obj ((tensorPullback f).obj F).presheafModuleCat)) : Prop :=
  ∀ (n : ℕ) (a : ((cechComplexFunctor U).obj F.presheafModuleCat).X n)
    (y : Fin (n + 1) → ι'),
    TopCat.Presheaf.cechComplexFunctorXAddEquiv U'
        ((tensorPullback f).obj F).presheafModuleCat n (gamma.f n a) y =
      ((tensorPullback f).obj F).presheaf.map
        (cechRefinementIntersection f U U' refine hrefine n y).op
        (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app F).val.app
          (op (⨅ j, U (refine (y j))))
          (TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat n a
            (refine ∘ y)))

/-- Pullback and restriction define a unique refinement cochain map.
Source: Stacks, Tag 01FD (blueprint: def-sc-cech-refinement-cochain-map).
Proof: use the specified tuple components and the product universal property to define
its degree maps. Pullback of sections and restrictions are additive. Each omitted-vertex
restriction commutes with these maps, so the alternating sums commute with the
 differential. Uniqueness follows by the product projections in every degree.
No covering hypothesis is needed for the cochain construction. -/
theorem exists_unique_cechRefinementMap {X X' : Scheme.{uR}} (f : X' ⟶ X)
    {ι ι' : Type uR} (U : ι → X.Opens) (U' : ι' → X'.Opens)
    (refine : ι' → ι) (hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i)) (F : X.Modules) :
    ∃! gamma : ((forget₂ (ModuleCat.{uR} Γ(X, ⊤)) AddCommGrpCat.{uR}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj F.presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{uR} Γ(X', ⊤)) AddCommGrpCat.{uR}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          ((cechComplexFunctor U').obj ((tensorPullback f).obj F).presheafModuleCat),
      IsCechRefinementMap f U U' refine hrefine F gamma := by
  let G := (tensorPullback f).obj F
  let φ := (Classical.choose (exists_tensorPullbackAdjunction f)).unit.app F
  let P := F.presheafModuleCat ⋙ forget₂ _ AddCommGrpCat
  let Q := G.presheafModuleCat ⋙ forget₂ _ AddCommGrpCat
  let t (n : ℕ) : TopCat.Presheaf.CechCochain U P n →+
      TopCat.Presheaf.CechCochain U' Q n :=
    AddMonoidHom.pi fun y ↦
      (G.presheaf.map (cechRefinementIntersection f U U' refine hrefine n y).op).hom.comp
        ((φ.val.app (op (⨅ j, U (refine (y j))))).hom.toAddMonoidHom.comp
          (Pi.evalAddMonoidHom _ (refine ∘ y)))
  have t_apply (n : ℕ) (a : TopCat.Presheaf.CechCochain U P n)
      (y : Fin (n + 1) → ι') : t n a y =
      G.presheaf.map (cechRefinementIntersection f U U' refine hrefine n y).op
        (φ.val.app (op (⨅ j, U (refine (y j)))) (a (refine ∘ y))) := rfl
  have ht (n : ℕ) (a : TopCat.Presheaf.CechCochain U P n) :
      ((TopCat.Presheaf.cechComplex U').obj Q).d n (n + 1) (t n a) =
        t (n + 1) (((TopCat.Presheaf.cechComplex U).obj P).d n (n + 1) a) := by
    funext y
    simp only [t_apply, TopCat.Presheaf.cechComplex_d_apply, map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    let h := TopCat.Presheaf.iInf_le_iInf_comp U (refine ∘ y) i.succAbove
    have hφ : φ.val.app (op (⨅ j, U (refine (y j))))
        (P.map (homOfLE h).op (a ((refine ∘ y) ∘ i.succAbove))) =
        G.presheaf.map ((Opens.map f.base).map (homOfLE h)).op
          (φ.val.app (op (⨅ j, U (refine ((y ∘ i.succAbove) j))))
            (a ((refine ∘ y) ∘ i.succAbove))) :=
      PresheafOfModules.naturality_apply φ.val (homOfLE h).op _
    rw [hφ]
    change G.presheaf.map _ (G.presheaf.map _ _) =
      G.presheaf.map _ (G.presheaf.map _ _)
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← G.presheaf.map_comp, ← G.presheaf.map_comp]
    congr 2
  let γ : (TopCat.Presheaf.cechComplex U).obj P ⟶
      (TopCat.Presheaf.cechComplex U').obj Q :=
    { f := fun n ↦ AddCommGrpCat.ofHom (t n)
      comm' := by
        rintro n _ rfl
        exact AddCommGrpCat.ext (ht n) }
  let e := TopCat.Presheaf.cechComplexFunctorIso U F.presheafModuleCat
  let e' := TopCat.Presheaf.cechComplexFunctorIso U' G.presheafModuleCat
  refine ⟨e.hom ≫ γ ≫ e'.inv, ?_, ?_⟩
  · intro n a y
    change (TopCat.Presheaf.cechComplexFunctorXAddEquiv U' G.presheafModuleCat n)
      ((TopCat.Presheaf.cechComplexFunctorXAddEquiv U' G.presheafModuleCat n).symm
        (t n (TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat n a))) y = _
    rw [AddEquiv.apply_symm_apply]
    rfl
  · intro δ hδ
    ext n : 1
    apply AddCommGrpCat.ext
    intro a
    apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv U' G.presheafModuleCat n).injective
    funext y
    rw [hδ n a y]
    change _ = (TopCat.Presheaf.cechComplexFunctorXAddEquiv U' G.presheafModuleCat n)
      ((TopCat.Presheaf.cechComplexFunctorXAddEquiv U' G.presheafModuleCat n).symm
        (t n (TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat n a))) y
    rw [AddEquiv.apply_symm_apply]
    rfl

/-- The refinement map on cohomology, transported through the canonical homology
comparison for forgetting scalars on each scheme.
Source: Stacks, Tag 01FD (blueprint: def-sc-cech-refinement-cochain-map). -/
def cechRefinementHomology {X X' : Scheme.{uR}} {f : X' ⟶ X}
    {ι ι' : Type uR} {U : ι → X.Opens} {U' : ι' → X'.Opens} {F : X.Modules}
    (gamma : ((forget₂ (ModuleCat.{uR} Γ(X, ⊤)) AddCommGrpCat.{uR}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj F.presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{uR} Γ(X', ⊤)) AddCommGrpCat.{uR}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          ((cechComplexFunctor U').obj ((tensorPullback f).obj F).presheafModuleCat))
    (p : ℕ) :
    (forget₂ _ AddCommGrpCat).obj
        (((cechComplexFunctor U).obj F.presheafModuleCat).homology p) ⟶
      (forget₂ _ AddCommGrpCat).obj
        (((cechComplexFunctor U').obj ((tensorPullback f).obj F).presheafModuleCat).homology p) :=
  ((((cechComplexFunctor U).obj F.presheafModuleCat).sc p).mapHomologyIso
      (forget₂ _ AddCommGrpCat)).inv ≫
    HomologicalComplex.homologyMap gamma p ≫
    ((((cechComplexFunctor U').obj
      ((tensorPullback f).obj F).presheafModuleCat).sc p).mapHomologyIso
        (forget₂ _ AddCommGrpCat)).hom

end
end AlgebraicGeometry.Scheme.Modules
