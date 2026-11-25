/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import Mathlib.Topology.Sheaves.Abelian
import WeilConjectures.Algebra.Homology.OpenExtensionCounitStalk

/-! # A concentrated approximation on an open support

Source: Stacks Project, Cohomology, Tags 08BS and 08BT.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

private theorem zero_of_faithful {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D) [F.Faithful]
    [F.PreservesZeroMorphisms] (M : C) (h : IsZero (F.obj M)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  apply F.map_injective
  rw [F.map_id, F.map_zero]
  exact h.eq_of_src (𝟙 _) 0

private theorem zero_of_stalks (X : RingedSpace.{u})
    (M : SheafOfModules.{u} (moduleRings X))
    (h : ∀ x : X, IsZero ((RingedSpace.moduleStalkFunctor X x).obj M)) : IsZero M := by
  apply zero_of_faithful (SheafOfModules.toSheaf (moduleRings X)) M
  apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
  intro x
  exact (forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}).map_isZero (h x)

set_option backward.isDefEq.respectTransparency false in
/-- Exact extension by zero of the restriction of `K` gives a concentrated object
mapping to `K`. Maps from `S` to degree-`n` homology factor through this counit.
This is a statement about a local approximation, not an isomorphism with `K`.

Source: Stacks Project, Cohomology, Tags 08BS and 08BT (exact extension by zero
and its adjunction); Modules, Tag 01AG (stalkwise detection).
(blueprint: lem-sc-open-supported-homology-approximation)

Proof: Let j be the inclusion of U. Restriction R and extension by zero J
are exact and additive, with sheaf adjunction counit epsilon : R followed by J
-> identity. Their composite F is an exact additive endofunctor of modules on
X. Choose a complex P representing K and apply F termwise. Set L = Q(F(P));
apply Q to the chain map whose components are epsilon(P^m), then compose with
the representative isomorphism Q(P) -> K to obtain b : L -> K. Exactness gives
H^m(L) isomorphic to F(H^m(K)). The homology map of this chain map is epsilon
on homology: this follows from its commutation with cycles and the quotient
from cycles to homology. Thus the comparisons identify H^m(b) with the
sheaf counit. This construction uses only the given derived category on X.

For m != n the sheaf F(H^m(K)) has zero stalks everywhere. Off U this is the
extension-by-zero stalk formula. On U its counit stalk is an isomorphism to
the zero stalk specified by hlocal. Stalkwise detection makes this sheaf zero.
Similarly epsilon(S) : F(S) -> S is an isomorphism: on U its stalk is an
isomorphism and off U its source and target have zero stalks by hsource.
For a : S -> H^n(K), define c by epsilon(S)^{-1} followed by F(a), then the
inverse of the homology comparison H^n(L) -> F(H^n(K)). Counit naturality
and the homology comparison for b give c followed by H^n(b) equal to a.
For empty U, S and L are zero. For U = X the counit is an isomorphism.
No truncation or derived lift from a single object is asserted here. -/
theorem open_supported_homology_approximation (X : RingedSpace.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    (U : Opens X) (S : SheafOfModules.{u} (moduleRings X))
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings X))) (n : ℤ)
    (hsource : ∀ x : X, x ∉ U → IsZero ((RingedSpace.moduleStalkFunctor X x).obj S))
    (hlocal : ∀ m : ℤ, m ≠ n → ∀ x : X, x ∈ U →
      IsZero ((RingedSpace.moduleStalkFunctor X x).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings X)) m).obj K))) :
    ∃ (L : DerivedCategory (SheafOfModules.{u} (moduleRings X))) (b : L ⟶ K),
      (∀ m : ℤ, m ≠ n → IsZero
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings X)) m).obj L)) ∧
      ∀ a : S ⟶ (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X)) n).obj K,
        ∃ c : S ⟶ (DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X)) n).obj L,
          c ≫ (DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X)) n).map b = a := by
  classical
  let C := SheafOfModules.{u} (moduleRings X)
  let R := SheafOfModules.overFunctor.{u} (moduleRings X) U
  let J := SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
    PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)
  obtain ⟨hRlim, hRcolim, hJlim, hJcolim, ha⟩ :=
    open_restriction_adjunction_exact X U
  let adj : J ⊣ R := Classical.choice ha
  let F : C ⥤ C := R ⋙ J
  let ε : F ⟶ 𝟭 C := adj.counit
  have : PreservesFiniteLimits R := hRlim
  have : PreservesFiniteColimits R := hRcolim
  have : PreservesFiniteLimits J := hJlim
  have : PreservesFiniteColimits J := hJcolim
  have : F.Additive := CategoryTheory.leftExactFunctor_le_additiveFunctor C C F
    (by rw [leftExactFunctor_iff]; infer_instance)
  have stalk (M : C) (x : X) :=
    SheafOfModules.open_extension_counit_stalk X (moduleRings X) rfl U J adj M x
  have zero (M : C)
      (h : ∀ x : X, x ∈ U → IsZero ((RingedSpace.moduleStalkFunctor X x).obj M)) :
      IsZero (F.obj M) := by
    apply zero_of_stalks X
    intro x
    let A := forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}
    apply zero_of_faithful A
    by_cases hx : x ∈ U
    · have hi := (stalk M x).1 hx
      exact (A.map_isZero (h x hx)).of_iso (asIso
        ((SheafOfModules.toSheaf (moduleRings X) ⋙
          TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (ε.app M)))
    · exact (stalk M x).2 hx
  have hs : IsIso (ε.app S) := by
    let g := (SheafOfModules.toSheaf (moduleRings X)).map (ε.app S)
    have hg (x : X) : IsIso
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map g.hom) := by
      by_cases hx : x ∈ U
      · exact (stalk S x).1 hx
      · exact ((stalk S x).2 hx).isIso
          ((forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}).map_isZero
            (hsource x hx)) _
    have : ∀ x : X, IsIso
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map g.hom) := hg
    have : IsIso g := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso g
    exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf (moduleRings X))
  -- Work with a representative complex, so no derived category on U is required.
  let P : CochainComplex C ℤ := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let FP := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let f : FP ⟶ P := (NatTrans.mapHomologicalComplex ε (ComplexShape.up ℤ)).app P
  let L := DerivedCategory.Q.obj FP
  let b : L ⟶ K := DerivedCategory.Q.map f ≫ e.hom
  -- Include the identity-functor comparison used by mapNatTrans on short complexes.
  let q (m : ℤ) : P.homology m ≅ (DerivedCategory.homologyFunctor C m).obj K :=
    ((P.sc m).mapHomologyIso (𝟭 C)).symm ≪≫
      ((DerivedCategory.homologyFunctorFactors C m).app P).symm ≪≫
      (DerivedCategory.homologyFunctor C m).mapIso e
  let t (m : ℤ) : (DerivedCategory.homologyFunctor C m).obj L ≅
      F.obj ((DerivedCategory.homologyFunctor C m).obj K) :=
    (DerivedCategory.homologyFunctorFactors C m).app FP ≪≫
      (P.sc m).mapHomologyIso F ≪≫ F.mapIso (q m)
  have hb (m : ℤ) : (DerivedCategory.homologyFunctor C m).map b =
      (t m).hom ≫ ε.app ((DerivedCategory.homologyFunctor C m).obj K) := by
    dsimp only [b, t, q, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    simp only [Category.assoc]
    erw [ε.naturality]
    simp only [Functor.id_map]
    have hf : (DerivedCategory.homologyFunctor C m).map (DerivedCategory.Q.map f) =
        ((DerivedCategory.homologyFunctorFactors C m).app FP).hom ≫
          HomologicalComplex.homologyMap f m ≫
          ((DerivedCategory.homologyFunctorFactors C m).app P).inv := by
      apply (cancel_mono ((DerivedCategory.homologyFunctorFactors C m).app P).hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact DerivedCategory.homologyFunctorFactors_hom_naturality f m
    have hh : HomologicalComplex.homologyMap f m =
        ((P.sc m).mapHomologyIso F).hom ≫ ε.app (P.homology m) ≫
          ((P.sc m).mapHomologyIso (𝟭 C)).inv := by
      exact ShortComplex.homologyMap_mapNatTrans (P.sc m) ε
    erw [Functor.map_comp, hf, hh]
    simp only [Category.assoc]
    rfl
  refine ⟨L, b, ?_, ?_⟩
  · intro m hm
    exact (zero _ (hlocal m hm)).of_iso (t m)
  · intro a
    refine ⟨inv (ε.app S) ≫ F.map a ≫ (t n).inv, ?_⟩
    rw [hb]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [ε.naturality]
    simp

end AlgebraicGeometry
