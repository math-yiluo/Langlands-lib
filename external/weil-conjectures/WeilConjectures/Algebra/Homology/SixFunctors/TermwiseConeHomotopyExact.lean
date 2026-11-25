/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorTriangulated
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

/-! # Mapping cones of termwise natural transformations

Source: Stacks Project, derived.tex, mapping cones and distinguished triangles;
blueprint finite-extension proof, first paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace CochainComplex
universe u v u' v'
variable {A : Type u} [Category.{v} A] [Preadditive A]
  {B : Type u'} [Category.{v'} B] [Preadditive B] [HasBinaryBiproducts B]

/-- The cone of the termwise natural transformation, with its diagonal maps. -/
def termwiseCone (F G : A ⥤ B) [F.Additive] [G.Additive] (τ : F ⟶ G) :
    CochainComplex A ℤ ⥤ CochainComplex B ℤ where
  obj X := mappingCone ((τ.mapHomologicalComplex (.up ℤ)).app X)
  map f := mappingCone.map _ _
    ((F.mapHomologicalComplex (.up ℤ)).map f)
    ((G.mapHomologicalComplex (.up ℤ)).map f)
    ((τ.mapHomologicalComplex (.up ℤ)).naturality f).symm
  map_id X := by
    ext i
    simp [mappingCone.ext_from_iff _ (i + 1) i rfl, mappingCone.map]
  map_comp f g := by
    ext i
    simp [mappingCone.ext_from_iff _ (i + 1) i rfl, mappingCone.map]

set_option synthInstance.maxSize 4096

namespace TermwiseConeProof
open HomologicalComplex

private local instance additive_limits (J : Type*) [Category J] [HasLimitsOfShape J B] :
    (additiveFunctor A B).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro F ⟨c⟩
    constructor
    intro X Y f g
    have hlim := isLimitOfPreserves ((evaluation A B).obj Y) c.isLimit
    apply hlim.hom_ext
    intro j
    change F.map (f + g) ≫ (c.π.app j).app Y =
      (F.map f + F.map g) ≫ (c.π.app j).app Y
    have : (c.diag.obj j).Additive := c.prop_diag_obj j
    rw [NatTrans.naturality, Preadditive.add_comp, NatTrans.naturality,
      NatTrans.naturality, Functor.map_add, Preadditive.comp_add]

private local instance additive_zero [HasZeroObject B] : (additiveFunctor A B).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, inferInstanceAs (0 : A ⥤ B).Additive⟩

private local instance additive_biproducts [HasZeroObject B] :
    HasBinaryBiproducts (A ⥤+ B) := by
  exact HasBinaryBiproducts.of_hasBinaryProducts

private local instance bundled_additive (F : A ⥤+ B) :
    ((AdditiveFunctor.forget A B).obj F).Additive := F.property

variable [HasBinaryBiproducts A] [HasZeroObject A]
  [HasZeroObject B] [HasCountableCoproducts B]

private def singleMap (F G : A ⥤ B) [F.Additive] [G.Additive] (τ : F ⟶ G) :
    (HomologicalComplex.single (A ⥤+ B) (.up ℤ) 0).obj (AdditiveFunctor.of F) ⟶
    (HomologicalComplex.single (A ⥤+ B) (.up ℤ) 0).obj (AdditiveFunctor.of G) :=
  (HomologicalComplex.single _ _ _).map (ObjectProperty.homMk τ)

private def squareIso {K L K' L' : CochainComplex B ℤ}
    (f : K ⟶ L) (f' : K' ⟶ L') (e : K ≅ K') (e' : L ≅ L')
    (h : f ≫ e'.hom = e.hom ≫ f') : mappingCone f ≅ mappingCone f' where
  hom := mappingCone.map f f' e.hom e'.hom h
  inv := mappingCone.map f' f e.inv e'.inv (by
    rw [← cancel_epi e.hom, ← cancel_mono e'.hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.hom_inv_id_assoc, h])
  hom_inv_id := by
    rw [← mappingCone.map_comp]
    simpa only [Iso.hom_inv_id] using mappingCone.map_id f
  inv_hom_id := by
    rw [← mappingCone.map_comp]
    simpa only [Iso.inv_hom_id] using mappingCone.map_id f'

omit [HasBinaryBiproducts A] [HasZeroObject A] [HasBinaryBiproducts B]
  [HasCountableCoproducts B] in
private theorem single_naturality (F G : A ⥤ B) [F.Additive] [G.Additive]
    (τ : F ⟶ G) (P : CochainComplex A ℤ) :
    mapBifunctorMap (singleMap F G τ) (𝟙 P) (AdditiveFunctor.forget A B) (.up ℤ) ≫
      (mapBifunctorSingle₁Iso (AdditiveFunctor.forget A B) (AdditiveFunctor.of G) P).hom =
    (mapBifunctorSingle₁Iso (AdditiveFunctor.forget A B) (AdditiveFunctor.of F) P).hom ≫
      (τ.mapHomologicalComplex (.up ℤ)).app P := by
  rw [← cancel_epi
    (mapBifunctorSingle₁Iso (AdditiveFunctor.forget A B) (AdditiveFunctor.of F) P).inv]
  ext n
  simp [singleMap, mapBifunctorSingle₁Iso, mapBifunctorSingle₁XIso,
    single_map_f_self, singleObjXSelf, ← NatTrans.comp_app,
    ← ObjectProperty.FullSubcategory.comp_hom]

private def comparisonObj (F G : A ⥤ B) [F.Additive] [G.Additive]
    (τ : F ⟶ G) (P : CochainComplex A ℤ) :
    HomologicalComplex.mapBifunctor (mappingCone (singleMap F G τ)) P
      (AdditiveFunctor.forget A B) (.up ℤ) ≅
      mappingCone ((τ.mapHomologicalComplex (.up ℤ)).app P) :=
  mapBifunctorMappingCone₁Iso _ _ _ ≪≫
    squareIso _ _ (mapBifunctorSingle₁Iso _ (AdditiveFunctor.of F) P)
      (mapBifunctorSingle₁Iso _ (AdditiveFunctor.of G) P) (single_naturality F G τ P)

omit [HasBinaryBiproducts A] [HasZeroObject A] in
private theorem comparison_inv_naturality (F G : A ⥤ B) [F.Additive] [G.Additive]
    (τ : F ⟶ G) {P Q : CochainComplex A ℤ} (f : P ⟶ Q) :
    mappingCone.map _ _
        ((F.mapHomologicalComplex (.up ℤ)).map f)
        ((G.mapHomologicalComplex (.up ℤ)).map f)
        ((τ.mapHomologicalComplex (.up ℤ)).naturality f).symm ≫
        (comparisonObj F G τ Q).inv =
      (comparisonObj F G τ P).inv ≫
        mapBifunctorMap (𝟙 (mappingCone (singleMap F G τ))) f
          (AdditiveFunctor.forget A B) (.up ℤ) := by
  ext n
  apply mappingCone.ext_from _ (n + 1) n rfl
  all_goals
    simp [comparisonObj, squareIso, mappingCone.map,
      mapBifunctorMappingCone₁Iso, mapBifunctorMappingCone₁Iso.inv,
      mapBifunctorSingle₁Iso_inv_f,
      mapBifunctorMappingCone₁Iso.ι₁]

end TermwiseConeProof

attribute [local instance] TermwiseConeProof.additive_limits TermwiseConeProof.additive_zero
  TermwiseConeProof.additive_biproducts TermwiseConeProof.bundled_additive

/-- The two-column totalization of a termwise natural transformation is exact on
homotopy categories.
Source: Stacks Project, derived.tex, definitions of cones and distinguished triangles;
blueprint lem-coef-integral-finite-extension.proof.md, first paragraph
(blueprint: lem-sf-termwise-cone-homotopy-exact).

Proof: on a degree-minus-one homotopy use the diagonal homotopy on the two cone
summands, with a minus sign on the shifted F summand. Naturality of τ cancels the
cross terms, so this defines a functor H on the homotopy quotient. The cone shift
comparison multiplies the shifted summand by (-1)^n; its zero and addition laws
follow from multiplication of these signs. For a chain map f, compare H(Cone f)
with Cone(H f): interchange the two cone directions and negate their doubly shifted
summand. The four block entries commute with the differentials by naturality of τ.
The comparison is the identity on the first two vertices, intertwines the cone
inclusion, and intertwines the boundary using the signed shift just specified.
Consequently H sends every standard cone triangle to a distinguished triangle.
Every distinguished homotopy triangle is isomorphic to a standard cone triangle,
so H is triangulated. No exactness, flatness, boundedness, or abelian hypothesis
on F or G is needed; zero functors and zero natural transformations are included.
The Lean proof realizes this construction as evaluation of the cone of the map
F[0] → G[0] in the category of additive functors. The existing totalized-bifunctor
triangulation theorem supplies its exactness. The countable-coproduct hypothesis
provides all totalizations required by that theorem's current interface. -/
theorem termwiseCone_homotopy_exact [HasZeroObject A] [HasBinaryBiproducts A]
    [HasZeroObject B] [HasCountableCoproducts B] (F G : A ⥤ B) [F.Additive] [G.Additive]
    (τ : F ⟶ G) :
    ∃ (H : HomotopyCategory A (.up ℤ) ⥤ HomotopyCategory B (.up ℤ))
      (_ : HomotopyCategory.quotient A (.up ℤ) ⋙ H ≅
        termwiseCone F G τ ⋙ HomotopyCategory.quotient B (.up ℤ))
      (c : H.CommShift ℤ), letI := c; H.IsTriangulated := by
  let E := AdditiveFunctor.forget A B
  let K := mappingCone (TermwiseConeProof.singleMap F G τ)
  let H := (E.bifunctorMapHomotopyCategory (.up ℤ) (.up ℤ) (.up ℤ)).obj
    ((HomotopyCategory.quotient _ _).obj K)
  let e : (E.map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)).obj K ≅
      termwiseCone F G τ :=
    (NatIso.ofComponents (fun P ↦ (TermwiseConeProof.comparisonObj F G τ P).symm)
      (fun f ↦ TermwiseConeProof.comparison_inv_naturality F G τ f)).symm
  exact ⟨H, E.quotientCompBifunctorMapHomotopyObjIso (.up ℤ) (.up ℤ) (.up ℤ) K ≪≫
    Functor.isoWhiskerRight e (HomotopyCategory.quotient B (.up ℤ)),
    inferInstance, inferInstance⟩

end CochainComplex
