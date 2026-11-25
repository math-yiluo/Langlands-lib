/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenTensorRestrictionIso
public import WeilConjectures.AlgebraicGeometry.OpenDerivedAdditiveStalkIso
public import WeilConjectures.AlgebraicGeometry.AffineSpectrumOrdinaryComparisonSquare
public import WeilConjectures.AlgebraicGeometry.StalkComparisonPullbackNaturality
import WeilConjectures.Algebra.Homology.BaseDerivedTensorRingTransport
import WeilConjectures.AlgebraicGeometry.OpenOrdinaryTensorGermTransport

/-! # Open restriction of the ordinary tensor comparison

Source: Stacks Project, perfect.tex, equation-bc before Tag 0DJ8 and Tag 0DJ9.
(blueprint: lem-pc-single-complex-open-ordinary-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry
open SingleComplexBaseChange
set_option synthInstance.maxSize 2048

/-- Inverting a pullback counit and then applying it recovers the ordinary comparison.
Source: the definition of `comparisonIntoPullback`.
(blueprint: lem-pc-single-complex-open-ordinary-comparison). -/
theorem comparisonIntoPullback_comp_counit
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (z : X')
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (i : ℤ) :
    comparisonIntoPullback f f' g g' sq z P hcP i ≫
      (comparisonStalkCohomology X' z i).map
        (cast (by rfl) ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) =
      comparisonIntoTensorPullback f f' g g' sq z P i := by
  have := hcP
  simp only [comparisonIntoPullback, comparisonIntoTensorPullback, cast_eq, Category.assoc,
    ← Functor.map_comp, IsIso.inv_hom_id]
  simp

private theorem open_comparison_paste
    {C₀ C D : Type*} [Category C₀] [Category C] [Category D]
    (F₀ : C₀ ⥤ D) (F : C ⥤ D)
    {A₀ B₀ E₀ G₀ : C₀} {A B E : C}
    (m₀ : A₀ ⟶ B₀) (m : A ⟶ B) (k₀ : B₀ ⟶ E₀) (k : B ⟶ E)
    (β : E₀ ⟶ G₀) (ν : F₀.obj G₀ ⟶ F.obj E)
    (r : F₀.obj B₀ ⟶ F.obj B) (l : F₀.obj A₀ ⟶ F.obj A)
    (ht : F₀.map k₀ ≫ F₀.map β ≫ ν = r ≫ F.map k)
    (hl : F₀.map m₀ ≫ r = l ≫ F.map m) :
    F₀.map (m₀ ≫ k₀) ≫ F₀.map β ≫ ν = l ≫ F.map (m ≫ k) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [ht, ← Category.assoc, hl]
  simp only [Category.assoc]

/-- Scalar transport of the base-derived tensor comparison to the ordinary pullback.
This statement concerns arbitrary complexes, without K-flatness or derived counits.

Proof: identify the four open stalk rings with the original stalk rings by the
open-immersion stalk maps. The identities `stalkMap_comp`, `hj`, and the two
restriction squares identify their algebra structures and tensor-to-stalk maps.
The natural same-germ restriction-stalk isomorphism identifies the input complexes
semilinearly. Exact equivalences along the ring isomorphisms transport the universal
left-derived scalar extensions and their counits. Apply cohomology. Naturality for
multiplication and `cohomologyIso_smul` identify the tensor-algebra actions, so this
cohomology isomorphism is semilinear over the tensor-algebra isomorphism. Extend to
the final stalk ring and forget scalars to obtain l. The equations `comparison_eq`
and `localized_eq` identify the transported comparison with the original one.
The tensor-stalk identifications and the conjugate-of-pushforward ordinary pullback
composition send each germ tensor to the same germ tensor. Thus their comparison
is exactly `singleComplexOpenTensorRestrictionMap`. The exact restriction and
homology localization factors give the displayed square with the constructed nu.
There are no points on empty opens; top opens, zero complexes, and zero stalk rings
require no separate argument. No flatness over the base stalk is used.

Source: Stacks Project, perfect.tex, equation-bc before Tag 0DJ8 and Tag 0DJ9,
first paragraph; cohomology.tex, Tags 08HY and 08FE.
(blueprint: lem-pc-single-complex-open-ordinary-comparison). -/
theorem exists_singleComplexOpen_ordinary_comparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (sq₀ : IsPullback j (f' ∣_ V') (f ∣_ V) (g.resLE V V' hV'))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (z : (f' ⁻¹ᵁ V').toScheme) (i : ℤ) :
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).Additive :=
      schemeOpenRestriction_additive X (f ⁻¹ᵁ V)
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    let Q := ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapHomologicalComplex (.up ℤ)).obj P
    let F₀ := forget₂ (ModuleCat.{u} ((f' ⁻¹ᵁ V').toScheme.presheaf.stalk z)) AddCommGrpCat.{u}
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z.val)) AddCommGrpCat.{u}
    let H₀ := comparisonStalkCohomology (f' ⁻¹ᵁ V').toScheme z i
    let β := singleComplexOpenTensorRestrictionMap g' (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj P
    let ν := openDerivedAdditiveStalkIso X' (f' ⁻¹ᵁ V') z i
    ∃ l : F₀.obj ((Arrow.mk (comparisonIntoTensorPullback (f ∣_ V) (f' ∣_ V')
        (g.resLE V V' hV') j sq₀ z Q i)).left) ≅
        F.obj ((Arrow.mk (comparisonIntoTensorPullback f f' g g' sq z.val P i)).left),
      F₀.map (comparisonIntoTensorPullback (f ∣_ V) (f' ∣_ V')
          (g.resLE V V' hV') j sq₀ z Q i) ≫
        F₀.map (H₀.map β) ≫
          ν.hom.app (DerivedCategory.Q.obj
            (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)) =
      l.hom ≫ F.map (comparisonIntoTensorPullback f f' g g' sq z.val P i) := by
  dsimp only
  have : (schemeOpenRestriction X (f ⁻¹ᵁ V)).Additive :=
    schemeOpenRestriction_additive X (f ⁻¹ᵁ V)
  let Q₀ := ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapHomologicalComplex (.up ℤ)).obj P
  let := leftAlgebra (f ∣_ V) j z
  let := rightAlgebra (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z
  let := (tensorMap (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z).toAlgebra
  let := leftAlgebra f g' z.val
  let := rightAlgebra f f' g g' sq z.val
  let := (tensorMap f f' g g' sq z.val).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (R (f ∣_ V) j z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (B (f' ∣_ V') z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z.val))
  let := HasDerivedCategory.standard (ModuleCat.{u} (B f' z.val))
  -- Select the data without nested existential eliminations over the large comparison goal.
  choose eR eA eB eC hRA hRB hCA hCB α hα τ hτ ht using
    exists_openOrdinaryTensor_germ_transport f f' g g' sq V V' hV' j hj sq₀ P z i
  let M := cohomologyModel (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z Q₀
  let N := cohomologyModel f f' g g' sq z.val P
  choose l hl using ModuleCat.exists_baseDerivedTensor_ring_transport
    (stalkComplex j z Q₀) (stalkComplex g' z.val P) M N
    eR eA eB eC hRA hRB hCA hCB α hα τ hτ i
  let F₀ := forget₂ (ModuleCat.{u} ((f' ⁻¹ᵁ V').toScheme.presheaf.stalk z)) AddCommGrpCat.{u}
  let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z.val)) AddCommGrpCat.{u}
  let T₀ := tensorComplex (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z Q₀
  let T := tensorComplex f f' g g' sq z.val P
  let k₀ := HomologicalComplex.homologyMap
    (tensorStalkIso (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z Q₀).hom i ≫
    (comparisonStalkHomologyIso (f' ⁻¹ᵁ V').toScheme z
      (((Scheme.Modules.tensorPullback j).mapHomologicalComplex (.up ℤ)).obj Q₀) i).inv
  let k := HomologicalComplex.homologyMap (tensorStalkIso f f' g g' sq z.val P).hom i ≫
    (comparisonStalkHomologyIso X' z.val
      (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) i).inv
  let r := ((T₀.sc i).mapHomologyIso F₀).inv ≫
    HomologicalComplex.homologyMap τ.hom i ≫ ((T.sc i).mapHomologyIso F).hom
  let H₀ := comparisonStalkCohomology (f' ⁻¹ᵁ V').toScheme z i
  let β := singleComplexOpenTensorRestrictionMap g' (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj P
  let ν := openDerivedAdditiveStalkIso X' (f' ⁻¹ᵁ V') z i
  let W := letI : HasDerivedCategory.{w} X'.Modules :=
      (inferInstance : ∀ Y : Scheme.{u},
        HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))) X'
    DerivedCategory.Q.obj
      (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)
  have ht' : F₀.map k₀ ≫ F₀.map (H₀.map β) ≫ ν.hom.app W = r ≫ F.map k := ht
  have hl' : F₀.map (M.localizedComparison i) ≫ r =
      l.hom ≫ F.map (N.localizedComparison i) := hl
  refine ⟨l, ?_⟩
  change F₀.map (M.localizedComparison i ≫ k₀) ≫
      F₀.map (H₀.map β) ≫ ν.hom.app W =
    l.hom ≫ F.map (N.localizedComparison i ≫ k)
  exact open_comparison_paste F₀ F (M.localizedComparison i) (N.localizedComparison i)
    k₀ k (H₀.map β) (ν.hom.app W) r l.hom ht' hl'

end AlgebraicGeometry
