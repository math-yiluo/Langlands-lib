/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData
public import WeilConjectures.AlgebraicGeometry.StalkComparisonPullbackNaturality
public import Mathlib.CategoryTheory.Comma.Arrow
public import WeilConjectures.AlgebraicGeometry.OpenDerivedAdditiveStalkIso
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.OpenRestrictionKFlatModel
import WeilConjectures.AlgebraicGeometry.IsomorphismPullbackCounit
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenOrdinaryComparison
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenTermwiseCounitCompatibility

/-! # The normalized comparison on a termwise restricted complex

Source: Stacks Project, perfect.tex, Tag 0DJ9 first paragraph and equation-bc
preceding Tag 0DJ8; cohomology.tex, Tags 08HY and 08FE.
(blueprint: lem-pc-single-complex-open-termwise-comparison).
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

@[reassoc] private theorem termwise_counit_transport
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    (F : C ⥤ D) [F.Additive] (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex C ℤ) :
    L.map ((DerivedCategory.quotientCompQhIso C).inv.app P) ≫
      ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
      (DerivedCategory.quotientCompQhIso D).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) := by
  change L.map (𝟙 _) ≫ ε.app _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _ = _
  erw [L.map_id, DerivedCategory.Qh.map_id]
  change 𝟙 _ ≫ ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) ≫ 𝟙 _ ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

private theorem comparison_square_cancel
    {C : Type*} [Category C] {S₀ S T₀ T U₀ W₀ V₀ V : C}
    (p₀ : S₀ ⟶ T₀) (p : S ⟶ T) (l : S₀ ⟶ S) (d : T₀ ⟶ U₀)
    (ν : U₀ ⟶ T) (e : T ⟶ V) [Mono e]
    (e₀ : T₀ ⟶ W₀) (β : W₀ ⟶ V₀) (r : U₀ ⟶ V₀) (μ : V₀ ⟶ V)
    (hd : d ≫ r = e₀ ≫ β) (hν : r ≫ μ = ν ≫ e)
    (o₀ : S₀ ⟶ W₀) (o : S ⟶ V)
    (h₀ : p₀ ≫ e₀ = o₀) (h : p ≫ e = o)
    (ho : o₀ ≫ β ≫ μ = l ≫ o) :
    p₀ ≫ d ≫ ν = l ≫ p := by
  apply (cancel_mono e).mp
  simp only [Category.assoc]
  rw [← hν, ← Category.assoc d r, hd]
  calc
    p₀ ≫ (e₀ ≫ β) ≫ μ = o₀ ≫ β ≫ μ := by
      simp only [Category.assoc]
      rw [← Category.assoc p₀ e₀, h₀]
    _ = l ≫ o := ho
    _ = l ≫ p ≫ e := by rw [← h]

set_option linter.unusedVariables false in
-- Keep the original unused local H in the statement unchanged.
/-- Open restriction transports the normalized tensor comparison on the literal
termwise restriction of the source complex. There is no independently chosen
restricted representative or representing isomorphism.

Proof: put U = f⁻¹V and U' = f'⁻¹V'. The open stalk maps identify the four
local rings with their unrestricted counterparts. The identities stalkMap_comp,
hj, and the restricted cartesian square identify every structure map and the
map from the tensor algebra to the last stalk ring. Restrict P degreewise.
Restriction is tensor pullback along the open immersion and preserves K-flatness.
The universal derived counit is invertible on this K-flat complex; uniqueness of
the left-derived functor transfers that property to the pinned counit hcP0.
The restriction-stalk isomorphism identifies its stalk complex with the
original stalk complex after extension along the open stalk-ring isomorphism.
Transport the universal left-derived scalar extension through these exact ring
equivalences. Its counit-compatible uniqueness identifies the derived tensor
cohomology objects; naturality of multiplication and cohomologyIso_smul make
this identification linear over the identified tensor algebra. Extension to
the last stalk ring gives the source isomorphism l. The natural isomorphism ν is
openDerivedAdditiveStalkIso, constructed from exact restriction and
restrictStalkNatIso by localization and cohomology.
The comparison_eq and localized_eq equations express both comparison maps
by the same transported scalar-extension counit. The factorization identity
for leftDerivedUnique in singleComplexOpenPullbackIso and the pinned composition
comparisons identify the map to restricted derived pullback with the displayed
restricted identity coefficient. Apply cohomology to obtain the stated square.
The representing isomorphism a is the localization factor of actual termwise
restriction; no comparison of arbitrary representatives is part of this lemma.
For empty opens there is no z; top opens, zero complexes and zero rings use
exactly the same isomorphisms. No base flatness or bounds are needed.

Source: Stacks Project, perfect.tex, Tag 0DJ9 first paragraph and equation-bc
preceding Tag 0DJ8; cohomology.tex, Tags 08HY and 08FE.
(blueprint: lem-pc-single-complex-open-termwise-comparison). -/
theorem exists_singleComplexOpen_termwise_comparison
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
    (hP : P.IsKFlatTensor)
    (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (z : (f' ⁻¹ᵁ V').toScheme) (i : ℤ) :
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).Additive :=
      schemeOpenRestriction_additive X (f ⁻¹ᵁ V)
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    let K := DerivedCategory.Q.obj P
    let Q := ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapHomologicalComplex (.up ℤ)).obj P
    let a : DerivedCategory.Q.obj Q ≅
        (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj K :=
      (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategoryFactors.symm.app P
    let F₀ := forget₂ (ModuleCat.{u} ((f' ⁻¹ᵁ V').toScheme.presheaf.stalk z)) AddCommGrpCat.{u}
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z.val)) AddCommGrpCat.{u}
    let H₀ := comparisonStalkCohomology (f' ⁻¹ᵁ V').toScheme z i
    let H := comparisonStalkCohomology X' z.val i
    let θ := singleComplexRestrictedCoefficient g' K ((derivedPullback g').obj K) (𝟙 _)
      (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj
    ∃ (_hP₀ : CochainComplex.IsKFlatTensor (R := (f ⁻¹ᵁ V).toScheme.sheaf) Q),
    ∃ (hcP₀ : IsIso ((counit j).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj Q))),
    let ν := openDerivedAdditiveStalkIso X' (f' ⁻¹ᵁ V') z i
    ∃ l : F₀.obj ((Arrow.mk (comparisonIntoPullback (f ∣_ V) (f' ∣_ V')
        (g.resLE V V' hV') j sq₀ z Q hcP₀ i)).left) ≅
        F.obj ((Arrow.mk (comparisonIntoPullback f f' g g' sq z.val P hcP i)).left),
      F₀.map (comparisonIntoPullback (f ∣_ V) (f' ∣_ V')
          (g.resLE V V' hV') j sq₀ z Q hcP₀ i ≫
        H₀.map ((derivedPullback j).map a.hom ≫ θ)) ≫
          ν.hom.app ((derivedPullback g').obj K) =
      l.hom ≫ F.map (comparisonIntoPullback f f' g g' sq z.val P hcP i) := by
  classical
  have : (schemeOpenRestriction X (f ⁻¹ᵁ V)).Additive :=
    schemeOpenRestriction_additive X (f ⁻¹ᵁ V)
  have : (schemeOpenRestriction X (f ⁻¹ᵁ V)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  have hQ : CochainComplex.IsKFlatTensor (R := (f ⁻¹ᵁ V).toScheme.sheaf)
      (((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapHomologicalComplex (.up ℤ)).obj P) :=
    openRestriction_isKFlat X (f ⁻¹ᵁ V) P hP
  let Q := ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapHomologicalComplex (.up ℤ)).obj P
  have hcQ := counit_isIso_kFlat j Q hQ
  refine ⟨hQ, hcQ, ?_⟩
  have hs := exists_singleComplexOpen_ordinary_comparison
    f f' g g' sq V V' hV' j hj sq₀ P z i
  let l := hs.choose
  have hl := hs.choose_spec
  refine ⟨l, ?_⟩
  let K := DerivedCategory.Q.obj P
  let a := (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategoryFactors.symm.app P
  let F₀ := forget₂ (ModuleCat.{u} ((f' ⁻¹ᵁ V').toScheme.presheaf.stalk z))
    AddCommGrpCat.{u}
  let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z.val)) AddCommGrpCat.{u}
  let H₀ := comparisonStalkCohomology (f' ⁻¹ᵁ V').toScheme z i
  let H := comparisonStalkCohomology X' z.val i
  let θ := singleComplexRestrictedCoefficient g' K ((derivedPullback g').obj K) (𝟙 _)
    (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj
  let β := singleComplexOpenTensorRestrictionMap g' (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj P
  let ν := openDerivedAdditiveStalkIso X' (f' ⁻¹ᵁ V') z i
  let ε := (counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  let ε₀ := (counit j).app ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)
  have : IsIso ε := hcP
  have hcompat := singleComplexOpen_termwise_counit_compatibility
    g' (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj P
  have hcompat' :
      F₀.map (H₀.map ((derivedPullback j).map a.hom ≫ θ)) ≫
          F₀.map (H₀.map
            ((schemeOpenRestriction X' (f' ⁻¹ᵁ V')).mapDerivedCategory.map ε)) =
        F₀.map (H₀.map ε₀) ≫ F₀.map (H₀.map β) := by
    have : (Scheme.Modules.tensorPullback g').Additive := tensorPullbackAdditive g'
    have : (Scheme.Modules.tensorPullback j).Additive := tensorPullbackAdditive j
    dsimp only at hcompat
    simp only [termwise_counit_transport
      (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (D := SheafOfModules.{u} (moduleRings X'.toRingedSpace))
      (Scheme.Modules.tensorPullback g') (derivedPullback g') (counit g') P,
      termwise_counit_transport_assoc
        (C := SheafOfModules.{u} (moduleRings (f ⁻¹ᵁ V).toScheme.toRingedSpace))
        (D := SheafOfModules.{u} (moduleRings (f' ⁻¹ᵁ V').toScheme.toRingedSpace))
        (Scheme.Modules.tensorPullback j)
        (derivedPullback j) (counit j)
        (((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapHomologicalComplex (.up ℤ)).obj P)] at hcompat
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun t => F₀.map (H₀.map t)) hcompat
  have hν := ν.hom.naturality ε
  have hP₀ := congrArg F₀.map (comparisonIntoPullback_comp_counit
    (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z Q hcQ i)
  have hP' := congrArg F.map
    (comparisonIntoPullback_comp_counit f f' g g' sq z.val P hcP i)
  have hn :
      F₀.map (H₀.map
          ((schemeOpenRestriction X' (f' ⁻¹ᵁ V')).mapDerivedCategory.map ε)) ≫
        ν.hom.app (DerivedCategory.Q.obj
          (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)) =
      ν.hom.app ((derivedPullback g').obj K) ≫ F.map (H.map ε) := hν
  have hh := comparison_square_cancel
    (F₀.map (comparisonIntoPullback (f ∣_ V) (f' ∣_ V')
      (g.resLE V V' hV') j sq₀ z Q hcQ i))
    (F.map (comparisonIntoPullback f f' g g' sq z.val P hcP i))
    l.hom (F₀.map (H₀.map ((derivedPullback j).map a.hom ≫ θ)))
    (ν.hom.app ((derivedPullback g').obj K)) (F.map (H.map ε))
    (F₀.map (H₀.map ε₀)) (F₀.map (H₀.map β))
    (F₀.map (H₀.map
      ((schemeOpenRestriction X' (f' ⁻¹ᵁ V')).mapDerivedCategory.map ε)))
    (ν.hom.app (DerivedCategory.Q.obj
      (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)))
    hcompat' hn
    (F₀.map (comparisonIntoTensorPullback (f ∣_ V) (f' ∣_ V')
      (g.resLE V V' hV') j sq₀ z Q i))
    (F.map (comparisonIntoTensorPullback f f' g g' sq z.val P i))
    (by simpa only [cast_eq, Functor.map_comp] using hP₀)
    (by simpa only [cast_eq, Functor.map_comp] using hP') hl
  simpa only [Functor.map_comp, Category.assoc] using hh

end AlgebraicGeometry
