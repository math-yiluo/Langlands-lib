/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.AlgebraicGeometry.OpenUnionImageComplexExact
import WeilConjectures.AlgebraicGeometry.LocalizedOpenImageComplexComparisons
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective

/-! # Short exact presentation on an arbitrary open union

Source: Stacks Project, Tag 08BV, applied on the open union and pushed to X.
(blueprint: lem-sc-derived-open-union-ses-presentation).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Pretriangulated
namespace AlgebraicGeometry

private theorem exists_injective_representative
    {M : Type*} [Category.{u} M] [Abelian M] [IsGrothendieckAbelian.{u} M]
    [HasDerivedCategory.{w} M] (E : DerivedCategory M) :
    ∃ I : CochainComplex M ℤ, I.IsKInjective ∧
      (∀ n : ℤ, Injective (I.X n)) ∧ Nonempty (DerivedCategory.Q.obj I ≅ E) := by
  classical
  let K := DerivedCategory.Q.objPreimage E
  let I := (CochainComplex.kInjectiveResolutionFunctor.{u} M).obj K
  let η : K ⟶ I := (CochainComplex.toKInjectiveResolution.{u} M).app K
  have : QuasiIso η :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} M K).2
  refine ⟨I, CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} M K,
    fun n ↦ CochainComplex.injective_kInjectiveResolutionFunctor_obj_X.{u} K n,
    ⟨(asIso (DerivedCategory.Q.map η)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso E⟩⟩

private theorem map_pair_comparison
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C]
    [HasZeroMorphisms D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (Q : C ⥤ D) [Q.PreservesZeroMorphisms] [PreservesBinaryBiproducts Q]
    {A B C' : C} {A' B' C'' : D} (f : A ⟶ B) (g : A ⟶ C')
    (eA : Q.obj A ≅ A') (eB : Q.obj B ≅ B') (eC : Q.obj C' ≅ C'')
    (a : A' ⟶ B') (b : A' ⟶ C'')
    (hf : Q.map f ≫ eB.hom = eA.hom ≫ a)
    (hg : Q.map g ≫ eC.hom = eA.hom ≫ b) :
    Q.map (biprod.lift f g) ≫
        (Q.mapBiprod B C' ≪≫ biprod.mapIso eB eC).hom =
      eA.hom ≫ biprod.lift a b := by
  dsimp only [Iso.trans_hom, biprod.mapIso]
  rw [← Category.assoc, biprod.map_lift_mapBiprod]
  apply biprod.hom_ext
  · simpa only [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc,
      biprod.lift_fst] using hf
  · simpa only [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc,
      biprod.lift_snd] using hg

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
/-- A short exact sequence of complexes representing the three direct-image terms
on an arbitrary open union, with the first arrow identified by adjunction.
No connecting morphism, integer shift, or distinguished triangle is asserted.

Source: Stacks Project, Tag 08BV (lemma-exact-sequence-j-star), its short exact
sequence of complexes applied on the union; Tag 079W (lemma-adjoint).
(blueprint: lem-sc-derived-open-union-ses-presentation).

Proof: Write W = U union V and O = U intersect V. Choose a K-injective
representative I of E with injective terms. Exact restriction to each open
preserves K-injectivity, because extension by zero is an exact left adjoint.
For T = W, U, V, O, form J_T by applying the ordinary open direct image to
I restricted to T, term by term. Thus J_T represents the right derived direct
image of the restriction of E. Take S to have terms J_W, J_U direct-sum J_V,
and J_O, with first map the pair of restrictions and second map their difference.
On any open Z, its degree n sequence is the section sequence on Z intersect W,
Z intersect U, Z intersect V, and Z intersect O. Since U and V cover W,
sheaf gluing gives injectivity and exactness at the middle. The last map is
surjective: injectivity implies flasqueness and a section on Z intersect O
lifts to Z intersect U. Hence S is short exact in every degree.
Compare localized-site restriction with restriction to the open subscheme by
Modules.overEquiv and exact derived factorization. The derived direct-image
adjunction then identifies Q(J_T) with G_T R_T(E) by uniqueness of right
adjoints, giving eA, eB, eC (using the biproduct comparison for eB).
These comparisons are compatible with counits. The union counit is the
transpose of identity on G_W R_W(E). Its restriction to U is obtained by
conjugating the image under nested restriction by the canonical composition
comparison, exactly derivedOpenHomRestriction. The adjunction mate is the
U component of the first map; the same argument gives its V component.
The biproduct universal property gives the displayed equality. This
construction uses no compactness or quasi-coherence. When either open is
empty the corresponding direct-image term is zero; when U = V the sequence
is the diagonal/difference split sequence. Thus these edge cases need no
additional hypotheses. -/
theorem derived_open_union_ses_presentation
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ W : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    (U V : X.Opens)
    (G : ∀ W : X.Opens,
      DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W)) ⥤
        schemeDerivedCategory X)
    (adj : ∀ W : X.Opens,
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory ⊣
        G W)
    (E : schemeDerivedCategory X) :
    let R := fun W : X.Opens ↦
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory
    let A := (G (U ⊔ V)).obj ((R (U ⊔ V)).obj E)
    let B := (G U).obj ((R U).obj E) ⊞ (G V).obj ((R V).obj E)
    let C := (G (U ⊓ V)).obj ((R (U ⊓ V)).obj E)
    let β := ((adj (U ⊔ V)).homEquiv A ((R (U ⊔ V)).obj E)).symm (𝟙 A)
    let b := biprod.lift
      ((adj U).homEquiv A ((R U).obj E)
        (derivedOpenHomRestriction X.toRingedSpace (homOfLE le_sup_left) β))
      ((adj V).homEquiv A ((R V).obj E)
        (derivedOpenHomRestriction X.toRingedSpace (homOfLE le_sup_right) β))
    ∃ (S : ShortComplex
        (CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ))
      (eA : DerivedCategory.Q.obj S.X₁ ≅ A)
      (eB : DerivedCategory.Q.obj S.X₂ ≅ B)
      (_ : DerivedCategory.Q.obj S.X₃ ≅ C),
      S.ShortExact ∧ DerivedCategory.Q.map S.f ≫ eB.hom = eA.hom ≫ b := by
  classical
  dsimp only
  let M := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let : Abelian M := inferInstance
  have : IsGrothendieckAbelian.{u} M :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  have hrep := exists_injective_representative.{u, w} (M := M) E
  let I := hrep.choose
  have : I.IsKInjective := hrep.choose_spec.1
  have hI : ∀ n : ℤ, Injective (I.X n) := hrep.choose_spec.2.1
  let e := hrep.choose_spec.2.2.some
  let Q : CochainComplex M ℤ ⥤ schemeDerivedCategory X := DerivedCategory.Q
  change DerivedCategory.Q.obj I ≅ E at e
  have hc := schemeOpenModuleImageComplex_localized_comparisons.{u, w} X G adj I E e
  dsimp only at hc
  obtain ⟨eT, hT⟩ := hc
  have hs := schemeOpenUnionImageComplex_shortExact X U V I hI
  dsimp only at hs
  obtain ⟨hz, hS⟩ := hs
  let f := biprod.lift
    (schemeOpenModuleImageComplexRestriction X (homOfLE (le_sup_left : U ≤ U ⊔ V)) I)
    (schemeOpenModuleImageComplexRestriction X (homOfLE (le_sup_right : V ≤ U ⊔ V)) I)
  let g := biprod.desc
    (schemeOpenModuleImageComplexRestriction X (homOfLE (inf_le_left : U ⊓ V ≤ U)) I)
    (-(schemeOpenModuleImageComplexRestriction X (homOfLE (inf_le_right : U ⊓ V ≤ V)) I))
  let S := ShortComplex.mk f g hz
  have : PreservesBinaryBiproducts Q := preservesBinaryBiproducts_of_preservesBiproducts Q
  let eB := Q.mapBiprod (schemeOpenModuleImageComplex X U I)
    (schemeOpenModuleImageComplex X V I) ≪≫ biprod.mapIso (eT U) (eT V)
  refine ⟨S, eT (U ⊔ V), eB, eT (U ⊓ V), hS, ?_⟩
  change DerivedCategory.Q.map S.f ≫ eB.hom = _
  exact map_pair_comparison Q
    (schemeOpenModuleImageComplexRestriction X (homOfLE (le_sup_left : U ≤ U ⊔ V)) I)
    (schemeOpenModuleImageComplexRestriction X (homOfLE (le_sup_right : V ≤ U ⊔ V)) I)
    (eT (U ⊔ V)) (eT U) (eT V) _ _
    (hT (U ⊔ V) U (homOfLE le_sup_left))
    (hT (U ⊔ V) V (homOfLE le_sup_right))

end AlgebraicGeometry
