/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisData
import WeilConjectures.AlgebraicGeometry.OpenUnionModuleImagePullback
import WeilConjectures.AlgebraicGeometry.InjectiveRestrictionSurjective
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.Algebra.Homology.HomologicalComplexBiprod

/-! # Exactness of the concrete complex on an arbitrary open union

Source: Stacks Project, Tag 08BV, displayed sequence applied on the union.
(blueprint: lem-pc-open-union-image-complex-exact).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem schemeRestrictUnit_epi
    (X : Scheme.{u}) (U : X.Opens)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [Injective M] :
    Epi ((Scheme.Modules.restrictAdjunction U.ι).unit.app M) := by
  have hv : Epi ((Scheme.Modules.restrictAdjunction U.ι).unit.app M).val := by
    apply PresheafOfModules.epi_of_surjective
    intro T
    change Function.Surjective
      (Scheme.Modules.Hom.app ((Scheme.Modules.restrictAdjunction U.ι).unit.app M) T.unop)
    rw [Scheme.Modules.restrictAdjunction_unit_app_app]
    exact (injective_restriction_surjective X.toRingedSpace
      (U.ι.image_preimage_le T.unop) M).1
  constructor
  intro Z g h eq
  apply SheafOfModules.hom_ext
  exact (cancel_epi ((Scheme.Modules.restrictAdjunction U.ι).unit.app M).val).mp
    (congrArg SheafOfModules.Hom.val eq)

private theorem schemeOpenModuleUnit_epi
    (X : Scheme.{u}) (U : X.Opens)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [Injective M] :
    Epi ((schemeOpenModuleAdjunction X U).unit.app M) := by
  have := schemeRestrictUnit_epi X U M
  change Epi ((Scheme.Modules.restrictAdjunction U.ι).unit.app M ≫
    (Scheme.Modules.pushforward U.ι).map ((Scheme.Modules.overFunctorEquiv U).inv.app M))
  infer_instance

private theorem schemeOpenModuleImageRestriction_epi
    (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [Injective M] :
    Epi ((schemeOpenModuleImageRestriction X i).app M) := by
  have := schemeOpenModuleUnit_epi X W M
  have : Epi ((schemeOpenModuleAdjunction X U).unit.app M ≫
      (schemeOpenModuleImageRestriction X i).app M) := by
    rw [schemeOpenModuleImage_unit_restriction]
    infer_instance
  exact epi_of_epi ((schemeOpenModuleAdjunction X U).unit.app M) _

private theorem shortExact_of_degreewise_pullback
    {C : Type*} [Category C] [Abelian C]
    {A B D E : CochainComplex C ℤ}
    (a : A ⟶ B) (b : A ⟶ D) (c : B ⟶ E) (d : D ⟶ E)
    (h : ∀ n, IsPullback (a.f n) (b.f n) (c.f n) (d.f n))
    (hc : ∀ n, Epi (c.f n)) :
    ∃ hz : biprod.lift a b ≫ biprod.desc c (-d) = 0,
      (ShortComplex.mk (biprod.lift a b) (biprod.desc c (-d)) hz).ShortExact := by
  have hz : biprod.lift a b ≫ biprod.desc c (-d) = 0 := by
    rw [biprod.lift_desc, Preadditive.comp_neg]
    apply add_neg_eq_zero.mpr
    ext n
    exact (h n).w
  refine ⟨hz, ?_⟩
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
    (ShortComplex.mk (biprod.lift a b) (biprod.desc c (-d)) hz)
  intro n
  have : Epi (c.f n) := hc n
  have : Epi (h n).shortComplex'.g := by
    have : Epi (biprod.inl ≫ (h n).shortComplex'.g) := by
      simpa only [CommSq.shortComplex'_g, biprod.inl_desc] using hc n
    exact epi_of_epi biprod.inl _
  have he : (h n).shortComplex'.ShortExact :=
    ShortComplex.ShortExact.mk' (IsPullback.exact_shortComplex' (h n))
      (h n).mono_shortComplex'_f inferInstance
  let F := HomologicalComplex.eval C (ComplexShape.up ℤ) n
  let e : (ShortComplex.mk (biprod.lift a b) (biprod.desc c (-d)) hz).map F ≅
      (h n).shortComplex' :=
    ShortComplex.isoMk (Iso.refl _) (F.mapBiprod B D) (Iso.refl _) (by
      change 𝟙 _ ≫ biprod.lift (a.f n) (b.f n) = _
      rw [Category.id_comp]
      exact (biprod.map_lift_mapBiprod F B D a b).symm) (by
      change _ ≫ biprod.desc (c.f n) (-d.f n) = _ ≫ 𝟙 _
      rw [Category.comp_id]
      exact biprod.mapBiprod_hom_desc F B D c (-d))
  exact ShortComplex.shortExact_of_iso e.symm he

/-- The pair of restrictions from the union and the difference to the overlap
form a short exact sequence for a complex with injective terms.

Source: Stacks Project, Tag 08BV, lemma-exact-sequence-j-star, the displayed
sequence of complexes; Tag 01EB, lemma-mayer-vietoris, its sectionwise proof.
(blueprint: lem-pc-open-union-image-complex-exact).

Proof: In degree n over a test open T, identify the four direct-image terms
with I^n(T intersection (U union V)), I^n(T intersection U),
I^n(T intersection V), and I^n(T intersection U intersection V).
The underived adjunction mate defining each arrow is ordinary restriction:
the nested-restriction comparison identifies iterated restriction, and its
counit cancels the repeated restriction to the larger open. The two iterated
restrictions to the overlap agree, so the pair followed by the difference is
zero. The opens T intersection U and T intersection V cover
T intersection (U union V). Sheaf uniqueness gives injectivity of the first
map; sheaf gluing identifies its image with the kernel of the second map.
Injectivity of I^n makes restriction from T intersection U to the overlap
surjective (injective_restriction_surjective), so pairing a lift with zero
gives surjectivity of the difference. The sectionwise kernel property is
natural in T, hence a kernel in presheaf modules and, by the fully faithful
inclusion, in sheaf modules. Sectionwise injectivity and surjectivity give
monicity and epicity. Evaluation of complexes preserves biproducts; use its
biproduct comparison and HomologicalComplex.shortExact_of_degreewise_shortExact
to conclude. No K-injectivity or derived category is used. Empty opens give
zero summands; repeated opens give the diagonal/difference split sequence. -/
theorem schemeOpenUnionImageComplex_shortExact
    (X : Scheme.{u}) (U V : X.Opens)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hI : ∀ n : ℤ, Injective (I.X n)) :
    let f := biprod.lift
      (schemeOpenModuleImageComplexRestriction X (homOfLE (le_sup_left : U ≤ U ⊔ V)) I)
      (schemeOpenModuleImageComplexRestriction X (homOfLE (le_sup_right : V ≤ U ⊔ V)) I)
    let g := biprod.desc
      (schemeOpenModuleImageComplexRestriction X (homOfLE (inf_le_left : U ⊓ V ≤ U)) I)
      (-(schemeOpenModuleImageComplexRestriction X (homOfLE (inf_le_right : U ⊓ V ≤ V)) I))
    ∃ h : f ≫ g = 0, (ShortComplex.mk f g h).ShortExact := by
  apply shortExact_of_degreewise_pullback
    (schemeOpenModuleImageComplexRestriction X (homOfLE (le_sup_left : U ≤ U ⊔ V)) I)
    (schemeOpenModuleImageComplexRestriction X (homOfLE (le_sup_right : V ≤ U ⊔ V)) I)
    (schemeOpenModuleImageComplexRestriction X (homOfLE (inf_le_left : U ⊓ V ≤ U)) I)
    (schemeOpenModuleImageComplexRestriction X (homOfLE (inf_le_right : U ⊓ V ≤ V)) I)
  · exact fun n ↦ schemeOpenUnionModuleImage_isPullback X U V (I.X n)
  · intro n
    have : Injective (I.X n) := hI n
    exact schemeOpenModuleImageRestriction_epi X _ (I.X n)

end AlgebraicGeometry
