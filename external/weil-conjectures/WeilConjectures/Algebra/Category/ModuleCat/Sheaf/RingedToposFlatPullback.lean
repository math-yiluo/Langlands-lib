/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite

import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits

/-!
# Pullback of flat modules along morphisms of ringed topoi

Source: Stacks Project, Modules on Sites, Tag 05VD, lemma-pullback-flat
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe uC vC uD vD r m

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

section ScalarExtension

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max r m}]
  [HasWeakSheafify J AddCommGrpCat.{max r m}]
  {R S : Sheaf J CommRingCat.{r}} (c : R ⟶ S)
  (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))

omit [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})] in
private theorem forget_preserves_colimits (A : Sheaf J RingCat.{r}) :
    PreservesFiniteColimits (toSheaf.{max r m} A) := by
  constructor
  intro K _ _
  constructor
  intro F
  let L := PresheafOfModules.sheafification.{max r m} (𝟙 A.obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{max r m} (𝟙 A.obj)
  let G := F ⋙ (SheafOfModules.forget A ⋙ PresheafOfModules.restrictScalars (𝟙 A.obj))
  let e : G ⋙ L ≅ F := Functor.isoWhiskerLeft F (asIso adj.counit) ≪≫ F.rightUnitor
  have : PreservesColimitsOfShape K (presheafToSheaf J AddCommGrpCat.{max r m}) :=
    (sheafificationAdjunction J AddCommGrpCat.{max r m}).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  have : PreservesColimit G (L ⋙ toSheaf.{max r m} A) :=
    preservesColimit_of_natIso G (PresheafOfModules.sheafificationCompToSheaf (𝟙 A.obj)).symm
  let hc := colimit.isColimit G
  have : PreservesColimit (G ⋙ L) (toSheaf.{max r m} A) :=
    preservesColimit_of_preserves_colimit_cocone (isColimitOfPreserves L hc)
      (isColimitOfPreserves (L ⋙ toSheaf.{max r m} A) hc)
  exact preservesColimit_of_iso_diagram (toSheaf.{max r m} A) e

private theorem restrict_exact :
    exactFunctor _ _ (restrictScalars.{max r m}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map c)) := by
  let R' := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
  let S' := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S
  let res := restrictScalars.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map c)
  have := forget_preserves_colimits.{uC, vC, r, m} R'
  have := forget_preserves_colimits.{uC, vC, r, m} S'
  have : PreservesFiniteLimits (res ⋙ toSheaf R') :=
    inferInstanceAs (PreservesFiniteLimits (toSheaf.{max r m} S'))
  have : PreservesFiniteColimits (res ⋙ toSheaf R') :=
    inferInstanceAs (PreservesFiniteColimits (toSheaf.{max r m} S'))
  have : ReflectsFiniteColimits (toSheaf.{max r m} R') :=
    inferInstance
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves res (toSheaf R'),
    preservesFiniteColimits_of_reflects_of_preserves res (toSheaf R')⟩

private theorem scalarFlat_of_tensorComparison
    (e : restrictScalars ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map c) ⋙
      siteSheafTensorRight M ⋙
        toSheaf.{max r m} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ≅
      siteSheafTensorRight (changeOfRingsOfUniverses c M) ⋙
        toSheaf.{max r m} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
    (hM : IsFlatOnSite M) : IsFlatOnSite (changeOfRingsOfUniverses c M) := by
  have hres := restrict_exact.{uC, vC, r, m} c
  have := forget_preserves_colimits.{uC, vC, r, m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
  have := forget_preserves_colimits.{uC, vC, r, m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)
  let res := restrictScalars.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map c)
  have : PreservesFiniteLimits res := hres.1
  have : PreservesFiniteColimits res := hres.2
  have : PreservesFiniteLimits (siteSheafTensorRight M) := hM.1
  have : PreservesFiniteColimits (siteSheafTensorRight M) := hM.2
  have : PreservesFiniteLimits (res ⋙ siteSheafTensorRight M) :=
    comp_preservesFiniteLimits res (siteSheafTensorRight M)
  have : PreservesFiniteColimits (res ⋙ siteSheafTensorRight M) :=
    comp_preservesFiniteColimits res (siteSheafTensorRight M)
  have : PreservesFiniteLimits
      (restrictScalars ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map c) ⋙
        siteSheafTensorRight M ⋙
          toSheaf.{max r m} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
    comp_preservesFiniteLimits (res ⋙ siteSheafTensorRight M)
      (toSheaf.{max r m} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
  have : PreservesFiniteColimits
      (restrictScalars ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map c) ⋙
        siteSheafTensorRight M ⋙
          toSheaf.{max r m} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
    comp_preservesFiniteColimits (res ⋙ siteSheafTensorRight M)
      (toSheaf.{max r m} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
  have : PreservesFiniteLimits (siteSheafTensorRight (changeOfRingsOfUniverses c M) ⋙
      toSheaf.{max r m} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)) :=
    preservesFiniteLimits_of_natIso e
  have : PreservesFiniteColimits (siteSheafTensorRight (changeOfRingsOfUniverses c M) ⋙
      toSheaf.{max r m} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)) :=
    preservesFiniteColimits_of_natIso e
  have : ReflectsFiniteColimits
      (toSheaf.{max r m} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)) :=
    inferInstance
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _
    (toSheaf.{max r m} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)),
    preservesFiniteColimits_of_reflects_of_preserves _
    (toSheaf.{max r m} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S))⟩
private theorem isFlat_changeOfRingsOfUniverses (hM : IsFlatOnSite M) :
    IsFlatOnSite (changeOfRingsOfUniverses c M) := by
  obtain ⟨e⟩ := nonempty_scalarTensorComparisonOfUniverses c M
  exact scalarFlat_of_tensorComparison c M e hM

end ScalarExtension

/-- Pullback along an arbitrary morphism of ringed topoi preserves flat module sheaves.
The algebraic inverse-image presentation specifies transport of all ring and module
operations along the underlying inverse image. The pullback is its change of rings.
Source: Stacks Project, Tag 05VD, lemma-pullback-flat
(auxiliary; not a blueprint node).

Proof plan:
1. Use lem-weil-pbc-ringed-topos-site-presentation to present the geometric morphism by
   a continuous finite-limit-preserving site functor, up to ringed-topos equivalences.
2. Such equivalences preserve exactness and tensor products, hence flatness.
3. By situation-conventions and
   lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction, inverse image is the
   sheafification of the filtered-colimit presheaf. The underlying-set and module
   sheafification interfaces identify the transported algebraic structures.
4. By lem-weil-pbc-site-sheafification-sections-local and
   lem-weil-pbc-filtered-colimit-sets-elementwise, any finite relation locally comes
   from a relation at one common stage; eventual equality makes it zero there.
   For an empty relation use the final object as a stage.
5. Apply lem-weil-pbc-site-flat-equational-criterion to the flat source module,
   obtaining local matrix factorizations of this relation.
6. Pull these coverings back by fibre products. Continuity and the site axioms
   give coverings, and the transported matrices satisfy the same equations.
   The converse equational criterion proves flatness over the inverse-image ring.
7. Finally, (G tensor B) tensor N is G tensor Res(N), by the balanced tensor
   universal property. Restriction of scalars is exact, and exactness is detected
   on underlying abelian sheaves, proving flatness after arbitrary change of rings.
-/
theorem isFlat_ringedToposPullback
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{r} ⋙ uliftFunctor.{max r m, r})]
    [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{r} ⋙ uliftFunctor.{max r m, r})]
    [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max r m} ⋙ uliftFunctor.{r, max r m})]
    [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max r m} ⋙ uliftFunctor.{r, max r m})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max r m}] [HasWeakSheafify J AddCommGrpCat.{max r m}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max r m}]
    [HasWeakSheafify K AddCommGrpCat.{max r m}]
    {R : Sheaf J CommRingCat.{r}} {RI S : Sheaf K CommRingCat.{r}}
    (uInv : Sheaf J (Type (max r m)) ⥤ Sheaf K (Type (max r m)))
    (uPush : Sheaf K (Type (max r m)) ⥤ Sheaf J (Type (max r m)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImageOfUniverses uInv R RI) (c : RI ⟶ S)
    (F : SheafOfModules.{max r m}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (hF : IsFlatOnSite F) : IsFlatOnSite (changeOfRingsOfUniverses (J := K) c (I.modules.obj F))
      := by
  -- The inverse-image lemma isolates steps 1–6; scalar extension is proved above.
  exact isFlat_changeOfRingsOfUniverses c (I.modules.obj F)
    (isFlat_algebraicInverseImageOfUniverses uInv uPush adj I F hF)

end SheafOfModules
