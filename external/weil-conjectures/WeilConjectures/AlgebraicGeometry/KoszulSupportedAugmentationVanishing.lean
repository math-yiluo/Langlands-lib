/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem
import WeilConjectures.AlgebraicGeometry.AffinePerfectOpenRepresentCohomology
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Localization.HomEquiv

/-! # Supported maps are eventually killed by Koszul augmentations

Source: Stacks Project, Tags 08DC, 08DD and 09IR.
(blueprint: lem-pc-koszul-supported-augmentation-vanishing).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

-- Transporting the comparison across three chosen localization categories needs extra elaboration.
set_option backward.isDefEq.respectTransparency false in
/-- The unshifted Hom diagram of Koszul tails into a supported quasi-coherent
object has a singleton colimit, independently of the chosen localization universes.
Source: Stacks Project, Equation 36.9.4.1 (Tag 08DC) and Proposition 36.9.5 (Tag 08DD).
(blueprint: lem-pc-koszul-supported-augmentation-vanishing).

Proof: Represent E by a complex K. Choose the standard derived localizations on
Spec A, its localized sites, and the scheme of U. Transport quasi-coherence of K
using the homology comparison isomorphisms. The given derived restriction is zero;
mapDerivedCategoryFactors identifies it with the localized restricted complex.
Transport this zero object along the localization equivalence on the localized site.
Thus in the standard localizations the restriction is also zero. Apply
`affine_perfect_open_represent_cohomology` to the standard image of K. The
comparison target is Hom(O_U,E|_U), a singleton since E|_U is zero; restriction
from the localized site to the scheme U is the exact equivalence
Scheme.Modules.overEquiv U, which preserves zero. Transport the resulting colimit
cocone along the natural equivalence of Hom diagrams induced by uniqueness of
localization. This equivalence identifies every transition with precomposition
by the given koszulOpenMap, by naturality of the localization comparison.
Its cocone point remains a singleton. For r=0, every tail is zero and the open
is empty, so the same comparison gives the singleton colimit. The zero ring,
zero E, and vanishing or invertible entries require no additional assumptions. -/
private theorem supported_hom_colimit
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (U : (Spec (.of A)).Opens)
    (hU : U = ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))]
    (E : schemeDerivedQCohCategory (Spec (.of A)))
    (hres : IsZero ((SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory.obj E.obj)) :
    ∃ c : Cocone (koszulOpenHomDiagram A r f E.obj),
      Nonempty (IsColimit c) ∧ Subsingleton c.pt := by
  subst U
  let S := SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)
  let T := SheafOfModules.{u}
    ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f))
  let : HasDerivedCategory.{w} T := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u}
      ((moduleRings (Spec (.of A)).toRingedSpace).over
        (⨆ i : Fin r, PrimeSpectrum.basicOpen (f i)))))
  let F : S ⥤ T := SheafOfModules.overFunctor.{u}
    (moduleRings (Spec (.of A)).toRingedSpace) (koszulOpen A r f)
  let Qw : CochainComplex S ℤ ⥤ DerivedCategory S := DerivedCategory.Q
  let QwU : CochainComplex T ℤ ⥤ DerivedCategory T := DerivedCategory.Q
  let Rw := F.mapDerivedCategory
  let Dw := koszulOpenHomDiagram A r f E.obj
  let K := Qw.objPreimage E.obj
  let eK : Qw.obj K ≅ E.obj := Qw.objObjPreimageIso E.obj
  have hK (n : ℤ) : (K.homology n).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent
      (moduleRings (Spec (.of A)).toRingedSpace)).prop_of_iso
      (((DerivedCategory.homologyFunctorFactors S n).app K).symm ≪≫
        (DerivedCategory.homologyFunctor S n).mapIso eK).symm (E.property n)
  let C := (F.mapHomologicalComplex (.up ℤ)).obj K
  have hzCw : IsZero (QwU.obj C) :=
    (hres.of_iso (Rw.mapIso eK)).of_iso (F.mapDerivedCategoryFactors.app K).symm
  let := HasDerivedCategory.standard S
  let : ∀ V : (Spec (.of A)).Opens, HasDerivedCategory
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V)) :=
    fun _ ↦ HasDerivedCategory.standard _
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
  let Qs : CochainComplex S ℤ ⥤ DerivedCategory S := DerivedCategory.Q
  let := HasDerivedCategory.standard T
  let QsU : CochainComplex T ℤ ⥤ DerivedCategory T := DerivedCategory.Q
  let Es : schemeDerivedQCohCategory (Spec (.of A)) := ⟨Qs.obj K, fun n ↦
    (SheafOfModules.isQuasicoherent
      (moduleRings (Spec (.of A)).toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctorFactors S n).app K).symm (hK n)⟩
  let eU := Localization.uniq QwU QsU (HomologicalComplex.quasiIso T (.up ℤ))
  let GU := eU.functor
  let : PreservesLimit (Functor.empty _) GU :=
    eU.symm.toAdjunction.rightAdjoint_preservesLimits.preservesLimitsOfShape.preservesLimit
  let : GU.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  have hzCs : IsZero (QsU.obj C) := (GU.map_isZero hzCw).of_iso
    ((Localization.compUniqFunctor QwU QsU
      (HomologicalComplex.quasiIso T (.up ℤ))).app C).symm
  have hzRs : IsZero (F.mapDerivedCategory.obj Es.obj) :=
    hzCs.of_iso (F.mapDerivedCategoryFactors.app K)
  let H := Equivalence.functor
    (C := T)
    (D := SheafOfModules.{u}
      (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv (koszulOpen A r f))
  let : H.Additive := Functor.additive_of_preserves_binary_products H
  let : PreservesFiniteLimits (F ⋙ H) := comp_preservesFiniteLimits F H
  let : PreservesFiniteColimits (F ⋙ H) := comp_preservesFiniteColimits F H
  have hzH := H.mapDerivedCategory.map_isZero hzRs
  let Qv := DerivedCategory.Q
    (C := SheafOfModules.{u}
      (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
  let ecomp : (F ⋙ H).mapDerivedCategory.obj Es.obj ≅
      H.mapDerivedCategory.obj (F.mapDerivedCategory.obj Es.obj) :=
    (F ⋙ H).mapDerivedCategoryFactors.app K ≪≫
      Qv.mapIso ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ H))
        (.up ℤ)).app K).symm ≪≫
      (H.mapDerivedCategoryFactors.app C).symm ≪≫
      (H.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app K)).symm
  have hzFH : IsZero ((F ⋙ H).mapDerivedCategory.obj Es.obj) := hzH.of_iso ecomp
  obtain ⟨_, _, _, ι, _, ⟨hc⟩⟩ :=
    (affine_perfect_open_represent_cohomology A r f Es).2.2.2
  let Ds := koszulOpenHomDiagram A r f Es.obj
  let cs : Cocone Ds := Cocone.mk _ ι
  have hpt : Subsingleton cs.pt := ⟨fun x y ↦ hzFH.eq_of_tgt x y⟩
  let ct := Ds.coconeTypesEquiv.symm cs
  have hct : ct.IsColimit := (Types.isColimit_iff_coconeTypesIsColimit cs).mp ⟨hc⟩
  let W := HomologicalComplex.quasiIso S (.up ℤ)
  let e : ∀ j, Dw.obj j ≃ Ds.obj j := fun j ↦
    (Iso.homCongr (Iso.refl _) eK.symm).trans (Localization.homEquiv W Qw Qs)
  have he : ∀ {i j : ℕ} (g : i ⟶ j), e j ∘ Dw.map g = Ds.map g ∘ e i := by
    intro i j g
    funext φ
    dsimp only [e, Equiv.trans_apply, Iso.homCongr, Equiv.coe_fn_mk,
      Iso.refl_inv, Iso.symm_hom, Function.comp_apply]
    simp only [Category.id_comp]
    let t := ((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).map
      (HomologicalComplex.extendMap (koszulOpenTransition A r f i j (leOfHom g))
        ComplexShape.embeddingDownNat)
    change Localization.homEquiv W Qw Qs ((Qw.map t ≫ φ) ≫ eK.inv) =
      Qs.map t ≫ Localization.homEquiv W Qw Qs (φ ≫ eK.inv)
    calc
      _ = Localization.homEquiv W Qw Qs (Qw.map t ≫ (φ ≫ eK.inv)) :=
        congrArg (Localization.homEquiv W Qw Qs) (Category.assoc _ _ _)
      _ = Localization.homEquiv W Qw Qs (Qw.map t) ≫
          Localization.homEquiv W Qw Qs (φ ≫ eK.inv) :=
        Localization.homEquiv_comp W Qw Qs (Qw.map t) (φ ≫ eK.inv)
      _ = _ := congrArg (fun k ↦ k ≫ Localization.homEquiv W Qw Qs (φ ≫ eK.inv))
        (Localization.homEquiv_map W Qw Qs t)
  let cw := ct.precompose (fun j ↦ e j) he
  have hcw : cw.IsColimit := hct.precompose e he
  let ep : cw.pt ≃ PUnit.{w + 1} :=
    { toFun := fun _ ↦ PUnit.unit
      invFun := fun _ ↦ (0 : cs.pt)
      left_inv := fun _ ↦ hpt.elim _ _
      right_inv := fun _ ↦ rfl }
  let cp := cw.postcomp ep
  have hcp : cp.IsColimit := hcw.of_equiv ep (fun _ _ ↦ rfl)
  refine ⟨Dw.coconeTypesEquiv cp, cp.isColimit_iff.mp hcp, ?_⟩
  change Subsingleton PUnit
  infer_instance

-- Obtain augmentation compatibility in the standard localization, then use naturality
-- of the localization comparison to identify the two composites in the chosen category.
set_option backward.isDefEq.respectTransparency false in
private theorem augmentation_compatibility
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (E : schemeDerivedQCohCategory (Spec (.of A))) (a b : ℕ) (hab : a ≤ b) :
    koszulOpenMap A r f a b hab ≫ koszulOpenUnit A r f a =
      koszulOpenUnit A r f b := by
  let S := SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)
  let Qw : CochainComplex S ℤ ⥤ DerivedCategory S := DerivedCategory.Q
  let T := (koszulOpenTilde A).mapHomologicalComplex (ComplexShape.up ℤ)
  let t := T.map (HomologicalComplex.extendMap (koszulOpenTransition A r f a b hab)
    ComplexShape.embeddingDownNat)
  let ua := T.map (HomologicalComplex.extendMap (koszulOpenAugmentation A r f a)
    ComplexShape.embeddingDownNat)
  let ub := T.map (HomologicalComplex.extendMap (koszulOpenAugmentation A r f b)
    ComplexShape.embeddingDownNat)
  change Qw.map t ≫ Qw.map ua = Qw.map ub
  let K := Qw.objPreimage E.obj
  let eK : Qw.obj K ≅ E.obj := Qw.objObjPreimageIso E.obj
  have hK (n : ℤ) : (K.homology n).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent
      (moduleRings (Spec (.of A)).toRingedSpace)).prop_of_iso
      (((DerivedCategory.homologyFunctorFactors S n).app K).symm ≪≫
        (DerivedCategory.homologyFunctor S n).mapIso eK).symm (E.property n)
  let := HasDerivedCategory.standard S
  let : ∀ V : (Spec (.of A)).Opens, HasDerivedCategory
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V)) :=
    fun _ ↦ HasDerivedCategory.standard _
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
  let Qs : CochainComplex S ℤ ⥤ DerivedCategory S := DerivedCategory.Q
  let Es : schemeDerivedQCohCategory (Spec (.of A)) := ⟨Qs.obj K, fun n ↦
    (SheafOfModules.isQuasicoherent
      (moduleRings (Spec (.of A)).toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctorFactors S n).app K).symm (hK n)⟩
  have hs := (affine_perfect_open_represent_cohomology A r f Es).2.2.1 a b hab
  let G := (Localization.uniq Qs Qw (HomologicalComplex.quasiIso S (.up ℤ))).functor
  let c : Qs ⋙ G ≅ Qw := Localization.compUniqFunctor Qs Qw
    (HomologicalComplex.quasiIso S (.up ℤ))
  have ht := congrArg G.map hs
  change G.map (Qs.map t ≫ Qs.map ua) = G.map (Qs.map ub) at ht
  rw [Functor.map_comp] at ht
  change (Qs ⋙ G).map t ≫ (Qs ⋙ G).map ua = (Qs ⋙ G).map ub at ht
  simp only [← NatIso.naturality_2 c, Category.assoc,
    Iso.inv_hom_id_app_assoc] at ht
  have ht' := congrArg (fun k ↦ c.inv.app _ ≫ k ≫ c.hom.app _) ht
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
    Category.comp_id] using ht'

set_option backward.isDefEq.respectTransparency false in
/-- A map from a shifted structure object into an object supported on the complement
of the finite principal open is killed by an augmentation in the Koszul power system.
No orthogonality hypothesis is made.
Source: Stacks Project, Equation 36.9.4.1, Tag 08DC; Proposition 36.9.5, Tag 08DD;
Lemma 36.15.2, Tag 09IR, reduction to an object restricting to zero.
(blueprint: lem-pc-koszul-supported-augmentation-vanishing).

Proof: Move the shift on the source to the inverse shift on the target. This shifted
object still has quasi-coherent cohomology and restricts to zero. Apply the canonical
colimit comparison of `affine_perfect_open_represent_cohomology` to it. At index zero,
precompose the given map with the augmentation. Its image in the colimit is zero:
the comparison is restriction followed by the inverse restricted augmentation,
and restriction of the target is zero. Equality in this filtered colimit of Hom
sets is witnessed at some later index b. The transition maps preserve zero, and
compatibility of the augmentations identifies the transitioned map with
precomposition by the b-th augmentation. Move the target shift back to the source.
For arbitrary localization universes, choose the standard localizations while applying
the comparison theorem and transport the complexes and maps using the canonical
localization equivalences. The derived restrictions commute with this transport
because both are induced by the same restriction on complexes. Transport restriction
to the scheme of the open by `Scheme.Modules.overEquiv`; that equivalence preserves
zero. This supplies the extra localizations required by the comparison theorem
without adding assumptions to the assertion. If r = 0, the tail complex is zero,
so every augmentation already kills the map. The zero ring and E = 0 give zero
Hom groups. The argument requires no regularity or nonzero hypothesis on f. -/
theorem koszul_supported_augmentation_eventually_zero
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (U : (Spec (.of A)).Opens)
    (hU : U = ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))]
    (E : schemeDerivedQCohCategory (Spec (.of A)))
    (hres : IsZero ((SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory.obj E.obj))
    (n : ℤ) (φ : (koszulOpenStructure A)⟦n⟧ ⟶ E.obj) :
    ∃ e : ℕ, (koszulOpenUnit A r f e)⟦n⟧' ≫ φ = 0 := by
  let S := SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)
  let E' : schemeDerivedQCohCategory (Spec (.of A)) := ⟨E.obj⟦-n⟧, fun i ↦
    (SheafOfModules.isQuasicoherent
      (moduleRings (Spec (.of A)).toRingedSpace)).prop_of_iso
      (((DerivedCategory.homologyFunctor S 0).shiftIso (-n) i (-n + i) rfl).app
        E.obj).symm (E.property (-n + i))⟩
  let R := (SheafOfModules.overFunctor.{u}
    (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory
  have hres' : IsZero (R.obj E'.obj) :=
    ((shiftFunctor _ (-n)).map_isZero hres).of_iso ((R.commShiftIso (-n)).app E.obj)
  obtain ⟨c, ⟨hc⟩, hpt⟩ := supported_hom_colimit A r f U hU E' hres'
  let adj := (shiftEquiv (schemeDerivedCategory (Spec (.of A))) n).toAdjunction
  let ψ : koszulOpenStructure A ⟶ E'.obj := adj.homEquiv _ _ φ
  have heq : c.ι.app 0 (koszulOpenUnit A r f 0 ≫ ψ) =
      c.ι.app 0 (0 : koszulOpenObject A r f 0 ⟶ E'.obj) :=
    hpt.elim _ _
  obtain ⟨b, g, hg⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc _ _).mp heq
  change koszulOpenMap A r f 0 b (leOfHom g) ≫
    (koszulOpenUnit A r f 0 ≫ ψ) = koszulOpenMap A r f 0 b (leOfHom g) ≫ 0 at hg
  have hb : koszulOpenUnit A r f b ≫ ψ = 0 := by
    simpa only [← Category.assoc, augmentation_compatibility A r f E' 0 b
      (leOfHom g), comp_zero] using hg
  refine ⟨b, (adj.homEquiv _ _).injective ?_⟩
  calc
    _ = koszulOpenUnit A r f b ≫ ψ :=
      adj.homEquiv_naturality_left (koszulOpenUnit A r f b) φ
    _ = 0 := hb
    _ = adj.homEquiv _ _ 0 := by simp [Adjunction.homEquiv_apply]

end AlgebraicGeometry
