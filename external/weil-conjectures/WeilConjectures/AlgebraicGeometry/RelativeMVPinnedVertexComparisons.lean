/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeMayerVietorisMaps
import WeilConjectures.AlgebraicGeometry.RelativeMVInverseOpenComparisons
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Pinned relative Mayer--Vietoris vertex comparisons

Source: Stacks Project, Cohomology, Tags 08HY and 08HZ.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Pretriangulated
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

private theorem map_lift_comparison
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] {A U V : C} {U' V' : D}
    [PreservesBinaryBiproduct U V F]
    (eU : F.obj U ≅ U') (eV : F.obj V ≅ V')
    (u : A ⟶ U) (v : A ⟶ V) :
    F.map (biprod.lift u v) ≫ (F.mapBiprod U V ≪≫ biprod.mapIso eU eV).hom =
      biprod.lift (F.map u ≫ eU.hom) (F.map v ≫ eV.hom) := by
  rw [Iso.trans_hom, ← Category.assoc, biprod.map_lift_mapBiprod]
  ext <;> simp [biprod.mapIso, Category.assoc]

private theorem map_desc_comparison
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] {U V W : C} {U' V' W' : D}
    [PreservesBinaryBiproduct U V F]
    (eU : F.obj U ≅ U') (eV : F.obj V ≅ V') (eW : F.obj W ≅ W')
    (rU : U ⟶ W) (rV : V ⟶ W) (sU : U' ⟶ W') (sV : V' ⟶ W')
    (hU : F.map rU ≫ eW.hom = eU.hom ≫ sU)
    (hV : F.map rV ≫ eW.hom = eV.hom ≫ sV) :
    F.map (biprod.desc rU (-rV)) ≫ eW.hom =
      (F.mapBiprod U V ≪≫ biprod.mapIso eU eV).hom ≫ biprod.desc sU (-sV) := by
  apply (cancel_epi (F.mapBiprod U V).inv).mp
  simp only [Iso.trans_hom, ← Category.assoc, Iso.inv_hom_id, Category.id_comp,
    biprod.mapBiprod_inv_map_desc]
  ext <;> simp [biprod.mapIso, hU, hV]

/-- Vertex comparisons for the canonical exact-restriction presentation of the
relative Mayer--Vietoris rows. The overlap component satisfies the vertical-pasting
identity. No boundary, distinguishedness, or morphism of triangles is asserted.

Source: Stacks Project, Cohomology, Tags 08BV, 08HZ and 08HY; Derived Categories
of Schemes, Tag 0DJ9, the induction diagram.
(blueprint: lem-pc-relative-mv-pinned-vertex-comparisons).

Proof: For each open W, compare derived exact restriction with derived pullback
using leftAdjointUniq for mvOpenRestrictionAdjunction and relativeMVAdj. Apply
the direct-image functor and compose with relativeMVImageComp W.ι f. Apply Lg*
to obtain the source comparisons. On the inverse-image cover, identify its open
scheme with the chosen pullback using the projection-preserving canonical scheme
isomorphism. Derive this isomorphism and use the same adjunction and composition
comparisons to obtain the target comparisons. At the middle vertices compose the
additive functors' biproduct comparison with biprod.mapIso of the two open
comparisons. The unit identity for leftAdjointUniq proves the two first-arrow
identities. Transpose the restricted counits under these adjunction comparisons;
the counit identity and composition coherence prove the two second-arrow
identities, with subtraction on the V summand. For the overlap expand the
base-change map as the mate of the pulled-back counit. Substitute the composite
adjunction counit formula and cancel both triangle identities. The two pullback
projection composites are equal; transport along this equality and compose the
two pinned pullback comparisons. The remaining map is precisely
relativeMVLocalArrow. This gives the last equality. No compactness,
quasi-coherence, or cover condition is used by these comparisons; empty opens,
zero objects, repeated opens and the zero object map obey the same identities. -/
theorem relativeMV_pinned_vertex_comparisons
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') (U V : X.Opens) :
    let F := schemeDerivedDirectImage f ⋙ derivedPullback g
    let G := schemeDerivedDirectImage f'
    let T := mvBaseChangeTriangle X U V (U ⊓ V) (homOfLE inf_le_left)
      (homOfLE inf_le_right) (mvOpenRestrictionAdjunction X U)
      (mvOpenRestrictionAdjunction X V) (mvOpenRestrictionAdjunction X (U ⊓ V)) K 0
    let T' := mvBaseChangeTriangle X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) (g' ⁻¹ᵁ (U ⊓ V))
      ((TopologicalSpace.Opens.map g'.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U)))
      ((TopologicalSpace.Opens.map g'.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V)))
      (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ U))
      (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ V))
      (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ (U ⊓ V))) K' 0
    let a := relativeMVLocalArrow f f' g g' hpull K K' φ
    ∃ (e₂ : F.obj T.obj₂ ≅ (a U).left ⊞ (a V).left)
      (e₃ : F.obj T.obj₃ ≅ (a (U ⊓ V)).left)
      (e₂' : G.obj T'.obj₂ ≅ (a U).right ⊞ (a V).right)
      (e₃' : G.obj T'.obj₃ ≅ (a (U ⊓ V)).right),
      F.map T.mor₁ ≫ e₂.hom = relativeMVSourceFirst f g U V K ∧
      F.map T.mor₂ ≫ e₃.hom = e₂.hom ≫ relativeMVSourceSecond f g U V K ∧
      G.map T'.mor₁ ≫ e₂'.hom = relativeMVTargetFirst g' f' U V K' ∧
      G.map T'.mor₂ ≫ e₃'.hom = e₂'.hom ≫ relativeMVTargetSecond g' f' U V K' ∧
      mvBaseChangeOpenMap f f' g g' hpull.w K K' φ (U ⊓ V) ≫ e₃'.hom =
        e₃.hom ≫ (a (U ⊓ V)).hom := by
  classical
  have : (derivedPullback g).IsLeftAdjoint := (relativeMVAdj g).isLeftAdjoint
  have : (schemeDerivedDirectImage f).IsRightAdjoint := (relativeMVAdj f).isRightAdjoint
  have : (schemeDerivedDirectImage f').IsRightAdjoint := (relativeMVAdj f').isRightAdjoint
  have : (derivedPullback g).Additive := by
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (derivedPullback g)
    exact Functor.additive_of_preservesBinaryBiproducts _
  have : (schemeDerivedDirectImage f).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (schemeDerivedDirectImage f').Additive :=
    Functor.additive_of_preserves_binary_products _
  dsimp only
  let F := schemeDerivedDirectImage f ⋙ derivedPullback g
  let G := schemeDerivedDirectImage f'
  have : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  have : PreservesBinaryBiproducts G := preservesBinaryBiproducts_of_preservesBiproducts G
  let s (W : X.Opens) := (derivedPullback g).mapIso (relativeMVExactOpenIso f W K)
  have ht :=
    relativeMV_inverse_open_comparisons f f' g g' hpull K K' φ
  let t := Classical.choose ht
  have htUnit := (Classical.choose_spec ht).1
  have htRestriction := (Classical.choose_spec ht).2.1
  have htPaste := (Classical.choose_spec ht).2.2
  refine ⟨F.mapBiprod _ _ ≪≫ biprod.mapIso (s U) (s V), s (U ⊓ V),
    G.mapBiprod _ _ ≪≫ biprod.mapIso (t U) (t V), t (U ⊓ V), ?_, ?_, ?_, ?_,
    htPaste (U ⊓ V)⟩
  · change F.map (biprod.lift _ _) ≫ _ = _
    rw [map_lift_comparison]
    change biprod.lift
      ((derivedPullback g).map ((schemeDerivedDirectImage f).map
        ((mvOpenRestrictionAdjunction X U).unit.app K)) ≫ (s U).hom)
      ((derivedPullback g).map ((schemeDerivedDirectImage f).map
        ((mvOpenRestrictionAdjunction X V).unit.app K)) ≫ (s V).hom) = _
    simp only [s, Functor.mapIso_hom, ← Functor.map_comp, relativeMVExactOpenIso_unit]
    rfl
  · change F.map (biprod.desc _ (-_)) ≫ _ = _
    apply map_desc_comparison
    · simpa only [F, s, Functor.comp_map, Functor.mapIso_hom, Functor.map_comp] using
        congrArg ((derivedPullback g).map)
          (relativeMVExactOpenIso_restriction f (W := U ⊓ V) (U := U) inf_le_left K)
    · simpa only [F, s, Functor.comp_map, Functor.mapIso_hom, Functor.map_comp] using
        congrArg ((derivedPullback g).map)
          (relativeMVExactOpenIso_restriction f (W := U ⊓ V) (U := V) inf_le_right K)
  · change G.map (biprod.lift _ _) ≫ _ = _
    refine (map_lift_comparison G (t U) (t V) _ _).trans ?_
    exact congrArg₂ biprod.lift (htUnit U) (htUnit V)
  · change G.map (biprod.desc _ (-_)) ≫ _ = _
    apply map_desc_comparison
    · exact htRestriction (U ⊓ V) U inf_le_left
    · exact htRestriction (U ⊓ V) V inf_le_right

end AlgebraicGeometry
