/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GabberH0ZariskiConstructions
public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparison
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparisonNaturality

/-! # Local transport through the composition comparison

Source: Stacks Project, Tag 09ZF, third and fourth proof paragraphs.
(blueprint: lem-weil-pbc-gabber-h0-zariski-local-comparison).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

private noncomputable abbrev B {S T : Scheme.{u}} (f : T ⟶ S) :=
  MorphismProperty.Over.pullback @Etale ⊤ f

private noncomputable abbrev L {S T : Scheme.{u}} (f : T ⟶ S) :=
  Scheme.etaleSetPullback f

private lemma sectionComparison_unit {R S T : Scheme.{u}}
    (h : T ⟶ S) (f : S ⟶ R) (k : T ⟶ R) (hk : h ≫ f = k)
    (F : Sheaf R.smallEtaleTopology (Type (u + 1))) (U : R.Etale)
    (s : F.obj.obj (op U)) :
    etaleSetSectionComparison h f k hk F U (etaleSetDescentUnit f F U s) =
      etaleSetDescentUnit k F U s := by
  subst k
  have hc := (Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).1
    R S T f h F U s
  unfold etaleSetSectionComparison
  simp only [eqToHom_refl, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
    Category.id_comp, comp_apply]
  change ((L (h ≫ f)).obj F).obj.map
    ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) h f).hom.app U).op
    (_) = _
  simp only [etaleSetDescentUnit]
  erw [hc]
  rw [← comp_apply, ← Functor.map_comp, ← op_comp, Iso.hom_inv_id_app,
    op_id, CategoryTheory.Functor.map_id, id_apply]

private lemma identityPullback_hom_ext {S T : Scheme.{u}} (f : T ⟶ S)
    {V : T.Etale} (a b : V ⟶ (B f).obj (Scheme.Etale.mk (𝟙 S))) : a = b := by
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono (pullback.snd (𝟙 S) f)).1
  exact (MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm

/-- The local representative calculation before identifying the global target section.
Source: Stacks Project, Tag 09ZF, third and fourth proof paragraphs;
Sites, Tags 03CB and 03CC.
(blueprint: lem-weil-pbc-gabber-h0-zariski-local-comparison).

Proof: Let j be the second projection and k = j followed by h. Naturality of the
unit for j moves the representative's restriction through that unit. Naturality
of the composition isomorphism then moves the preimage-open restriction through
its component. The composition-unit equation identifies the result with the
unit for k restricted along d, where d is the preimage-open map followed by the
base change of pullback.lift phi W.ι hphi and the inverse pasting isomorphism.
The composition-unit equation along the first projection identifies that unit
with the section comparison applied to the unit for i. Substitute hs. Naturality
of section comparison with respect to the map U to the identity object gives
the restriction of the compared global section along d followed by the base
change of U to X. This map equals the top-open inclusion followed by the canonical
identity-pullback isomorphism: both are over the same scheme and the second
projection of the identity pullback is an isomorphism, so cancellation proves
equality. Presheaf functoriality gives the two restrictions on the right. This
calculation needs neither a closed immersion nor a covering, and remains valid
for empty opens. -/
theorem gabberZariskiLocalComparison
    {X Z U X' : Scheme.{u}} (i : Z ⟶ X)
    (q : U ⟶ X) [Etale q] (h : X' ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (t : ((Scheme.etaleSetPullback i).obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj (Scheme.Etale.mk (𝟙 X)))))
    (s : F.obj.obj (op (Scheme.Etale.mk q)))
    (hs : etaleSetDescentUnit i F (Scheme.Etale.mk q) s =
      ((Scheme.etaleSetPullback i).obj F).obj.map
        ((MorphismProperty.Over.pullback @Etale ⊤ i).map
          (MorphismProperty.Over.homMk q (Category.comp_id q) :
            Scheme.Etale.mk q ⟶ Scheme.Etale.mk (𝟙 X))).op t)
    (W : X'.Opens) (phi : W.toScheme ⟶ U) (hphi : phi ≫ q = W.ι ≫ h)
 :
    ((((Classical.choose etaleSetInverseImageCompositionUnits.2.2)
      X X' (pullback i h) h (pullback.snd i h)).hom.app F).hom.app
        (op (Scheme.Etale.mk ((pullback.snd i h) ⁻¹ᵁ W).ι)))
          (((Scheme.etaleSetPullback (pullback.snd i h)).obj
            ((Scheme.etaleSetPullback h).obj F)).obj.map
              (gabberPreimageEtaleIso (pullback.snd i h) W).hom.op
              (etaleSetDescentUnit (pullback.snd i h) ((Scheme.etaleSetPullback h).obj F)
                (Scheme.Etale.mk W.ι) (gabberLocalRepresentative q h F s W phi hphi))) =
      ((Scheme.etaleSetPullback (pullback.snd i h ≫ h)).obj F).obj.map
        ((gabberOpenEtale (pullback i h)).map (homOfLE le_top)).op
        (((Scheme.etaleSetPullback (pullback.snd i h ≫ h)).obj F).obj.map
          (gabberTopPullbackIso (pullback.snd i h ≫ h)).hom.op
          (etaleSetSectionComparison (pullback.fst i h) i (pullback.snd i h ≫ h)
            pullback.condition F (Scheme.Etale.mk (𝟙 X)) t)) := by
  set_option backward.isDefEq.respectTransparency.types false in
    let j := pullback.snd i h
    let k := j ≫ h
    let A := Scheme.Etale.mk q
    let V := Scheme.Etale.mk (j ⁻¹ᵁ W).ι
    let H := (L h).obj F
    let K := (L j).obj H
    let P := (L k).obj F
    let β := (Classical.choose etaleSetInverseImageCompositionUnits.2.2
      X X' (pullback i h) h j).hom.app F
    let a := (gabberPreimageEtaleIso j W).hom
    let r : Scheme.Etale.mk W.ι ⟶ (B h).obj A :=
      MorphismProperty.Over.homMk (pullback.lift phi W.ι hphi)
        (pullback.lift_snd phi W.ι hphi)
    let m : V ⟶ (B j).obj ((B h).obj A) := a ≫ (B j).map r
    let δ := MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) j h
    let d : V ⟶ (B k).obj A := m ≫ δ.inv.app A
    let v : A ⟶ Scheme.Etale.mk (𝟙 X) := MorphismProperty.Over.homMk q (Category.comp_id q)
    have hη := etaleSetInverseImageCompositionUnits.1
      X' (pullback i h) j H ((B h).obj A) (Scheme.Etale.mk W.ι) r
        (etaleSetDescentUnit h F A s)
    have hc := (Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).1
      X X' (pullback i h) h j F A s
    have hn := ConcreteCategory.congr_hom (β.hom.naturality m.op)
      (etaleSetDescentUnit j H ((B h).obj A) (etaleSetDescentUnit h F A s))
    change β.hom.app (op ((B j).obj ((B h).obj A)))
      (etaleSetDescentUnit j H ((B h).obj A) (etaleSetDescentUnit h F A s)) =
        P.obj.map (δ.inv.app A).op (etaleSetDescentUnit k F A s) at hc
    change β.hom.app (op V)
      (K.obj.map m.op
        (etaleSetDescentUnit j H ((B h).obj A) (etaleSetDescentUnit h F A s))) =
      P.obj.map m.op (β.hom.app (op ((B j).obj ((B h).obj A)))
        (etaleSetDescentUnit j H ((B h).obj A) (etaleSetDescentUnit h F A s))) at hn
    -- Move the local representative through the unit and composition comparison.
    have hlocal :
        β.hom.app (op V) (K.obj.map a.op
          (etaleSetDescentUnit j H (Scheme.Etale.mk W.ι)
            (H.obj.map r.op (etaleSetDescentUnit h F A s)))) =
          P.obj.map d.op (etaleSetDescentUnit k F A s) := by
      change etaleSetDescentUnit j H (Scheme.Etale.mk W.ι)
        (H.obj.map r.op (etaleSetDescentUnit h F A s)) =
        K.obj.map ((B j).map r).op
        (etaleSetDescentUnit j H ((B h).obj A) (etaleSetDescentUnit h F A s)) at hη
      rw [hη]
      rw [← comp_apply, ← Functor.map_comp, ← op_comp]
      change β.hom.app (op V) (K.obj.map m.op _) = _
      rw [hn]
      change P.obj.map m.op
        (β.hom.app (op ((B j).obj ((B h).obj A))) _) = _
      rw [hc]
      simp only [d, op_comp, Functor.map_comp, comp_apply]
      rfl
    -- Compare the unit for the composite with the restriction of the given section.
    have hsection : etaleSetDescentUnit k F A s =
        P.obj.map ((B k).map v).op
          (etaleSetSectionComparison (pullback.fst i h) i (pullback.snd i h ≫ h)
            (pullback.condition (f := i) (g := h)) F (Scheme.Etale.mk (𝟙 X)) t) := by
      have hu := sectionComparison_unit (pullback.fst i h) i (pullback.snd i h ≫ h)
        (pullback.condition (f := i) (g := h)) F A s
      have hs' : etaleSetDescentUnit i F A s =
          ((L i).obj F).obj.map ((B i).map v).op t := hs
      have hn' := ConcreteCategory.congr_hom
        (etaleSetSectionComparison_naturality (R := X) (S := Z) (T := pullback i h)
          (pullback.fst i h) i (pullback.snd i h ≫ h) (pullback.condition (f := i) (g := h)) F
          (V := A) (W := Scheme.Etale.mk (𝟙 X)) v) t
      simp only [comp_apply] at hn'
      exact hu.symm.trans ((congrArg
        (etaleSetSectionComparison (pullback.fst i h) i (pullback.snd i h ≫ h)
          (pullback.condition (f := i) (g := h)) F A)
        hs').trans hn'.symm)
    -- Maps into the identity pullback agree because its second projection is mono.
    have hd : d ≫ (B k).map v =
        (gabberOpenEtale (pullback i h)).map (homOfLE le_top) ≫
          (gabberTopPullbackIso k).hom := by
      exact identityPullback_hom_ext k _ _
    change β.hom.app (op V) (K.obj.map a.op
      (etaleSetDescentUnit j H (Scheme.Etale.mk W.ι)
        (H.obj.map r.op (etaleSetDescentUnit h F A s)))) = _
    rw [hlocal, hsection]
    rw [← comp_apply, ← Functor.map_comp, ← op_comp, hd]
    rw [op_comp, Functor.map_comp, comp_apply]
    rfl

end AlgebraicGeometry
