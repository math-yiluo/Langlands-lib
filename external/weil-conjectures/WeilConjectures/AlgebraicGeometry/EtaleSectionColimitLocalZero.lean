/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf

import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheafSectionUniverse

/-! # Local vanishing before finite selection in etale sheaf colimits

Source: Stacks Project, Sites, Lemma Tag 0738, proof of part (2).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem comparison_locallyInjective_of_univLE
    (X : Scheme.{u}) (Λ : Type v) [CommRing Λ] [UnivLE.{u, max v w}]
    (I : Type w) [SmallCategory I] [IsFiltered I]
    (G : I ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{max v w} Λ))
    (c : Cocone G) (hc : IsColimit c) :
    Presheaf.IsLocallyInjective X.smallEtaleTopology
      (colimit.desc (G ⋙ sheafToPresheaf X.smallEtaleTopology (ModuleCat.{max v w} Λ))
        ((sheafToPresheaf X.smallEtaleTopology (ModuleCat.{max v w} Λ)).mapCocone c)) := by
  have : Small.{max v w} (SmallModel.{u} X.AffineEtale) := inferInstance
  let : EssentiallySmall.{max v w} X.AffineEtale :=
    essentiallySmall_of_fully_faithful (equivSmallModel.{u} X.AffineEtale).functor
  let : PreservesFilteredColimits (forget (ModuleCat.{max v w} Λ)) :=
    { preserves_filtered_colimits := fun J _ _ ↦
        { preservesColimit := fun {F} ↦
            preservesColimit_of_preserves_colimit_cocone
              (ModuleCat.FilteredColimits.colimitCoconeIsColimit F)
              (Types.TypeMax.colimitCoconeIsColimit
                (F ⋙ forget (ModuleCat.{max v w} Λ))) } }
  let : HasSheafify (Scheme.AffineEtale.topology X) (ModuleCat.{max v w} Λ) :=
    hasSheafifyEssentiallySmallSite.{u, max v w, u + 1, (max v w) + 1, max v w}
      (Scheme.AffineEtale.topology X)
      (ModuleCat.{max v w} Λ)
  let : HasLimitsOfSize.{u, u} (ModuleCat.{max v w} Λ) := ModuleCat.hasLimitsOfSize
  let : ((Scheme.AffineEtale.Spec X).sheafPushforwardContinuous (ModuleCat.{max v w} Λ)
    (Scheme.AffineEtale.topology X) X.smallEtaleTopology).IsEquivalence :=
    Functor.isEquivalence_of_isOneHypercoverDense _ _ _ _
  let : HasSheafify X.smallEtaleTopology (ModuleCat.{max v w} Λ) :=
    Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
      (Scheme.AffineEtale.topology X) X.smallEtaleTopology (Scheme.AffineEtale.Spec X)
  let : ∀ (W : X.AffineEtaleᵒᵖ), HasLimitsOfShape
      (StructuredArrow W (equivSmallModel.{max v w} X.AffineEtale).inverse.op)
      (ModuleCat.{max v w} Λ) := fun W ↦ ModuleCat.hasLimitsOfShape
  let : (Scheme.AffineEtale.topology X).WEqualsLocallyBijective
      (ModuleCat.{max v w} Λ) := .ofEssentiallySmall (Scheme.AffineEtale.topology X)
  let : X.smallEtaleTopology.WEqualsLocallyBijective (ModuleCat.{max v w} Λ) :=
    .transport _ _ _
      (Functor.IsDenseSubsite.coverPreserving (Scheme.AffineEtale.topology X) _
        (Scheme.AffineEtale.Spec X))
  let F := G ⋙ sheafToPresheaf X.smallEtaleTopology (ModuleCat.{max v w} Λ)
  let d := (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{max v w} Λ)).mapCocone c
  let c' := Sheaf.sheafifyCocone (colimit.cocone F)
  have hc' : IsColimit c' := Sheaf.isColimitSheafifyCocone _ (colimit.isColimit F)
  let e := hc'.coconePointUniqueUpToIso hc
  let b : colimit F ⟶ c.pt.obj := toSheafify X.smallEtaleTopology (colimit F) ≫ e.hom.hom
  have hb (i : I) : colimit.ι F i ≫ b = d.ι.app i := by
    dsimp only [b]
    have hι : (c'.ι.app i).hom =
        colimit.ι F i ≫ toSheafify X.smallEtaleTopology (colimit F) := by
      simpa only [colimit.cocone_ι, colimit.cocone_x] using
        Sheaf.sheafifyCocone_ι_app_val (colimit.cocone F) i
    rw [← Category.assoc, ← hι]
    change (c'.ι.app i ≫ e.hom).hom = (c.ι.app i).hom
    exact congrArg (fun f ↦ f.hom) (hc'.comp_coconePointUniqueUpToIso_hom hc i)
  have heq : colimit.desc F d = b := by
    apply colimit.hom_ext
    intro i
    rw [colimit.ι_desc, hb]
  rw [heq]
  infer_instance


/-- A zero colimit image gives local eventual vanishing on a covering sieve.
Source: Stacks Project, Sites, Lemma Tag 0738 (lemma-directed-colimits-sections),
proof of part (2), the local equality assertion before finite-cover selection.
(blueprint: lem-weil-pbc-etale-section-colimit-local-zero-sieve).

Proof: Form the presheaf P whose value on an etale object V is the filtered
colimit of the modules G_i(V). The cocone maps give P a map to the colimit
sheaf H. Identify this map with the sheafification unit, respecting each
coprojection, using the sheaf-colimit universal property. The image in P(U)
of s and the zero section have equal images in H(U). Local injectivity of
sheafification gives a covering sieve on which their restrictions agree in
P. On each arrow of that sieve, the filtered module-colimit equality criterion
puts the restricted section and zero at a common later index. Its transition
map from i is the required killing arrow. The resulting arrows are closed
under restriction by naturality, so they contain a covering sieve S as asserted.
Only local equality is used here: no finite subfamily and no global separatedness
conclusion is asserted. In the independent universes of this statement, the
identification must be established on an affine etale basis, with its finite
coverings; an arbitrary HasWeakSheafify instance alone does not supply local
injectivity. Quasi-compact etale objects admit finite affine refinements, so
these finite matching diagrams and the filtered sectionwise colimit stay in
the coefficient universe. -/
theorem etale_section_colimit_local_zero_sieve
    (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    (U : X.Etale) [CompactSpace U.left]
    (I : Type w) [SmallCategory I] [IsFiltered I]
    (G : I ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{max v w} Λ))
    (c : Cocone G) (hc : IsColimit c) (i : I)
    (s : (G.obj i).obj.obj (Opposite.op U))
    (hs : ((c.ι.app i).hom.app (Opposite.op U)).hom s = 0) :
    ∃ S : Sieve U, S ∈ X.smallEtaleTopology U ∧
      ∀ (V : X.Etale) (q : V ⟶ U), S q →
        ∃ (j : I) (f : i ⟶ j),
          ((G.map f).hom.app (Opposite.op V)).hom
            (((G.obj i).obj.map q.op).hom s) = 0 := by
  classical
  by_cases hs0 : s = 0
  · refine ⟨⊤, X.smallEtaleTopology.top_mem U, ?_⟩
    intro V q _
    exact ⟨i, 𝟙 i, by simp [hs0]⟩
  let : UnivLE.{u, max v w} := etale_module_sheaf_section_univLE X Λ (G.obj i) U s hs0
  let F := G ⋙ sheafToPresheaf X.smallEtaleTopology (ModuleCat.{max v w} Λ)
  let d := (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{max v w} Λ)).mapCocone c
  let a : colimit F ⟶ c.pt.obj := colimit.desc F d
  have ha : Presheaf.IsLocallyInjective X.smallEtaleTopology a :=
    comparison_locallyInjective_of_univLE X Λ I G c hc
  let x : (colimit F).obj (Opposite.op U) :=
    (colimit.ι F i).app (Opposite.op U) s
  have hax : a.app (Opposite.op U) x = a.app (Opposite.op U) 0 := by
    rw [map_zero]
    have hfac := ConcreteCategory.congr_hom
      (NatTrans.congr_app (colimit.ι_desc d i) (Opposite.op U)) s
    exact hfac.trans hs
  refine ⟨Presheaf.equalizerSieve x 0,
    Presheaf.equalizerSieve_mem X.smallEtaleTopology a x 0 hax, ?_⟩
  intro V q hq
  have hxV : (colimit.ι F i).app (Opposite.op V)
      (((G.obj i).obj.map q.op).hom s) = 0 := by
    have hn := ConcreteCategory.congr_hom ((colimit.ι F i).naturality q.op) s
    change (colimit.ι F i).app (Opposite.op V)
      (((G.obj i).obj.map q.op).hom s) = (colimit F).map q.op x at hn
    rw [hn]
    change (colimit F).map q.op x = (colimit F).map q.op 0 at hq
    simpa only [map_zero] using hq
  let E : I ⥤ ModuleCat.{max v w} Λ :=
    F ⋙ (evaluation X.Etaleᵒᵖ (ModuleCat.{max v w} Λ)).obj (Opposite.op V)
  have : PreservesColimit E (forget (ModuleCat.{max v w} Λ)) :=
    preservesColimit_of_preserves_colimit_cocone
      (ModuleCat.FilteredColimits.colimitCoconeIsColimit E)
      (Types.TypeMax.colimitCoconeIsColimit (E ⋙ forget (ModuleCat.{max v w} Λ)))
  let e : Cocone E := ((evaluation X.Etaleᵒᵖ (ModuleCat.{max v w} Λ)).obj
    (Opposite.op V)).mapCocone (colimit.cocone F)
  have he : IsColimit e :=
    isColimitOfPreserves ((evaluation _ _).obj (Opposite.op V)) (colimit.isColimit F)
  have hzero : e.ι.app i (((G.obj i).obj.map q.op).hom s) = e.ι.app i 0 := by
    dsimp only [e]
    simp only [Functor.mapCocone_ι_app, colimit.cocone_ι]
    change (colimit.ι F i).app (Opposite.op V)
      (((G.obj i).obj.map q.op).hom s) = (colimit.ι F i).app (Opposite.op V) 0
    simpa only [map_zero] using hxV
  obtain ⟨j, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq E he
    (((G.obj i).obj.map q.op).hom s) 0 hzero
  exact ⟨j, f, hfg.trans (map_zero (E.map g).hom)⟩

end AlgebraicGeometry
