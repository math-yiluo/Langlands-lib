/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Source.SourceIsomorphismNormalizedPresheafEvaluation
import Mathlib.CategoryTheory.Adjunction.Comma

/-! # Universal normalization arrows on etale source sites

Source: Stacks Project, Tags 06YY, 03ED and 09BV.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t u v w
open CategoryTheory CategoryTheory.Limits Opposite
-- The following elementary helpers reproduce the universal-factorization and square
-- transport proofs of NormalizedDerivedIsomorphismTransport, without importing its
-- downstream scalar-extension and proper-base-change applications.
namespace CategoryTheory
section TransportSquare
variable {H S P Q : Type*} [Category H] [Category S] [Category P] [Category Q]
    (ER : H ⥤ P) (ES : S ⥤ Q) (RS : S ⥤ H) (RP : Q ⥤ P)
    (c : RS ⋙ ER ≅ ES ⋙ RP)
    {A D : H} {A' D' : S} {A₀ D₀ : P} {A₁ D₁ : Q}
    (δA : ER.obj A ≅ A₀) (δD : ER.obj D ≅ D₀)
    (εA : ES.obj A' ≅ A₁) (εD : ES.obj D' ≅ D₁)
    (dA : A ⟶ RS.obj A') (dD : D ⟶ RS.obj D')
    (dA₀ : A₀ ⟶ RP.obj A₁) (dD₀ : D₀ ⟶ RP.obj D₁)
    (hA : δA.hom ≫ dA₀ = ER.map dA ≫ c.hom.app A' ≫ RP.map εA.hom)
    (hD : δD.hom ≫ dD₀ = ER.map dD ≫ c.hom.app D' ≫ RP.map εD.hom)
include hA hD in
private theorem normalizationSquareTransport
    (e : A ≅ D) (e' : A' ≅ D')
    (he : e.hom ≫ dD = dA ≫ RS.map e'.hom) :
    (δA.symm ≪≫ ER.mapIso e ≪≫ δD).hom ≫ dD₀ =
      dA₀ ≫ RP.map (εA.symm ≪≫ ES.mapIso e' ≪≫ εD).hom := by
  apply (cancel_epi δA.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp]
  rw [hD, reassoc_of% hA]
  simp only [← RP.map_comp_assoc, Iso.hom_inv_id_assoc]
  rw [← ER.map_comp_assoc, he, ER.map_comp, Category.assoc]
  have hn := c.hom.naturality e'.hom
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]

end TransportSquare
end CategoryTheory

namespace CategoryTheory.StructuredArrow
variable {C : Type u} [Category.{v} C] {D : Type t} [Category.{w} D]
  {R : C ⥤ D} {A A' : D} {K K' : C}
  {d : A ⟶ R.obj K} {d' : A' ⟶ R.obj K'}
private noncomputable def normalizationUniversalIso
    (h : IsUniversal (mk d)) (h' : IsUniversal (mk d')) (e : A ≅ A') : K ≅ K' where
  hom := h.desc (mk (e.hom ≫ d'))
  inv := h'.desc (mk (e.inv ≫ d))
  hom_inv_id := by
    apply h.hom_ext
    rw [Functor.map_comp, ← Category.assoc, h.fac]
    change (e.hom ≫ d') ≫ R.map (h'.desc (mk (e.inv ≫ d))) = d ≫ R.map (𝟙 K)
    rw [Category.assoc]
    have hf : d' ≫ R.map (h'.desc (mk (e.inv ≫ d))) = e.inv ≫ d := h'.fac _
    rw [hf]
    change e.hom ≫ e.inv ≫ d = d ≫ R.map (𝟙 K)
    rw [← Category.assoc, e.hom_inv_id]
    simp
  inv_hom_id := by
    apply h'.hom_ext
    rw [Functor.map_comp, ← Category.assoc, h'.fac]
    change (e.inv ≫ d) ≫ R.map (h.desc (mk (e.hom ≫ d'))) = d' ≫ R.map (𝟙 K')
    rw [Category.assoc]
    have hf : d ≫ R.map (h.desc (mk (e.hom ≫ d'))) = e.hom ≫ d' := h.fac _
    rw [hf]
    change e.inv ≫ e.hom ≫ d' = d' ≫ R.map (𝟙 K')
    rw [← Category.assoc, e.inv_hom_id]
    simp
private theorem normalizationUniversalIso_fac
    (h : IsUniversal (mk d)) (h' : IsUniversal (mk d')) (e : A ≅ A') :
    d ≫ R.map (normalizationUniversalIso h h' e).hom = e.hom ≫ d' :=
  h.fac _

end CategoryTheory.StructuredArrow

namespace AlgebraicGeometry.Scheme

/-- The canonical coefficient mate for etale inverse image, localized exactly.
Source: Stacks Tags 03DA and 03ED.
(blueprint: def-weil-pbc-etale-universal-normalization). -/
def etaleNormalizationCoefficients {Y Z : Scheme.{t}} (f : Z ⟶ Y)
    {R S : Type (t + 1)} [CommRing R] [CommRing S] (q : R →+* S) :
    normalizationRestrict Y.smallEtaleTopology q ⋙
        (Etale.upperStar (ModuleCat.{t + 1} R) f).mapDerivedCategory ≅
      (Etale.upperStar (ModuleCat.{t + 1} S) f).mapDerivedCategory ⋙
        normalizationRestrict Z.smallEtaleTopology q := by
  letI : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).IsContinuous
      Y.smallEtaleTopology Z.smallEtaleTopology := Etale.isContinuous_overPullback f
  letI : (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f)
      (ModuleCat.{t + 1} R) Y.smallEtaleTopology Z.smallEtaleTopology).Additive := by
    change (Etale.upperStar (ModuleCat.{t + 1} R) f).Additive
    infer_instance
  letI : (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f)
      (ModuleCat.{t + 1} S) Y.smallEtaleTopology Z.smallEtaleTopology).Additive := by
    change (Etale.upperStar (ModuleCat.{t + 1} S) f).Additive
    infer_instance
  letI : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f)
      (ModuleCat.{t + 1} R) Y.smallEtaleTopology Z.smallEtaleTopology) := by
    change PreservesFiniteLimits (Etale.upperStar (ModuleCat.{t + 1} R) f)
    infer_instance
  letI : PreservesFiniteColimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f)
      (ModuleCat.{t + 1} R) Y.smallEtaleTopology Z.smallEtaleTopology) := by
    change PreservesFiniteColimits (Etale.upperStar (ModuleCat.{t + 1} R) f)
    infer_instance
  letI : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f)
      (ModuleCat.{t + 1} S) Y.smallEtaleTopology Z.smallEtaleTopology) := by
    change PreservesFiniteLimits (Etale.upperStar (ModuleCat.{t + 1} S) f)
    infer_instance
  letI : PreservesFiniteColimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f)
      (ModuleCat.{t + 1} S) Y.smallEtaleTopology Z.smallEtaleTopology) := by
    change PreservesFiniteColimits (Etale.upperStar (ModuleCat.{t + 1} S) f)
    infer_instance
  exact Functor.mapDerivedCategorySquareIso
    (normalizationPullbackIso Y.smallEtaleTopology
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f)
      Z.smallEtaleTopology q)

/-- A specified coefficient arrow is universal on source sites and has the canonical
restriction coherence. This contains no isomorphism-presheaf map.
Source: Stacks Tags 06YY and 03ED.
(blueprint: def-weil-pbc-etale-universal-normalization). -/
structure EtaleUniversalNormalization (Y : Scheme.{t})
    {R S : Type (t + 1)} [CommRing R] [CommRing S] (q : R →+* S)
    {C : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{t + 1} R))}
    {C' : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{t + 1} S))}
    (d : C ⟶ (normalizationRestrict Y.smallEtaleTopology q).obj C') : Prop where
  universal : ∀ U : Y.Etale, Nonempty (StructuredArrow.IsUniversal
    (StructuredArrow.mk (etaleIsomorphismNormalizationArrow Y q d U)))
  coherence : ∀ {U V : Y.Etale} (f : U ⟶ V),
    (localIsomorphismRestrictionComp Y R f).inv.app C ≫
        etaleIsomorphismNormalizationArrow Y q d U =
      (Etale.upperStar (ModuleCat.{t + 1} R) f.left).mapDerivedCategory.map
          (etaleIsomorphismNormalizationArrow Y q d V) ≫
        (etaleNormalizationCoefficients f.left q).hom.app
          ((localIsomorphismRestriction Y S V).obj C') ≫
        (normalizationRestrict U.left.smallEtaleTopology q).map
          ((localIsomorphismRestrictionComp Y S f).inv.app C')

/-- Two coherent universal arrows induce a normalized map on the actual source-site
Isom presheaves. No sheafification, finite coefficient, or stalk assumption is needed.
Source: Stacks Tags 06YY and 09BV.
(blueprint: lem-weil-pbc-etale-universal-normalization-presheaf).
Proof: at each object use initiality of the two structured arrows to transport an
isomorphism. The two descended maps are inverse by uniqueness. For restriction, pull
its defining square back through the canonical coefficient mate. The coherence equations
identify its edges with the arrows on the smaller source. Their universality makes the
pulled square's solution unique, proving naturality. The factorization equation is
exactly the required normalization equation. -/
theorem etaleUniversalNormalization_presheaf (Y : Scheme.{t})
    {R S : Type (t + 1)} [CommRing R] [CommRing S] (q : R →+* S)
    (C K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{t + 1} R)))
    (C' K' : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{t + 1} S)))
    (dC : C ⟶ (normalizationRestrict Y.smallEtaleTopology q).obj C')
    (dK : K ⟶ (normalizationRestrict Y.smallEtaleTopology q).obj K')
    (hC : EtaleUniversalNormalization Y q dC) (hK : EtaleUniversalNormalization Y q dK) :
    ∃ p : derivedLocalIsomorphismPresheaf C K ⟶ derivedLocalIsomorphismPresheaf C' K',
      ∀ (U : Y.Etale) (e : (localIsomorphismRestriction Y R U).obj C ≅
          (localIsomorphismRestriction Y R U).obj K),
        e.hom ≫ etaleIsomorphismNormalizationArrow Y q dK U =
          etaleIsomorphismNormalizationArrow Y q dC U ≫
            (normalizationRestrict U.left.smallEtaleTopology q).map
              (p.app (op U) e).hom := by
  classical
  let r (U : Y.Etale) :=
    StructuredArrow.normalizationUniversalIso (hC.universal U).some (hK.universal U).some
  let p : derivedLocalIsomorphismPresheaf C K ⟶
      derivedLocalIsomorphismPresheaf C' K' :=
    { app U := TypeCat.ofHom (r U.unop)
      naturality := by
        intro U V f
        apply ConcreteCategory.hom_ext
        intro e
        apply Iso.ext
        apply (hC.universal V.unop).some.hom_ext
        have he := (StructuredArrow.normalizationUniversalIso_fac
          (hC.universal U.unop).some (hK.universal U.unop).some e).symm
        have ht := normalizationSquareTransport
          (Etale.upperStar (ModuleCat.{t + 1} R) f.unop.left).mapDerivedCategory
          (Etale.upperStar (ModuleCat.{t + 1} S) f.unop.left).mapDerivedCategory
          (normalizationRestrict U.unop.left.smallEtaleTopology q)
          (normalizationRestrict V.unop.left.smallEtaleTopology q)
          (etaleNormalizationCoefficients f.unop.left q)
          ((localIsomorphismRestrictionComp Y R f.unop).app C).symm
          ((localIsomorphismRestrictionComp Y R f.unop).app K).symm
          ((localIsomorphismRestrictionComp Y S f.unop).app C').symm
          ((localIsomorphismRestrictionComp Y S f.unop).app K').symm
          (etaleIsomorphismNormalizationArrow Y q dC U.unop)
          (etaleIsomorphismNormalizationArrow Y q dK U.unop)
          (etaleIsomorphismNormalizationArrow Y q dC V.unop)
          (etaleIsomorphismNormalizationArrow Y q dK V.unop)
          (hC.coherence f.unop) (hK.coherence f.unop) e (r U.unop e) he
        exact (StructuredArrow.normalizationUniversalIso_fac
          (hC.universal V.unop).some (hK.universal V.unop).some
          (localIsomorphismMap C K f.unop e)).trans ht }
  exact ⟨p, fun U e ↦ (StructuredArrow.normalizationUniversalIso_fac
    (hC.universal U).some (hK.universal U).some e).symm⟩

end AlgebraicGeometry.Scheme
