import Langlands.GroupScheme.Rational.PseudoParabolicAmbientTransport
import Langlands.GroupScheme.Unipotent.BaseChange
import Langlands.GroupScheme.Torus.SplitDescent
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.CocharacterTransport
import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.GroupScheme.Dynamic.DescentTransport
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicRangeReduction

/-! # Unipotent radicals under field isomorphisms and Galois transport -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RadicalFieldTransport

/-- The pullback comparison along a section is natural in the group scheme. -/
theorem sectionIso_naturality {S S' : Scheme.{u}}
    (b : S' ⟶ S) (a : S ⟶ S') (ha : a ≫ b = 𝟙 S)
    {U G : GroupScheme S} (i : U ⟶ G) :
    (GroupScheme.baseChange a).map ((GroupScheme.baseChange b).map i) ≫
        (baseChangeSectionIso b a ha G).hom =
      (baseChangeSectionIso b a ha U).hom ≫ i := by
  have heq : ∀ {c d : S ⟶ S} (h : c = d),
      (GroupScheme.baseChange c).map i ≫
          (eqToIso (congrArg (fun t => (GroupScheme.baseChange t).obj G) h)).hom =
        (eqToIso (congrArg (fun t => (GroupScheme.baseChange t).obj U) h)).hom ≫
          (GroupScheme.baseChange d).map i := by
    intro c d h
    subst d
    simp
  have hc :=
    (((Functor.mapGrpNatIso (Over.pullbackComp a b)) ≪≫
      Functor.mapGrpCompIso).inv.naturality i)
  change (GroupScheme.baseChange a).map ((GroupScheme.baseChange b).map i) ≫
      (baseChangeCompIso b a G).inv =
    (baseChangeCompIso b a U).inv ≫ (GroupScheme.baseChange (a ≫ b)).map i at hc
  have hi :=
    (((Functor.mapGrpNatIso Over.pullbackId) ≪≫
      Functor.mapGrpIdIso).hom.naturality i)
  change (GroupScheme.baseChange (𝟙 S)).map i ≫ (baseChangeIdIso G).hom =
    (baseChangeIdIso U).hom ≫ i at hi
  change (GroupScheme.baseChange a).map ((GroupScheme.baseChange b).map i) ≫
      ((baseChangeCompIso b a G).inv ≫
        (eqToIso (congrArg (fun t => (GroupScheme.baseChange t).obj G) ha)).hom ≫
          (baseChangeIdIso G).hom) = _
  rw [← Category.assoc, hc, Category.assoc, ← Category.assoc _ _ (baseChangeIdIso G).hom,
    heq ha, Category.assoc, hi]
  simp only [baseChangeSectionIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]

/-- The inverse pullback comparison satisfies the same commuting square. -/
theorem sectionIso_inv_naturality {S S' : Scheme.{u}}
    (b : S' ⟶ S) (a : S ⟶ S') (ha : a ≫ b = 𝟙 S)
    {U G : GroupScheme S} (i : U ⟶ G) :
    i ≫ (baseChangeSectionIso b a ha G).inv =
      (baseChangeSectionIso b a ha U).inv ≫
        (GroupScheme.baseChange a).map ((GroupScheme.baseChange b).map i) := by
  apply (cancel_mono (baseChangeSectionIso b a ha G).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    sectionIso_naturality, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Unipotence is preserved by a specified field homomorphism. -/
theorem isUnipotent_map {k K : Type u} [Field k] [Field K]
    (f : k →+* K) {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] (hH : IsUnipotent H) :
    IsUnipotent ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom f))).obj H) := by
  let : Algebra k K := f.toAlgebra
  exact hH.baseChange

/-- A base isomorphism preserves connectedness of a group scheme. -/
theorem connectedSpace_map {S S' : Scheme.{u}} (b : S' ⟶ S) [IsIso b]
    (H : GroupScheme S) (hc : ConnectedSpace H.X.left) :
    ConnectedSpace ((GroupScheme.baseChange b).obj H).X.left :=
  (Scheme.homeoOfIso (asIso (pullback.fst H.X.hom b))).connectedSpace_iff.mpr hc

/-- Containment after inverse pullback and the section comparison implies
containment after the original pullback. -/
theorem range_le_of_section {S S' : Scheme.{u}}
    (b : S' ⟶ S) (a : S ⟶ S') (ha : a ≫ b = 𝟙 S)
    [QuasiCompact a] [Flat a] [Surjective a]
    {U G : GroupScheme S} {H : GroupScheme S'} (i : U ⟶ G)
    (j : H ⟶ (GroupScheme.baseChange b).obj G)
    [Mono ((GroupScheme.baseChange b).map i).hom.hom]
    (h : SubgroupFunctor.range
        ((GroupScheme.baseChange a).map j ≫ (baseChangeSectionIso b a ha G).hom) ≤
      SubgroupFunctor.range i) :
    SubgroupFunctor.range j ≤ SubgroupFunctor.range ((GroupScheme.baseChange b).map i) := by
  apply SubgroupFunctor.le_range_of_baseChange_le a ((GroupScheme.baseChange b).map i)
  rw [← SubgroupFunctor.range_baseChangeHom,
    ← SubgroupFunctor.range_baseChangeHom]
  have h' := SubgroupFunctor.range_comp_mono h (baseChangeSectionIso b a ha G).inv
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h'
  rw [sectionIso_inv_naturality] at h'
  intro T x hx
  obtain ⟨z, hz⟩ := h' T hx
  change z ≫ ((baseChangeSectionIso b a ha U).inv ≫
    (GroupScheme.baseChange a).map ((GroupScheme.baseChange b).map i)).hom.hom = x at hz
  refine ⟨z ≫ (baseChangeSectionIso b a ha U).inv.hom.hom, ?_⟩
  change (z ≫ (baseChangeSectionIso b a ha U).inv.hom.hom) ≫
    ((GroupScheme.baseChange a).map ((GroupScheme.baseChange b).map i)).hom.hom = x
  simpa only [Grp.comp_hom_hom, Category.assoc] using hz

end RadicalFieldTransport

section FieldIso

variable {k K : Type u} [Field k] [Field K]
  {G U : GroupScheme (Spec (CommRingCat.of k))}

/-- A represented ground-field unipotent radical is preserved by an actual
isomorphism of the ground fields. -/
theorem IsUnipotentRadical.baseChange_ringEquiv
    {i : U ⟶ G} [IsAffineHom G.X.hom] (hi : IsUnipotentRadical i)
    (f : k ≃+* K) :
    IsUnipotentRadical ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom f.toRingHom))).map i) := by
  let b := Spec.map (CommRingCat.ofHom f.toRingHom)
  let a := Spec.map (CommRingCat.ofHom f.symm.toRingHom)
  have ha : a ≫ b = 𝟙 _ := by
    dsimp [a, b]
    rw [← Spec.map_comp]
    change Spec.map
      (CommRingCat.ofHom f.toRingHom ≫ CommRingCat.ofHom f.symm.toRingHom) = _
    have h : CommRingCat.ofHom f.toRingHom ≫ CommRingCat.ofHom f.symm.toRingHom =
        𝟙 (CommRingCat.of k) := by
      ext x
      exact f.symm_apply_apply x
    rw [h, Spec.map_id]
  have : IsIso b := isIso_SpecMap_iff.mpr f.bijective
  have : IsIso a := isIso_SpecMap_iff.mpr f.symm.bijective
  let : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  let : IsAffineHom U.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  let : Smooth U.X.hom := hi.smooth
  have hs : Smooth ((GroupScheme.baseChange b).obj U).X.hom := by
    change Smooth (pullback.snd U.X.hom b)
    infer_instance
  let : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  refine ⟨hi.isClosedSubgroup.baseChange b, hs,
    RadicalFieldTransport.connectedSpace_map b U hi.connectedSpace,
    RadicalFieldTransport.isUnipotent_map f.toRingHom hi.isUnipotent, ?_, ?_⟩
  · rw [SubgroupFunctor.range_baseChangeHom]
    exact hi.isNormal.baseChange b
  · intro H j hj hs hc hu hn
    let : IsClosedImmersion j.hom.hom.left := hj
    let : IsAffineHom H.X.hom := by
      rw [← Over.w j.hom.hom]
      infer_instance
    let : Smooth H.X.hom := hs
    let e := baseChangeSectionIso b a ha G
    have hj' := (hj.baseChange a).comp_iso e
    have hn' : (SubgroupFunctor.range
        ((GroupScheme.baseChange a).map j ≫ e.hom)).IsNormal := by
      rw [SubgroupFunctor.range_comp_iso, SubgroupFunctor.range_baseChangeHom]
      exact (hn.baseChange a).comap e.inv
    have hle := hi.greatest ((GroupScheme.baseChange a).obj H)
      ((GroupScheme.baseChange a).map j ≫ e.hom) hj'
      (show Smooth (pullback.snd H.X.hom a) from inferInstance)
      (RadicalFieldTransport.connectedSpace_map a H hc)
      (RadicalFieldTransport.isUnipotent_map f.symm.toRingHom hu) hn'
    let : IsClosedImmersion ((GroupScheme.baseChange b).map i).hom.hom.left :=
      hi.isClosedSubgroup.baseChange b
    let : Mono ((GroupScheme.baseChange b).map i).hom.hom :=
      Over.mono_of_mono_left _
    exact RadicalFieldTransport.range_le_of_section b a ha i j hle

end FieldIso

section Galois

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {U : GroupScheme (Spec (CommRingCat.of K))}
    {i : U ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj G}

/-- The actual canonical Galois translate of a represented subgroup inclusion. -/
def radicalGaloisHom (i : U ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
    (σ : K ≃ₐ[k] K) :
    (GroupScheme.baseChange (galoisBaseMap k K σ)).obj U ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G :=
  (GroupScheme.baseChange (galoisBaseMap k K σ)).map i ≫
    (descentBaseChangeIso (algebraBaseMap k K) (galoisBaseMap k K σ)
      (galoisBaseMap_over k K σ) G).hom

/-- Canonical Galois transport preserves the greatest ground-field radical. -/
theorem IsUnipotentRadical.galoisTransport [IsAffineHom G.X.hom]
    (hi : IsUnipotentRadical i) (σ : K ≃ₐ[k] K) :
    IsUnipotentRadical (radicalGaloisHom i σ) := by
  let : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
    infer_instance
  exact (hi.baseChange_ringEquiv σ.toRingEquiv).comp_iso
    (descentBaseChangeIso (algebraBaseMap k K) (galoisBaseMap k K σ)
      (galoisBaseMap_over k K σ) G)

/-- A represented radical and its canonical Galois translate have the same
image on every relative test scheme. -/
theorem IsUnipotentRadical.range_galoisTransport [IsAffineHom G.X.hom]
    (hi : IsUnipotentRadical i) (σ : K ≃ₐ[k] K) :
    SubgroupFunctor.range (radicalGaloisHom i σ) = SubgroupFunctor.range i :=
  (hi.galoisTransport σ).range_eq hi

/-- The all-test subgroup functor of a represented radical is Galois invariant. -/
theorem IsUnipotentRadical.descentTransport_range [IsAffineHom G.X.hom]
    (hi : IsUnipotentRadical i) (σ : K ≃ₐ[k] K) :
    SubgroupFunctor.descentTransport (algebraBaseMap k K) (galoisBaseMap k K σ)
      (galoisBaseMap_over k K σ) G (SubgroupFunctor.range i) =
        SubgroupFunctor.range i := by
  rw [SubgroupFunctor.descentTransport, ← SubgroupFunctor.range_baseChangeHom,
    ← SubgroupFunctor.range_comp_iso]
  exact hi.range_galoisTransport σ

/-- The actual comparison between a Galois-translated radical and the original
source group scheme, characterized by their common embedding. -/
def IsUnipotentRadical.galoisSourceIso [IsAffineHom G.X.hom]
    (hi : IsUnipotentRadical i) (σ : K ≃ₐ[k] K) :
    (GroupScheme.baseChange (galoisBaseMap k K σ)).obj U ≅ U :=
  (hi.galoisTransport σ).isClosedSubgroup.sourceIsoOfRangeEq hi.isClosedSubgroup
    (hi.range_galoisTransport σ)

/-- The comparison of source group schemes commutes with the actual inclusions. -/
theorem IsUnipotentRadical.galoisSourceIso_hom_comp [IsAffineHom G.X.hom]
    (hi : IsUnipotentRadical i) (σ : K ≃ₐ[k] K) :
    (hi.galoisSourceIso σ).hom ≫ i = radicalGaloisHom i σ :=
  (hi.galoisTransport σ).isClosedSubgroup.sourceIsoOfRangeEq_hom_comp hi.isClosedSubgroup
    (hi.range_galoisTransport σ)

end Galois

end Langlands.GroupScheme
