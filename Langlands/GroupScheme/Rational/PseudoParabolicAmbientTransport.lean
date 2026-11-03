import Langlands.GroupScheme.Rational.MinimalPseudoParabolic
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.GroupScheme.Rational.SplitUnipotentTransport

/-! # Ambient isomorphisms of pseudo-parabolic subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G G' P : GroupScheme S}

/-- Postcomposition by an ambient isomorphism transports an fppf-local
factorization and keeps the same relative cover. -/
theorem FppfLocallyInProduct.comp_iso {F N : SubgroupFunctor G}
    (e : G ≅ G') {T : Over S} {x : T ⟶ G.X}
    (hx : FppfLocallyInProduct F N x) :
    FppfLocallyInProduct (F.comap e.inv) (N.comap e.inv)
      (x ≫ e.hom.hom.hom) := by
  obtain ⟨V, v, hf, hs, hl, p, n, hp, hn, he⟩ := hx
  refine ⟨V, v, hf, hs, hl, p ≫ e.hom.hom.hom, n ≫ e.hom.hom.hom, ?_, ?_, ?_⟩
  · simpa only [mem_comap, Category.assoc, ← Grp.comp_hom_hom,
      e.hom_inv_id, Grp.id_hom_hom, Category.comp_id] using hp
  · simpa only [mem_comap, Category.assoc, ← Grp.comp_hom_hom,
      e.hom_inv_id, Grp.id_hom_hom, Category.comp_id] using hn
  · rw [← MonObj.mul_comp, ← Category.assoc, he]

/-- An ambient isomorphism preserves and reflects local product membership. -/
theorem fppfLocallyInProduct_comap_iso_iff (e : G ≅ G')
    (F N : SubgroupFunctor G) {T : Over S} (x : T ⟶ G'.X) :
    FppfLocallyInProduct (F.comap e.inv) (N.comap e.inv) x ↔
      FppfLocallyInProduct F N (x ≫ e.inv.hom.hom) := by
  constructor
  · intro hx
    simpa only [Iso.symm_inv, Iso.symm_hom, ← comap_comp, Iso.hom_inv_id, comap_id] using
      hx.comp_iso e.symm
  · intro hx
    simpa only [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
      Grp.id_hom_hom, Category.comp_id] using hx.comp_iso e

/-- Represented fppf-local products transport through any ambient isomorphism. -/
theorem IsFppfProduct.comp_iso {F N : SubgroupFunctor G} {i : P ⟶ G}
    (hi : IsFppfProduct F N i) (e : G ≅ G') :
    IsFppfProduct (F.comap e.inv) (N.comap e.inv) (i ≫ e.hom) := by
  refine ⟨hi.isClosedSubgroup.comp_iso e, ?_⟩
  intro T x
  rw [range_comp_iso, mem_comap, hi.mem_range_iff,
    fppfLocallyInProduct_comap_iso_iff]

end SubgroupFunctor

variable {k : Type u} [Field k]
  {G G' P U : GroupScheme (Spec (CommRingCat.of k))}

/-- A greatest ground-field unipotent radical transports through an ambient
isomorphism, including its all-test normality and greatestness. -/
theorem IsUnipotentRadical.comp_iso {i : U ⟶ G}
    (hi : IsUnipotentRadical i) (e : G ≅ G') :
    IsUnipotentRadical (i ≫ e.hom) := by
  refine ⟨hi.isClosedSubgroup.comp_iso e, hi.smooth, hi.connectedSpace,
    hi.isUnipotent, ?_, ?_⟩
  · rw [SubgroupFunctor.range_comp_iso]
    exact hi.isNormal.comap e.inv
  · intro H j hj hs hc hu hn
    have hn' : (SubgroupFunctor.range (j ≫ e.inv)).IsNormal := by
      have hr : SubgroupFunctor.range (j ≫ e.inv) =
          (SubgroupFunctor.range j).comap e.hom := by
        simpa only [Iso.symm_hom, Iso.symm_inv] using
          SubgroupFunctor.range_comp_iso j e.symm
      rw [hr]
      exact hn.comap e.hom
    have hle := hi.greatest H (j ≫ e.inv) (hj.comp_iso e.symm) hs hc hu hn'
    have hle' := SubgroupFunctor.range_comp_mono hle e.hom
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hle'

/-- A greatest split ground-field unipotent radical transports through an
ambient isomorphism without changing its split series. -/
theorem IsSplitUnipotentRadical.comp_iso {i : U ⟶ G}
    (hi : IsSplitUnipotentRadical i) (e : G ≅ G') :
    IsSplitUnipotentRadical (i ≫ e.hom) := by
  refine ⟨hi.isClosedSubgroup.comp_iso e, hi.smooth, hi.connectedSpace,
    hi.isUnipotent, hi.isSplitUnipotent, ?_, ?_⟩
  · rw [SubgroupFunctor.range_comp_iso]
    exact hi.isNormal.comap e.inv
  · intro H j hj hs hc hu hsplit hn
    have hn' : (SubgroupFunctor.range (j ≫ e.inv)).IsNormal := by
      have hr : SubgroupFunctor.range (j ≫ e.inv) =
          (SubgroupFunctor.range j).comap e.hom := by
        simpa only [Iso.symm_hom, Iso.symm_inv] using
          SubgroupFunctor.range_comp_iso j e.symm
      rw [hr]
      exact hn.comap e.hom
    have hle := hi.greatest H (j ≫ e.inv) (hj.comp_iso e.symm) hs hc hu hsplit hn'
    have hle' := SubgroupFunctor.range_comp_mono hle e.hom
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hle'

/-- Pseudo-parabolic subgroups are preserved by ambient group isomorphisms. -/
theorem IsPseudoParabolicSubgroup.comp_iso {i : P ⟶ G}
    (hi : IsPseudoParabolicSubgroup i) (e : G ≅ G') :
    IsPseudoParabolicSubgroup (i ≫ e.hom) := by
  have : IsIso e.inv.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e.symm)).hom)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Over.w e.inv.hom.hom]
    let : Smooth G.X.hom := hi.smooth
    infer_instance
  · exact (Scheme.homeoOfIso ((Over.forget _).mapIso
      ((Grp.forget _).mapIso e))).connectedSpace_iff.mp hi.connectedSpace
  · rw [← Over.w e.inv.hom.hom]
    let : IsAffineHom G.X.hom := hi.isAffineHom
    infer_instance
  · obtain ⟨U, j, χ, hj, hprod⟩ := hi.presentation
    refine ⟨U, j ≫ e.hom, χ ≫ e.hom, hj.comp_iso e, ?_⟩
    have hpar : Dynamic.parabolic (χ ≫ e.hom) = (Dynamic.parabolic χ).comap e.inv := by
      simpa only [Iso.symm_hom, Dynamic.comp_hom_comp_inv] using
        Dynamic.parabolic_eq_comap_of_iso (χ ≫ e.hom) e.symm
    rw [hpar, SubgroupFunctor.range_comp_iso]
    exact hprod.comp_iso e

/-- Pseudo-parabolic structure is invariant under ambient group isomorphisms. -/
theorem IsPseudoParabolicSubgroup.comp_iso_iff (i : P ⟶ G) (e : G ≅ G') :
    IsPseudoParabolicSubgroup (i ≫ e.hom) ↔ IsPseudoParabolicSubgroup i := by
  constructor
  · intro hi
    simpa using hi.comp_iso e.symm
  · exact fun hi => hi.comp_iso e

/-- Minimal pseudo-parabolic subgroups transport through ambient isomorphisms. -/
theorem IsMinimalPseudoParabolicSubgroup.comp_iso {i : P ⟶ G}
    (hi : IsMinimalPseudoParabolicSubgroup i) (e : G ≅ G') :
    IsMinimalPseudoParabolicSubgroup (i ≫ e.hom) := by
  refine ⟨hi.1.comp_iso e, ?_⟩
  intro Q j hj hle
  have hle' : SubgroupFunctor.range (j ≫ e.inv) ≤ SubgroupFunctor.range i := by
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      SubgroupFunctor.range_comp_mono hle e.inv
  have heq := hi.2 Q (j ≫ e.inv) (hj.comp_iso e.symm) hle'
  apply le_antisymm hle
  have hreverse := SubgroupFunctor.range_comp_mono heq.ge e.hom
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hreverse

/-- Minimal pseudo-parabolic structure is invariant under ambient isomorphisms. -/
theorem IsMinimalPseudoParabolicSubgroup.comp_iso_iff (i : P ⟶ G) (e : G ≅ G') :
    IsMinimalPseudoParabolicSubgroup (i ≫ e.hom) ↔ IsMinimalPseudoParabolicSubgroup i := by
  constructor
  · intro hi
    simpa using hi.comp_iso e.symm
  · exact fun hi => hi.comp_iso e

/-- Postcomposition identifies minimal pseudo-parabolic embeddings of a fixed
source into isomorphic ambient group schemes. -/
def minimalPseudoParabolicEmbeddingEquiv (P : GroupScheme (Spec (CommRingCat.of k)))
    (e : G ≅ G') :
    {i : P ⟶ G // IsMinimalPseudoParabolicSubgroup i} ≃
      {j : P ⟶ G' // IsMinimalPseudoParabolicSubgroup j} where
  toFun i := ⟨i.1 ≫ e.hom, i.2.comp_iso e⟩
  invFun j := ⟨j.1 ≫ e.inv, j.2.comp_iso e.symm⟩
  left_inv i := Subtype.ext (by simp [Category.assoc])
  right_inv j := Subtype.ext (by simp [Category.assoc])

@[simp] theorem minimalPseudoParabolicEmbeddingEquiv_apply
    (e : G ≅ G') (i : {i : P ⟶ G // IsMinimalPseudoParabolicSubgroup i}) :
    (minimalPseudoParabolicEmbeddingEquiv P e i).1 = i.1 ≫ e.hom := rfl

end Langlands.GroupScheme
