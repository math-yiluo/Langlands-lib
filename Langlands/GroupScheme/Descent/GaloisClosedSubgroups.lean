import Langlands.GroupScheme.Rational.UnipotentRadicalDescent

/-! # Closed-subgroup descent from finite Galois invariance -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

open Descent

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
variable [FiniteDimensional k L] [IsGalois k L]
variable {G : GroupScheme (Spec (CommRingCat.of k))}
variable {H : GroupScheme (Spec (CommRingCat.of L))}
variable {i : H ⟶ (GroupScheme.baseChange (algebraBaseMap k L)).obj G}

/-- Invariance under every Galois automorphism implies invariance over the full
canonical descent overlap, with subgroup images tested on all relative schemes. -/
theorem IsClosedSubgroup.overlap_range_eq_of_galois_range_eq
    (hi : IsClosedSubgroup i)
    (h : ∀ σ : L ≃ₐ[k] L, SubgroupFunctor.range
      ((GroupScheme.baseChange (galoisBaseMap k L σ)).map i ≫
        (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
          (galoisBaseMap_over k L σ) G).hom) = SubgroupFunctor.range i) :
    SubgroupFunctor.range
        ((GroupScheme.baseChange (fst (fieldMap k L))).map i ≫
          (canonicalOverlap (fieldMap k L) G).hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange (snd (fieldMap k L))).map i) := by
  let e (σ : L ≃ₐ[k] L) :
      (GroupScheme.baseChange (galoisBaseMap k L σ)).obj H ≅ H :=
    ((hi.baseChange (galoisBaseMap k L σ)).comp_iso
      (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
        (galoisBaseMap_over k L σ) G)).sourceIsoOfRangeEq hi (h σ)
  have he (σ : L ≃ₐ[k] L) :
      (e σ).hom ≫ i = (GroupScheme.baseChange (galoisBaseMap k L σ)).map i ≫
        (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
          (galoisBaseMap_over k L σ) G).hom :=
    IsClosedSubgroup.sourceIsoOfRangeEq_hom_comp _ _ (h σ)
  have hinv (σ : L ≃ₐ[k] L) :
      (baseChangeIdIso H ≪≫ (e σ).symm).hom ≫
          (GroupScheme.baseChange (galoisBaseMap k L σ)).map i =
        (GroupScheme.baseChange (𝟙 _)).map i ≫
          (baseChangeIdIso ((GroupScheme.baseChange (algebraBaseMap k L)).obj G) ≪≫
            (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
              (galoisBaseMap_over k L σ) G).symm).hom := by
    apply (cancel_mono (descentBaseChangeIso (algebraBaseMap k L)
      (galoisBaseMap k L σ) (galoisBaseMap_over k L σ) G).hom).mp
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    rw [← he σ, Iso.inv_hom_id_assoc]
    exact (((Functor.mapGrpNatIso Over.pullbackId) ≪≫
      Functor.mapGrpIdIso).hom.naturality i).symm
  let ecomp (j : Fin (Module.finrank k L)) :=
    pullbackComparison (fst (fieldMap k L)) (finiteGaloisComponent k L j) (𝟙 _)
        (finiteGaloisComponent_fst k L j) H ≪≫
      baseChangeIdIso H ≪≫ (e (galoisIndexEquiv k L j)).symm ≪≫
        (pullbackComparison (snd (fieldMap k L)) (finiteGaloisComponent k L j)
          (galoisBaseMap k L (galoisIndexEquiv k L j))
            (finiteGaloisComponent_snd k L j) H).symm
  have hcomp (j : Fin (Module.finrank k L)) :
      (ecomp j).hom ≫
          (GroupScheme.baseChange (finiteGaloisComponent k L j)).map
            ((GroupScheme.baseChange (snd (fieldMap k L))).map i) =
        (GroupScheme.baseChange (finiteGaloisComponent k L j)).map
            ((GroupScheme.baseChange (fst (fieldMap k L))).map i) ≫
          (GroupScheme.baseChange (finiteGaloisComponent k L j)).map
            (canonicalOverlap (fieldMap k L) G).hom := by
    let q := finiteGaloisComponent k L j
    let a := galoisBaseMap k L (galoisIndexEquiv k L j)
    have hf : q ≫ fst (fieldMap k L) = 𝟙 _ := finiteGaloisComponent_fst k L j
    have hg : q ≫ snd (fieldMap k L) = a := finiteGaloisComponent_snd k L j
    apply (cancel_epi (pullbackComparison (fst (fieldMap k L)) q (𝟙 _) hf H).inv).mp
    apply (cancel_mono (pullbackComparison (snd (fieldMap k L)) q a hg
      ((GroupScheme.baseChange (algebraBaseMap k L)).obj G)).hom).mp
    simp only [Category.assoc]
    rw [pullbackComparison_naturality]
    change (pullbackComparison (fst (fieldMap k L)) q (𝟙 _) hf H).inv ≫
        ((pullbackComparison (fst (fieldMap k L)) q (𝟙 _) hf H).hom ≫
          (baseChangeIdIso H).hom ≫ (e (galoisIndexEquiv k L j)).inv ≫
            (pullbackComparison (snd (fieldMap k L)) q a hg H).inv) ≫
          (pullbackComparison (snd (fieldMap k L)) q a hg H).hom ≫
            (GroupScheme.baseChange a).map i = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    change (baseChangeIdIso H ≪≫ (e (galoisIndexEquiv k L j)).symm).hom ≫
      (GroupScheme.baseChange a).map i = _
    rw [hinv]
    rw [← pullIso_canonicalOverlap_eq (fieldMap k L) G a
      (galoisBaseMap_over k L (galoisIndexEquiv k L j)) q hf hg]
    change (GroupScheme.baseChange (𝟙 _)).map i ≫
        (pullIso q hf hg (canonicalOverlap (fieldMap k L) G)).hom = _
    rw [pullIso_hom]
    simp only [pullHom]
    rw [pullbackComparison_inv_naturality_assoc]
  let E := FiniteComponents.groupIso (finiteGaloisComponent k L) ecomp
  have hE : E.hom ≫ (GroupScheme.baseChange (snd (fieldMap k L))).map i =
      (GroupScheme.baseChange (fst (fieldMap k L))).map i ≫
        (canonicalOverlap (fieldMap k L) G).hom := by
    apply FiniteComponents.groupHom_ext (finiteGaloisComponent k L)
    intro j
    simpa only [Functor.map_comp, E, FiniteComponents.groupIso,
      FiniteComponents.map_groupHom] using hcomp j
  rw [← hE]
  exact SubgroupFunctor.range_iso_comp E _

namespace IsClosedSubgroup

variable (hi : IsClosedSubgroup i)
    (h : ∀ σ : L ≃ₐ[k] L, SubgroupFunctor.range
      ((GroupScheme.baseChange (galoisBaseMap k L σ)).map i ≫
        (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
          (galoisBaseMap_over k L σ) G).hom) = SubgroupFunctor.range i)

/-- The actual descent datum of a closed subgroup invariant under every
automorphism of a finite Galois extension. Its cocycle is derived by cancellation
of the closed inclusion. -/
def finiteGaloisDatum : Datum (fieldMap k L) H :=
  (canonicalDatum (fieldMap k L) G).closedSubgroup hi
    (hi.overlap_range_eq_of_galois_range_eq h)

/-- The original inclusion respects the constructed datum and the canonical
ambient datum. -/
theorem compatible_finiteGaloisDatum :
    Compatible (hi.finiteGaloisDatum h) (canonicalDatum (fieldMap k L) G) i :=
  (canonicalDatum (fieldMap k L) G).compatible_closedSubgroup hi
    (hi.overlap_range_eq_of_galois_range_eq h)

include hi h in
/-- Over an affine ambient group, finite Galois invariance gives an actual
affine closed subgroup over the original field and an exact recovery equation. -/
theorem exists_descent_of_galois_range_eq [IsAffineHom G.X.hom] :
    ∃ (H₀ : GroupScheme (Spec (CommRingCat.of k))) (j : H₀ ⟶ G)
      (e : (GroupScheme.baseChange (fieldMap k L)).obj H₀ ≅ H),
      IsAffine H₀.X.left ∧ IsClosedSubgroup j ∧
        (GroupScheme.baseChange (fieldMap k L)).map j = e.hom ≫ i := by
  let : Flat (fieldMap k L) := (fieldExtension_fpqc k L).2.1
  let : Surjective (fieldMap k L) := (fieldExtension_fpqc k L).1
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact hi.exists_descent_of_overlap_range_eq (fieldMap k L)
    (hi.overlap_range_eq_of_galois_range_eq h)

end IsClosedSubgroup

end Langlands.GroupScheme
