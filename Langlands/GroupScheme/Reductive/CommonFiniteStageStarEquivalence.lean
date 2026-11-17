import Langlands.GroupScheme.Reductive.StarActionFiniteStageProof
import Langlands.GroupScheme.Torus.CommonFiniteGaloisSplitting
import Mathlib.FieldTheory.Normal.Basic

/-! # Simultaneous finite-stage realization of an absolute star equivalence -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace CommonFiniteStageStarEquivalence

section RootData

variable {J J' I I' M M' N N' U U' V V' : Type u}
  [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup U] [AddCommGroup U'] [AddCommGroup V] [AddCommGroup V']
  {P : RootDatum J M N} {P' : RootDatum J' M' N'}
  {Q : RootDatum I U V} {Q' : RootDatum I' U' V'}

/-- Intertwining is transported through equivalences on both source and target root data. -/
theorem intertwine_transport
    (e : RootPairing.Equiv P Q) (e' : RootPairing.Equiv P' Q')
    (f : RootPairing.Equiv Q Q') (a : P.Aut) (a' : P'.Aut) (b : Q.Aut) (b' : Q'.Aut)
    (he : e.comp a = b.comp e) (he' : e'.comp a' = b'.comp e')
    (hf : f.comp b = b'.comp f) :
    ((RootPairing.Equiv.symm _ _ e').comp (f.comp e)).comp a =
      a'.comp ((RootPairing.Equiv.symm _ _ e').comp (f.comp e)) := by
  have h1 (x : M) : e.weightEquiv (a.weightEquiv x) = b.weightEquiv (e.weightEquiv x) :=
    congrArg (fun z : RootPairing.Equiv P Q => z.weightMap x) he
  have h2 (x : M') : e'.weightEquiv (a'.weightEquiv x) = b'.weightEquiv (e'.weightEquiv x) :=
    congrArg (fun z : RootPairing.Equiv P' Q' => z.weightMap x) he'
  have h3 (x : U) : f.weightEquiv (b.weightEquiv x) = b'.weightEquiv (f.weightEquiv x) :=
    congrArg (fun z : RootPairing.Equiv Q Q' => z.weightMap x) hf
  apply StarActionIndependence.equiv_ext_of_weightMap
  intro x
  apply e'.weightEquiv.injective
  change e'.weightEquiv (e'.weightEquiv.symm
      (f.weightEquiv (e.weightEquiv (a.weightEquiv x)))) =
    e'.weightEquiv (a'.weightEquiv
      (e'.weightEquiv.symm (f.weightEquiv (e.weightEquiv x))))
  rw [LinearEquiv.apply_symm_apply, h1, h3, h2, LinearEquiv.apply_symm_apply]

end RootData

end CommonFiniteStageStarEquivalence

/-- An absolute based star equivalence between two Galois pinning data is realized over
one finite Galois extension of the ground field. -/
def CommonFiniteStageStarEquivalenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G H : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    (d : GaloisPinningData k (SeparableClosure k) G)
    (d' : GaloisPinningData k (SeparableClosure k) H)
    (f : RootPairing.Equiv d.toSplitPinning.rootDatum d'.toSplitPinning.rootDatum)
    (_hb : ∀ a, a ∈ d.toSplitPinning.base.support ↔
      f.indexEquiv a ∈ d'.toSplitPinning.base.support)
    (_hstar : ∀ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
      f.comp (d.starAction σ).val = (d'.starAction σ).val.comp f),
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : FiniteDimensional k L)
      (_ : IsGalois k L) (δ : GaloisPinningData k L G) (δ' : GaloisPinningData k L H)
      (fL : RootPairing.Equiv δ.toSplitPinning.rootDatum δ'.toSplitPinning.rootDatum),
      (∀ a, a ∈ δ.toSplitPinning.base.support ↔
        fL.indexEquiv a ∈ δ'.toSplitPinning.base.support) ∧
      ∀ σ : L ≃ₐ[k] L, fL.comp (δ.starAction σ).val = (δ'.starAction σ).val.comp fL

/-- The common finite stage is obtained from one splitting field for both tori and
transport of the supplied equivalence through the two finite-stage comparisons. -/
theorem commonFiniteStageStarEquivalence : CommonFiniteStageStarEquivalenceStatement.{u} := by
  intro k _ G H _ _ _ _ d d' f hb hstar
  have hT : IsTorus d.torus.toGrp :=
    ⟨SeparableClosure k, inferInstance, inferInstance, d.isSplitTorus⟩
  have hT' : IsTorus d'.torus.toGrp :=
    ⟨SeparableClosure k, inferInstance, inferInstance, d'.isSplitTorus⟩
  let s := hT.commonFiniteGaloisSplitting hT'
  let L := s.carrier
  let ι : L →ₐ[k] SeparableClosure k := IsSepClosed.lift
  let : Algebra L (SeparableClosure k) := ι.toRingHom.toAlgebra
  let : IsScalarTower k L (SeparableClosure k) :=
    IsScalarTower.of_algebraMap_eq' ι.comp_algebraMap.symm
  have hc : algebraBaseMap L (SeparableClosure k) ≫ algebraBaseMap k L =
      algebraBaseMap k (SeparableClosure k) := by
    simp only [algebraBaseMap, ← Spec.map_comp]
    congr 1
    ext x
    exact congrArg Subtype.val (ι.commutes x)
  obtain ⟨δ, e, he, hδ⟩ := StarActionFiniteStage.exists_stage d hc s.split_left
  obtain ⟨δ', e', he', hδ'⟩ := StarActionFiniteStage.exists_stage d' hc s.split_right
  let fL := (RootPairing.Equiv.symm _ _ e').comp (f.comp e)
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    δ, δ', fL, ?_, fun σ => ?_⟩
  · intro a
    change a ∈ δ.toSplitPinning.base.support ↔
      e'.indexEquiv.symm (f.indexEquiv (e.indexEquiv a)) ∈ δ'.toSplitPinning.base.support
    rw [he a, he' _, Equiv.apply_symm_apply]
    exact hb (e.indexEquiv a)
  · let τ : SeparableClosure k ≃ₐ[k] SeparableClosure k := σ.liftNormal (SeparableClosure k)
    have hστ (x : L) : τ (algebraMap L (SeparableClosure k) x) =
        algebraMap L (SeparableClosure k) (σ x) :=
      σ.liftNormal_commutes (SeparableClosure k) x
    exact CommonFiniteStageStarEquivalence.intertwine_transport e e' f
      (δ.starAction σ).val (δ'.starAction σ).val (d.starAction τ).val (d'.starAction τ).val
      (hδ σ τ hστ) (hδ' σ τ hστ) (hstar τ)

end Langlands.GroupScheme
