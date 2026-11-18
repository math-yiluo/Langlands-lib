import Langlands.GroupScheme.SimplyConnected.TypeE7WeylInversion
import Langlands.GroupScheme.SimplyConnected.TypeDVectorQuotient
import Langlands.GroupScheme.Rational.RelativeWeylAbsoluteRestrictionProof

/-! # Rational lifting of actual E7 inversion -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- Inversion of a torus restricts to inversion along every commutative-group map. -/
theorem IsNormalizingPoint.restrict_negIso {S : Scheme.{u}}
    {T U : CommGroupScheme S} {G : GroupScheme S} {j : T.toGrp ⟶ G}
    {n : Over.mk (𝟙 S) ⟶ G.X}
    (hn : IsNormalizingPoint j n (SpecialLinearTorusAutomorphism.negIso T))
    (f : U ⟶ T) :
    IsNormalizingPoint (CommGroupScheme.groupHom f ≫ j) n
      (SpecialLinearTorusAutomorphism.negIso U) := by
  unfold IsNormalizingPoint at hn ⊢
  rw [Category.assoc, hn, ← Category.assoc]
  have hf : f ≫ (SpecialLinearTorusAutomorphism.negIso T).hom =
      (SpecialLinearTorusAutomorphism.negIso U).hom ≫ f := by
    simp only [SpecialLinearTorusAutomorphism.negIso, Preadditive.comp_neg,
      Preadditive.neg_comp, Category.comp_id, Category.id_comp]
  change CommGroupScheme.groupHom
    (f ≫ (SpecialLinearTorusAutomorphism.negIso T).hom) ≫ j = _
  rw [hf]
  rfl

namespace TitsIndexData

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)

/-- The precise proposition implemented by `exists_rational_normalizer_and_geometric_inversion_of_E7`. -/
def E7RationalInversionStatement : Prop :=
  ∀ (_hsc : IsSimplyConnected G) (e : d.Vertex ≃ Fin 7)
    (_he : ∀ a b, d.cartan a b = CartanMatrix.E 7 (e a) (e b)),
    ∃ (n : normalizerPoints d.splitInclusion) (σ : d.splitTorus ≅ d.splitTorus)
      (m : normalizerPoints d.pinning.toSplitPinning.inclusion),
      IsNormalizingPoint d.splitInclusion n σ ∧
      (CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).mapIso σ =
        SpecialLinearTorusAutomorphism.negIso
          ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj d.splitTorus) ∧
      IsNormalizingPoint d.pinning.toSplitPinning.inclusion m
        (SpecialLinearTorusAutomorphism.negIso d.pinning.toSplitPinning.torus)

/-- A rational normalizer and a geometric full-torus inverter have the same
actual action on the base-changed distinguished split torus. -/
theorem exists_rational_normalizer_and_geometric_inversion_of_E7
    (hsc : IsSimplyConnected G) (e : d.Vertex ≃ Fin 7)
    (he : ∀ a b, d.cartan a b = CartanMatrix.E 7 (e a) (e b)) :
    ∃ (n : normalizerPoints d.splitInclusion) (σ : d.splitTorus ≅ d.splitTorus)
      (m : normalizerPoints d.pinning.toSplitPinning.inclusion),
      IsNormalizingPoint d.splitInclusion n σ ∧
      (CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).mapIso σ =
        SpecialLinearTorusAutomorphism.negIso
          ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj d.splitTorus) ∧
      IsNormalizingPoint d.pinning.toSplitPinning.inclusion m
        (SpecialLinearTorusAutomorphism.negIso d.pinning.toSplitPinning.torus) := by
  obtain ⟨m, hm⟩ := d.pinning.toSplitPinning.exists_normalizer_inverts_torus_of_E7
    (d.pinning_corootSpan_eq_top hsc) e he
  dsimp only [GaloisPinningData.toSplitPinning] at m hm ⊢
  have hS := hm.restrict_negIso
    ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map d.torusMap)
  have hsquare : CommGroupScheme.groupHom
      ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map d.torusMap) ≫
        d.pinning.toSplitPinning.inclusion =
      (GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map d.splitInclusion := by
    rw [← d.square, Functor.map_comp]
    rfl
  dsimp only [GaloisPinningData.toSplitPinning] at hsquare
  unfold IsNormalizingPoint at hS
  rw [hsquare] at hS
  obtain ⟨n, σ, hn, hσ⟩ := exists_isNormalizingPoint_baseChange_mapIso
    d.isSemisimple.isConnectedReductive d.maximalSplit hS
  exact ⟨⟨n, σ, hn⟩, σ, m, hn, hσ, hm⟩

end TitsIndexData
end Langlands.GroupScheme
