import Langlands.GroupScheme.Reductive.SplitWeylRationalityStatement
import Langlands.GroupScheme.Torus.FieldAutomorphismDescent
import Langlands.GroupScheme.Torus.FieldTransporterDescent
import Langlands.GroupScheme.Reductive.LocalSplitCorootTransport
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof

/-! # Rational representatives for split maximal-torus Weyl actions -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme
namespace SplitWeylRationality

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
  (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
  (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
  (n' : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X)
  (σ' : (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T ≅
    (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
  (hn' : IsNormalizingPoint ((GroupScheme.baseChange (algebraBaseMap k K)).map i) n' σ')

include hG hi hn'

/-- The descended torus automorphism admits a rational normalizing point. -/
theorem exists_normalizingPoint :
    ∃ n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      IsNormalizingPoint i n (hT.descendedAutomorphism (algebraBaseMap k K) σ') := by
  let b := algebraBaseMap k K
  let σ := hT.descendedAutomorphism b σ'
  have hσ : (CommGroupScheme.baseChange b).mapIso σ = σ' :=
    hT.descendedAutomorphism_spec b σ'
  have hx' : PointwiseSchemeAction.IsTransporter
      ((GroupScheme.baseChange b).map (CommGroupScheme.groupHom σ.hom ≫ i))
      ((GroupScheme.baseChange b).map i) n' := by
    have h := hn'.isTransporter
    rw [← hσ] at h
    change PointwiseSchemeAction.IsTransporter
      ((GroupScheme.baseChange b).map (CommGroupScheme.groupHom σ.hom) ≫
        (GroupScheme.baseChange b).map i) ((GroupScheme.baseChange b).map i) n' at h
    simpa only [Functor.map_comp] using h
  let U := (Over.map b).obj (Over.mk (𝟙 (Spec (CommRingCat.of K))))
  let x : U ⟶ G.X := baseChangePointsEquiv b G _ n'
  have hx : PointwiseSchemeAction.IsTransporter (CommGroupScheme.groupHom σ.hom ≫ i) i x :=
    hx'.baseChangePointsEquiv b
  have hcover : Flat b ∧ Surjective b :=
    (flat_and_surjective_SpecMap_iff _).2
      (RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance)
  have : Flat U.hom := by
    change Flat (𝟙 _ ≫ b)
    simpa only [Category.id_comp] using hcover.1
  have : Surjective U.hom := by
    change Surjective (𝟙 _ ≫ b)
    simpa only [Category.id_comp] using hcover.2
  have : IsAffineHom U.hom := by
    change IsAffineHom (𝟙 _ ≫ b)
    rw [Category.id_comp]
    change IsAffineHom (Spec.map _)
    infer_instance
  have : IsClosedImmersion i.hom.hom.left := hi.2.1
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  obtain ⟨n, hn⟩ := PointwiseSchemeAction.exists_transporter_of_cover hT hx
    (maximalTorusCentralizer k G hG T i hi)
  exact ⟨n, IsNormalizingPoint.of_isTransporter hn⟩

/-- Choose a ground-field normalizer inducing the specified extension-field action. -/
def normalizingPoint : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X :=
  (exists_normalizingPoint k K G hG T hT i hi n' σ' hn').choose

/-- The chosen point induces the descended automorphism of the actual torus. -/
theorem normalizingPoint_spec :
    IsNormalizingPoint i (normalizingPoint k K G hG T hT i hi n' σ' hn')
      (hT.descendedAutomorphism (algebraBaseMap k K) σ') :=
  (exists_normalizingPoint k K G hG T hT i hi n' σ' hn').choose_spec

end SplitWeylRationality

/-- Every extension-field normalizer action on a split maximal torus has a
rational normalizer representative over the ground field. -/
theorem splitMaximalTorusWeylRationality : SplitMaximalTorusWeylRationalityStatement.{u} := by
  intro k K _ _ _ G hG T hT i hi n' σ' hn'
  exact ⟨SplitWeylRationality.normalizingPoint k K G hG T hT i hi n' σ' hn',
    hT.descendedAutomorphism (algebraBaseMap k K) σ',
    SplitWeylRationality.normalizingPoint_spec k K G hG T hT i hi n' σ' hn',
    hT.descendedAutomorphism_spec (algebraBaseMap k K) σ'⟩

end Langlands.GroupScheme
