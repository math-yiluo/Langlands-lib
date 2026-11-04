import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.Torus.NormalizerRepresentationWeights
import Langlands.GroupScheme.Torus.RepresentationWeightWeylFinite

/-! # Finite full Weyl images of closed split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

/-- For a standard split torus, a closed faithful matrix representation and its
finite generating weight set control the whole character-lattice Weyl image. -/
theorem finite_weylImage_standard
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (I : Type u) [Finite I] (j : splitTorus (Spec (CommRingCat.of k)) I ⟶ G)
    (hj : IsClosedSubgroup j) :
    have : IsClosedImmersion j.hom.hom.left := hj
    Finite (weylImage (T := splitTorus.commGroupScheme _ I) j) := by
  classical
  let := Fintype.ofFinite I
  have : IsClosedImmersion j.hom.hom.left := hj
  obtain ⟨N, ρ, hρ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  have hmono : Mono (j.hom.hom ≫ ρ.hom.hom).left := by
    change Mono (j.hom.hom.left ≫ ρ.hom.hom.left)
    infer_instance
  exact RepresentationWeightWeylFinite.finite_weylImage_of_weight_stable I ρ j hmono
    (fun n _ hm => NormalizerRepresentationWeights.weight_ne_zero_normalizingAut
      I ρ j n hm)

/-- The full actual normalizer image of every closed split torus in an affine
algebraic group is finite. -/
theorem splitTorusWeylImageFinite : SplitTorusWeylImageFiniteStatement.{u} :=
  splitTorusWeylImageFinite_of_standard (fun _ _ G _ _ I _ j hj =>
    finite_weylImage_standard G I j hj)

/-- A finite enumeration of the actual full Weyl-image subgroup, for any closed
split torus in an affine algebraic group. -/
@[instance_reducible]
def weylImageFintypeOfClosedSplitTorus
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsClosedSubgroup i) :
    haveI : IsClosedImmersion i.hom.hom.left := hi
    Fintype (weylImage i) := by
  haveI : IsClosedImmersion i.hom.hom.left := hi
  haveI : Finite (weylImage i) := splitTorusWeylImageFinite k G T hT i hi
  exact Fintype.ofFinite _

end Langlands.GroupScheme
