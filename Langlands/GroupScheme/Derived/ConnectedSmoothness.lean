import Langlands.GroupScheme.SmoothConnectedGeometryProof
import Langlands.GroupScheme.ImageGenerationPointed
import Langlands.GroupScheme.Derived.CommutatorEnvelope

/-! # Smoothness of derived subgroups of connected smooth affine groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Choose a smooth connected representative of the actual commutator envelope of a
smooth connected affine group over an arbitrary field. -/
def smoothConnectedCommutatorImage
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hsm : Smooth G.X.hom) (haff : IsAffineHom G.X.hom)
    (hconn : ConnectedSpace G.X.left) :
    { E : GeneratedImage (commutatorMap (𝟙 G) (𝟙 G)) //
      E.HasSmoothConnectedGeneration } := by
  have hGeneration : ∃ E : GeneratedImage (commutatorMap (𝟙 G) (𝟙 G)),
      E.HasSmoothConnectedGeneration := by
    obtain ⟨hVAff, hVFin, _, hVInt⟩ :=
      smoothConnectedAffineGeometry.2 k G G hsm haff hconn hsm haff hconn
    exact ImageGeneration.pointedImageGeneration k G hsm haff (G.X ⊗ G.X)
      hVAff hVFin hVInt
      (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X) 1)
      (commutatorMap (𝟙 G) (𝟙 G)) (by simp)
  exact ⟨Classical.choose hGeneration, Classical.choose_spec hGeneration⟩

namespace IsDerivedSubgroup

/-- The actual derived subgroup of a smooth connected affine group is smooth,
over any field and without any additional hypothesis on the representative. -/
theorem smooth_of_connected
    {k : Type u} [Field k] {G D : GroupScheme (Spec (CommRingCat.of k))}
    {d : D ⟶ G} (hd : IsDerivedSubgroup d)
    (hsm : Smooth G.X.hom) (haff : IsAffineHom G.X.hom)
    (hconn : ConnectedSpace G.X.left) : Smooth D.X.hom := by
  let E := smoothConnectedCommutatorImage k G hsm haff hconn
  exact hd.smooth_of_generatedImage E.val E.property.1

end IsDerivedSubgroup

end Langlands.GroupScheme
