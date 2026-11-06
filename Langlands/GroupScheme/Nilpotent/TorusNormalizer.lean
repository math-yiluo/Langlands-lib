import Langlands.GroupScheme.Nilpotent.TorusDescent
import Langlands.GroupScheme.Rational.TorusNormalizer

/-! # Every point of a nilpotent group normalizes every torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

/-- Every point centralizes a central torus homomorphism. -/
theorem IsCentral.mem_torusCentralizer {S : Scheme.{u}} {T : CommGroupScheme S}
    {G : GroupScheme S} {i : T.toGrp ⟶ G} (hi : IsCentral i) (U : Over S) (g : U ⟶ G.X) :
    g ∈ (torusCentralizer i).carrier U := by
  intro V a t
  have h := hi V t V (𝟙 V) (a ≫ g)
  rw [Category.id_comp] at h
  exact h.symm

/-- Every point normalizes a central torus homomorphism. -/
theorem IsCentral.mem_torusNormalizer {S : Scheme.{u}} {T : CommGroupScheme S}
    {G : GroupScheme S} {i : T.toGrp ⟶ G} (hi : IsCentral i) (U : Over S) (g : U ⟶ G.X) :
    g ∈ (torusNormalizer i).carrier U :=
  torusCentralizer_le_torusNormalizer i U (hi.mem_torusCentralizer U g)

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- In a smooth connected affine geometrically nilpotent group, every point over every test
scheme normalizes every homomorphism from a torus, in particular every maximal torus. -/
theorem IsNilpotentGroupScheme.mem_torusNormalizer (hG : IsNilpotentGroupScheme G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsTorus T.toGrp) (i : T.toGrp ⟶ G)
    (U : Over (Spec (CommRingCat.of k))) (g : U ⟶ G.X) :
    g ∈ (torusNormalizer i).carrier U :=
  (hG.isCentral_of_isTorus T hT i).mem_torusNormalizer U g

/-- Statement form of this module's main theorem: in a smooth connected affine geometrically
nilpotent group over a field, every point over every test scheme normalizes every homomorphism
from a torus. -/
def NilpotentTorusNormalizerStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    IsNilpotentGroupScheme G → ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))),
      IsTorus T.toGrp → ∀ (i : T.toGrp ⟶ G) (U : Over (Spec (CommRingCat.of k)))
        (g : U ⟶ G.X), g ∈ (torusNormalizer i).carrier U

/-- Proof of `NilpotentTorusNormalizerStatement`. -/
theorem nilpotentTorusNormalizer : NilpotentTorusNormalizerStatement.{u} :=
  fun _ _ _ _ _ _ hG _ hT i U g => hG.mem_torusNormalizer hT i U g

end Langlands.GroupScheme
