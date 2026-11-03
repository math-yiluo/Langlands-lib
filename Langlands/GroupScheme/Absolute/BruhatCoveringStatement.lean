import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.InnerAutomorphismHom

/-! # Absolute Bruhat covering for an actual Borel pair -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
variable {G B : GroupScheme (Spec (CommRingCat.of k))}
variable {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The absolute covering `G(k) = B(k) N_G(T)(k) B(k)`, with normalizer
membership expressed by an actual automorphism of the embedded torus. -/
def BorelTorusBruhatCovering (i : B ⟶ G) (j : T.toGrp ⟶ G) : Prop :=
  ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
    ∃ (b₁ b₂ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X)
      (n : normalizerPoints j),
      g = (b₁ ≫ i.hom.hom) * (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) *
        (b₂ ≫ i.hom.hom)

/-- Absolute geometric Bruhat covering for every Borel pair of a connected
reductive group over an algebraically closed field (Borel--Tits 1965, §2.4). -/
def AbsoluteBruhatCoveringStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (B : GroupScheme (Spec (CommRingCat.of k)))
      (T : CommGroupScheme (Spec (CommRingCat.of k)))
      (i : B ⟶ G) (j : T.toGrp ⟶ G),
      IsBorelPair i j → BorelTorusBruhatCovering i j

end Langlands.GroupScheme
