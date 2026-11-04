import Langlands.GroupScheme.Reductive.RadicalFieldExtension.Unipotence
import Langlands.GroupScheme.Absolute.BorelFieldExtensionKSide

/-! # Interface of the rational-side contradiction

The internal statement that the module `RationalSide` proves and the module `KSide` uses.
Over an algebraically closed field, a smooth affine group scheme with trivial unipotent
radical has no prime of global functions strictly inside the augmentation ideal whose rational
zeros all lie in a normal solvable group of rational points acting unipotently in a closed
embedding into `GL_N`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RadicalFieldExtension

/-- The rational-side contradiction, as a proposition. -/
def RationalSideStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom], HasTrivialUnipotentRadical G →
    ∀ (N : Type) [Fintype N] [DecidableEq N] (ρ : MatrixRepresentation G N),
    IsClosedImmersion ρ.hom.hom.left →
    ∀ (𝔭 : Ideal Γ(G.X.left, ⊤)), 𝔭.IsPrime →
    𝔭 < RingHom.ker (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X).left.appTop.hom →
    ∀ (Γ : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)), Γ.Normal →
    Group.IsSolvable Γ →
    (∀ g ∈ Γ, IsNilpotent ((ρ.rationalMatrix g : Matrix N N k) - 1)) →
    (∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      𝔭 ≤ RingHom.ker x.left.appTop.hom → x ∈ Γ) →
    False

end Langlands.GroupScheme.RadicalFieldExtension
