import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Torus.Weights
import Langlands.GroupScheme.Torus.KernelCocharacters

/-! # Statement: kernels of torus maps through which every root factors are central -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Kernel centrality** (derived; compare Milne Propositions 21.7 and 21.8). Let `G` be a
smooth connected affine group scheme over a field, `i : T ⟶ G` a homomorphism from a split
torus, and `t : T ⟶ T'` a homomorphism of commutative group schemes. If every root of `i` is
of the form `t ≫ α'`, then the actual scheme kernel of `t`, mapped into `G` by `i`, is
central in `G` on every test scheme. -/
def SplitTorusKernelCentralityStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (T T' : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp →
    ∀ (i : T.toGrp ⟶ G) (t : T ⟶ T'),
      (∀ α ∈ roots i, ∃ α' : characterLattice T', α = t ≫ α') →
        IsCentral (CommGroupScheme.groupHom (CommGroupScheme.kernelι t) ≫ i)

end Langlands.GroupScheme
