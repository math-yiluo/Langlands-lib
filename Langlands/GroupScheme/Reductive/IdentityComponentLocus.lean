import Langlands.GroupScheme.IdentityComponent.Transport
import Langlands.GroupScheme.Reductive.AlgebraicallyClosedPseudoReductive

/-! # The reductive identity-component locus of a smooth affine group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} (G : GroupScheme S)
  [Smooth G.X.hom] [IsAffineHom G.X.hom]

local instance geometricFiber_smooth (s : S) :
    Smooth (geometricFiber G s).X.hom :=
  inferInstanceAs (Smooth (Limits.pullback.snd G.X.hom (geometricPoint S s)))

local instance geometricFiber_isAffineHom (s : S) :
    IsAffineHom (geometricFiber G s).X.hom :=
  inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (geometricPoint S s)))

/-- Points where the actual identity component of the geometric fibre is reductive. -/
def identityComponentReductiveLocus : Set S :=
  {s | IsConnectedReductive (identityComponent (geometricFiber G s))}

/-- Conrad's openness theorem for the reductive identity-component locus of an arbitrary
smooth affine group scheme, without a connectedness assumption on its fibres. -/
def IdentityComponentReductiveLocusOpenStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom],
    IsOpen (identityComponentReductiveLocus G)

/-- On a connected geometric fibre, membership in the identity-component locus implies
connected reductivity of the whole actual geometric fibre. -/
theorem isConnectedReductive_geometricFiber_of_mem_identityComponentReductiveLocus
    (s : S) [ConnectedSpace (geometricFiber G s).X.left]
    (hs : s ∈ identityComponentReductiveLocus G) :
    IsConnectedReductive (geometricFiber G s) :=
  hs.of_iso (IdentityComponent.connectedIso (geometricFiber G s)).symm

/-- For a connected geometric fibre, the locus condition is exactly triviality of its
ground-field unipotent radical over the algebraic closure of the residue field. -/
theorem mem_identityComponentReductiveLocus_iff_hasTrivialUnipotentRadical
    (s : S) [ConnectedSpace (geometricFiber G s).X.left] :
    s ∈ identityComponentReductiveLocus G ↔
      HasTrivialUnipotentRadical (geometricFiber G s) := by
  constructor
  · intro hs
    exact (isConnectedReductive_geometricFiber_of_mem_identityComponentReductiveLocus
      G s hs).hasTrivialUnipotentRadical
  · intro hs
    have h : IsPseudoReductive (geometricFiber G s) :=
      ⟨inferInstance, inferInstance, inferInstance, hs⟩
    exact h.isConnectedReductive_of_isAlgClosed.identityComponent

end Langlands.GroupScheme
