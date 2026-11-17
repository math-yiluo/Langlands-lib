import Langlands.GroupScheme.Reductive.GenericFiberGeometry
import Langlands.GroupScheme.Reductive.AlgebraicallyClosedPseudoReductive
import Langlands.GroupScheme.RelativeIdentityComponent.QuasiCompactOfFibres

/-! # Geometry from connected reductive residue fibres -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} (G : GroupScheme S)

/-- Every actual residue-field fibre of the group scheme is connected reductive. -/
def HasConnectedReductiveResidueFibers : Prop :=
  ∀ s : S, IsConnectedReductive (RelativeIdentityComponent.residueFiber G s)

/-- Connected reductivity of every actual residue fibre is preserved by
arbitrary change of the base scheme. -/
theorem connectedReductive_residueFibers_baseChange
    (hG : HasConnectedReductiveResidueFibers G)
    {S' : Scheme.{u}} (b : S' ⟶ S) (s' : S') :
    IsConnectedReductive
      (RelativeIdentityComponent.residueFiber ((baseChange b).obj G) s') := by
  have h := fieldReductive_of_residueReductive G Set.univ
    (fun s _ => hG s) (S'.fromSpecResidueField s' ≫ b) (Set.mem_univ _)
  exact h.of_iso (baseChangeCompIso b (S'.fromSpecResidueField s') G).symm

/-- Connected reductive residue fibres imply quasi-compactness of the structure
morphism, without any quasi-separatedness assumption on the base. -/
theorem quasiCompact_of_connectedReductive_residueFibers
    (hG : HasConnectedReductiveResidueFibers G) :
    QuasiCompact G.X.hom := by
  refine IsZariskiLocalAtTarget.of_openCover S.affineOpenCover.openCover fun a => ?_
  let H := (baseChange (S.affineOpenCover.f a)).obj G
  have hH : ∀ s, IsConnectedReductive (RelativeIdentityComponent.residueFiber H s) :=
    connectedReductive_residueFibers_baseChange G hG (S.affineOpenCover.f a)
  exact RelativeIdentityComponent.quasiCompact_of_residueFibers H
    (fun s => (hH s).smooth)
    (fun s => (hH s).connectedSpace)
    (fun s => by
      have : IsAffineHom (RelativeIdentityComponent.residueFiber H s).X.hom :=
        (hH s).isAffineHom
      exact QuasiCompact.compactSpace_of_compactSpace
        (RelativeIdentityComponent.residueFiber H s).X.hom)

/-- For a smooth affine group scheme, connected reductivity of the residue
fibres supplies the geometric-fibre clause of reductivity. -/
theorem isReductive_of_isAffineHom_of_connectedReductive_residueFibers
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hG : HasConnectedReductiveResidueFibers G) :
    IsReductive G := by
  refine ⟨inferInstance, inferInstance, fun s => ?_⟩
  exact (fieldReductive_of_residueReductive G Set.univ
    (fun t _ => hG t) (geometricPoint S s) (Set.mem_univ _)).isPseudoReductive

end Langlands.GroupScheme
