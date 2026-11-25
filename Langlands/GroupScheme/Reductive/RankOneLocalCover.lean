import Langlands.GroupScheme.Reductive.RankOneLocalAssembly
import Langlands.GroupScheme.Reductive.RankOneCentralCoverStatement

/-! # Conditional assembly of the rank-one central cover

The target `RankOneCentralCoverStatement` from two inputs stated as propositions:
the root-cell-to-cover step (`rankOneCentralCover_of_rootCell`) and the
local line crux. See the paired Markdown.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RankOneLocalCover

/-- The root-cell-to-cover step: a root cell for `(α, αv)` with `⟨α, αv⟩ = 2` in a connected
reductive group gives the central cover of the target. -/
def RootCellCoverInput : Prop :=
  ∀ {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (_hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (_hT : IsSplitTorus T.toGrp)
    {i : T.toGrp ⟶ G} {α : characterLattice T} {αv : cocharacterLattice T}
    {xp xm : RootCell.Ga k ⟶ G} (_D : RootCell.IsRootCell i α αv xp xm)
    (_h2 : latticePairing T α αv = 2),
    ∃ (C : CommGroupScheme (Spec (CommRingCat.of k))), IsSplitTorus C.toGrp ∧
      ∃ (f : SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k) ⊗ C.toGrp ⟶ G)
        (t : CommGroupScheme.prod
          (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin 1))) C ⟶ T),
        IsCentralIsogeny f ∧ IsIsogeny (CommGroupScheme.groupHom t) ∧
        (SpecialLinear.FinSucc.diagonalTorus 1 (CommRingCat.of k) ⊗ₘ 𝟙 C.toGrp) ≫ f =
          CommGroupScheme.groupHom t ≫ i

/-- The local line crux: in semisimple rank one, each root `α` is positive on a cocharacter
`ν` for which `α` (`-α`) is the only root positive (negative) on `ν`, and the root spaces of
`±α` are lines. -/
def LocalLineCrux : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → ∀ i : T.toGrp ⟶ G, IsMaximalTorus i →
      haveI := hG.isAffineHom
      (∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β]) →
      ∀ α ∈ roots i, ∃ ν : cocharacterLattice T, 0 < latticePairing T α ν ∧
        (∀ β ∈ roots i, 0 < latticePairing T β ν → β = α) ∧
        (∀ β ∈ roots i, latticePairing T β ν < 0 → β = -α) ∧
        Nonempty (k ≃ₗ[k] weightSpace i α) ∧ Nonempty (k ≃ₗ[k] weightSpace i (-α))

/-- **Conditional assembly.** The two inputs give the rank-one central cover. -/
theorem rankOneCentralCover_of_inputs (hS4 : RootCellCoverInput.{u})
    (hcrux : LocalLineCrux.{u}) : RankOneCentralCoverStatement.{u} := by
  intro k _ _ G hG T hT i hi hne hdep
  have : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨α, hα⟩ := hne
  obtain ⟨ν, hν, hpos, hneg, hline, hline'⟩ := hcrux k G hG T hT i hi hdep α hα
  obtain ⟨h, xp, xm, pair, hrc⟩ := RankOneLocalAssembly.exists_isRootCell hG hT i hi hdep hα
    hν hpos hneg hline hline'
  exact hS4 hG hT hrc pair

end RankOneLocalCover

end Langlands.GroupScheme
