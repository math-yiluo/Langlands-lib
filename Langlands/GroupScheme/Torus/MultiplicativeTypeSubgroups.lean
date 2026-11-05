import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.GroupScheme.Torus.ClosedSubgroupPresentationProof
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Closed subgroups of groups of multiplicative type -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- Multiplicative type is invariant under isomorphism of the actual groups. -/
theorem IsMultiplicativeType.of_iso (e : H ≅ G)
    (hG : IsMultiplicativeType G) : IsMultiplicativeType H := by
  obtain ⟨K, hK, aK, Λ, hΛ, hfg, ⟨d⟩⟩ := hG
  exact ⟨K, hK, aK, Λ, hΛ, hfg,
    ⟨(GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapIso e ≪≫ d⟩⟩

/-- Closed subgroups retain multiplicative type, including character torsion. -/
theorem IsMultiplicativeType.of_isClosedSubgroup
    (hG : IsMultiplicativeType G) (i : H ⟶ G) (hi : IsClosedSubgroup i) :
    IsMultiplicativeType H := by
  obtain ⟨K, hK, aK, Λ, hΛ, hfg, ⟨e⟩⟩ := hG
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  obtain ⟨Λ', hΛ', hfg', ⟨d⟩⟩ := Diagonalizable.closedSubgroupPresentation K Λ
    ((GroupScheme.baseChange b).obj H)
    ((GroupScheme.baseChange b).map i ≫ e.hom) ((hi.baseChange b).comp_iso e)
  exact ⟨K, hK, aK, Λ', hΛ', hfg', ⟨d⟩⟩

/-- A closed subgroup of an already split torus is diagonalizable over the
original field, with a finitely generated full character group. -/
theorem exists_diagonalizableIso_of_isClosedSubgroup_splitTorus
    (hG : IsSplitTorus G) (i : H ⟶ G) (hi : IsClosedSubgroup i) :
    ∃ (Λ : Type u) (_ : AddCommGroup Λ) (_ : AddGroup.FG Λ),
      Nonempty (H ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp) := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hG
  let : Fintype I := Fintype.ofFinite I
  let d := e ≪≫ (Diagonalizable.splitIso (CommRingCat.of k)
    (AddEquiv.refl (I → ℤ))).symm
  exact Diagonalizable.closedSubgroupPresentation k (I → ℤ) H
    (i ≫ d.hom) (hi.comp_iso d)

end Langlands.GroupScheme
