import Langlands.GroupScheme.Reductive.PositiveRootTangentDimension
import Langlands.GroupScheme.Lie.SubgroupCellDimension
import Langlands.GroupScheme.Dynamic.OppositeCellPoints

/-! # Positive roots and the dimension of an actual opposite dynamic quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Dynamic

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] in
/-- The canonical map from the actual opposite dynamic cell to a supplied
quotient. Its open immersion property follows from the exact fpqc fiber law. -/
def oppositeQuotientCellMorphism [IsAffine G.X.left]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q) :
    (Affine.unipotentScheme (OppositeCell.opposite χ)).X ⟶ Q :=
  OppositeCell.cellMap χ ≫ q

/-- The intrinsic tangent dimension of the opposite dynamic unipotent
subgroup is bounded by the dimension of every exact fpqc quotient by `P(χ)`. -/
theorem finrank_tangentSubmodule_opposite_unipotent_cast_le
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
    (hf : ∀ (Y : Over (Spec (CommRingCat.of k))) (g h : Y ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (parabolic χ).carrier Y)
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left] :
    (Module.finrank k
      (RelativeRoot.tangentSubmodule (unipotent (OppositeCell.opposite χ))) :
        WithBot ℕ∞) ≤ topologicalKrullDim Q.left := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let U := Affine.unipotentScheme (OppositeCell.opposite χ)
  let j : U ⟶ G := Affine.unipotentHom (OppositeCell.opposite χ)
  have hj : (unipotent (OppositeCell.opposite χ)).IsRepresentedBy j :=
    Affine.isRepresentedBy_unipotentHom _
  have : IsClosedImmersion j.hom.hom.left := Affine.isClosedSubgroup_unipotentHom _
  have : IsAffineHom U.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have : Smooth U.X.hom := (dynamicSmooth k G _ U j).2.2 hj
  have hcell : IsOpenImmersion (oppositeQuotientCellMorphism χ q).left :=
    OppositeCell.isOpenImmersion_cell χ q hf
  have : IsOpenImmersion (j.hom.hom ≫ q).left := hcell
  exact RelativeRoot.finrank_tangentSubmodule_cast_le_of_openImmersion
    (unipotent (OppositeCell.opposite χ)) j hj (j.hom.hom ≫ q)

end Dynamic

namespace RelativeRoot

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] in
private theorem opposite_neg_cocharacter (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) :
    Dynamic.OppositeCell.opposite (CommGroupScheme.groupHom (-ν) ≫ i) =
      CommGroupScheme.groupHom ν ≫ i := by
  change CommGroupScheme.groupHom (Gm.powerHom _ (-1)) ≫
    (CommGroupScheme.groupHom (-ν) ≫ i) = _
  rw [← Category.assoc]
  change CommGroupScheme.groupHom (Gm.powerHom _ (-1) ≫ (-ν)) ≫ i = _
  simp only [Gm.powerHom_apply, neg_one_zsmul, Preadditive.neg_comp,
    Category.id_comp, neg_neg]

/-- The positive dynamic tangent submodule is bounded by the dimension of
an exact fpqc quotient by the dynamic parabolic of the negative cocharacter. -/
theorem finrank_tangentSubmodule_unipotent_cast_le_oppositeQuotient
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
    (hf : ∀ (Y : Over (Spec (CommRingCat.of k))) (g h : Y ⟶ G.X),
      g ≫ q = h ≫ q ↔
        g⁻¹ * h ∈ (Dynamic.parabolic (CommGroupScheme.groupHom (-ν) ≫ i)).carrier Y)
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left] :
    (Module.finrank k
      (tangentSubmodule (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i))) :
        WithBot ℕ∞) ≤ topologicalKrullDim Q.left := by
  have h := Dynamic.finrank_tangentSubmodule_opposite_unipotent_cast_le
    (CommGroupScheme.groupHom (-ν) ≫ i) q hf
  rw [opposite_neg_cocharacter i ν] at h
  exact h

/-- Two distinct positive actual roots force every exact opposite dynamic
quotient to have topological Krull dimension at least two. -/
theorem two_le_dimension_oppositeQuotient_of_distinct_positive_roots
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
    (hf : ∀ (Y : Over (Spec (CommRingCat.of k))) (g h : Y ⟶ G.X),
      g ≫ q = h ≫ q ↔
        g⁻¹ * h ∈ (Dynamic.parabolic (CommGroupScheme.groupHom (-ν) ≫ i)).carrier Y)
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    {α β : characterLattice T} (hα : α ∈ roots i) (hβ : β ∈ roots i)
    (hαpos : 0 < latticePairing T α ν) (hβpos : 0 < latticePairing T β ν)
    (hne : α ≠ β) :
    (2 : WithBot ℕ∞) ≤ topologicalKrullDim Q.left := by
  have htwo := two_le_finrank_tangentSubmodule_unipotent_of_distinct_positive_roots
    hT i ν hα hβ hαpos hβpos hne
  have hcast : (2 : WithBot ℕ∞) ≤
      (Module.finrank k
        (tangentSubmodule (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i))) :
          WithBot ℕ∞) := by exact_mod_cast htwo
  exact hcast.trans (finrank_tangentSubmodule_unipotent_cast_le_oppositeQuotient i ν q hf)

/-- A dimension-at-most-one exact opposite dynamic quotient implies
uniqueness of a positive actual root. The dimension bound remains an input. -/
theorem positive_roots_eq_of_oppositeQuotient_dimension_le_one
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
    (hf : ∀ (Y : Over (Spec (CommRingCat.of k))) (g h : Y ⟶ G.X),
      g ≫ q = h ≫ q ↔
        g⁻¹ * h ∈ (Dynamic.parabolic (CommGroupScheme.groupHom (-ν) ≫ i)).carrier Y)
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (hQ : topologicalKrullDim Q.left ≤ 1)
    {α β : characterLattice T} (hα : α ∈ roots i) (hβ : β ∈ roots i)
    (hαpos : 0 < latticePairing T α ν) (hβpos : 0 < latticePairing T β ν) :
    α = β := by
  apply positive_roots_eq_of_tangentSubmodule_unipotent_finrank_le_one
    hT i ν _ hα hβ hαpos hβpos
  have h := (finrank_tangentSubmodule_unipotent_cast_le_oppositeQuotient i ν q hf).trans hQ
  exact_mod_cast h

end RelativeRoot

end Langlands.GroupScheme
