import Langlands.GroupScheme.Absolute.SolvableTorusQuotientReduction
import Langlands.GroupScheme.UnipotentClosedSubgroupProof

/-! # Unipotence of solvable groups with no rational characters -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- If all rational characters of `H` vanish, every homomorphism from `H`
to a split torus is trivial. -/
theorem IsSplitTorus.hom_eq_zero_of_characters_eq_zero
    {H D : GroupScheme (Spec (CommRingCat.of k))} (hD : IsSplitTorus D)
    (hH : ∀ χ : rationalCharacters H, χ = 0) (f : H ⟶ D) : f = 0 := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hD
  have heq : f ≫ e.hom = 0 := by
    apply hom_ext_points
    intro T x
    apply (splitTorus.pointsEquiv I T).injective
    funext i
    have hχ := hH (Additive.ofMul
      (f ≫ e.hom ≫ Pi.π (fun _ : I => (Gm (Spec (CommRingCat.of k))).toGrp) i))
    have hval := congrArg (fun χ : rationalCharacters H => characterEval χ T x) hχ
    rw [characterEval_zero] at hval
    change Gm.pointsEquiv _ T
      (x ≫ (f ≫ e.hom ≫ Pi.π (fun _ : I => (Gm (Spec (CommRingCat.of k))).toGrp) i).hom.hom) =
        1 at hval
    rw [show x ≫ (0 : H ⟶ splitTorus (Spec (CommRingCat.of k)) I).hom.hom = 1 from
      MonObj.comp_one x, map_one]
    simpa only [splitTorus.pointsEquiv_apply, Grp.comp_hom_hom, Category.assoc,
      Pi.one_apply] using hval
  apply (cancel_mono e.hom).mp
  simpa only [zero_comp] using heq

namespace TriangularTorusQuotientData

variable {H : GroupScheme (Spec (CommRingCat.of k))}
    (Q : TriangularTorusQuotientData H)

/-- The diagonal map of a chosen closed triangular embedding. -/
abbrev diagonalMap :=
  Q.embedding ≫ GeneralLinear.blockLimitHom (Fin Q.dimension) (CommRingCat.of k)
    (fun i => -(i.val : ℤ))

/-- With no rational characters, the diagonal map of the triangular embedding
is zero. -/
theorem diagonalMap_eq_zero (hH : ∀ χ : rationalCharacters H, χ = 0) :
    Q.diagonalMap = 0 := by
  have hq := Q.split_torus.hom_eq_zero_of_characters_eq_zero hH Q.quotient
  rw [diagonalMap, ← Q.factorization, hq, zero_comp]

/-- Identify the whole group with its diagonal kernel when every rational
character vanishes. The inverse is the original kernel inclusion. -/
def diagonalKernelIsoOfCharactersEqZero
    (hH : ∀ χ : rationalCharacters H, χ = 0) :
    H ≅ kernel Q.diagonalMap where
  hom := pullback.lift (𝟙 H) 0 (by
    simpa only [Category.id_comp, zero_comp] using Q.diagonalMap_eq_zero hH)
  inv := kernelι Q.diagonalMap
  hom_inv_id := pullback.lift_fst _ _ _
  inv_hom_id := by
    apply Grp.hom_ext
    apply (cancel_mono (kernelι Q.diagonalMap).hom.hom).mp
    change ((kernelι Q.diagonalMap ≫ pullback.lift (𝟙 H) 0 _) ≫
      kernelι Q.diagonalMap).hom.hom =
      ((𝟙 (kernel Q.diagonalMap)) ≫ kernelι Q.diagonalMap).hom.hom
    apply congrArg (fun f : kernel Q.diagonalMap ⟶ H => f.hom.hom)
    change (kernelι Q.diagonalMap ≫ pullback.lift (𝟙 H) 0 _) ≫
      pullback.fst _ _ = 𝟙 _ ≫ kernelι Q.diagonalMap
    rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]

/-- The canonical comparison to the diagonal kernel preserves the original
kernel inclusion. -/
@[reassoc (attr := simp)]
theorem diagonalKernelIsoOfCharactersEqZero_hom_ι
    (hH : ∀ χ : rationalCharacters H, χ = 0) :
    (Q.diagonalKernelIsoOfCharactersEqZero hH).hom ≫ kernelι Q.diagonalMap = 𝟙 H :=
  (Q.diagonalKernelIsoOfCharactersEqZero hH).hom_inv_id

include Q in
/-- The original group is unipotent when its chosen triangular embedding
has trivial diagonal, as implied by vanishing rational characters. -/
theorem isUnipotent_of_characters_eq_zero
    (hH : ∀ χ : rationalCharacters H, χ = 0) : IsUnipotent H :=
  IsUnipotent.of_iso (Q.diagonalKernelIsoOfCharactersEqZero hH)
    (Q.isUnipotent_kernel unipotentClosedSubgroup)

end TriangularTorusQuotientData

/-- A smooth connected affine solvable group over an algebraically closed
field is unipotent if every rational character is zero. -/
theorem IsSolvableGroupScheme.isUnipotent_of_characters_eq_zero
    [IsAlgClosed k] {H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (hH : IsSolvableGroupScheme H) (hχ : ∀ χ : rationalCharacters H, χ = 0) :
    IsUnipotent H :=
  hH.triangularTorusQuotient.isUnipotent_of_characters_eq_zero hχ

end Langlands.GroupScheme
