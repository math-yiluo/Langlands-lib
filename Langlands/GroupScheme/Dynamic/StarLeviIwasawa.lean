import Langlands.GroupScheme.Dynamic.HermitianLeviIwasawa
import Langlands.GroupScheme.Dynamic.NormalCocharacterWeights
import Langlands.GroupScheme.Dynamic.LeviCocharacterCombination
import Langlands.GroupScheme.Dynamic.NormalizedLimits

/-! # Levi-compatible Iwasawa from simultaneous star realization -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {𝕜 : Type u} [RCLike 𝕜]
  {G : GroupScheme (Spec (CommRingCat.of 𝕜))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Evaluating a represented cocharacter agrees with evaluating its composite
as a cocharacter of the actual general linear group scheme. -/
theorem affineMatrix_cocharacterPointHom_eq_cocharacterUnitsHom
    (ρ : MatrixRepresentation G n)
    (χ : (Gm (Spec (CommRingCat.of 𝕜))).toGrp ⟶ G) (t : 𝕜ˣ) :
    ρ.affineMatrix (CommAlgCat.of 𝕜 𝕜)
        (Dynamic.cocharacterPointHom χ (CommAlgCat.of 𝕜 𝕜) t) =
      GeneralLinear.cocharacterUnitsHom (χ ≫ ρ) 𝕜 t := by
  change GeneralLinear.affinePointsEquiv n _ _
      (((Gm.algebraPointsEquiv 𝕜).symm t ≫ χ.hom.hom) ≫ ρ.hom.hom) = _
  rw [Category.assoc, ← Grp.comp_hom_hom]
  rfl

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.Dynamic

variable {𝕜 : Type u} [RCLike 𝕜]
  {G P M : GroupScheme (Spec (CommRingCat.of 𝕜))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Star stability of a represented centralizer makes every represented
scalar-unit value of the cocharacter normal. -/
theorem isStarNormal_cocharacterUnitsHom_of_centralizer_star_stable
    (ρ : MatrixRepresentation G n)
    (χ : (Gm (Spec (CommRingCat.of 𝕜))).toGrp ⟶ G)
    (m : M ⟶ G) (hm : (centralizer χ).IsRepresentedBy m)
    (hstar : ∀ q ∈ ((ρ.restrict m).affineMatrix (CommAlgCat.of 𝕜 𝕜)).range,
      star q ∈ ((ρ.restrict m).affineMatrix (CommAlgCat.of 𝕜 𝕜)).range)
    (t : 𝕜ˣ) :
    IsStarNormal (GeneralLinear.cocharacterUnitsHom (χ ≫ ρ) 𝕜 t :
      Matrix n n 𝕜) := by
  let A := CommAlgCat.of 𝕜 𝕜
  let T := (algSpec (CommRingCat.of 𝕜)).obj (op A)
  let a : T ⟶ (Gm (Spec (CommRingCat.of 𝕜))).X :=
    (Gm.algebraPointsEquiv 𝕜).symm t
  have hx : a ≫ χ.hom.hom ∈ (centralizer χ).carrier T :=
    range_le_centralizer χ T (SubgroupFunctor.mem_range.mpr ⟨a, rfl⟩)
  rw [← hm.2] at hx
  obtain ⟨x, hx⟩ := SubgroupFunctor.mem_range.mp hx
  obtain ⟨y, hy⟩ := hstar _ ⟨x, rfl⟩
  have hyc : y ≫ m.hom.hom ∈ (centralizer χ).carrier T := by
    rw [← hm.2]
    exact SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩
  have hcomm := (commute_cocharacter_of_mem_centralizer χ hyc a).map
    (ρ.affineMatrix A)
  have hxρ : (ρ.restrict m).affineMatrix A x =
      GeneralLinear.cocharacterUnitsHom (χ ≫ ρ) 𝕜 t := by
    rw [MatrixRepresentation.affineMatrix_restrict, hx]
    exact ρ.affineMatrix_cocharacterPointHom_eq_cocharacterUnitsHom χ t
  rw [← MatrixRepresentation.affineMatrix_restrict, hy, hxρ] at hcomm
  change Commute (star (GeneralLinear.cocharacterUnitsHom (χ ≫ ρ) 𝕜 t))
    (ρ.affineMatrix A (cocharacterPointHom χ A t)) at hcomm
  rw [MatrixRepresentation.affineMatrix_cocharacterPointHom_eq_cocharacterUnitsHom] at hcomm
  exact ⟨by
    simpa only [Units.coeHom_apply, Units.coe_star] using hcomm.map (Units.coeHom _)⟩

/-- Normality at the positive scalar two follows from simultaneous
star stability on the actual centralizer point image. -/
theorem hasNormalPositivePoint_of_centralizer_star_stable
    (ρ : MatrixRepresentation G n)
    (χ : (Gm (Spec (CommRingCat.of 𝕜))).toGrp ⟶ G)
    (m : M ⟶ G) (hm : (centralizer χ).IsRepresentedBy m)
    (hstar : ∀ q ∈ ((ρ.restrict m).affineMatrix (CommAlgCat.of 𝕜 𝕜)).range,
      star q ∈ ((ρ.restrict m).affineMatrix (CommAlgCat.of 𝕜 𝕜)).range) :
    GeneralLinear.HasNormalPositivePoint (χ ≫ ρ) :=
  isStarNormal_cocharacterUnitsHom_of_centralizer_star_stable ρ χ m hm hstar
    (GeneralLinear.positiveTwoUnit 𝕜)

/-- Simultaneous closed star realization of the ambient group and its specified
dynamic Levi, with a common cocharacter representing the supplied pair. -/
def HasStarLeviRealization (p : P ⟶ G) (m : M ⟶ G) : Prop :=
  ∃ (d : ℕ) (ρ : MatrixRepresentation G (Fin d))
    (χ : (Gm (Spec (CommRingCat.of 𝕜))).toGrp ⟶ G),
    IsClosedSubgroup ρ ∧
      (parabolic χ).IsRepresentedBy p ∧ (centralizer χ).IsRepresentedBy m ∧
      (∀ q ∈ (ρ.affineMatrix (CommAlgCat.of 𝕜 𝕜)).range,
        star q ∈ (ρ.affineMatrix (CommAlgCat.of 𝕜 𝕜)).range) ∧
      ∀ q ∈ ((ρ.restrict m).affineMatrix (CommAlgCat.of 𝕜 𝕜)).range,
        star q ∈ ((ρ.restrict m).affineMatrix (CommAlgCat.of 𝕜 𝕜)).range

/-- Simultaneous star realization supplies Hermitian cocharacter weights. -/
theorem HasStarLeviRealization.hasHermitianStarLeviRealization
    {p : P ⟶ G} {m : M ⟶ G} (h : HasStarLeviRealization p m) :
    HasHermitianStarLeviRealization p m := by
  obtain ⟨d, ρ, χ, hc, hp, hm, hs, hms⟩ := h
  exact ⟨d, ρ, χ, hc,
    (hasNormalPositivePoint_of_centralizer_star_stable ρ χ m hm hms).hasHermitianWeightProjectors,
    hp, hm, hs⟩

/-- Simultaneous star realization supplies the compatible diagonal data. -/
theorem HasStarLeviRealization.hasDiagonalStarLeviRealization
    {p : P ⟶ G} {m : M ⟶ G} (h : HasStarLeviRealization p m) :
    HasDiagonalStarLeviRealization p m :=
  h.hasHermitianStarLeviRealization.hasDiagonalStarLeviRealization

local instance starLeviIwasawaPointTopology (H : GroupScheme (Spec (CommRingCat.of 𝕜))) :
    TopologicalSpace (H.affinePoints (CommAlgCat.of 𝕜 𝕜)) :=
  H.affinePointsTopologicalSpace (CommAlgCat.of 𝕜 𝕜)

/-- Simultaneous star realization constructs a compact with all four actual
Levi-compatible Iwasawa conclusions. -/
theorem HasStarLeviRealization.hasLeviCompatibleDecomposition
    [IsAffine G.X.left] {p : P ⟶ G} {m : M ⟶ G}
    (h : HasStarLeviRealization p m) :
    CompactIwasawa.HasLeviCompatibleDecomposition
      (P.affinePointsTarget p (CommAlgCat.of 𝕜 𝕜))
      (M.affinePointsTarget m (CommAlgCat.of 𝕜 𝕜)) :=
  h.hasDiagonalStarLeviRealization.hasLeviCompatibleDecomposition

end Langlands.GroupScheme.Dynamic
