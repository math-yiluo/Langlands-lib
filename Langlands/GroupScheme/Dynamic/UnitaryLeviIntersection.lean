import Langlands.GroupScheme.Dynamic.ClosedSubgroup
import Langlands.GroupScheme.Dynamic.GeneralLinearOrbit
import Langlands.GroupScheme.MatrixRepresentation
import Langlands.GroupScheme.AffinePoints
import Langlands.Group.MatrixPolarCompact

/-! # Unitary intersections for a compatible diagonal dynamic Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme.GeneralLinear

variable {𝕜 : Type u} [RCLike 𝕜]
  {n : Type} [Fintype n] [DecidableEq n]

/-- A unitary matrix in a weight-block parabolic is weight-block diagonal. -/
theorem mem_blockLeviSubgroup_of_unitary
    (e : n → ℤ) {g : GL n 𝕜}
    (hp : g ∈ blockParabolicSubgroup 𝕜 e)
    (hu : (g : Matrix n n 𝕜) ∈ Matrix.unitaryGroup n 𝕜) :
    g ∈ blockLeviSubgroup 𝕜 e := by
  have hinv : (g⁻¹ : GL n 𝕜).val = star (g : Matrix n n 𝕜) := by
    calc
      (g⁻¹ : GL n 𝕜).val =
          (g⁻¹ : GL n 𝕜).val * ((g : Matrix n n 𝕜) * star (g : Matrix n n 𝕜)) := by
        rw [(Matrix.mem_unitaryGroup_iff.mp hu), mul_one]
      _ = star (g : Matrix n n 𝕜) := by
        rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact (mem_blockParabolicSubgroup 𝕜 e).mp hp i j h
  · have hz := (mem_blockParabolicSubgroup 𝕜 e).mp
      ((blockParabolicSubgroup 𝕜 e).inv_mem hp) j i h
    rw [hinv] at hz
    simpa only [Matrix.star_apply, star_eq_zero] using hz

/-- Taking conjugate transpose preserves the weight-block diagonal condition. -/
theorem blockLevi_star_condition (e : n → ℤ) {g : GL n 𝕜}
    (hg : g ∈ blockLeviSubgroup 𝕜 e) :
    ∀ i j, e i ≠ e j → star (g : Matrix n n 𝕜) i j = 0 := by
  intro i j hij
  simp only [Matrix.star_apply, hg j i hij.symm, star_zero]

end Langlands.GroupScheme.GeneralLinear

namespace Langlands.GroupScheme.Dynamic

variable {k : Type u} [Field k]
  {G P M : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- A fixed closed matrix representation realizes the specified parabolic and Levi
as the dynamic parabolic and centralizer of a cocharacter diagonal in that same
representation. This is compatibility data, whose existence is not asserted here. -/
def IsDiagonalLeviPair (ρ : MatrixRepresentation G n)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (e : n → ℤ)
    (p : P ⟶ G) (m : M ⟶ G) : Prop :=
  IsClosedSubgroup ρ ∧
    χ ≫ ρ = GeneralLinear.diagonalCocharacter n (CommRingCat.of k) e ∧
    (parabolic χ).IsRepresentedBy p ∧ (centralizer χ).IsRepresentedBy m

variable (ρ : MatrixRepresentation G n)
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (e : n → ℤ)

/-- The parabolic membership test on actual affine points uses coefficients in the
test algebra itself. -/
theorem mem_parabolic_iff_affineMatrix
    (hc : IsClosedSubgroup ρ)
    (hχ : χ ≫ ρ = GeneralLinear.diagonalCocharacter n (CommRingCat.of k) e)
    (A : CommAlgCat.{u} (CommRingCat.of k)) (x : G.affinePoints A) :
    x ∈ (parabolic χ).carrier ((algSpec (CommRingCat.of k)).obj (op A)) ↔
      ρ.affineMatrix A x ∈ GeneralLinear.blockParabolicSubgroup A e := by
  rw [parabolic_eq_comap_of_isClosedSubgroup χ ρ hc, SubgroupFunctor.mem_comap,
    hχ, GeneralLinear.parabolic_diagonalCocharacter]
  change ρ.pointMatrix _ x ∈ GeneralLinear.blockParabolicSubgroup _ e ↔ _
  simp only [GeneralLinear.mem_blockParabolicSubgroup]
  rw [ρ.pointMatrix_eq_affineMatrix]
  constructor
  · intro h i j hij
    have hz := h i j hij
    change (Corepresented.affineSectionsIso (R := CommRingCat.of k) A).inv.hom
      (ρ.affineMatrix A x i j) = 0 at hz
    exact (ConcreteCategory.bijective_of_isIso
      (Corepresented.affineSectionsIso (R := CommRingCat.of k) A).inv).1
      (hz.trans (map_zero _).symm)
  · intro h i j hij
    change (Corepresented.affineSectionsIso (R := CommRingCat.of k) A).inv.hom
      (ρ.affineMatrix A x i j) = 0
    rw [h i j hij, map_zero]

/-- The analogous centralizer membership test on actual affine points. -/
theorem mem_centralizer_iff_affineMatrix
    (hc : IsClosedSubgroup ρ)
    (hχ : χ ≫ ρ = GeneralLinear.diagonalCocharacter n (CommRingCat.of k) e)
    (A : CommAlgCat.{u} (CommRingCat.of k)) (x : G.affinePoints A) :
    x ∈ (centralizer χ).carrier ((algSpec (CommRingCat.of k)).obj (op A)) ↔
      ρ.affineMatrix A x ∈ GeneralLinear.blockLeviSubgroup A e := by
  rw [centralizer_eq_comap_of_isClosedSubgroup χ ρ hc, SubgroupFunctor.mem_comap,
    hχ, GeneralLinear.centralizer_diagonalCocharacter]
  change ρ.pointMatrix _ x ∈ GeneralLinear.blockLeviSubgroup _ e ↔ _
  rw [ρ.pointMatrix_eq_affineMatrix]
  constructor
  · intro h i j hij
    have hz := h i j hij
    change (Corepresented.affineSectionsIso (R := CommRingCat.of k) A).inv.hom
      (ρ.affineMatrix A x i j) = 0 at hz
    exact (ConcreteCategory.bijective_of_isIso
      (Corepresented.affineSectionsIso (R := CommRingCat.of k) A).inv).1
      (hz.trans (map_zero _).symm)
  · intro h i j hij
    change (Corepresented.affineSectionsIso (R := CommRingCat.of k) A).inv.hom
      (ρ.affineMatrix A x i j) = 0
    rw [h i j hij, map_zero]

variable {ρ χ e}

/-- The specified parabolic has exactly the block-parabolic matrix membership
test on actual affine points. -/
theorem IsDiagonalLeviPair.mem_parabolic_range_iff
    {p : P ⟶ G} {m : M ⟶ G} (h : IsDiagonalLeviPair ρ χ e p m)
    (A : CommAlgCat.{u} (CommRingCat.of k)) (x : G.affinePoints A) :
    x ∈ (P.affinePointsTarget p A).range ↔
      ρ.affineMatrix A x ∈ GeneralLinear.blockParabolicSubgroup A e := by
  change x ∈ (SubgroupFunctor.range p).carrier _ ↔ _
  rw [h.2.2.1.2]
  exact mem_parabolic_iff_affineMatrix ρ χ e h.1 h.2.1 A x

/-- The specified Levi has exactly the block-diagonal matrix membership
test on actual affine points. -/
theorem IsDiagonalLeviPair.mem_levi_range_iff
    {p : P ⟶ G} {m : M ⟶ G} (h : IsDiagonalLeviPair ρ χ e p m)
    (A : CommAlgCat.{u} (CommRingCat.of k)) (x : G.affinePoints A) :
    x ∈ (M.affinePointsTarget m A).range ↔
      ρ.affineMatrix A x ∈ GeneralLinear.blockLeviSubgroup A e := by
  change x ∈ (SubgroupFunctor.range m).carrier _ ↔ _
  rw [h.2.2.2.2]
  exact mem_centralizer_iff_affineMatrix ρ χ e h.1 h.2.1 A x

section RCLike

variable {𝕜 : Type u} [RCLike 𝕜]
  {G P M : GroupScheme (Spec (CommRingCat.of 𝕜))} {d : ℕ}
  {ρ : MatrixRepresentation G (Fin d)}
  {χ : (Gm (Spec (CommRingCat.of 𝕜))).toGrp ⟶ G}
  {e : Fin d → ℤ} {p : P ⟶ G} {m : M ⟶ G}

open Langlands.Group.MatrixPolarCompact

/-- The unitary inverse image on the restricted representation is exactly the
inverse image on the actual specified-Levi point carrier. -/
theorem unitarySubgroup_restrict :
    unitarySubgroup ((ρ.restrict m).affineMatrix
        (CommAlgCat.of (CommRingCat.of 𝕜) 𝕜)) =
      (unitarySubgroup (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of 𝕜) 𝕜))).comap
        (M.affinePointsTarget m (CommAlgCat.of (CommRingCat.of 𝕜) 𝕜)) := by
  rfl

/-- For a compatible diagonal pair, the actual parabolic and specified Levi
have the same intersection with the inverse image of the standard unitary group. -/
theorem IsDiagonalLeviPair.range_inf_unitarySubgroup
    (h : IsDiagonalLeviPair ρ χ e p m) :
    (P.affinePointsTarget p (CommAlgCat.of (CommRingCat.of 𝕜) 𝕜)).range ⊓
        unitarySubgroup (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of 𝕜) 𝕜)) =
      (M.affinePointsTarget m (CommAlgCat.of (CommRingCat.of 𝕜) 𝕜)).range ⊓
        unitarySubgroup (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of 𝕜) 𝕜)) := by
  ext x
  constructor
  · rintro ⟨hp, hk⟩
    refine ⟨(h.mem_levi_range_iff _ x).mpr ?_, hk⟩
    exact GeneralLinear.mem_blockLeviSubgroup_of_unitary e
      ((h.mem_parabolic_range_iff _ x).mp hp)
      ((mem_unitarySubgroup _ x).mp hk)
  · rintro ⟨hm, hk⟩
    refine ⟨(h.mem_parabolic_range_iff _ x).mpr ?_, hk⟩
    apply (GeneralLinear.mem_blockParabolicSubgroup 𝕜 e).mpr
    intro i j hij
    exact ((h.mem_levi_range_iff _ x).mp hm) i j hij.ne

/-- Ambient conjugate-transpose stability passes to the actual representation
restricted to the specified compatible Levi. -/
theorem IsDiagonalLeviPair.restrict_star_stable
    (h : IsDiagonalLeviPair ρ χ e p m)
    (hstar : ∀ x : G.affinePoints (CommAlgCat.of (CommRingCat.of 𝕜) 𝕜),
      ∃ y : G.affinePoints (CommAlgCat.of (CommRingCat.of 𝕜) 𝕜),
        (ρ.affineMatrix _ y : Matrix (Fin d) (Fin d) 𝕜) =
          star (ρ.affineMatrix _ x : Matrix (Fin d) (Fin d) 𝕜)) :
    ∀ x : M.affinePoints (CommAlgCat.of (CommRingCat.of 𝕜) 𝕜),
      ∃ y : M.affinePoints (CommAlgCat.of (CommRingCat.of 𝕜) 𝕜),
        ((ρ.restrict m).affineMatrix _ y : Matrix (Fin d) (Fin d) 𝕜) =
          star ((ρ.restrict m).affineMatrix _ x : Matrix (Fin d) (Fin d) 𝕜) := by
  intro x
  obtain ⟨g, hg⟩ := hstar (M.affinePointsTarget m _ x)
  have hx : ρ.affineMatrix _ (M.affinePointsTarget m _ x) ∈
      GeneralLinear.blockLeviSubgroup 𝕜 e :=
    (h.mem_levi_range_iff _ _).mp ⟨x, rfl⟩
  have hgm : g ∈ (M.affinePointsTarget m _).range := by
    apply (h.mem_levi_range_iff _ g).mpr
    intro i j hij
    rw [hg]
    exact GeneralLinear.blockLevi_star_condition e hx i j hij
  obtain ⟨y, hy⟩ := hgm
  refine ⟨y, ?_⟩
  change (ρ.affineMatrix _ (M.affinePointsTarget m _ y) :
      Matrix (Fin d) (Fin d) 𝕜) =
    star (ρ.affineMatrix _ (M.affinePointsTarget m _ x) :
      Matrix (Fin d) (Fin d) 𝕜)
  rw [hy]
  exact hg

end RCLike

end Langlands.GroupScheme.Dynamic
