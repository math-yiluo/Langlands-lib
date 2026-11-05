import Langlands.Representation.Plancherel.ParabolicPointIntertwiningRegion
import Langlands.Representation.Plancherel.RationalModerateGrowthStatement
import Langlands.Representation.CompactCoefficient.GroupTransport
import Langlands.Representation.Smooth.FiniteLengthGrothendieckTransport

/-! # Moderate growth of coefficients on the literal Levi point subgroup -/

noncomputable section

universe u uV uL

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.GroupScheme.MatrixRepresentation

section Growth

variable {L : Type uL} [Group L] [TopologicalSpace L]

/-- One exponent `d` bounds every coefficient: for every vector `v` and smooth functional `ℓ`
there is `c > 0` with `‖ℓ (π(m) v)‖ ≤ c * H(m) ^ d` for all `m`. -/
def HasCommonCoefficientGrowth (π : SmoothRep.{0, uL, uV} ℂ L) (H : L → ℝ) : Prop :=
  ∃ d : ℕ, ∀ (v : π) (ℓ : SmoothDual π.representation),
    ∃ c : ℝ, 0 < c ∧ ∀ m : L, ‖ℓ.val (π.representation m v)‖ ≤ c * H m ^ d

end Growth

section Levi

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {M G P : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance leviGrowthAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance leviGrowthTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [IsAffine M.X.left] in
/-- The height of a Levi point for the restricted representation is the ambient height of
its image. -/
theorem rationalMatrixNorm_restrict_leviComposite {N : ℕ} [Nonempty (Fin N)]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (ρ₀ : MatrixRepresentation G (Fin N)) (g : rationalPoints M) :
    rationalMatrixNorm F (ρ₀.restrict (l ≫ p)) g =
      rationalMatrixNorm F ρ₀ (rationalPoints.map (l ≫ p) g) := by
  unfold rationalMatrixNorm
  rw [rationalMatrix_restrict]
  rfl

include r in
/-- **Coefficient growth on the Levi points.** The finite-length moderate-growth statement,
applied to the connected reductive Levi scheme `M` and transported along the canonical
topological isomorphism `M(F) ≃ₜ* Mpt`, gives for every admissible finite-length
representation `π` of `Mpt` one exponent `d` such that every coefficient is bounded by a
constant times `‖m‖ ^ d`, the height of `m` for a closed representation `ρ₀` of `G`. -/
theorem parabolicLevi_exists_coefficientGrowth
    (hgrowth : RationalFiniteLengthModerateGrowthStatement.{u, uV})
    [LocallyOfFiniteType M.X.hom]
    {N : ℕ} [Nonempty (Fin N)] (ρ₀ : MatrixRepresentation G (Fin N)) (hρ₀ : IsClosedSubgroup ρ₀)
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) (hadm : π.IsAdmissible)
    (hfin : π.HasFiniteLength) :
    HasCommonCoefficientGrowth π (fun m => rationalMatrixNorm F ρ₀ (m : rationalPoints G)) := by
  let e := parabolicLeviPointHomeomorph r
  have hM : IsConnectedReductive M := r.isCompatible.levi.isConnectedReductive
  have hcl : IsClosedSubgroup (ρ₀.restrict (l ≫ p)) :=
    (r.isCompatible.levi.isClosedSubgroup.comp r.isCompatible.parabolic.isClosedSubgroup).comp hρ₀
  let π' := SmoothRep.pullback e π
  have hadm' : π'.IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv π.representation e hadm
  have hfin' : π'.HasFiniteLength := SmoothRep.pullbackFunctor_preservesFiniteLength e π hfin
  obtain ⟨d, hd⟩ := hgrowth F M hM (Fin N) (ρ₀.restrict (l ≫ p)) hcl π' hadm' hfin'
  refine ⟨d, fun v ℓ => ?_⟩
  let φ : SmoothDual π'.representation :=
    ⟨ℓ.val, (isSmoothVector_dual_comp_continuousMulEquiv_iff π.representation e ℓ.val).mpr ℓ.2⟩
  obtain ⟨c, hc, hb⟩ := hd v φ
  refine ⟨c, hc, fun m => ?_⟩
  have h1 := hb (e.symm m)
  have h2 : (π'.representation (e.symm m) v) = π.representation m v := by
    change π.representation (e (e.symm m)) v = _
    rw [e.apply_symm_apply]
  have h3 : rationalMatrixNorm F (ρ₀.restrict (l ≫ p)) (e.symm m) =
      rationalMatrixNorm F ρ₀ (m : rationalPoints G) := by
    rw [rationalMatrixNorm_restrict_leviComposite]
    have h4 := parabolicLeviPointHomeomorph_apply_coe r (e.symm m)
    change ((e (e.symm m) : parabolicLeviPointSubgroup p l) : rationalPoints G) =
      rationalPoints.map (l ≫ p) (e.symm m) at h4
    rw [← h4, e.apply_symm_apply]
  rw [h2, h3] at h1
  exact h1

end Levi

end Langlands.Plancherel
