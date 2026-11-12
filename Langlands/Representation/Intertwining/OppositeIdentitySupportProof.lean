import Langlands.Representation.Intertwining.OppositeIdentitySupportStatement
import Langlands.Representation.Intertwining.PQIdentitySupportProof
import Langlands.Representation.Exponents.LeviJacquetContragredientStructure
import Langlands.GroupScheme.Dynamic.OppositeParabolicUniquenessProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof
import Langlands.Representation.Plancherel.RationalOpenCellConullProof
import Langlands.GroupScheme.Rational.ParabolicLeviRealization

/-! # The identity support image for opposite rational parabolics -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- For opposite represented rational parabolics `P` and `Q` with the same actual Levi, the
identity double coset `P(F) Q(F)` is dense in `G(F)`. -/
theorem dense_identityParabolicDoubleCoset_of_opposite
    {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    {G P M Q U : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {p : P ⟶ G} {l : M ⟶ P} (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    {q : Q ⟶ G} {lQ : M ⟶ Q} {rQ : U ⟶ Q}
    (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
    (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
    (hlev : lQ ≫ q = l ≫ p)
    (hpts : pointImage p ⊓ pointImage q = pointImage (l ≫ p)) :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    Dense (DoubleCoset.quotToDoubleCoset (pointImage p) (pointImage q)
      (identityParabolicDoubleCoset p q)) := by
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  have := hG.connectedSpace
  obtain ⟨-, hint⟩ := Plancherel.RationalCellConull.noetherian_and_integral k G
  have := hint
  obtain ⟨χ, hPχ, hMχ⟩ :=
    DynamicLeviConjugacy.exists_cocharacter_parabolic_levi parabolicDynamic
      dynamicGeometricUnipotentRadical hG hp hl
  have hU := pointImage_opposite_radical_eq_dynamic parabolicDynamic
    oppositeDynamicParabolicUniqueness hG χ l hPχ hMχ hq hlQ hrQ hlev hpts
  obtain ⟨Z, hZc, hZne, hZeq⟩ := Plancherel.rationalDynamicOpenCellBoundary k G χ
  have hempty := Plancherel.RationalCellConull.interior_evaluation_preimage_eq_empty k G.X
    ⟨Z, hZc⟩ (fun h => hZne
      (congrArg (fun W : TopologicalSpace.Closeds G.X.left => (W : Set G.X.left)) h))
  change interior ((fun x : rationalPoints G => x.left (IsLocalRing.closedPoint k)) ⁻¹' Z) = ∅
    at hempty
  rw [hZeq, interior_eq_empty_iff_dense_compl, compl_compl] at hempty
  refine hempty.mono ?_
  rintro _ ⟨⟨a, v⟩, rfl⟩
  have ha : (a : rationalPoints G) ∈ pointImage p := by
    rw [pointImage_eq_range_carrier, hPχ]
    exact a.2
  have hv : (v : rationalPoints G) ∈ pointImage (rQ ≫ q) := by
    rw [hU]
    exact v.2
  rw [DoubleCoset.mem_quotToDoubleCoset_iff]
  exact DoubleCoset.eq.mpr ⟨(a : rationalPoints G)⁻¹, (pointImage p).inv_mem ha,
    (v : rationalPoints G), pointImage_comp_le q rQ hv,
    by simp [HarishChandraSchwartz.openCellMap]⟩

/-- The identity boundary-support image in `r_Q i_P(σ)` is equivariantly isomorphic to `σ`,
for opposite represented rational parabolics `P` and `Q` with the same actual Levi. -/
theorem oppositeIdentitySupport : OppositeIdentitySupportStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N Q U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hlev hpts σ
  let := leviPointTopology l hl
  have hcl : closure (DoubleCoset.quotToDoubleCoset (pointImage p) (pointImage q)
      (identityParabolicDoubleCoset p q)) = Set.univ :=
    (dense_identityParabolicDoubleCoset_of_opposite hG hp hl hq hlQ hrQ hlev hpts).closure_eq
  have hS : ((closureSupportImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
      (identityParabolicDoubleCoset p q)).obj σ).toSubmodule = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨y, hy, rfl⟩
    have h := (Geometric.mem_rawSmoothVanishingSubfunctor_iff (R := ℂ) (pointImage p)
      (pointImage q) _ (Geometric.closure_doubleCoset_mul_mem _ _ (identityParabolicDoubleCoset p q))
      ((leviInducingFunctor p l r hp hr hl hmul).obj σ) y).mp hy
    have hy0 : y = 0 :=
      Subtype.ext (Subtype.ext (funext fun g => h g (hcl ▸ Set.mem_univ g)))
    rw [hy0]
    exact (Jacquet.Localization.mk _ _ 1).map_zero
  have hL : ((closureSupportImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
      (identityParabolicDoubleCoset p q)).lowerInUpper
      (boundarySupportImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
        (identityParabolicDoubleCoset p q)) σ).toSubmodule = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx' := Submodule.mem_comap.mp hx
    rw [hS] at hx'
    exact Subtype.ext ((Submodule.mem_bot ℂ).mp hx')
  obtain ⟨-, e, -⟩ := pqSupportGraded k G hG P M N Q U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ
    hmulQ hlev.symm
  let e0 : ((boundarySupportImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
        (identityParabolicDoubleCoset p q)).obj σ).toRepresentation.Equiv
      ((closureSupportImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
        (identityParabolicDoubleCoset p q)).quotientObj
        (boundarySupportImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
          (identityParabolicDoubleCoset p q)) σ).ρ :=
    Representation.Equiv.mk (Submodule.quotEquivOfEqBot _ hL).symm
      (fun _ => LinearMap.ext fun _ => rfl)
  exact ⟨e0.trans (e σ)⟩

end Langlands.Aubert.General.RepresentedParabolic
