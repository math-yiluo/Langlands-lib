import Langlands.GroupScheme.Dynamic.CommutingRefinements
import Langlands.GroupScheme.Dynamic.OppositeCellContraction
import Langlands.Representation.Aubert.General.RationalGeometricStabilizerProjection

/-! # Common-Levi refinements on the actual rational geometric intersections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme

section Points

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The exact rational-point data supplied by a commuting refinement.
Both products take place in the original rational-point group. -/
def IsPointCommutingRefinement
    (P M U Q N V : Subgroup (GroupScheme.rationalPoints G))
    (ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) : Prop :=
  (Dynamic.parabolic ψ).rationalPoints ≤ P ∧
    (Dynamic.centralizer ψ).rationalPoints = M ⊓ N ∧
    U ≤ (Dynamic.unipotent ψ).rationalPoints ∧
    (↑((Dynamic.unipotent ψ).rationalPoints) : Set (GroupScheme.rationalPoints G)) =
      (↑(M ⊓ V) : Set (GroupScheme.rationalPoints G)) *
        (↑U : Set (GroupScheme.rationalPoints G)) ∧
    (↑((Dynamic.parabolic ψ).rationalPoints) : Set (GroupScheme.rationalPoints G)) =
      (↑(M ⊓ Q) : Set (GroupScheme.rationalPoints G)) *
        (↑U : Set (GroupScheme.rationalPoints G))

private theorem pointRefinement_of_dynamic
    (P M U Q N V : Subgroup (GroupScheme.rationalPoints G))
    (χ τ ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (h : Dynamic.IsCommutingRefinement χ τ ψ)
    (hP : (Dynamic.parabolic χ).rationalPoints = P)
    (hM : (Dynamic.centralizer χ).rationalPoints = M)
    (hU : (Dynamic.unipotent χ).rationalPoints = U)
    (hQ : (Dynamic.parabolic τ).rationalPoints = Q)
    (hN : (Dynamic.centralizer τ).rationalPoints = N)
    (hV : (Dynamic.unipotent τ).rationalPoints = V) :
    IsPointCommutingRefinement P M U Q N V ψ := by
  have inf_points (A B : SubgroupFunctor G) :
      (A ⊓ B).rationalPoints = A.rationalPoints ⊓ B.rationalPoints := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hP]
    exact h.1 _
  · rw [h.2.1, inf_points, hM, hN]
  · rw [← hU]
    exact h.2.2.1 _
  · rw [← hM, ← hV, ← hU]
    exact h.2.2.2.1 _
  · rw [← hM, ← hQ, ← hU]
    exact h.2.2.2.2 _

private theorem centralizer_points_conjugate
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (g : GroupScheme.rationalPoints G) :
    (Dynamic.centralizer (χ ≫ (G.innerIso g).hom)).rationalPoints =
      (Dynamic.centralizer χ).rationalPoints.map (MulAut.conj g).toMonoidHom := by
  have h := Dynamic.centralizer_eq_comap_of_iso χ (G.innerIso g)
  have hc := congrArg
    (fun F : SubgroupFunctor G => F.comap (G.innerIso g).inv) h
  rw [← SubgroupFunctor.comap_comp, Iso.inv_hom_id, SubgroupFunctor.comap_id] at hc
  rw [← hc, SubgroupFunctor.rationalPoints_comap_innerIso_inv]

private theorem unipotent_points_conjugate
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (g : GroupScheme.rationalPoints G) :
    (Dynamic.unipotent (χ ≫ (G.innerIso g).hom)).rationalPoints =
      (Dynamic.unipotent χ).rationalPoints.map (MulAut.conj g).toMonoidHom := by
  have h := Dynamic.unipotent_eq_comap_of_iso χ (G.innerIso g)
  have hc := congrArg
    (fun F : SubgroupFunctor G => F.comap (G.innerIso g).inv) h
  rw [← SubgroupFunctor.comap_comp, Iso.inv_hom_id, SubgroupFunctor.comap_id] at hc
  rw [← hc, SubgroupFunctor.rationalPoints_comap_innerIso_inv]

end Points

section Standard

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Refinements of the original standard parabolic and the forward-conjugate
standard parabolic, sharing the literal target intersection Levi. -/
def GeometricCommonLeviRefinements
    (I J : Finset (SimpleRoot i ν))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (ψ θ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) : Prop :=
  IsPointCommutingRefinement
    (parabolic i ν I) (levi i ν I) (unipotent i ν I)
    ((parabolic i ν J).map (MulAut.conj (n : GroupScheme.rationalPoints G)).toMonoidHom)
    ((levi i ν J).map (MulAut.conj (n : GroupScheme.rationalPoints G)).toMonoidHom)
    ((unipotent i ν J).map (MulAut.conj (n : GroupScheme.rationalPoints G)).toMonoidHom)
    ψ ∧
  IsPointCommutingRefinement
    ((parabolic i ν J).map (MulAut.conj (n : GroupScheme.rationalPoints G)).toMonoidHom)
    ((levi i ν J).map (MulAut.conj (n : GroupScheme.rationalPoints G)).toMonoidHom)
    ((unipotent i ν J).map (MulAut.conj (n : GroupScheme.rationalPoints G)).toMonoidHom)
    (parabolic i ν I) (levi i ν I) (unipotent i ν I) θ ∧
  (Dynamic.centralizer ψ).rationalPoints =
    geometricTargetIntersection (levi i ν I) (levi i ν J)
      (n : GroupScheme.rationalPoints G) ∧
  (Dynamic.centralizer θ).rationalPoints =
    geometricTargetIntersection (levi i ν I) (levi i ν J)
      (n : GroupScheme.rationalPoints G)

/-- The two exact common-Levi refinements exist for every pair of standard
indices and every actual normalizer point. No minimality is required. -/
theorem exists_geometric_common_levi_refinements
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
    (I J : Finset (SimpleRoot i ν))
    (n : Group.RelativeWeyl.normalizer (torusPoints i)) :
    ∃ ψ θ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      GeometricCommonLeviRefinements i ν I J n ψ θ := by
  have := hG.isSeparated
  have := hG.smooth
  obtain ⟨⟨α, hα⟩, hcmpI⟩ :=
    hStandard k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)
  obtain ⟨hPI, hMI, hUI⟩ := hcmpI α hα
  obtain ⟨⟨β, hβ⟩, hcmpJ⟩ :=
    hStandard k G hG T i hi ν hν (rootSet i ν J) (rootSet_subset i ν J)
  obtain ⟨hPJ, hMJ, hUJ⟩ := hcmpJ β hβ
  let ns := (normalizerEquiv i hN).symm n
  let βn := cocharacterAut (normalizingAut i ns) β
  let χ := CommGroupScheme.groupHom α ≫ i
  let τ := CommGroupScheme.groupHom βn ≫ i
  have hconj : τ = (CommGroupScheme.groupHom β ≫ i) ≫
      (G.innerIso (n : GroupScheme.rationalPoints G)).hom :=
    groupHom_cocharacterAut_comp i ns β
  have hPχ : (Dynamic.parabolic χ).rationalPoints = parabolic i ν I :=
    (congrArg SubgroupFunctor.rationalPoints hPI).symm
  have hMχ : (Dynamic.centralizer χ).rationalPoints = levi i ν I :=
    (congrArg SubgroupFunctor.rationalPoints hMI).symm
  have hUχ : (Dynamic.unipotent χ).rationalPoints = unipotent i ν I :=
    (congrArg SubgroupFunctor.rationalPoints hUI).symm
  have hPτ : (Dynamic.parabolic τ).rationalPoints =
      (parabolic i ν J).map (MulAut.conj (n : GroupScheme.rationalPoints G)).toMonoidHom := by
    rw [hconj, Dynamic.rationalPoints_parabolic_conjugate, ← hPJ]
  have hMτ : (Dynamic.centralizer τ).rationalPoints =
      (levi i ν J).map (MulAut.conj (n : GroupScheme.rationalPoints G)).toMonoidHom := by
    rw [hconj, centralizer_points_conjugate, ← hMJ]
  have hUτ : (Dynamic.unipotent τ).rationalPoints =
      (unipotent i ν J).map (MulAut.conj (n : GroupScheme.rationalPoints G)).toMonoidHom := by
    rw [hconj, unipotent_points_conjugate, ← hUJ]
  obtain ⟨ψ, θ, hψ, hθ, hZ⟩ := Dynamic.exists_common_levi_refinements χ τ
    (Dynamic.range_comp_le_centralizer_comp i
      (CommGroupScheme.groupHom βn) (CommGroupScheme.groupHom α))
  have hψp := pointRefinement_of_dynamic _ _ _ _ _ _ χ τ ψ hψ
    hPχ hMχ hUχ hPτ hMτ hUτ
  have hθp := pointRefinement_of_dynamic _ _ _ _ _ _ τ χ θ hθ
    hPτ hMτ hUτ hPχ hMχ hUχ
  refine ⟨ψ, θ, hψp, hθp, hψp.2.1, ?_⟩
  rw [← hZ]
  exact hψp.2.1

end Standard

end Langlands.Aubert.General.RationalPointFamily
