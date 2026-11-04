import Langlands.Representation.Aubert.General.RefinedIntersectionCoordinates
import Langlands.Representation.Aubert.General.RationalGeometricCommonLeviRefinements
import Langlands.Representation.Aubert.General.ConjugateParabolicTopology
import Langlands.GroupScheme.Dynamic.CommonTorusIntersections

/-! # Actual refined radical intersections on rational points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Aubert.General

section ForwardConjugation

variable {A : Type*} [Group A]

private theorem map_conj_eq_conjugateSubgroup (g : A) (H : Subgroup A) :
    H.map (MulAut.conj g).toMonoidHom = conjugateSubgroup g H := by
  ext x
  simp [Subgroup.map_equiv_eq_comap_symm, conjugateSubgroup]

private theorem mem_map_conj (g : A) (H : Subgroup A) (x : A) :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  rw [map_conj_eq_conjugateSubgroup]
  exact mem_conjugateSubgroup g H x

variable [TopologicalSpace A] [IsTopologicalGroup A]

/-- The actual semidirect decomposition under forward conjugation. -/
theorem IsSemidirectDecomposition.forwardConjugate {P M U : Subgroup A}
    (d : IsSemidirectDecomposition P M U) (g : A) :
    IsSemidirectDecomposition (P.map (MulAut.conj g).toMonoidHom)
      (M.map (MulAut.conj g).toMonoidHom) (U.map (MulAut.conj g).toMonoidHom) := by
  simpa only [map_conj_eq_conjugateSubgroup] using d.conjugate g

/-- Forward conjugation retains continuity of the original projection. -/
theorem IsSemidirectDecomposition.continuous_forwardConjugate_projection
    {P M U : Subgroup A} (d : IsSemidirectDecomposition P M U)
    (hp : Continuous d.projection) (g : A) :
    Continuous (d.forwardConjugate g).projection :=
  continuous_projection_conj d (d.forwardConjugate g) g
    (mem_map_conj g P) (mem_map_conj g M) (mem_map_conj g U) hp

end ForwardConjugation

end Langlands.Aubert.General

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

omit [IsAffineHom G.X.hom] in
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

omit [IsAffineHom G.X.hom] in
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


/-- The original radical-parabolic intersection is the exact ordered product
of its actual Levi and radical intersections. -/
theorem geometricUnipotentParabolic_eq_mul
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
    (I J : Finset (SimpleRoot i ν))
    (n : Group.RelativeWeyl.normalizer (torusPoints i)) :
    (↑(geometricTargetIntersection (unipotent i ν I) (parabolic i ν J)
      (n : GroupScheme.rationalPoints G)) : Set (GroupScheme.rationalPoints G)) =
    (↑(geometricTargetIntersection (unipotent i ν I) (levi i ν J)
      (n : GroupScheme.rationalPoints G)) : Set (GroupScheme.rationalPoints G)) *
    (↑(geometricTargetIntersection (unipotent i ν I) (unipotent i ν J)
      (n : GroupScheme.rationalPoints G)) : Set (GroupScheme.rationalPoints G)) := by
  have := hG.isSeparated
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
  have hprod := ((Dynamic.semistandardIntersectionProducts hG i α βn).identityTest).2
  change (↑((Dynamic.unipotent χ).rationalPoints ⊓
      (Dynamic.parabolic τ).rationalPoints) : Set (GroupScheme.rationalPoints G)) =
    (↑((Dynamic.unipotent χ).rationalPoints ⊓
      (Dynamic.centralizer τ).rationalPoints) : Set (GroupScheme.rationalPoints G)) *
    (↑((Dynamic.unipotent χ).rationalPoints ⊓
      (Dynamic.unipotent τ).rationalPoints) : Set (GroupScheme.rationalPoints G)) at hprod
  rw [hUχ, hPτ, hMτ, hUτ] at hprod
  exact hprod

section Refinements

variable (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
  (I J : Finset (SimpleRoot i ν))
  (n : Group.RelativeWeyl.normalizer (torusPoints i))
  (ψ θ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
  (h : GeometricCommonLeviRefinements i ν I J n ψ θ)

local notation "A" => GroupScheme.rationalPoints G
local notation "PI" => parabolic i ν I
local notation "MI" => levi i ν I
local notation "UI" => unipotent i ν I
local notation "Q" => (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (n : A))) (parabolic i ν J))
local notation "N" => (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (n : A))) (levi i ν J))
local notation "V" => (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (n : A))) (unipotent i ν J))
local notation "R" => (SubgroupFunctor.rationalPoints (Dynamic.unipotent ψ))
local notation "S" => (SubgroupFunctor.rationalPoints (Dynamic.unipotent θ))

include hStandard hG hi hν hN h

/-- The two constructed refined radicals intersect in the exact three
original endpoint and common radical factors. -/
theorem geometricRefinedRadicalIntersection_eq_mul :
    (↑(R ⊓ S) : Set A) = (↑(MI ⊓ V) : Set A) *
      ((↑(UI ⊓ N) : Set A) * (↑(UI ⊓ V) : Set A)) := by
  exact RefinedIntersection.eq_triple_mul MI UI Q N V R S
    h.1.2.2.2.1 h.2.1.2.2.2.1
    ((Dynamic.unipotent_le_parabolic θ _).trans h.2.1.1)
    (geometricUnipotentParabolic_eq_mul i ν hStandard hG hi hν hN I J n)

variable [TopologicalSpace (GroupScheme.rationalPoints G)]
  [IsTopologicalGroup (GroupScheme.rationalPoints G)]
  (dI : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
  (dJ : IsSemidirectDecomposition (parabolic i ν J) (levi i ν J) (unipotent i ν J))

/-- Actual ordered multiplication coordinates on the intersection of the
refined radicals, with continuity inherited from the two standard projections. -/
def geometricRefinedRadicalIntersectionCoordinates
    (hpI : Continuous dI.projection) (hpJ : Continuous dJ.projection) :
    geometricTargetIntersection MI (unipotent i ν J) (n : A) ×
      (geometricTargetIntersection UI (levi i ν J) (n : A) ×
        geometricTargetIntersection UI (unipotent i ν J) (n : A)) ≃ₜ ↥(R ⊓ S) :=
  RefinedIntersection.coordinates MI UI Q N V R S
    h.1.2.2.2.1 h.2.1.2.2.2.1
    ((Dynamic.unipotent_le_parabolic θ _).trans h.2.1.1)
    (geometricUnipotentParabolic_eq_mul i ν hStandard hG hi hν hN I J n)
    dI (dJ.forwardConjugate (n : A)) hpI
      (dJ.continuous_forwardConjugate_projection hpJ (n : A))

@[simp]
theorem geometricRefinedRadicalIntersectionCoordinates_apply
    (hpI : Continuous dI.projection) (hpJ : Continuous dJ.projection)
    (b : geometricTargetIntersection MI (unipotent i ν J) (n : A))
    (a : geometricTargetIntersection UI (levi i ν J) (n : A))
    (c : geometricTargetIntersection UI (unipotent i ν J) (n : A)) :
    (geometricRefinedRadicalIntersectionCoordinates i ν hStandard hG hi hν hN
      I J n ψ θ h dI dJ hpI hpJ (b, a, c) : A) =
      (b : A) * ((a : A) * (c : A)) := rfl


end Refinements

end Langlands.Aubert.General.RationalPointFamily
