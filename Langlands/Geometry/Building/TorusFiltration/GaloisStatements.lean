import Langlands.Geometry.Building.TorusFiltration.Points
import Langlands.GroupScheme.IntegralModel.UnramifiedSmoothDescentProof
import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent
import Langlands.GroupScheme.Torus.BaseChange
import Langlands.GroupScheme.Torus.Geometry
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyFamily
import Langlands.GaloisCohomology.Field.Modules
import Langlands.Cohomology.Profinite.Dimension.Basic

/-! # Unramified Galois stability, model descent and cohomology -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.ProfiniteCohomology
open scoped CategoryTheory.MonObj NNReal ValuativeRel

namespace Langlands.Geometry.Building

set_option maxHeartbeats 2400000 in
private theorem isOpen_subgroup_of_rationalPointStabilizer
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsIntegral k L]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] (x : rationalPoints (baseChanged k L G))
    (H : Subgroup (L ≃ₐ[k] L))
    (hH : ∀ σ : L ≃ₐ[k] L, rationalConjugate k L G σ x = x → σ ∈ H) :
    IsOpen (H : Set (L ≃ₐ[k] L)) := by
  have hf : Algebra.FiniteType k (AffineCoordinateRing k G.X) :=
    (affineCoordinate_finiteType_iff k G.X).mpr inferInstance
  obtain ⟨s, hs⟩ := hf.out
  let a := GaloisPoint.coordinates k G L (baseChangeCoeffEquiv k L G x)
  let B : Set L := a '' (s : Set (AffineCoordinateRing k G.X))
  let E := IntermediateField.adjoin k B
  have hB : B.Finite := (Finset.finite_toSet s).image a
  let : Finite B := hB.to_subtype
  let : FiniteDimensional k E := IntermediateField.finiteDimensional_adjoin
    (S := B) fun z _ => Algebra.IsIntegral.isIntegral (R := k) z
  refine Subgroup.isOpen_mono (H₁ := E.fixingSubgroup) ?_ E.fixingSubgroup_isOpen
  intro σ hσ
  apply hH σ
  apply (baseChangeCoeffEquiv k L G).injective
  rw [baseChangeCoeffEquiv_rationalConjugate]
  apply (GaloisPoint.coordinates k G L).injective
  apply AlgHom.ext_of_adjoin_eq_top hs
  intro z hz
  rw [GaloisPoint.coordinates_conjugate]
  exact (IntermediateField.mem_fixingSubgroup_iff E σ).mp hσ (a z)
    (IntermediateField.subset_adjoin k _ ⟨z, hz, rfl⟩)

section Local

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  [IsAffine (torusUnramifiedBaseChange F T).X.left] (hT : IsTorus T.toGrp)

local notation "K" => inertiaFixedField F
local notation "Γ" => (K ≃ₐ[F] K)
local notation "Tₖ" => torusUnramifiedBaseChange F T
local notation "P" => minimalCongruentPoints F Tₖ (IsTorus.baseChange hT)

/-- The natural coefficient Galois action preserves the constructed subgroup. -/
def MinimalCongruentGaloisStable (r : ℝ≥0) : Prop :=
  ∀ (σ : Γ) (x : rationalPoints (Tₖ).toGrp), x ∈ P r →
    rationalConjugate F K T.toGrp σ x ∈ P r

/-- The restricted action on the actual subgroup, as an action by group endomorphisms. -/
def minimalCongruentGaloisAction (r : ℝ≥0) (h : MinimalCongruentGaloisStable F T hT r) :
    Γ →* Monoid.End (P r) where
  toFun σ :=
    ((rationalConjugate F K T.toGrp σ).toMonoidHom.comp (P r).subtype).codRestrict
      (P r) fun x => h σ x x.property
  map_one' := by
    ext x : 1
    exact Subtype.ext (rationalConjugate_one F K T.toGrp x.val)
  map_mul' σ τ := by
    ext x : 1
    exact Subtype.ext (rationalConjugate_mul F K T.toGrp σ τ x.val)

/-- The discrete Galois coefficient module on the constructed subgroup,
written additively. -/
def minimalCongruentGaloisModule (r : ℝ≥0) (h : MinimalCongruentGaloisStable F T hT r) :
    Rep.{u} (ULift.{u} ℤ) Γ :=
  Rep.of (Langlands.GaloisCohomology.intRepOfMonoidEnd.{u}
    (minimalCongruentGaloisAction F T hT r h))

set_option maxHeartbeats 800000 in
/-- A point has an open stabilizer because its finitely many affine coordinates
are all contained in one finite coefficient extension. -/
theorem minimalCongruentGaloisModule_isSmooth (r : ℝ≥0)
    (h : MinimalCongruentGaloisStable F T hT r) :
    IsSmoothRep (minimalCongruentGaloisModule F T hT r h) := by
  let : IsAffine T.X.left := SplittingAssembly.isAffine_of_isTorus T.toGrp hT
  let : Smooth T.X.hom := IsTorus.smooth hT
  apply IsSmoothRep.of_isOpen_stabilizer
  intro v
  let x : P r := Additive.toMul v
  refine isOpen_subgroup_of_rationalPointStabilizer F K T.toGrp x.val _ ?_
  intro σ hx
  rw [mem_vectorStabilizer]
  change Additive.ofMul (minimalCongruentGaloisAction F T hT r h σ x) = Additive.ofMul x
  exact congrArg Additive.ofMul (Subtype.ext hx)

set_option maxHeartbeats 800000 in
/-- The descent conclusion follows from stability by KP Fact 2.10.16
and the base-field integral-point comparison. -/
theorem exists_descendedMinimalCongruentModel (r : ℝ≥0)
    (h : MinimalCongruentGaloisStable F T hT r)
    (N : IntegralModel (fixedFieldIntegers F) K (Tₖ).toGrp)
    (hN : N.IsSmooth) (hPts : N.integralPoints = P r) :
    ∃ M : IntegralModel ↥𝒪[F] F T.toGrp,
      M.IsSmooth ∧ Nonempty (M.baseChangeUnramified.Iso N (Iso.refl _)) ∧
        M.integralPoints = minimalCongruentBasePoints F T hT.baseChange r := by
  obtain ⟨M, hM, ⟨e⟩⟩ := IntegralModel.unramifiedSmoothModelDescent F T.toGrp N hN
    (fun σ g hg => hPts.ge (h σ g (hPts.le hg)))
  refine ⟨M, hM, ⟨e⟩, ?_⟩
  calc
    M.integralPoints = M.baseChangeUnramified.integralPoints.comap
        (rationalExtend F K T.toGrp) := M.integralPoints_eq_comap_baseChangeUnramified
    _ = N.integralPoints.comap (rationalExtend F K T.toGrp) :=
      congrArg (Subgroup.comap (rationalExtend F K T.toGrp)) e.integralPoints_eq
    _ = minimalCongruentBasePoints F T hT.baseChange r :=
      congrArg (Subgroup.comap (rationalExtend F K T.toGrp)) hPts

end Local

/-- Corrected KP Remark B.10.15. Every subgroup of the constructed
filtration is Galois stable. Every corresponding smooth model descends
over the identity on the generic fibre. -/
def MinimalCongruentUnramifiedDescentStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffine (torusUnramifiedBaseChange F T).X.left] (hT : IsTorus T.toGrp) (r : ℝ≥0),
    MinimalCongruentGaloisStable F T hT r ∧
      ∀ (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
          (torusUnramifiedBaseChange F T).toGrp),
        N.IsSmooth →
        N.integralPoints = minimalCongruentPoints F (torusUnramifiedBaseChange F T)
          (IsTorus.baseChange hT) r →
          ∃ M : IntegralModel ↥𝒪[F] F T.toGrp,
            M.IsSmooth ∧ Nonempty (M.baseChangeUnramified.Iso N (Iso.refl _)) ∧
              M.integralPoints = minimalCongruentBasePoints F T (IsTorus.baseChange hT) r

/-- Corrected KP Corollary B.10.14 over nonarchimedean local fields.
The residue-field dimension bound is required at zero depth. -/
def MinimalCongruentCohomologyStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffine (torusUnramifiedBaseChange F T).X.left] (hT : IsTorus T.toGrp)
    (r : ℝ≥0),
    (0 < r ∨ cdSup (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) ≤ 1) →
      ∃ h : MinimalCongruentGaloisStable F T hT r,
        letI := minimalCongruentGaloisModule_isSmooth F T hT r h
        ∀ n : ℕ, 0 < n → Subsingleton (cohomology (minimalCongruentGaloisModule F T hT r h) n)

end Langlands.Geometry.Building
