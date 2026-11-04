import Langlands.BruhatTits.RationalPoints.OpenHomCocompactness
import Langlands.BruhatTits.RationalPoints.SmoothRealStructureStatement
import Langlands.Representation.Plancherel.RationalCharacterTopology
import Langlands.BruhatTits.Unipotent.RationalPointCompactOpen
import Langlands.GroupScheme.Reductive.CentralTorusSurjectivityStatement
import Langlands.GroupScheme.Torus.ImageProof
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.Rational.ProductDetection
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.GroupScheme.NormalSubgroupQuotientProof
import Langlands.GroupScheme.Derived.RepresentabilityProof
import Langlands.GroupScheme.Derived.SmoothnessProof
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Langlands.AlgebraicGeometry.PointTopology.SmoothOpenMapStatement
import Langlands.Representation.Plancherel.TorusNormKernelCompactnessStatement

/-! # Cocompactness of derived points from a quotient onto a compact-kernel group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.RationalPoints

open GroupScheme

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- A homomorphism `q : M ⟶ Q` whose kernel on rational points consists of derived
points, which is open on rational points, and whose target has compact norm kernel,
makes the norm kernel of `M` compact modulo every subgroup containing the derived
points. -/
theorem compactSpace_normKernel_quotient_of_isOpenMap
    (M Q : GroupScheme (Spec (CommRingCat.of F))) [IsAffine M.X.left] [IsAffine Q.X.left]
    [LocallyOfFiniteType M.X.hom] [LocallyOfFiniteType Q.X.hom] (q : M ⟶ Q)
    (H : Subgroup (rationalPoints M))
    (hkerD : ∀ x : rationalPoints M, rationalPoints.map q x = 1 →
      x ∈ (derivedSubgroup M).carrier (Over.mk (𝟙 _)))
    (hDK : (derivedSubgroup M).carrier (Over.mk (𝟙 _)) ≤ Plancherel.rationalCommonNormKernel M)
    (hDH : (derivedSubgroup M).carrier (Over.mk (𝟙 _)) ≤ H)
    (hopen :
      letI : TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X
      letI : TopologicalSpace (rationalPoints Q) := rationalPointTopology F Q.X
      IsOpenMap (rationalPoints.map q))
    (hcpt :
      letI : TopologicalSpace (rationalPoints Q) := rationalPointTopology F Q.X
      IsCompact (Plancherel.rationalCommonNormKernel Q : Set (rationalPoints Q))) :
    letI : TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X
    CompactSpace (Plancherel.rationalCommonNormKernel M ⧸
      H.subgroupOf (Plancherel.rationalCommonNormKernel M)) := by
  let : TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X
  let : TopologicalSpace (rationalPoints Q) := rationalPointTopology F Q.X
  let : T2Space F := BruhatTits.localField_t2Space F
  let : IsTopologicalGroup (rationalPoints M) := rationalPoint_isTopologicalGroup F M
  let : IsTopologicalGroup (rationalPoints Q) := rationalPoint_isTopologicalGroup F Q
  let : LocallyCompactSpace (rationalPoints M) := rationalPoint_locallyCompactSpace F M
  have hker : ∀ x ∈ (rationalPoints.map q).ker,
      x ∈ (derivedSubgroup M).carrier (Over.mk (𝟙 _)) := fun x hx => hkerD x hx
  refine compactSpace_quotient_subgroupOf_of_isOpenMap (rationalPoints.map q) hopen
    (Plancherel.rationalCommonNormKernel M) H
    (Plancherel.isClosed_rationalCommonNormKernel M)
    (fun x hx => hDK (hker x hx)) (fun x hx => hDH (hker x hx)) hcpt ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, Plancherel.mem_rationalCommonNormKernel] at hx ⊢
  intro χ
  have := hx (characterRestrict q χ)
  rwa [rationalCharacterEval_characterRestrict] at this

/-- The rational points of the scheme-theoretic derived subgroup lie in the norm kernel. -/
theorem derivedPoints_le_rationalCommonNormKernel
    (M : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom M.X.hom]
    [LocallyOfFiniteType M.X.hom] :
    (derivedSubgroup M).carrier (Over.mk (𝟙 _)) ≤ Plancherel.rationalCommonNormKernel M := by
  obtain ⟨D, d, -, -, hd⟩ := derivedSubgroupRepresentability F M
  intro x hx
  rw [← hd.2] at hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
  rw [Plancherel.mem_rationalCommonNormKernel]
  intro χ
  have := rationalCharacterEval_characterRestrict d χ y
  rw [hd.characterRestrict_eq_zero χ, rationalCharacterEval_zero] at this
  rw [← rationalPoints.map_apply, ← this, map_one]

/-- Given a central torus covering the group together with its derived subgroup, a smooth
affine fppf quotient by the derived subgroup is a torus. -/
theorem isTorus_of_isFppfQuotient_derivedSubgroup
    (hS : ReductiveCentralTorusSurjectivityStatement.{u})
    {k : Type u} [Field k] {M D Q : GroupScheme (Spec (CommRingCat.of k))}
    (hM : IsConnectedReductive M) (d : D ⟶ M) (hd : IsDerivedSubgroup d) (q : M ⟶ Q)
    [Smooth Q.X.hom] [IsAffineHom Q.X.hom]
    (hq : RelativeRoot.IsFppfQuotient (derivedSubgroup M) q) : IsTorus Q := by
  obtain ⟨Z, i, -, -, hZ, -, -, hsurj⟩ := hS k M D d hM hd
  have hdq : d.hom.hom ≫ q.hom.hom = 1 := by
    have hmem : 𝟙 D.X ≫ d.hom.hom ∈ (derivedSubgroup M).carrier D.X := by
      rw [← hd.2]
      exact ⟨𝟙 _, rfl⟩
    rw [← hq.2.2.2, mem_range_kernelι_iff] at hmem
    simpa using hmem
  have hcomp : subgroupProductMap i d ≫ q.hom.hom =
      fst Z.toGrp.X D.X ≫ (i ≫ q).hom.hom := by
    rw [subgroupProductMap, MonObj.mul_comp, Category.assoc, Category.assoc, hdq,
      MonObj.comp_one, mul_one]
    rfl
  obtain ⟨Z', j, f, hZ', hj, hfj⟩ :=
    torusImageClosedTorusStatement k Q Z.toGrp hZ (i ≫ q)
  have hqsurj : Function.Surjective q.hom.hom.left := hq.2.1.surj
  have hcoe : ∀ {X Y W : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ W),
      (⇑(a ≫ b) : X → W) = ⇑b ∘ ⇑a := fun a b => funext (Scheme.Hom.comp_apply a b)
  have hesurj : Function.Surjective (i ≫ q).hom.hom.left := by
    have h1 : Function.Surjective (subgroupProductMap i d ≫ q.hom.hom).left := by
      rw [Over.comp_left, hcoe]
      exact hqsurj.comp hsurj
    rw [hcomp, Over.comp_left, hcoe] at h1
    exact Function.Surjective.of_comp h1
  have hjsurj : Function.Surjective j.hom.hom.left := by
    rw [← hfj] at hesurj
    change Function.Surjective (f.hom.hom.left ≫ j.hom.hom.left) at hesurj
    rw [hcoe] at hesurj
    exact Function.Surjective.of_comp hesurj
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Surjective j.hom.hom.left := ⟨hjsurj⟩
  let : AlgebraicGeometry.IsReduced Q.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k Q.X.left Q.X.hom
  let : IsIso j.hom.hom.left := isIso_of_isClosedImmersion_of_surjective _
  have : IsIso ((Over.forget _).map j.hom.hom) := by
    change IsIso j.hom.hom.left
    infer_instance
  have : IsIso j.hom.hom := isIso_of_reflects_iso j.hom.hom (Over.forget _)
  have : IsIso ((Mon.forget _).map j.hom) := by
    change IsIso j.hom.hom
    infer_instance
  have : IsIso j.hom := isIso_of_reflects_iso j.hom (Mon.forget _)
  have : IsIso ((Grp.forget₂Mon _).map j) := by
    change IsIso j.hom
    infer_instance
  have : IsIso j := isIso_of_reflects_iso j (Grp.forget₂Mon _)
  exact IsTorus.of_iso (asIso j).symm hZ'

set_option linter.defProp false in
/-- The cocompactness target follows from three published propositions: a central torus
covers each connected reductive group together with its derived subgroup, torus norm
kernels are compact, and smooth morphisms are open on local-field rational points. All
three remain explicit inputs. -/
def centralDerivedNormKernelCocompactness_of_premises
    (hS : ReductiveCentralTorusSurjectivityStatement.{u})
    (hT : Plancherel.TorusNormKernelCompactnessStatement.{u})
    (hO : SmoothRationalPointOpenMapStatement.{u}) :
    CentralDerivedNormKernelCocompactnessStatement.{u} := by
  intro F _ _ _ _ M hM
  have := hM.isAffineHom
  have := hM.smooth
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  obtain ⟨D, d, -, -, hd⟩ := derivedSubgroupRepresentability F M
  have hDsmooth : Smooth D.X.hom := derivedSubgroupSmoothness F M D d hd hM.smooth
  obtain ⟨Q, q, hQs, hQa, hq⟩ := normalSubgroupQuotient F M D d hd.1 hd.isNormal
  have : Smooth Q.X.hom := hQs
  have : IsAffineHom Q.X.hom := hQa
  have : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  rw [hd.2] at hq
  have hQ : IsTorus Q := isTorus_of_isFppfQuotient_derivedSubgroup hS hM d hd q hq
  have : QuasiCompact q.hom.hom.left := inferInstance
  have : Smooth q.hom.hom.left := hq.smooth_of_smooth_kernel hd.isRepresentedBy hDsmooth
  exact compactSpace_normKernel_quotient_of_isOpenMap M Q q _
    (fun x hx => by
      rw [← hq.2.2.2]
      exact (mem_range_kernelι_iff q x).2 hx)
    (derivedPoints_le_rationalCommonNormKernel M) le_sup_right
    (hO F M.X Q.X q.hom.hom) (hT F Q hQ)

end Langlands.BruhatTits.RationalPoints
