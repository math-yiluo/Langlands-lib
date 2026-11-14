import Langlands.GroupScheme.Adjoint.CocenterFinite
import Langlands.BruhatTits.RationalPoints.CentralDerivedNormKernelCocompactnessReduction
import Langlands.GroupScheme.Reductive.CentralTorusSurjectivityProof
import Langlands.Representation.Plancherel.TorusNormKernelCompactnessProof
import Langlands.AlgebraicGeometry.PointTopology.AffineFiniteBoundedness
import Langlands.AlgebraicGeometry.PointTopology.RationalSchemePoints
import Langlands.BruhatTits.RationalPoints.BoundedSetOperations

/-! # Bounded adjoint preimages in the rational character norm kernel -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry Topology
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.RationalPoints

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Pairing bounded subsets of finite-type affine schemes preserves boundedness. -/
theorem isAlgebraicallyBounded_pointPair
    (X Y : Over (Spec (CommRingCat.of F)))
    [IsAffine X.left] [IsAffine Y.left] [IsAffine (X ⊗ Y).left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {B : Set (RationalPoint F X)} {C : Set (RationalPoint F Y)}
    (hB : IsAlgebraicallyBounded F X B) (hC : IsAlgebraicallyBounded F Y C) :
    IsAlgebraicallyBounded F (X ⊗ Y)
      ((fun z : RationalPoint F X × RationalPoint F Y => lift z.1 z.2) '' (B ×ˢ C)) := by
  let : T2Space F := localField_t2Space F
  let : TopologicalSpace (RationalPoint F X) := rationalPointTopology F X
  let : TopologicalSpace (RationalPoint F Y) := rationalPointTopology F Y
  let : TopologicalSpace (RationalPoint F (X ⊗ Y)) := rationalPointTopology F (X ⊗ Y)
  have hc : Continuous (fun z : RationalPoint F X × RationalPoint F Y => lift z.1 z.2) := by
    have h := continuous_rationalSchemePointPair F X Y
    rw [← rationalPointTopology_eq_rationalSchemeTopology F X,
      ← rationalPointTopology_eq_rationalSchemeTopology F Y,
      ← rationalPointTopology_eq_rationalSchemeTopology F (X ⊗ Y)] at h
    exact h
  exact (isAlgebraicallyBounded_of_isCompact
    (((hB.isCompact_closure X).prod (hC.isCompact_closure Y)).image hc)).mono
      (Set.image_mono (Set.prod_mono subset_closure subset_closure))

/-- Rational-character norm kernels map into rational-character norm kernels. -/
theorem mapsTo_rationalCommonNormKernel
    {G Q : GroupScheme (Spec (CommRingCat.of F))} (p : G ⟶ Q) :
    Set.MapsTo (rationalPoints.map p)
      (Plancherel.rationalCommonNormKernel G : Set (rationalPoints G))
      (Plancherel.rationalCommonNormKernel Q : Set (rationalPoints Q)) := by
  intro x hx
  rw [SetLike.mem_coe, Plancherel.mem_rationalCommonNormKernel] at hx ⊢
  intro χ
  have h := hx (characterRestrict p χ)
  rwa [rationalCharacterEval_characterRestrict] at h

set_option linter.defProp false in
set_option backward.isDefEq.respectTransparency false in
/-- The preimage of a bounded set in an actual adjoint quotient is bounded inside
  the common kernel of all rational-character norms. -/
def isAlgebraicallyBounded_adjoint_preimage_inter_normKernel
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (A : GroupScheme (Spec (CommRingCat.of F))) (q : G ⟶ A)
    (hq : IsAdjointQuotient q)
    [IsAffine G.X.left] [IsAffine A.X.left]
    (B : Set (rationalPoints A)) (hB : IsAlgebraicallyBounded F A.X B) :
    IsAlgebraicallyBounded F G.X
      ((rationalPoints.map q ⁻¹' B) ∩
        (Plancherel.rationalCommonNormKernel G : Set (rationalPoints G))) := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let hA := hq.isAdjoint.isSemisimple.isConnectedReductive
  let : Smooth A.X.hom := hA.smooth
  let : IsAffineHom A.X.hom := hA.isAffineHom
  obtain ⟨D, d, -, -, hd⟩ := derivedSubgroupRepresentability F G
  obtain ⟨Q, p, hQs, hQa, hp⟩ := normalSubgroupQuotient F G D d hd.1 hd.isNormal
  let : Smooth Q.X.hom := hQs
  let : IsAffineHom Q.X.hom := hQa
  let : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  have hp' : RelativeRoot.IsFppfQuotient (derivedSubgroup G) p := by
    simpa only [hd.2] using hp
  have hQ : IsTorus Q := isTorus_of_isFppfQuotient_derivedSubgroup
    reductiveCentralTorusSurjectivity hG d hd p hp'
  let : IsAffine (A ⊗ Q).X.left := by
    change IsAffine (Limits.pullback A.X.hom Q.X.hom)
    infer_instance
  let : IsFinite (lift q p).hom.hom.left := isFinite_adjoint_cocenter hG d hd q hq p hp
  have hK : IsAlgebraicallyBounded F Q.X
      (Plancherel.rationalCommonNormKernel Q : Set (rationalPoints Q)) :=
    isAlgebraicallyBounded_of_isCompact (Plancherel.torusNormKernelCompactness F Q hQ)
  let C : Set (rationalPoints (A ⊗ Q)) :=
    (fun z : rationalPoints A × rationalPoints Q => lift z.1 z.2) ''
      (B ×ˢ (Plancherel.rationalCommonNormKernel Q : Set (rationalPoints Q)))
  have hC : IsAlgebraicallyBounded F (A ⊗ Q).X C :=
    isAlgebraicallyBounded_pointPair A.X Q.X hB hK
  apply (isAlgebraicallyBounded_preimage_of_finite F (lift q p).hom.hom C hC).mono
  intro x hx
  refine ⟨(rationalPoints.map q x, rationalPoints.map p x),
    ⟨hx.1, mapsTo_rationalCommonNormKernel p hx.2⟩, ?_⟩
  change lift (x ≫ q.hom.hom) (x ≫ p.hom.hom) = x ≫ (lift q p).hom.hom
  change lift (x ≫ q.hom.hom) (x ≫ p.hom.hom) = x ≫ lift q.hom.hom p.hom.hom
  simp only [comp_lift]

end Langlands.BruhatTits.RationalPoints
