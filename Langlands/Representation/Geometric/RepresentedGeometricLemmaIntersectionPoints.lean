import Langlands.Representation.Geometric.RepresentedGeometricLemmaStatement

/-! # Literal rational-point intersections of geometric-lemma data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

private theorem pointImage_inf_conjugate_of_range_eq
    {k : Type u} [Field k] {G A B C : GroupScheme (Spec (CommRingCat.of k))}
    (j : A ⟶ G) (a : B ⟶ G) (b : C ⟶ G) (z : rationalPoints G)
    (h : SubgroupFunctor.range j =
      SubgroupFunctor.range a ⊓ SubgroupFunctor.range (b ≫ (G.innerIso z).hom)) :
    pointImage j = pointImage a ⊓ (pointImage b).map (MulAut.conj z).toMonoidHom := by
  have hpoints := congrArg
    (fun H : SubgroupFunctor G => H.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))) h
  simp only [SubgroupFunctor.inf_carrier, ← pointImage_eq_range_carrier] at hpoints
  exact hpoints.trans (congrArg (fun H => pointImage a ⊓ H)
    (rationalPoints_range_comp_innerIso b z))

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P}
  {hp : IsParabolicSubgroup p} {hr : LeviSubgroup.IsGeometricUnipotentRadical r}
  {hl : IsRationalLeviSubgroup l} {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ rQ)}
  {z : rationalPoints G}

namespace GeometricLemmaIntersectionDatum

variable (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
  q lQ rQ hq hrQ hlQ hmulQ z)

/-- The source intersection parabolic on literal ambient rational points. -/
theorem sourceParabolicPoints_eq :
    pointImage (D.p' ≫ l ≫ p) =
      pointImage (l ≫ p) ⊓ (pointImage q).map (MulAut.conj z).toMonoidHom :=
  pointImage_inf_conjugate_of_range_eq _ _ _ _ D.parabolic_eq

/-- The source intersection Levi on literal ambient rational points. -/
theorem sourceLeviPoints_eq :
    pointImage (D.l' ≫ D.p' ≫ l ≫ p) =
      pointImage (l ≫ p) ⊓ (pointImage (lQ ≫ q)).map (MulAut.conj z).toMonoidHom := by
  apply pointImage_inf_conjugate_of_range_eq
  simpa only [Category.assoc] using D.levi_eq

/-- The source intersection radical on literal ambient rational points. -/
theorem sourceRadicalPoints_eq :
    pointImage (D.r' ≫ D.p' ≫ l ≫ p) =
      pointImage (l ≫ p) ⊓ (pointImage (rQ ≫ q)).map (MulAut.conj z).toMonoidHom := by
  apply pointImage_inf_conjugate_of_range_eq
  simpa only [Category.assoc] using D.radical_eq

/-- The target intersection parabolic on literal ambient rational points. -/
theorem targetParabolicPoints_eq :
    pointImage (D.q' ≫ lQ ≫ q) =
      pointImage (lQ ≫ q) ⊓ (pointImage p).map (MulAut.conj z⁻¹).toMonoidHom :=
  pointImage_inf_conjugate_of_range_eq _ _ _ _ D.parabolic_eq'

/-- The target intersection Levi on literal ambient rational points. -/
theorem targetLeviPoints_eq :
    pointImage (D.lQ' ≫ D.q' ≫ lQ ≫ q) =
      pointImage (lQ ≫ q) ⊓ (pointImage (l ≫ p)).map (MulAut.conj z⁻¹).toMonoidHom := by
  apply pointImage_inf_conjugate_of_range_eq
  simpa only [Category.assoc] using D.levi_eq'

/-- The target intersection radical on literal ambient rational points. -/
theorem targetRadicalPoints_eq :
    pointImage (D.rQ' ≫ D.q' ≫ lQ ≫ q) =
      pointImage (lQ ≫ q) ⊓ (pointImage (r ≫ p)).map (MulAut.conj z⁻¹).toMonoidHom := by
  apply pointImage_inf_conjugate_of_range_eq
  simpa only [Category.assoc] using D.radical_eq'

include D in
/-- The source intersection groups form an actual ambient semidirect decomposition. -/
theorem sourcePoints_isSemidirectDecomposition :
    IsSemidirectDecomposition
      (pointImage (l ≫ p) ⊓ (pointImage q).map (MulAut.conj z).toMonoidHom)
      (pointImage (l ≫ p) ⊓ (pointImage (lQ ≫ q)).map (MulAut.conj z).toMonoidHom)
      (pointImage (l ≫ p) ⊓ (pointImage (rQ ≫ q)).map (MulAut.conj z).toMonoidHom) := by
  rw [← D.sourceParabolicPoints_eq, ← D.sourceLeviPoints_eq, ← D.sourceRadicalPoints_eq]
  simpa only [Category.assoc] using
    isSemidirectDecomposition_pointImage (D.p' ≫ l ≫ p) D.l' D.r'
      (D.hp'.isClosedSubgroup.comp (hl.isClosedSubgroup.comp hp.isClosedSubgroup)) D.hr' D.hmul'

include D in
/-- The target intersection groups form an actual ambient semidirect decomposition. -/
theorem targetPoints_isSemidirectDecomposition :
    IsSemidirectDecomposition
      (pointImage (lQ ≫ q) ⊓ (pointImage p).map (MulAut.conj z⁻¹).toMonoidHom)
      (pointImage (lQ ≫ q) ⊓ (pointImage (l ≫ p)).map (MulAut.conj z⁻¹).toMonoidHom)
      (pointImage (lQ ≫ q) ⊓ (pointImage (r ≫ p)).map (MulAut.conj z⁻¹).toMonoidHom) := by
  rw [← D.targetParabolicPoints_eq, ← D.targetLeviPoints_eq, ← D.targetRadicalPoints_eq]
  simpa only [Category.assoc] using
    isSemidirectDecomposition_pointImage (D.q' ≫ lQ ≫ q) D.lQ' D.rQ'
      (D.hq'.isClosedSubgroup.comp (hlQ.isClosedSubgroup.comp hq.isClosedSubgroup)) D.hrQ' D.hmulQ'

/-- The supplied rational-point homeomorphism has exactly the ambient conjugation action. -/
theorem conjugationPoints_apply (x : rationalPoints D.L') :
    rationalPoints.map (D.l' ≫ D.p' ≫ l ≫ p) (D.e x) =
      z * rationalPoints.map (D.lQ' ≫ D.q' ≫ lQ ≫ q) x * z⁻¹ := by
  rw [D.e_apply]
  have h := congrArg (fun f : D.L' ⟶ G => rationalPoints.map f x) D.φ_comp
  simpa only [pointMap_comp_apply, rationalPoints_map_innerIso,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h

section Topology

variable [IsAffineHom G.X.hom]

local instance intersectionAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

open Langlands.AlgebraicGeometry.PointTopology

/-- The source represented Levi, in its own topology, is its literal ambient intersection. -/
def sourceLeviPointsEquiv :
    letI := leviPointTopology D.l' D.hl'
    rationalPoints D.M' ≃ₜ*
      ↥(pointImage (l ≫ p) ⊓ (pointImage (lQ ≫ q)).map (MulAut.conj z).toMonoidHom) := by
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let j := D.l' ≫ D.p' ≫ l ≫ p
  have hc : IsClosedSubgroup j := D.hl'.isClosedSubgroup.comp
    (D.hp'.isClosedSubgroup.comp (hl.isClosedSubgroup.comp hp.isClosedSubgroup))
  have : IsClosedImmersion j.hom.hom.left := hc
  have : IsAffine D.M'.X.left := isAffine_of_isAffineHom j.hom.hom.left
  letI := leviPointTopology D.l' D.hl'
  exact (rationalPointSubgroupHomeomorph k (SubgroupFunctor.range j) j
    hc.isRepresentedBy_range hc).trans
      (subgroupCongrContinuous ((pointImage_eq_range_carrier j).symm.trans D.sourceLeviPoints_eq))

@[simp]
theorem sourceLeviPointsEquiv_apply_coe (x : rationalPoints D.M') :
    (D.sourceLeviPointsEquiv x : rationalPoints G) =
      rationalPoints.map (D.l' ≫ D.p' ≫ l ≫ p) x := rfl

/-- The target represented Levi, in its own topology, is its literal ambient intersection. -/
def targetLeviPointsEquiv :
    letI := leviPointTopology D.lQ' D.hlQ'
    rationalPoints D.L' ≃ₜ*
      ↥(pointImage (lQ ≫ q) ⊓ (pointImage (l ≫ p)).map (MulAut.conj z⁻¹).toMonoidHom) := by
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let j := D.lQ' ≫ D.q' ≫ lQ ≫ q
  have hc : IsClosedSubgroup j := D.hlQ'.isClosedSubgroup.comp
    (D.hq'.isClosedSubgroup.comp (hlQ.isClosedSubgroup.comp hq.isClosedSubgroup))
  have : IsClosedImmersion j.hom.hom.left := hc
  have : IsAffine D.L'.X.left := isAffine_of_isAffineHom j.hom.hom.left
  letI := leviPointTopology D.lQ' D.hlQ'
  exact (rationalPointSubgroupHomeomorph k (SubgroupFunctor.range j) j
    hc.isRepresentedBy_range hc).trans
      (subgroupCongrContinuous ((pointImage_eq_range_carrier j).symm.trans D.targetLeviPoints_eq))

@[simp]
theorem targetLeviPointsEquiv_apply_coe (x : rationalPoints D.L') :
    (D.targetLeviPointsEquiv x : rationalPoints G) =
      rationalPoints.map (D.lQ' ≫ D.q' ≫ lQ ≫ q) x := rfl

include D in
/-- Transport of the actual conjugation homeomorphism to the literal intersection Levis. -/
def intersectionLeviPointsConjugation :
    ↥(pointImage (lQ ≫ q) ⊓ (pointImage (l ≫ p)).map (MulAut.conj z⁻¹).toMonoidHom) ≃ₜ*
      ↥(pointImage (l ≫ p) ⊓ (pointImage (lQ ≫ q)).map (MulAut.conj z).toMonoidHom) :=
  by
    letI := leviPointTopology D.l' D.hl'
    letI := leviPointTopology D.lQ' D.hlQ'
    exact D.targetLeviPointsEquiv.symm.trans (D.e.trans D.sourceLeviPointsEquiv)

/-- The transported homeomorphism is literal conjugation by the original representative. -/
theorem intersectionLeviPointsConjugation_apply_coe
    (x : ↥(pointImage (lQ ≫ q) ⊓ (pointImage (l ≫ p)).map (MulAut.conj z⁻¹).toMonoidHom)) :
    (D.intersectionLeviPointsConjugation x : rationalPoints G) = z * (x : rationalPoints G) * z⁻¹ := by
  let := leviPointTopology D.l' D.hl'
  let := leviPointTopology D.lQ' D.hlQ'
  change (D.sourceLeviPointsEquiv (D.e (D.targetLeviPointsEquiv.symm x)) : rationalPoints G) = _
  rw [D.sourceLeviPointsEquiv_apply_coe, D.conjugationPoints_apply,
    ← D.targetLeviPointsEquiv_apply_coe, D.targetLeviPointsEquiv.apply_symm_apply]

end Topology

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
