import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.GeneratorQuotients

/-! # Bounded matching realization from global generators and effective kernels -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent.GeneratorEvaluation

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {R : PresentedAffinoidAlgebra K}
  {c : Domain.FiniteCover (Domain.whole K R)} {F : LocalAlgebras c}
  (t : PairTransitions F) {n : ℕ} (s : Fin n → t.MatchingAlgebra)

local instance : IsClosed (globalKernel t s : Set (algebra t s)) := isClosed_globalKernel t s

/-- The actual inverse-image cover of the constructed global quotient. -/
def quotientCover : Domain.FiniteCover (Domain.whole K (quotientAlgebra t s)) where
  size := c.size
  obj i := Domain.pullback (quotientMap t s) ((cover t s).obj i)
  map i := ⟨(Domain.pullback (quotientMap t s) ((cover t s).obj i)).baseMap, rfl⟩
  covers x _ := (cover t s).covers (BanachSpectrum.comap (quotientMap t s).toBoundedRingHom x)
    (Set.mem_univ _)

theorem quotientMap_isAdmissibleEpi : (quotientMap t s).IsAdmissibleEpi :=
  ClosedQuotient.map_isAdmissibleEpi (algebra t s) (globalKernel t s)

/-- Restrict the quotient cover to any original full base subdomain. -/
def quotientRestriction (i : Fin c.size) (E : Domain K R)
    (hi : E.locus ⊆ (c.obj i).locus) :
    quotientDomain t s E ⟶ (quotientCover t s).obj i :=
  Domain.pullbackRestriction (quotientMap t s)
    (Domain.pullbackRestriction (baseMap t s) (Domain.inclusionOfSubset E (c.obj i) hi))

private theorem restrictedPushoutEquiv_left (i : Fin c.size) (E : Domain K R)
    (hi : E.locus ⊆ (c.obj i).locus) :
    (restrictedPushoutEquiv t s i E hi).toBoundedAlgHom.comp
      (AffinoidPushout.leftMap (localEvaluation t s i) (sourceRestriction t s i E hi)) =
        F.localMap i E hi := by
  have hpq : ((t.projection i).comp (globalEvaluation t s)).comp (baseMap t s) =
      (F.map i).comp (c.obj i).baseMap := by
    rw [BoundedAlgHom.comp_assoc, globalEvaluation_baseMap, t.projection_structuralMap]
    exact F.structuralMap_eq i
  exact AffinoidPushout.LiftBaseChange.forward_left (baseMap t s) (c.obj i).baseMap E.baseMap
    (restriction hi) (restriction_baseMap hi) ((t.projection i).comp (globalEvaluation t s))
    (F.map i) hpq

private theorem restrictedEvaluation_sourceRestriction (i : Fin c.size) (E : Domain K R)
    (hi : E.locus ⊆ (c.obj i).locus) :
    (restrictedEvaluation t s i E hi).comp (sourceRestriction t s i E hi) =
      (F.localMap i E hi).comp (localEvaluation t s i) := by
  calc
    _ = ((restrictedPushoutEquiv t s i E hi).toBoundedAlgHom.comp
        (AffinoidPushout.rightMap (localEvaluation t s i) (sourceRestriction t s i E hi))).comp
          (sourceRestriction t s i E hi) := congrArg (fun f => f.comp
        (sourceRestriction t s i E hi)) (restrictedPushoutEquiv_right t s i E hi).symm
    _ = (restrictedPushoutEquiv t s i E hi).toBoundedAlgHom.comp
        ((AffinoidPushout.leftMap (localEvaluation t s i) (sourceRestriction t s i E hi)).comp
          (localEvaluation t s i)) := congrArg
      (fun f => (restrictedPushoutEquiv t s i E hi).toBoundedAlgHom.comp f)
        (AffinoidPushout.condition (localEvaluation t s i) (sourceRestriction t s i E hi)).symm
    _ = _ := congrArg (fun f => f.comp (localEvaluation t s i))
      (restrictedPushoutEquiv_left t s i E hi)

variable (hs : ∀ i, Function.Surjective
  ((F.map i).coefficientMap fun k => t.projection i (s k)))

include hs in
/-- Original restricted quotient comparisons commute with the stored
restriction between actual quotient-cover members. -/
theorem domainQuotientEquiv_restriction (i : Fin c.size) (E : Domain K R)
    (hi : E.locus ⊆ (c.obj i).locus) :
    (domainQuotientEquiv t s hs i E hi).toBoundedAlgHom.comp
      (quotientRestriction t s i E hi).restriction =
        (F.localMap i E hi).comp (localQuotientComparison t s hs i).toBoundedAlgHom := by
  have hright := AffinoidPushout.rightMap_isAdmissibleEpi (quotientMap t s)
    ((cover t s).obj i).baseMap (quotientMap_isAdmissibleEpi t s)
  have H :
      ((domainQuotientEquiv t s hs i E hi).toBoundedAlgHom.comp
        (quotientRestriction t s i E hi).restriction).comp
          (Domain.pullbackMap (quotientMap t s) ((cover t s).obj i)) =
      ((F.localMap i E hi).comp (localQuotientComparison t s hs i).toBoundedAlgHom).comp
          (Domain.pullbackMap (quotientMap t s) ((cover t s).obj i)) := by
    calc
      _ = (domainQuotientEquiv t s hs i E hi).toBoundedAlgHom.comp
          ((Domain.pullbackMap (quotientMap t s) (restrictedDomain t s E)).comp
            (sourceRestriction t s i E hi)) := congrArg
        (fun f => (domainQuotientEquiv t s hs i E hi).toBoundedAlgHom.comp f)
          (Domain.pullbackRestriction_comp_pullbackMap (quotientMap t s)
            (Domain.pullbackRestriction (baseMap t s) (Domain.inclusionOfSubset E (c.obj i) hi)))
      _ = (restrictedEvaluation t s i E hi).comp (sourceRestriction t s i E hi) :=
        congrArg (fun f => f.comp (sourceRestriction t s i E hi))
          (domainQuotientEquiv_right t s hs i E hi)
      _ = (F.localMap i E hi).comp (localEvaluation t s i) :=
        restrictedEvaluation_sourceRestriction t s i E hi
      _ = _ := congrArg (fun f => (F.localMap i E hi).comp f)
        (localQuotientComparison_right t s hs i).symm
  apply BoundedAlgHom.ext
  intro x
  obtain ⟨a, rfl⟩ := hright.1 x
  exact congrArg (fun f => f a) H

include hs in
theorem domainQuotientEquiv_overlap (i j : Fin c.size) :
    (t.equiv i j).toBoundedAlgHom.comp
      (domainQuotientEquiv t s hs i (F.overlap i j) (F.overlapLeft i j)).toBoundedAlgHom =
        (domainQuotientEquiv t s hs j (F.overlap i j) (F.overlapRight i j)).toBoundedAlgHom := by
  have hright := AffinoidPushout.rightMap_isAdmissibleEpi (quotientMap t s)
    (restrictedDomain t s (F.overlap i j)).baseMap (quotientMap_isAdmissibleEpi t s)
  apply BoundedAlgHom.ext
  intro x
  obtain ⟨a, rfl⟩ := hright.1 x
  calc
    _ = (t.equiv i j) (restrictedEvaluation t s i (F.overlap i j) (F.overlapLeft i j) a) :=
      congrArg (t.equiv i j) (congrArg (fun f => f a)
        (domainQuotientEquiv_right t s hs i (F.overlap i j) (F.overlapLeft i j)))
    _ = restrictedEvaluation t s j (F.overlap i j) (F.overlapRight i j) a :=
      congrArg (fun f => f a) (restrictedEvaluation_overlap t s i j)
    _ = _ := (congrArg (fun f => f a)
      (domainQuotientEquiv_right t s hs j (F.overlap i j) (F.overlapRight i j))).symm

/-- Pull a matching tuple back to each actual quotient-cover algebra. -/
def localInverse (i : Fin c.size) :
    BoundedAlgHom K t.MatchingAlgebra ((quotientCover t s).obj i).algebra :=
  (localQuotientComparison t s hs i).symm.toBoundedAlgHom.comp (t.projection i)

include hs in
private theorem localInverse_restriction (i : Fin c.size) (E : Domain K R)
    (hi : E.locus ⊆ (c.obj i).locus) (m : t.MatchingAlgebra) :
    domainQuotientEquiv t s hs i E hi
      ((quotientRestriction t s i E hi).restriction (localInverse t s hs i m)) =
        F.localMap i E hi (t.projection i m) := by
  calc
    _ = F.localMap i E hi
        (localQuotientComparison t s hs i (localInverse t s hs i m)) :=
      congrArg (fun f => f (localInverse t s hs i m))
        (domainQuotientEquiv_restriction t s hs i E hi)
    _ = _ := congrArg (F.localMap i E hi)
      ((localQuotientComparison t s hs i).apply_symm_apply (t.projection i m))

include hs in
set_option maxHeartbeats 1000000 in
/-- The original overlap matching equations suffice for bounded algebra-map
gluing on the actual quotient cover. -/
theorem localInverse_compatible : (quotientCover t s).BoundedMapCompatible (localInverse t s hs) := by
  intro i j W p q
  let E := F.overlap i j
  have hW : W.locus ⊆ (quotientDomain t s E).locus :=
    fun x hx => ⟨p.subset hx, q.subset hx⟩
  let r := Domain.inclusionOfSubset W (quotientDomain t s E) hW
  let ri := quotientRestriction t s i E (F.overlapLeft i j)
  let rj := quotientRestriction t s j E (F.overlapRight i j)
  have hp : r ≫ ri = p := @Subsingleton.elim
    (Domain.Inclusion W ((quotientCover t s).obj i)) inferInstance _ _
  have hq : r ≫ rj = q := @Subsingleton.elim
    (Domain.Inclusion W ((quotientCover t s).obj j)) inferInstance _ _
  have H : ri.restriction.comp (localInverse t s hs i) =
      rj.restriction.comp (localInverse t s hs j) := by
    apply BoundedAlgHom.ext
    intro m
    apply (domainQuotientEquiv t s hs j E (F.overlapRight i j)).toAlgEquiv.injective
    calc
      _ = (t.equiv i j) (domainQuotientEquiv t s hs i E (F.overlapLeft i j)
          (ri.restriction (localInverse t s hs i m))) :=
        (congrArg (fun f => f (ri.restriction (localInverse t s hs i m)))
          (domainQuotientEquiv_overlap t s hs i j)).symm
      _ = (t.equiv i j) (F.localMap i E (F.overlapLeft i j) (t.projection i m)) :=
        congrArg (t.equiv i j) (localInverse_restriction t s hs i E (F.overlapLeft i j) m)
      _ = F.localMap j E (F.overlapRight i j) (t.projection j m) := m.property i j
      _ = _ := (localInverse_restriction t s hs j E (F.overlapRight i j) m).symm
  calc
    p.restriction.comp (localInverse t s hs i) =
        r.restriction.comp (ri.restriction.comp (localInverse t s hs i)) :=
      congrArg (fun p : W ⟶ (quotientCover t s).obj i =>
        p.restriction.comp (localInverse t s hs i)) hp.symm
    _ = r.restriction.comp (rj.restriction.comp (localInverse t s hs j)) :=
      congrArg (fun f => r.restriction.comp f) H
    _ = q.restriction.comp (localInverse t s hs j) :=
      congrArg (fun q : W ⟶ (quotientCover t s).obj j =>
        q.restriction.comp (localInverse t s hs j)) hq

/-- Glue the actual local bounded inverses through the original quotient cover. -/
def matchingInverse : BoundedAlgHom K t.MatchingAlgebra (quotientAlgebra t s) :=
  (quotientCover t s).glueBoundedAlgHom (localInverse t s hs) (localInverse_compatible t s hs)

theorem matchingInverse_restriction (i : Fin c.size) :
    ((quotientCover t s).map i).restriction.comp (matchingInverse t s hs) =
      localInverse t s hs i :=
  (quotientCover t s).restriction_comp_glueBoundedAlgHom _ _ i

include hs in
private theorem matchingMap_local (i : Fin c.size) :
    (localQuotientComparison t s hs i).toBoundedAlgHom.comp
      ((quotientCover t s).map i).restriction = (t.projection i).comp (matchingMap t s) := by
  apply BoundedAlgHom.ext
  intro x
  obtain ⟨a, rfl⟩ := (quotientMap_isAdmissibleEpi t s).1 x
  calc
    _ = localQuotientComparison t s hs i
        (Domain.pullbackMap (quotientMap t s) ((cover t s).obj i)
          (((cover t s).map i).restriction a)) :=
      congrArg (localQuotientComparison t s hs i) (congrArg (fun f => f a)
        (AffinoidPushout.condition (quotientMap t s) ((cover t s).obj i).baseMap))
    _ = localEvaluation t s i (((cover t s).map i).restriction a) :=
      congrArg (fun f => f (((cover t s).map i).restriction a))
        (localQuotientComparison_right t s hs i)
    _ = t.projection i (globalEvaluation t s a) :=
      congrArg (fun f => f a) (localEvaluation_left t s i)
    _ = _ := congrArg (t.projection i) (congrArg (fun f => f a)
      (matchingMap_quotientMap t s)).symm

include hs in
theorem matchingMap_matchingInverse (m : t.MatchingAlgebra) :
    matchingMap t s (matchingInverse t s hs m) = m := by
  apply t.matching_ext
  intro i
  calc
    _ = localQuotientComparison t s hs i
        (((quotientCover t s).map i).restriction (matchingInverse t s hs m)) :=
      (congrArg (fun f => f (matchingInverse t s hs m)) (matchingMap_local t s hs i)).symm
    _ = localQuotientComparison t s hs i (localInverse t s hs i m) :=
      congrArg (localQuotientComparison t s hs i)
        (congrArg (fun f => f m) (matchingInverse_restriction t s hs i))
    _ = _ := (localQuotientComparison t s hs i).apply_symm_apply (t.projection i m)

include hs in
theorem matchingInverse_matchingMap (x : quotientAlgebra t s) :
    matchingInverse t s hs (matchingMap t s x) = x :=
  matchingMap_injective t s (matchingMap_matchingInverse t s hs (matchingMap t s x))

/-- Global matching generation gives a genuine bounded affinoid realization
of the entire matching algebra, with a constructed bounded inverse. -/
def matchingEquiv : BoundedAlgEquiv K (quotientAlgebra t s) t.MatchingAlgebra :=
  BoundedAlgEquiv.ofHomInv (matchingMap t s) (matchingInverse t s hs)
    (matchingInverse_matchingMap t s hs) (matchingMap_matchingInverse t s hs)

def matchingPresentation : MatchingPresentation t :=
  ⟨quotientAlgebra t s, matchingEquiv t s hs⟩

end Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent.GeneratorEvaluation
