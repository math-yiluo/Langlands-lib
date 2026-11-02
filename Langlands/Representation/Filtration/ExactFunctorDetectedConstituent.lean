import Langlands.Representation.Filtration.ExactConstituentExtraction
import Langlands.Representation.Filtration.SimpleSubquotientFactorProof

/-! Actual constituent equivalences detected by an irreducible exact-functor image. -/

noncomputable section
open CategoryTheory

namespace Langlands

universe uG uH uV

namespace ObjectRepFiltration

private theorem adjacent_steps_ne_of_nontrivial
    {k G : Type*} [Field k] [Monoid G] {A : Rep k G} {r : ℕ}
    (s : ObjectRepFiltration A r) (i : Fin r)
    [Nontrivial (s.gradedRepresentation i)] :
    s.subrepresentation i.castSucc ≠ s.subrepresentation i.succ := by
  intro he
  have hz (x : s.gradedRepresentation i) : x = 0 := by
    obtain ⟨v, rfl⟩ := s.gradedProjection_surjective i x
    apply (s.gradedProjection_eq_zero_iff i v).mpr
    rw [he]
    exact v.property
  exact (not_nontrivial_iff_subsingleton.mpr
    ⟨fun x y => (hz x).trans (hz y).symm⟩) inferInstance

/-- An irreducible filtered object has at most one nonzero actual grade. -/
theorem index_eq_of_nontrivial_grades
    {k G : Type*} [Field k] [Monoid G] {A : Rep k G} {r : ℕ}
    (s : ObjectRepFiltration A r) (hA : A.ρ.IsIrreducible)
    (i j : Fin r) [Nontrivial (s.gradedRepresentation i)]
    [Nontrivial (s.gradedRepresentation j)] : i = j := by
  let : A.ρ.IsIrreducible := hA
  have hends (a : Fin r) [Nontrivial (s.gradedRepresentation a)] :
      s.subrepresentation a.castSucc = ⊥ ∧ s.subrepresentation a.succ = ⊤ := by
    have hne := adjacent_steps_ne_of_nontrivial s a
    have hle := s.monotone_subrepresentation (Fin.castSucc_le_succ a)
    have hl : s.subrepresentation a.castSucc = ⊥ :=
      (hA.eq_bot_or_eq_top _).resolve_right (fun ht =>
        hne (ht.trans (top_unique (ht ▸ hle)).symm))
    have hu : s.subrepresentation a.succ = ⊤ :=
      (hA.eq_bot_or_eq_top _).resolve_left (fun hb =>
        hne (hl.trans hb.symm))
    exact ⟨hl, hu⟩
  have impossible (a b : Fin r) [Nontrivial (s.gradedRepresentation a)]
      [Nontrivial (s.gradedRepresentation b)] (hab : a < b) : False := by
    have hle : a.succ ≤ b.castSucc := by
      change a.val + 1 ≤ b.val
      exact hab
    have hle' := s.monotone_subrepresentation hle
    rw [(hends a).2, (hends b).1] at hle'
    exact bot_ne_top (top_le_iff.mp hle')
  rcases lt_trichotomy i j with h | h | h
  · exact (impossible i j h).elim
  · exact h
  · exact (impossible j i h).elim

end ObjectRepFiltration

namespace ExactFunctorDetectedConstituent

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]
  (J : SmoothRep.{0,uG,uV} ℂ G ⥤ SmoothRep.{0,uH,uV} ℂ H)
  [J.PreservesZeroMorphisms]
  (hJ : Derivative.Mirabolic.MapsShortExactIntertwiners J)

/-- Construct an actual equivalence between two irreducible subquotients
detected nontrivially by a functor with irreducible ambient image. -/
def constituentEquiv
    (A : SmoothRep.{0,uG,uV} ℂ G) (hA : A.HasFiniteLength)
    (himage : (J.obj A).IsIrreducible)
    (D E : SmoothRep.{0,uG,uV} ℂ G)
    (hD : D.IsIrreducible) (hE : E.IsIrreducible)
    (hDA : SmoothRep.IsSubquotient D A)
    (hEA : SmoothRep.IsSubquotient E A)
    (hJD : Nontrivial (J.obj D)) (hJE : Nontrivial (J.obj E)) :
    D.representation.Equiv E.representation := by
  classical
  apply Classical.choice
  obtain ⟨c, hzero, htop⟩ := isFiniteLength_iff_exists_compositionSeries.mp hA
  obtain ⟨s, hs⟩ :=
    LengthCriterionProof.hasCompositionSeriesLength_of_compositionSeries c hzero htop
  obtain ⟨SD, UD, ⟨eD⟩⟩ := hDA
  obtain ⟨SE, UE, ⟨eE⟩⟩ := hEA
  obtain ⟨i, ⟨fD⟩⟩ := simpleSubquotientFactor ℂ G A _ s hs D SD UD hD
    ⟨SmoothRep.equivOfIso eD⟩
  obtain ⟨j, ⟨fE⟩⟩ := simpleSubquotientFactor ℂ G A _ s hs E SE UE hE
    ⟨SmoothRep.equivOfIso eE⟩
  let t := s.exactSmoothImage J
  let eDi := J.mapIso (SmoothRep.mkIso
    (show D.representation.Equiv (s.smoothGradedObject i).representation from fD))
  let eEj := J.mapIso (SmoothRep.mkIso
    (show E.representation.Equiv (s.smoothGradedObject j).representation from fE))
  let := hJD
  let := hJE
  have hJi : Nontrivial (J.obj (s.smoothGradedObject i)) :=
    (SmoothRep.equivOfIso eDi.symm).toLinearEquiv.toEquiv.nontrivial
  have hJj : Nontrivial (J.obj (s.smoothGradedObject j)) :=
    (SmoothRep.equivOfIso eEj.symm).toLinearEquiv.toEquiv.nontrivial
  let := hJi
  let := hJj
  have hi : Nontrivial (t.gradedRepresentation i) :=
    (SmoothRep.equivOfIso (s.exactSmoothImageGradedIso J hJ i)).toLinearEquiv.toEquiv.nontrivial
  have hj : Nontrivial (t.gradedRepresentation j) :=
    (SmoothRep.equivOfIso (s.exactSmoothImageGradedIso J hJ j)).toLinearEquiv.toEquiv.nontrivial
  let := hi
  let := hj
  have hij := t.index_eq_of_nontrivial_grades himage i j
  subst j
  exact ⟨fD.trans fE.symm⟩

/-- Actual constituent data, with actual equivalences to every detected simple
subquotient of the same ambient representation. -/
structure Data (A : SmoothRep.{0,uG,uV} ℂ G) where
  constituent : SmoothRep.{0,uG,uV} ℂ G
  irreducible : constituent.IsIrreducible
  occurs : SmoothRep.IsSubquotient constituent A
  image_nontrivial : Nontrivial (J.obj constituent)
  equivalence (E : SmoothRep.{0,uG,uV} ℂ G) (hE : E.IsIrreducible)
    (hEA : SmoothRep.IsSubquotient E A) (hJE : Nontrivial (J.obj E)) :
    constituent.representation.Equiv E.representation

/-- Choose an actual unique detected constituent, given finite length of the
source and irreducibility of its exact-functor image. -/
def choose
    (A : SmoothRep.{0,uG,uV} ℂ G) (hA : A.HasFiniteLength)
    (himage : (J.obj A).IsIrreducible) : Data J A := by
  classical
  apply Classical.choice
  obtain ⟨c, hzero, htop⟩ := isFiniteLength_iff_exists_compositionSeries.mp hA
  obtain ⟨s, hs⟩ :=
    LengthCriterionProof.hasCompositionSeriesLength_of_compositionSeries c hzero htop
  let t := s.exactSmoothImage J
  let : (J.obj A).IsIrreducible := himage
  let : Nontrivial (J.obj A) :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ H) (J.obj A).representation.asModule
  have hex : ∃ i, Nontrivial (t.gradedRepresentation i) := by
    by_contra h
    have hz (i) : Subsingleton (t.gradedRepresentation i) :=
      not_nontrivial_iff_subsingleton.mp (fun hi => h ⟨i, hi⟩)
    exact (not_nontrivial_iff_subsingleton.mpr
      (objectRepFiltrationSubsingleton ℂ H (J.obj A).obj _ t hz)) inferInstance
  let i := Classical.choose hex
  let : Nontrivial (t.smoothGradedObject i) :=
    show Nontrivial (t.gradedRepresentation i) from Classical.choose_spec hex
  let D := s.smoothGradedObject i
  have hJD : Nontrivial (J.obj D) :=
    (SmoothRep.equivOfIso (s.exactSmoothImageGradedIso J hJ i).symm).toLinearEquiv.toEquiv.nontrivial
  exact ⟨
    { constituent := D
      irreducible := hs i
      occurs := s.smoothGradedObject_isSubquotient i
      image_nontrivial := hJD
      equivalence := fun E hE hEA hJE =>
        constituentEquiv J hJ A hA himage D E (hs i) hE
          (s.smoothGradedObject_isSubquotient i) hEA hJD hJE }⟩

end ExactFunctorDetectedConstituent
end Langlands
