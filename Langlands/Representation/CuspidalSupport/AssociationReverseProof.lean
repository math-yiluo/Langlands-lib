import Langlands.Representation.CuspidalSupport.AssociationReverseStatement
import Langlands.Representation.CuspidalSupport.JacquetSubquotientProof
import Langlands.Representation.CuspidalSupport.MinimalJacquetProof
import Langlands.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.Representation.CuspidalSupport.NonassociatedJacquetSubquotientsProof
import Langlands.Representation.CuspidalSupport.AssociatedProof
import Langlands.Representation.CuspidalSupport.AssociationLawsProof
import Langlands.Representation.CuspidalSupport.CuspidalTensorAssociationProof
import Langlands.Representation.Filtration.SubquotientAlgebraProof
import Langlands.Representation.Filtration.LengthCriterionProof
import Langlands.Representation.Filtration.NonzeroHomCommonSubquotientProof
import Langlands.Representation.Filtration.CommonSubquotientStatement
import Langlands.Representation.Filtration.SimpleSubquotientFactorProof
import Langlands.Weil.Representation.IsomorphismInvarianceProof

/-! The common-subquotient-to-association direction from published Jacquet proofs. -/

namespace Langlands.CuspidalSupport.AssociationReverse

open GeneralLinear

universe uF uV uW

/-- A common nonzero subquotient descends to a common nonzero quasicuspidal
Jacquet module, and both source Levis associate to its Levi. -/
theorem commonJacquetDescent
    (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ (B C : BlockShape n)
      (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
      (τ : SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier))
      (D : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (E : SmoothRep.{0, uF, max uF uW} ℂ (GeneralLinear n F.Carrier)),
      IsLeviQuasicuspidal B σ.representation →
      IsLeviQuasicuspidal C τ.representation →
      Nontrivial D →
      SmoothRep.IsSubquotient D ((T.normalizedParabolicInductionFunctor B).obj σ) →
      SmoothRep.IsSubquotient E ((T.normalizedParabolicInductionFunctor C).obj τ) →
      Nonempty (D.representation.Equiv E.representation) →
      ∃ L : BlockShape n,
        LevisAssociated (F := F.Carrier) B L ∧
        LevisAssociated (F := F.Carrier) C L ∧
        Nontrivial ((T.normalizedJacquetFunctor L).obj D) ∧
        IsLeviQuasicuspidal L
          ((T.normalizedJacquetFunctor L).obj D).representation ∧
        SmoothRep.IsSubquotient ((T.normalizedJacquetFunctor L).obj D)
          ((T.normalizedJacquetFunctor L).obj
            ((T.normalizedParabolicInductionFunctor B).obj σ)) ∧
        SmoothRep.IsSubquotient ((T.normalizedJacquetFunctor L).obj E)
          ((T.normalizedJacquetFunctor L).obj
            ((T.normalizedParabolicInductionFunctor C).obj τ)) ∧
        Nonempty (((T.normalizedJacquetFunctor L).obj D).representation.Equiv
          ((T.normalizedJacquetFunctor L).obj E).representation) := by
  classical
  let := T.topology
  intro B C σ τ D E hσ hτ hD hsubD hsubE he
  obtain ⟨L, hnonzero, hquasi⟩ := minimalNonzeroJacquet p F T n D hD
  have hJD := normalizedJacquetSubquotient p F T n L _ _ hsubD
  have hJE := normalizedJacquetSubquotient p F T n L _ _ hsubE
  obtain ⟨e⟩ := normalizedJacquetEquivalence p F T n L D E he
  have hquasiE := (isLeviQuasicuspidal_iff_of_equiv L e).mp hquasi
  have hBL : LevisAssociated (F := F.Carrier) B L := by
    by_contra h
    let := hnonzero
    let := nonassociatedJacquetSubquotients.{uF, uV} F T n B L σ hσ h _ hJD hquasi
    exact not_subsingleton ((T.normalizedJacquetFunctor L).obj D) inferInstance
  have hCL : LevisAssociated (F := F.Carrier) C L := by
    by_contra h
    let := hnonzero
    let := nonassociatedJacquetSubquotients.{uF, uW} F T n C L τ hτ h _ hJE hquasiE
    let : Subsingleton ((T.normalizedJacquetFunctor L).obj D) :=
      e.injective.subsingleton
    exact not_subsingleton ((T.normalizedJacquetFunctor L).obj D) inferInstance
  exact ⟨L, hBL, hCL, hnonzero, hquasi, hJD, hJE, ⟨e⟩⟩

/-- A supplied associated Jacquet filtration has simple factors when the
inducing representation is irreducible. -/
theorem associatedJacquet_simpleFactors
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} :
    letI := T.topology
    ∀ (B L : BlockShape n) (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
      (r : ℕ) (e : Fin r ≃ MinimalConjugatingPermutations (F := F.Carrier) B L)
      (s : ObjectRepFiltration (Rep.of
        ((T.normalizedJacquetFunctor L).obj
          ((T.normalizedParabolicInductionFunctor B).obj σ)).representation) r),
      σ.IsIrreducible →
      (∀ i, Nonempty ((s.gradedRepresentation i).ρ.Equiv
        (transport B L (e i).val.val (e i).property σ.representation))) →
      s.HasSimpleFactors := by
  let := T.topology
  intro B L σ r e s hσ hs i
  let := hσ
  obtain ⟨ei⟩ := hs i
  apply (Weil.IsomorphismInvariance.irreducible_iff ei).mpr
  exact isIrreducible_comp_of_surjective σ.representation
    (leviConjugation B L (e i).val.val (e i).property).symm.toMonoidHom
    (leviConjugation B L (e i).val.val (e i).property).symm.surjective

/-- A common actual irreducible subquotient of two cuspidal inductions
forces association of the inducing data. -/
theorem commonSubquotientAssociated
    (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ (B C : BlockShape n)
      (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
      (τ : SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier)),
      σ.IsIrreducible → IsLeviCuspidal B σ.representation →
      τ.IsIrreducible → IsLeviCuspidal C τ.representation →
      HaveCommonIrreducibleSubquotient
        ((T.normalizedParabolicInductionFunctor B).obj σ)
        ((T.normalizedParabolicInductionFunctor C).obj τ) →
      RepresentationsAssociated B C σ.representation τ.representation := by
  classical
  let := T.topology
  intro B C σ τ hσ hcσ hτ hcτ hcommon
  let A := (T.normalizedParabolicInductionFunctor B).obj σ
  let A' := (T.normalizedParabolicInductionFunctor C).obj τ
  obtain ⟨S, Q, S', Q', hD, he⟩ := hcommon
  let D := SmoothRep.subquotient A S Q
  let E := SmoothRep.subquotient A' S' Q'
  let : D.IsIrreducible := hD
  have hDn : Nontrivial D := nontrivial_of_isIrreducible D.representation
  have hsubD : SmoothRep.IsSubquotient D A := ⟨S, Q, ⟨CategoryTheory.Iso.refl _⟩⟩
  have hsubE : SmoothRep.IsSubquotient E A' := ⟨S', Q', ⟨CategoryTheory.Iso.refl _⟩⟩
  obtain ⟨L, hBL, hCL, hJDn, _, hJDsub, hJEsub, ⟨e⟩⟩ :=
    commonJacquetDescent p F T n B C σ τ D E
      hcσ.2 hcτ.2 hDn hsubD hsubE he
  let JD := (T.normalizedJacquetFunctor L).obj D
  let JE := (T.normalizedJacquetFunctor L).obj E
  let JA := (T.normalizedJacquetFunctor L).obj A
  let JA' := (T.normalizedJacquetFunctor L).obj A'
  obtain ⟨_, r, er, sr, hsr⟩ := associatedJacquetFiltration.{uF, uV} F T n B L σ hcσ.2 hBL
  obtain ⟨_, t, et, st, hst⟩ := associatedJacquetFiltration.{uF, uW} F T n C L τ hcτ.2 hCL
  have hsrSimple := associatedJacquet_simpleFactors T B L σ r er sr hσ hsr
  have hstSimple := associatedJacquet_simpleFactors T C L τ t et st hτ hst
  have hArtJA' : IsArtinian (MonoidAlgebra ℂ (L.Levi F.Carrier))
      JA'.representation.asModule :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (LengthCriterionProof.isFiniteLength_of_hasCompositionSeriesLength
        ⟨st, hstSimple⟩)).2
  have hArtJE := smoothSubquotientArtinian ℂ (L.Levi F.Carrier) JA' JE hArtJA' hJEsub
  have henz : e.toIntertwiningMap ≠ 0 := by
    let := hJDn
    intro he0
    have heinj : Function.Injective e.toIntertwiningMap := e.injective
    exact not_subsingleton JD ⟨fun x y => heinj (by rw [he0]; rfl)⟩
  obtain ⟨U, V, U', V', hK, ⟨ek⟩⟩ :=
    nonzeroHomCommonSubquotient ℂ (L.Levi F.Carrier) JD JE hArtJE
      ⟨e.toIntertwiningMap, henz⟩
  let K := SmoothRep.subquotient JD U V
  let K' := SmoothRep.subquotient JE U' V'
  have hK' : K'.IsIrreducible :=
    (Weil.IsomorphismInvariance.irreducible_iff ek).mp hK
  have hKJA : SmoothRep.IsSubquotient K JA :=
    smoothSubquotientTransitivity ℂ (L.Levi F.Carrier) JA JD K
      ⟨U, V, ⟨CategoryTheory.Iso.refl _⟩⟩ hJDsub
  have hKJA' : SmoothRep.IsSubquotient K' JA' :=
    smoothSubquotientTransitivity ℂ (L.Levi F.Carrier) JA' JE K'
      ⟨U', V', ⟨CategoryTheory.Iso.refl _⟩⟩ hJEsub
  obtain ⟨SK, UK, ⟨eK⟩⟩ := hKJA
  obtain ⟨SK', UK', ⟨eK'⟩⟩ := hKJA'
  obtain ⟨i, ⟨ei⟩⟩ :=
    simpleSubquotientFactor.{0, uF, max uF uV, max uF uV}
      ℂ (L.Levi F.Carrier) JA r sr hsrSimple K SK UK hK ⟨SmoothRep.equivOfIso eK⟩
  obtain ⟨j, ⟨ej⟩⟩ :=
    simpleSubquotientFactor.{0, uF, max uF uW, max uF uW}
      ℂ (L.Levi F.Carrier) JA' t st hstSimple K' SK' UK' hK' ⟨SmoothRep.equivOfIso eK'⟩
  obtain ⟨esi⟩ := hsr i
  obtain ⟨esj⟩ := hst j
  have hσK' : RepresentationsAssociated B L σ.representation K'.representation :=
    ⟨(er i).val.val, (er i).property, ⟨(ei.trans esi).symm.trans ek⟩⟩
  have hτK' : RepresentationsAssociated C L τ.representation K'.representation :=
    ⟨(et j).val.val, (et j).property, ⟨(ej.trans esj).symm⟩⟩
  exact representationAssociationTransitivity F.Carrier n B L C σ K' τ
    σ.representation K'.representation τ.representation hσK'
    (representationAssociationSymmetry F.Carrier n C L τ K'
      τ.representation K'.representation hτK')

end Langlands.CuspidalSupport.AssociationReverse

namespace Langlands.CuspidalSupport

universe uF uV uW

/-- The full common-subquotient-to-association implication for every rank. -/
theorem cuspidalInductionReverseAssociation
    (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) :
    CuspidalInductionReverseAssociationTheorem.{uF, uV, uW} F T n :=
  AssociationReverse.commonSubquotientAssociated p F T n

end Langlands.CuspidalSupport
