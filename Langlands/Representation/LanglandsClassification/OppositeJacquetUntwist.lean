import Langlands.Representation.LanglandsClassification.LeviPositiveUnramifiedParameter
import Langlands.Representation.LanglandsClassification.JacquetExponentSubrepresentation
import Langlands.Representation.Smooth.Admissibility.EmbeddingProof
import Langlands.Representation.Exponents.GeometricLemmaExponentTransfer

/-! # Unitary-component untwists of actual opposite Jacquet subrepresentations

An actual opposite Jacquet exponent determines a positive unramified Levi
character. An irreducible Jacquet subrepresentation carrying that exponent
becomes a representation with unitary split-component character after the
inverse twist. Source admissibility and Jacquet finite length remain explicit.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic.OppositeStandardJacquetFamily

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

local instance untwistAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))

local instance untwistLeviPointTopology (J : StandardJacquetFamily.Index i ν) :
    TopologicalSpace (rationalPoints (StandardJacquetFamily.datum i ν hG hi hν J).M) :=
  leviPointTopology (StandardJacquetFamily.datum i ν hG hi hν J).l
    (StandardJacquetFamily.datum i ν hG hi hν J).hl

/-- The actual opposite normalized Jacquet module on the original standard
Levi points, with their canonical topology. -/
abbrev leviJacquetObject (J : StandardJacquetFamily.Index i ν) :
    letI := leviPointTopology
      (StandardJacquetFamily.datum i ν hG hi hν J).l
      (StandardJacquetFamily.datum i ν hG hi hν J).hl
    SmoothRep.{0, u, v} ℂ (rationalPoints (StandardJacquetFamily.datum i ν hG hi hν J).M) :=
  (leviJacquetFunctor (datum i ν hG hi hν J).p (datum i ν hG hi hν J).l
    (datum i ν hG hi hν J).r (datum i ν hG hi hν J).hp
    (datum i ν hG hi hν J).hr (datum i ν hG hi hν J).hl
    (datum i ν hG hi hν J).hmul).obj π

/-- Divide the actual exponent by the positive unramified realization on
its original component, as an actual character. -/
def unitaryComponentCharacter (x : exponents i ν hG hi hν π) :
    rationalPoints (component i ν hG hi hν x.1).A.toGrp →* ℂˣ :=
  letI := leviPointTopology
    (StandardJacquetFamily.datum i ν hG hi hν x.1).l
    (StandardJacquetFamily.datum i ν hG hi hν x.1).hl
  x.2.val / (positiveUnramifiedCharacter i ν hG hi hν π x).val.toMonoidHom.comp
    (rationalPoints.map (component i ν hG hi hν x.1).a)

/-- The quotient character is unitary at every actual component point. -/
theorem norm_unitaryComponentCharacter (x : exponents i ν hG hi hν π)
    (t : rationalPoints (component i ν hG hi hν x.1).A.toGrp) :
    ‖(unitaryComponentCharacter i ν hG hi hν π x t : ℂ)‖ = 1 :=
  norm_exponent_div_positiveUnramifiedCharacter i ν hG hi hν π x t

/-- The realizing character is smooth on the original actual Levi. -/
theorem positiveUnramifiedCharacter_isOpen_ker (x : exponents i ν hG hi hν π) :
    letI := leviPointTopology
      (StandardJacquetFamily.datum i ν hG hi hν x.1).l
      (StandardJacquetFamily.datum i ν hG hi hν x.1).hl
    IsOpen ((positiveUnramifiedCharacter i ν hG hi hν π x).val.toMonoidHom.ker :
      Set (rationalPoints (StandardJacquetFamily.datum i ν hG hi hν x.1).M)) := by
  let S := StandardJacquetFamily.datum i ν hG hi hν x.1
  let := leviPointTopology S.l S.hl
  let := leviPoints_nonarchimedeanGroup S.p S.l S.hp S.hl
  exact Plancherel.unramifiedCharacter_isOpen_ker _ _

/-- The inverse realizing character is smooth on that same Levi. -/
theorem inversePositiveUnramifiedCharacter_isOpen_ker
    (x : exponents i ν hG hi hν π) :
    letI := leviPointTopology
      (StandardJacquetFamily.datum i ν hG hi hν x.1).l
      (StandardJacquetFamily.datum i ν hG hi hν x.1).hl
    IsOpen (((positiveUnramifiedCharacter i ν hG hi hν π x).val.toMonoidHom⁻¹).ker :
      Set (rationalPoints (StandardJacquetFamily.datum i ν hG hi hν x.1).M)) := by
  let S := StandardJacquetFamily.datum i ν hG hi hν x.1
  let := leviPointTopology S.l S.hl
  have hk : ((positiveUnramifiedCharacter i ν hG hi hν π x).val.toMonoidHom⁻¹).ker =
      (positiveUnramifiedCharacter i ν hG hi hν π x).val.toMonoidHom.ker := by
    ext m
    simp
  rw [hk]
  exact positiveUnramifiedCharacter_isOpen_ker i ν hG hi hν π x

/-- Actual source, inverse twist, unitary scalar action, and retwisting
certificate for a supplied opposite Jacquet exponent. -/
structure UnitaryUntwist (x : exponents i ν hG hi hν π) where
  source :
    letI := leviPointTopology
      (StandardJacquetFamily.datum i ν hG hi hν x.1).l
      (StandardJacquetFamily.datum i ν hG hi hν x.1).hl
    SmoothRep.{0, u, v} ℂ (rationalPoints (StandardJacquetFamily.datum i ν hG hi hν x.1).M)
  source_irreducible : source.IsIrreducible
  inclusion : source ⟶ leviJacquetObject i ν hG hi hν π x.1
  inclusion_injective : Function.Injective (SmoothRep.hom inclusion)
  untwist :
    letI := leviPointTopology
      (StandardJacquetFamily.datum i ν hG hi hν x.1).l
      (StandardJacquetFamily.datum i ν hG hi hν x.1).hl
    SmoothRep.{0, u, v} ℂ (rationalPoints (StandardJacquetFamily.datum i ν hG hi hν x.1).M)
  untwist_eq : untwist = source.twist
    (positiveUnramifiedCharacter i ν hG hi hν π x).val.toMonoidHom⁻¹
    (inversePositiveUnramifiedCharacter_isOpen_ker i ν hG hi hν π x)
  untwist_irreducible : untwist.IsIrreducible
  untwist_admissible : untwist.IsAdmissible
  scalar : Classification.HasScalarCharacter untwist.representation
    (rationalPoints.map (component i ν hG hi hν x.1).a)
    (unitaryComponentCharacter i ν hG hi hν π x)
  recovery :
    letI := leviPointTopology
      (StandardJacquetFamily.datum i ν hG hi hν x.1).l
      (StandardJacquetFamily.datum i ν hG hi hν x.1).hl
    untwist.twist (positiveUnramifiedCharacter i ν hG hi hν π x).val.toMonoidHom
      (positiveUnramifiedCharacter_isOpen_ker i ν hG hi hν π x) ≅ source

set_option maxHeartbeats 400000 in
private theorem leviJacquetObject_isAdmissible
    (J : StandardJacquetFamily.Index i ν) (hadm : π.IsAdmissible) :
    letI := leviPointTopology
      (StandardJacquetFamily.datum i ν hG hi hν J).l
      (StandardJacquetFamily.datum i ν hG hi hν J).hl
    (leviJacquetObject i ν hG hi hν π J).IsAdmissible := by
  let O := datum i ν hG hi hν J
  let : TopologicalSpace (rationalPoints O.M) := leviPointTopology O.l O.hl
  have hJactual : letI := leviPointTopology O.l O.hl
      ((leviJacquetFunctor O.p O.l O.r O.hp O.hr O.hl O.hmul).obj π).IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv
      ((jacquetFunctor O.p O.l O.r O.hp O.hr O.hl O.hmul).obj π).representation
      (leviPointsEquiv O.p O.l O.hp O.hl)
      (arbitraryParabolicJacquetAdmissibility k G hG O.P O.M O.U
        O.p O.l O.r O.hp O.hl O.hr O.hmul π hadm)
  dsimp +instances only [leviJacquetObject, O, datum, leviPointTopology] at hJactual ⊢
  with_reducible exact hJactual

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
set_option maxHeartbeats 400000 in
private theorem exponent_isGeneralized (x : exponents i ν hG hi hν π) :
    IsGeneralizedEigencharacter
      ((leviJacquetObject i ν hG hi hν π x.1).representation.comp
        (rationalPoints.map (component i ν hG hi hν x.1).a)) x.2.val := by
  let O := datum i ν hG hi hν x.1
  let C := component i ν hG hi hν x.1
  have hx := x.2.property
  dsimp only [exponents, taggedActualJacquetExponents, normalizedJacquetExponents,
    Set.mem_ofPred_eq] at hx
  have hx' : IsNormalizedJacquetExponent O.p O.l O.r O.hp O.hl O.hr O.hmul C.ha π
      x.2.val := by
    with_reducible exact hx
  have hgenactual := (isNormalizedJacquetExponent_iff_leviJacquet
    O.p O.l O.r O.hp O.hl O.hr O.hmul C.ha π x.2.val).mp hx'
  dsimp +instances only [leviJacquetObject, O, datum, leviPointTopology] at hgenactual ⊢
  with_reducible exact hgenactual

set_option maxHeartbeats 400000 in
private theorem exists_exponentSubrepresentation (x : exponents i ν hG hi hν π)
    (hadm : π.IsAdmissible)
    (hfinite :
      letI := leviPointTopology
        (StandardJacquetFamily.datum i ν hG hi hν x.1).l
        (StandardJacquetFamily.datum i ν hG hi hν x.1).hl
      (leviJacquetObject i ν hG hi hν π x.1).HasFiniteLength) :
    letI := leviPointTopology
      (StandardJacquetFamily.datum i ν hG hi hν x.1).l
      (StandardJacquetFamily.datum i ν hG hi hν x.1).hl
    ∃ τ : SmoothRep.{0, u, v} ℂ
        (rationalPoints (StandardJacquetFamily.datum i ν hG hi hν x.1).M),
      τ.IsIrreducible ∧ ∃ j : τ ⟶ leviJacquetObject i ν hG hi hν π x.1,
        Function.Injective (SmoothRep.hom j) ∧
          Classification.HasScalarCharacter τ.representation
            (rationalPoints.map (component i ν hG hi hν x.1).a) x.2.val := by
  let S := StandardJacquetFamily.datum i ν hG hi hν x.1
  let := leviPointTopology S.l S.hl
  exact SmoothRep.exists_irreducible_scalarCharacter_subrepresentation
    (leviJacquetObject i ν hG hi hν π x.1)
    (rationalPoints.map (component i ν hG hi hν x.1).a)
    (fun t => (component i ν hG hi hν x.1).ha.isCentralSplitTorus.isCentral.map_mem_center t)
    x.2.val (leviJacquetObject_isAdmissible i ν hG hi hν π x.1 hadm)
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfinite).2
    (exponent_isGeneralized i ν hG hi hν π x)

set_option maxHeartbeats 400000 in
private def exponentSubrepresentation (x : exponents i ν hG hi hν π)
    (hadm : π.IsAdmissible)
    (hfinite :
      letI := leviPointTopology
        (StandardJacquetFamily.datum i ν hG hi hν x.1).l
        (StandardJacquetFamily.datum i ν hG hi hν x.1).hl
      (leviJacquetObject i ν hG hi hν π x.1).HasFiniteLength) :
    letI := leviPointTopology
      (StandardJacquetFamily.datum i ν hG hi hν x.1).l
      (StandardJacquetFamily.datum i ν hG hi hν x.1).hl
    {τ : SmoothRep.{0, u, v} ℂ
        (rationalPoints (StandardJacquetFamily.datum i ν hG hi hν x.1).M) //
      τ.IsIrreducible ∧ ∃ j : τ ⟶ leviJacquetObject i ν hG hi hν π x.1,
        Function.Injective (SmoothRep.hom j) ∧
          Classification.HasScalarCharacter τ.representation
            (rationalPoints.map (component i ν hG hi hν x.1).a) x.2.val} := by
  exact ⟨(exists_exponentSubrepresentation i ν hG hi hν π x hadm hfinite).choose,
    (exists_exponentSubrepresentation i ν hG hi hν π x hadm hfinite).choose_spec⟩

set_option maxHeartbeats 400000 in
private theorem nonempty_unitaryUntwist (x : exponents i ν hG hi hν π)
    (hadm : π.IsAdmissible)
    (hfinite :
      letI := leviPointTopology
        (StandardJacquetFamily.datum i ν hG hi hν x.1).l
        (StandardJacquetFamily.datum i ν hG hi hν x.1).hl
      (leviJacquetObject i ν hG hi hν π x.1).HasFiniteLength) :
    Nonempty (UnitaryUntwist i ν hG hi hν π x) := by
  let S := StandardJacquetFamily.datum i ν hG hi hν x.1
  let C := component i ν hG hi hν x.1
  let := leviPointTopology S.l S.hl
  let τ := exponentSubrepresentation i ν hG hi hν π x hadm hfinite
  let j := τ.property.2.choose
  have hj := τ.property.2.choose_spec.1
  have hscalar := τ.property.2.choose_spec.2
  let ψ := (positiveUnramifiedCharacter i ν hG hi hν π x).val.toMonoidHom
  have hψ := positiveUnramifiedCharacter_isOpen_ker i ν hG hi hν π x
  have hψinv := inversePositiveUnramifiedCharacter_isOpen_ker i ν hG hi hν π x
  let σ := τ.val.twist ψ⁻¹ hψinv
  have hτadm : τ.val.IsAdmissible := isAdmissible_of_injective (SmoothRep.hom j) hj
    (leviJacquetObject_isAdmissible i ν hG hi hν π x.1 hadm)
  refine ⟨?_⟩
  refine
    { source := τ.val
      source_irreducible := τ.property.1
      inclusion := j
      inclusion_injective := hj
      untwist := σ
      untwist_eq := rfl
      untwist_irreducible := (SmoothRep.isIrreducible_twist_iff ψ⁻¹ hψinv τ.val).mpr τ.property.1
      untwist_admissible := (SmoothRep.isAdmissible_twist_iff ψ⁻¹ hψinv τ.val).mpr hτadm
      scalar := ?_
      recovery := SmoothRep.mkIso (equivOfRepresentationEq (twist_twist_inv ψ τ.val.representation)) }
  intro t v
  have hcoeff (a b : ℂˣ) : ((b⁻¹ : ℂˣ) : ℂ) * (a : ℂ) = ((a / b : ℂˣ) : ℂ) := by
    simp only [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val, mul_comm]
  change (((ψ (rationalPoints.map C.a t))⁻¹ : ℂˣ) : ℂ) •
    τ.val.representation (rationalPoints.map C.a t) v = _
  exact (congrArg (fun w : τ.val => (((ψ (rationalPoints.map C.a t))⁻¹ : ℂˣ) : ℂ) • w)
    (hscalar t v)).trans ((smul_smul _ _ _).trans
      (congrArg (fun c : ℂ => c • v) (hcoeff (x.2.val t) (ψ (rationalPoints.map C.a t)))))

set_option maxHeartbeats 400000 in
/-- Construct the actual inverse twist from admissibility of the source
and explicit finite length of its chosen opposite Levi Jacquet module. -/
def irreducibleUnitaryUntwist (x : exponents i ν hG hi hν π)
    (hadm : π.IsAdmissible)
    (hfinite :
      letI := leviPointTopology
        (StandardJacquetFamily.datum i ν hG hi hν x.1).l
        (StandardJacquetFamily.datum i ν hG hi hν x.1).hl
      (leviJacquetObject i ν hG hi hν π x.1).HasFiniteLength) :
    UnitaryUntwist i ν hG hi hν π x :=
  Classical.choice (nonempty_unitaryUntwist i ν hG hi hν π x hadm hfinite)

end Langlands.Aubert.General.RepresentedParabolic.OppositeStandardJacquetFamily
