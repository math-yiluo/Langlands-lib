import Langlands.Representation.Classification.BernsteinShiftedHighestDerivativeUnitarizabilityProof
import Langlands.Representation.Classification.BernsteinUnitaryIrreducibilityCriterionStatement
import Langlands.Representation.Classification.SupercuspidalSupportTwist
import Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessProof
import Langlands.Representation.Derivative.GeneralLinearDerivativeFiniteLengthProof
import Langlands.Representation.Filtration.ExactFunctorIrreducibility
import Langlands.Representation.Smooth.Admissibility.FiniteLengthProof
import Langlands.Representation.Smooth.FiniteLengthGrothendieckTwist
import Langlands.Representation.Unitary.AdmissibleSemisimplicityProof
import Langlands.Representation.Unitary.CentralCharacterProof

/-! # Proof of the unitary finite-length highest-derivative irreducibility criterion -/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear HarmonicAnalysis

universe uF uV uG uW

section Semisimple

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Every actual subquotient of a semisimple unitarizable smooth representation is
unitarizable: the quotient map from the subrepresentation splits, so the subquotient
embeds in the ambient representation. -/
theorem isUnitarizable_of_isSubquotient_of_semisimple
    {A D : SmoothRep.{0, uG, uW} ℂ G}
    (hs : Representation.IsSemisimpleRepresentation A.representation)
    (hu : IsUnitarizable A.representation) (hDA : SmoothRep.IsSubquotient D A) :
    IsUnitarizable D.representation := by
  obtain ⟨C, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hDA
  let : IsSemisimpleModule (MonoidAlgebra ℂ G) A.representation.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp hs
  let : IsSemisimpleModule (MonoidAlgebra ℂ G) C.representation.asModule :=
    IsSemisimpleModule.of_injective
      (Representation.IntertwiningMap.equivLinearMapAsModule _ _ (SmoothRep.hom i)) hi
  obtain ⟨s, hs⟩ := IsSemisimpleModule.lifting_property
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _ (SmoothRep.hom q)) hq
    (LinearMap.id : D.representation.asModule →ₗ[MonoidAlgebra ℂ G]
      D.representation.asModule)
  let s' : D.representation.IntertwiningMap C.representation :=
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _).symm s
  have hqs (x : D) : SmoothRep.hom q (s' x) = x :=
    congrArg (fun k : D.representation.asModule →ₗ[MonoidAlgebra ℂ G]
      D.representation.asModule => k x) hs
  refine hu.of_injective ((SmoothRep.hom i).comp s') ?_
  intro x y hxy
  rw [← hqs x, ← hqs y]
  exact congrArg (SmoothRep.hom q) (hi hxy)

end Semisimple

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Compact open subgroups are cofinal among open subgroups of `GL_n(F)`. -/
theorem generalLinear_compactOpen_cofinal (n : ℕ) :
    letI := T.topology
    ∀ K : OpenSubgroup (GeneralLinear n F.Carrier), ∃ L : OpenSubgroup (GeneralLinear n F.Carrier),
      IsCompact (L : Set (GeneralLinear n F.Carrier)) ∧ L ≤ K := by
  let := T.topology
  intro K
  obtain ⟨L, hL, hLK⟩ :=
    T.generalLinearCompactOpen n (K : Set _) (K.isOpen.mem_nhds K.one_mem)
  exact ⟨L, hL, hLK⟩

/-- A finite-length unitarizable smooth representation of `GL_n(F)` is semisimple. -/
theorem isSemisimple_of_hasFiniteLength_of_isUnitarizable {n : ℕ}
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
    (hB : letI := T.topology; B.HasFiniteLength)
    (hBu : letI := T.topology; IsUnitarizable B.representation) :
    letI := T.topology; Representation.IsSemisimpleRepresentation B.representation := by
  let := T.topology
  have := T.generalLinearTopologicalGroup n
  exact admissibleUnitarySemisimplicity.{uF, uV} (GeneralLinear n F.Carrier)
    (generalLinear_compactOpen_cofinal F T n) B B.representation
    (glFiniteLengthAdmissibility.{uF, uV} F T n B hB) hBu

/-- An irreducible unitarizable smooth representation of `GL_n(F)` has Bernstein
central exponent `0`. -/
theorem hasBernsteinCentralExponent_zero_of_isUnitarizable {n : ℕ}
    (E : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
    (hE : letI := T.topology; E.IsIrreducible)
    (hEu : letI := T.topology; IsUnitarizable E.representation) :
    HasBernsteinCentralExponent T E 0 := by
  let := T.topology
  have := T.generalLinearTopologicalGroup n
  obtain ⟨c⟩ := unitarizableCentralCharacter.{uF, uV} E.representation
    (glFiniteLengthAdmissibility.{uF, uV} F T n E
      (SmoothRep.hasFiniteLength_of_isIrreducible hE)) hE hEu
  refine ⟨c.character.comp scalarToCenter, fun a v => c.acts (scalarToCenter a) v,
    fun a => ?_⟩
  rw [Real.rpow_zero]
  exact c.norm_eq_one _

/-- The criterion, assuming the unitarity half of Bernstein's shifted
highest-derivative theorem: for every irreducible unitarizable `π` of positive rank
and every highest positive derivative order of `π`, the shifted highest derivative
`ν^(1/2) π^(h)` is unitarizable. -/
theorem bernsteinUnitaryFiniteLengthIrreducibilityCriterion_of_unitarizability
    (hH : BernsteinShiftedHighestDerivativeUnitarizability.{uF, uV} F T) :
    BernsteinUnitaryFiniteLengthIrreducibilityCriterion.{uF, uV} F T := by
  let := T.topology
  intro N hN ψ A hA hAu hd hpos hirr _
  have hexact := Derivative.generalLinearDerivativeExactness.{uF, max uF uV} F T ψ N
  have hAsemi := isSemisimple_of_hasFiniteLength_of_isUnitarizable F T A hA hAu
  refine ExactFunctorIrreducibility.isIrreducible_of_obj
    (Derivative.generalLinearDerivative T ψ N hd.order hd.le_rank)
    (hexact hd.order hd.le_rank) A hA ?_
    ((SmoothRep.isIrreducible_twist_iff _ (T.isOpen_ker_determinantPowerCharacter _ _) _).mp hirr)
  intro D hD hDA
  have hDu : IsUnitarizable D.representation :=
    isUnitarizable_of_isSubquotient_of_semisimple hAsemi hAu hDA
  let := hD
  have hDne : Nontrivial D :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear N F.Carrier))
      D.representation.asModule
  let hdD := Derivative.chooseGeneralLinearHighestDerivativeOrder T ψ hN D hDne
  -- The derivative of `D` at any order is a subquotient of that of `A`.
  have hsub (k : ℕ) (hk : k ≤ N) : SmoothRep.IsSubquotient
      ((Derivative.generalLinearDerivative T ψ N k hk).obj D)
      ((Derivative.generalLinearDerivative T ψ N k hk).obj A) :=
    ExactSmoothTransport.map_isSubquotient _ (hexact k hk) hDA
  rcases lt_trichotomy hdD.order hd.order with hlt | heq | hgt
  · -- A lower highest order contradicts positivity of `ν^(1/2) A^(d)`.
    exfalso
    let S := shiftedHighestDerivative F T ψ hdD
    have hSu : IsUnitarizable S.representation := hH N hN ψ D hD hDu hdD
    have hSfin : S.HasFiniteLength :=
      (finiteLength_twist_iff _ _).mpr
        (Derivative.generalLinearDerivativeFiniteLength.{uF, max uF uV} F T ψ N
          hdD.order hdD.le_rank D (SmoothRep.hasFiniteLength_of_isIrreducible hD))
    have hSne : Nontrivial S := hdD.nonzero
    obtain ⟨E, hE, hES⟩ := SmoothRep.exists_irreducible_subquotient S hSfin
    have hEu : IsUnitarizable E.representation :=
      isUnitarizable_of_isSubquotient_of_semisimple
        (isSemisimple_of_hasFiniteLength_of_isUnitarizable F T S hSfin hSu) hSu hES
    have hEA : SmoothRep.IsSubquotient E
        (bernsteinShiftedDerivative T ψ A hdD.order hdD.le_rank) :=
      smoothSubquotientTransitivity _ _ _ S E hES
        ((hsub hdD.order hdD.le_rank).twist _ (T.isOpen_ker_determinantPowerCharacter _ _))
    exact lt_irrefl (0 : ℝ) (hpos hdD.order hdD.le_rank hlt 0
      ⟨E, hE, hEA, hasBernsteinCentralExponent_zero_of_isUnitarizable F T E hE hEu⟩)
  · -- The highest order of `D` is the highest order of `A`.
    have key : ∀ (k : ℕ) (hk : k ≤ N), k = hd.order →
        Nontrivial ((Derivative.generalLinearDerivative T ψ N k hk).obj D) →
        Nontrivial ((Derivative.generalLinearDerivative T ψ N hd.order hd.le_rank).obj D) := by
      intro k hk e hne
      subst e
      exact hne
    exact key hdD.order hdD.le_rank heq hdD.nonzero
  · -- A higher order is impossible: `A` has vanishing derivatives there.
    exfalso
    have hAz := hd.higher_vanish hdD.order hdD.le_rank hgt
    obtain ⟨X, i, q, hi, hq⟩ :=
      SmoothRep.isSubquotient_iff_exists.mp (hsub hdD.order hdD.le_rank)
    have hX : Subsingleton X := ⟨fun x y => hi (Subsingleton.elim _ _)⟩
    have hDz : Subsingleton ((Derivative.generalLinearDerivative T ψ N hdD.order
        hdD.le_rank).obj D) := by
      constructor
      intro a b
      obtain ⟨x, rfl⟩ := hq a
      obtain ⟨y, rfl⟩ := hq b
      exact congrArg (SmoothRep.hom q) (hX.elim x y)
    exact (not_nontrivial_iff_subsingleton.mpr hDz) hdD.nonzero

/-- Bernstein 1984, Proposition 8.1(a), for finite-length unitarizable
representations: the unitary finite-length highest-derivative irreducibility
criterion. -/
theorem bernsteinUnitaryFiniteLengthIrreducibilityCriterion :
    BernsteinUnitaryFiniteLengthIrreducibilityCriterion.{uF, uV} F T :=
  bernsteinUnitaryFiniteLengthIrreducibilityCriterion_of_unitarizability F T
    (bernsteinShiftedHighestDerivativeUnitarizability.{uF, uV} F T)

end Langlands.Classification
