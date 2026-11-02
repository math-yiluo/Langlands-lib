import Langlands.Representation.Aubert.General.StandardComplex
import Langlands.Representation.Aubert.General.SupportCategory

/-!
# Finite-length and irreducible consequences of the corrected Theorem 3.6

Proposition targets for Aubert's Corollaire 3.9 (1995, p. 2189) and its
finite-length specialization, stated with the actual terminal cokernel
`E# = StandardComplex.sharpObject … E I` of the normalized smooth complex, the
support category `Alg({I})` of the erratum (p. 4687), the cuspidal series `𝔈(I)`
(Notation 1.6) and Aubert's unadjusted operator `D_G = alternatingOperator`
(Définition 1.5) on the exact finite-length Grothendieck group.

Representations of `G` have carriers in `Type (max uI uG uV)`, the carrier
universe of `E#`, so that `E`, `E#` and `(E#)#` lie in one category and one
Grothendieck group.
-/

open CategoryTheory

namespace Langlands.Aubert.General

universe uI uG uV

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
  (h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J))
  (hclosed : ∀ J, IsClosed (U J : Set G))
  (hδ : ∀ J, IsUnimodularModulus (U J) (hclosed J))
  (hP : Monotone P) (hU : Antitone U)
  (hM : ∀ I, IsClosed (M I : Set G))
  (hL : ∀ (I : Finset ι) (K : Finset I),
    IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
      ((M (leviIndex I K)).subgroupOf (M I)) ((U (leviIndex I K)).subgroupOf (M I)))
  (IsAssociate : Finset ι → Finset ι → G → Prop)

/-- The finite-length obligation for `E#` (needed for Corollaire 3.9 (a)): the
terminal cokernel of a finite-length smooth representation has finite length. -/
def SharpFiniteLengthTarget : Prop :=
  ∀ (I : Finset ι) (E : SmoothRep.{0, uG, max uI uG uV} ℂ G), E.HasFiniteLength →
    (StandardComplex.sharpObject.{uI, uG, max uI uV} P M U h hclosed hδ hP hU E I).HasFiniteLength

/-- The finite-length specialization of the corrected Theorem 3.6 (Corollaire 3.9
(a), extended from `𝔈(I)` to `Alg({I})`): for a finite-length `E ∈ Alg({I})`,
`D_G([E]) = (-1)^{|I|} [E#]` in the exact finite-length Grothendieck group, where
`D_G` is the unadjusted alternating operator built from the finite-length
hypotheses `hfl`. -/
def SharpClassFormulaTarget : Prop :=
  ∀ (hfl : ∀ J, ParabolicFiniteLength.{uG, max uG (max uI uV)} (h J) (hclosed J))
    (I : Finset ι) (E : SmoothRep.{0, uG, max uI uG uV} ℂ G),
    IsInSupportCategory.{uI, uG, max uI uV} P M U h hclosed IsAssociate I (hM I) (hL I) E →
    ∀ (hE : E.HasFiniteLength)
      (hE' : (StandardComplex.sharpObject.{uI, uG, max uI uV}
        P M U h hclosed hδ hP hU E I).HasFiniteLength),
      alternatingOperator.{uI, uG, max uI uV} P M U h hclosed hfl
          (SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation E hE) =
        ((-1 : ℤ) ^ I.card) •
          SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation
            (StandardComplex.sharpObject.{uI, uG, max uI uV} P M U h hclosed hδ hP hU E I) hE'

/-- Retention of the support type: the terminal cokernel of a member of `Alg({I})`
lies in `Alg({I})`. -/
def SharpSupportRetentionTarget : Prop :=
  ∀ (I : Finset ι) (E : SmoothRep.{0, uG, max uI uG uV} ℂ G),
    IsInSupportCategory.{uI, uG, max uI uV} P M U h hclosed IsAssociate I (hM I) (hL I) E →
      IsInSupportCategory.{uI, uG, max uI uV} P M U h hclosed IsAssociate I (hM I) (hL I)
        (StandardComplex.sharpObject.{uI, uG, max uI uV} P M U h hclosed hδ hP hU E I)

/-- Corollaire 3.9 (b): for `E ∈ 𝔈(I)`, the terminal cokernel `E#` is an
irreducible (in particular nonzero) smooth representation. -/
def SharpIrreducibleTarget : Prop :=
  ∀ (I : Finset ι) (E : SmoothRep.{0, uG, max uI uG uV} ℂ G),
    IsInCuspidalSeries.{uI, uG, max uI uV} P M U h hclosed I (hM I) (hL I) E →
      (StandardComplex.sharpObject.{uI, uG, max uI uV} P M U h hclosed hδ hP hU E I).IsIrreducible

/-- Retention of the cuspidal series for `E ∈ 𝔈(I)`: `E#` lies in `𝔈(I')` for a
standard Levi `L_{I'}` associated to `L_I`. -/
def SharpCuspidalSeriesTarget : Prop :=
  ∀ (I : Finset ι) (E : SmoothRep.{0, uG, max uI uG uV} ℂ G),
    IsInCuspidalSeries.{uI, uG, max uI uV} P M U h hclosed I (hM I) (hL I) E →
      ∃ (I' : Finset ι) (n : G), IsAssociate I I' n ∧
        (∀ x : G, x ∈ M I' ↔ n⁻¹ * x * n ∈ M I) ∧
        IsInCuspidalSeries.{uI, uG, max uI uV} P M U h hclosed I' (hM I') (hL I')
          (StandardComplex.sharpObject.{uI, uG, max uI uV} P M U h hclosed hδ hP hU E I)

/-- Corollaire 3.9 (c): for `E ∈ 𝔈(I)`, `(E#)#` is isomorphic to `E` as a smooth
representation. Both cokernels are taken at the degree `|S| - |I|`. -/
def SharpInvolutionTarget : Prop :=
  ∀ (I : Finset ι) (E : SmoothRep.{0, uG, max uI uG uV} ℂ G),
    IsInCuspidalSeries.{uI, uG, max uI uV} P M U h hclosed I (hM I) (hL I) E →
      Nonempty (StandardComplex.sharpObject.{uI, uG, max uI uV} P M U h hclosed hδ hP hU
        (StandardComplex.sharpObject.{uI, uG, max uI uV} P M U h hclosed hδ hP hU E I) I ≅ E)

end Langlands.Aubert.General
