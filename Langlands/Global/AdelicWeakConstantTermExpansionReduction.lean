import Langlands.Global.AdelicSquareIntegrableHeightExpansion
import Langlands.Global.AdelicWeakConstantTermTop

/-! # Vanishing from square-integrable expansions of weak constant terms -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions

/-- All standard weak constant terms of a logarithmically square-integrable automorphic form
exist. This follows from ordinary constant-term automorphy and the finite expansion (3.2) of
Delorme, with the definition of the weak term in Definition 3.7. -/
def LogSquareIntegrableWeakConstantTermExistenceStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (fam : StandardParabolicFamily F G), IsIwasawaCompact (fam.p fam.bot) K →
    ∀ Φ : AdelicGroupPoints F G → ℂ,
      IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc Φ →
    ∀ J : StandardIndex F G fam.i fam.ν,
      ∃ ψ : AdelicGroupPoints F G → ℂ,
        fam.IsWeakConstantTerm hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J Φ ψ

/-- If the weak constant terms strictly below `P` vanish, the weak term at `P` has a finite
expansion with `A²_P` coefficients. Delorme Lemmas 3.8 and 3.10 (i) give the source
argument with a compact in good position. The analytic premise here asks for the expansion
for every allowed Iwasawa compact, with its own height and square-integrability condition. -/
def LogSquareIntegrableWeakConstantTermExpansionStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (fam : StandardParabolicFamily F G) (hK : IsIwasawaCompact (fam.p fam.bot) K)
      (Φ : AdelicGroupPoints F G → ℂ),
      IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc Φ →
    ∀ (J : StandardIndex F G fam.i fam.ν) (ψ : AdelicGroupPoints F G → ℂ),
      fam.IsWeakConstantTerm hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J Φ ψ →
      (∀ Q : StandardIndex F G fam.i fam.ν, Q < J →
        fam.IsWeakConstantTerm hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho Q Φ 0) →
      haveI : IsClosedImmersion (fam.p J).hom.hom.left := (fam.isCompatible J).parabolic.isClosedSubgroup
      fam.HasSquareIntegrableHeightExpansion rho hsmooth hcalc J (fam.isIwasawaCompact_of_bot hK J) ψ

/-- The existence and expansion inputs give Delorme's vanishing conclusion by induction on the
number of simple roots in the index. Orthogonality on every split-component slice kills each
finite height expansion, including the full-group weak term. -/
theorem temperedWeakConstantTermVanishing_of_expansion
    (hExists : LogSquareIntegrableWeakConstantTermExistenceStatement)
    (hExpand : LogSquareIntegrableWeakConstantTermExpansionStatement) :
    TemperedWeakConstantTermVanishingStatement := by
  classical
  intro F _ _ G _ _ _ hG K N d rho hsmooth hcalc hKmax hrho fam hK Φ hΦ hOrth g
  let Kinf := K.comap (ofInfinite F G).toMonoidHom
  let Idx := StandardIndex F G fam.i fam.ν
  have hFin := fam.maximalSplit.isSplitSubtorus.1.finite_simpleRelativeRoots fam.i fam.ν
  let indexSize (J : Idx) : ℕ := (hFin.subset J.property).toFinset.card
  have hSize {Q J : Idx} (hQJ : Q < J) : indexSize Q < indexSize J :=
    Finset.card_lt_card (Set.Finite.toFinset_strictMono (show Q.val ⊂ J.val from hQJ))
  have hZero (n : ℕ) (J : Idx) (hSizeJ : indexSize J = n) (ψ : AdelicGroupPoints F G → ℂ)
      (hψ : fam.IsWeakConstantTerm hsmooth Kinf rho J Φ ψ) : ψ = 0 := by
    induction n using Nat.strong_induction_on generalizing J ψ with
    | h n ih =>
      have hLower (Q : Idx) (hQ : Q < J) : fam.IsWeakConstantTerm hsmooth Kinf rho Q Φ 0 := by
        obtain ⟨w, hw⟩ := hExists F G hG K rho hsmooth hcalc hKmax hrho fam hK Φ hΦ Q
        have hlt := (hSize hQ).trans_eq hSizeJ
        have hz := ih (indexSize Q) hlt Q rfl w hw
        simpa only [hz] using hw
      let : IsClosedImmersion (fam.p J).hom.hom.left := (fam.isCompatible J).parabolic.isClosedSubgroup
      exact fam.eq_zero_of_squareIntegrableHeightExpansion_of_orthogonal rho hsmooth hcalc J
        (fam.isIwasawaCompact_of_bot hK J)
        (hExpand F G hG K rho hsmooth hcalc hKmax hrho fam hK Φ hΦ J ψ hψ hLower) (hOrth J ψ hψ)
  exact congrFun (hZero _ fam.top rfl Φ (fam.isWeakConstantTerm_top hΦ)) g

end Langlands.Global
