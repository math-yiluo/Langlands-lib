import Langlands.Global.AdelicEisensteinFamilyRegularComparison
import Langlands.Global.AdelicEisensteinStandardFamilyComparisonStatement

/-! # The family comparison for standard data and a compact in good position -/

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic Langlands.Aubert.General.RationalPointFamily

/-- **The standard case.** `StandardEisensteinFamilyComparisonStatement` gives the family
comparison for standard parabolics `P_I`, `P_Q` of one family with their standard
presentations, a normalizer point matching the simple roots and a compact in good position.
Families indexed by arbitrary finite types are reindexed by `Fin`. -/
theorem FamilyRegularComparison.of_standard
    (hfam : StandardEisensteinFamilyComparisonStatement.{u})
    {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (I Q : StandardIndex F G fam.i fam.ν)
    [Fintype (relativeWeylGroup fam.i)] [IsClosedImmersion (fam.p I).hom.hom.left]
    [Mono (CommGroupScheme.groupHom (fam.f I)).hom.hom.left]
    [IsClosedImmersion (fam.p Q).hom.hom.left]
    [Mono (CommGroupScheme.groupHom (fam.f Q)).hom.hom.left]
    [IsAffine (fam.P I).X.left] [IsAffine (fam.P Q).X.left] [IsAffine (fam.U Q).X.left]
    (n : normalizerPoints fam.i) (c : fam.M Q ⟶ fam.M I) (proj : fam.P Q ⟶ fam.M Q)
    (hproj : fam.l Q ≫ proj = 𝟙 (fam.M Q))
    (hc : IsWeylConjugation (fam.p I) (fam.l I) (fam.p Q) (fam.l Q) n.val c)
    (hIQ : ∀ α ∈ I.val, schemeWeylCharacterAction fam.i
      (QuotientGroup.mk n : relativeWeylGroup fam.i) α ∈ Q.val)
    (hQI : ∀ α ∈ Q.val, schemeWeylCharacterAction fam.i
      ((QuotientGroup.mk n : relativeWeylGroup fam.i)⁻¹) α ∈ I.val)
    {K : Subgroup (AdelicGroupPoints F G)} (hKI : IsIwasawaCompact (fam.p I) K)
    (hKQ : IsIwasawaCompact (fam.p Q) K) (hKmax : IsMaximalCompactSubgroup F G K)
    (hK0 : IsIwasawaCompact (fam.p ⟨∅, Set.empty_subset _⟩) K)
    (hKlevi : ∀ J : StandardIndex F G fam.i fam.ν, IsMaximalCompactSubgroup F (fam.M J)
      (K.comap (map F (fam.M J) G (fam.l J ≫ fam.p J)).toMonoidHom))
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hrho : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) :
    FamilyRegularComparison.{u, v, w} (fam.iU I) (fam.l I)
      (⟨⟨fam.T, fam.i, fam.ν, I.val, fam.f I⟩, fam.isCompatible I⟩ :
        ParabolicRootPresentation (fam.p I) (fam.l I) (fam.a I))
      (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1
      fam.maximalSplit.isSplitSubtorus.1 (fam.iU Q) (fam.l Q)
      (⟨⟨fam.T, fam.i, fam.ν, Q.val, fam.f Q⟩, fam.isCompatible Q⟩ :
        ParabolicRootPresentation (fam.p Q) (fam.l Q) (fam.a Q))
      (fam.isCompatible Q).splitComponent.isCentralSplitTorus.1.1
      fam.maximalSplit.isSplitSubtorus.1 proj n.val c hKI hKQ rho hsmooth hcalc := by
  classical
  intro Ix _ φ b Db hφ hb EP DP hEP hEPser Jx _ ψ coeff D hψ hcoeff hint R
  let eI := Fintype.equivFin Ix
  let eJ := Fintype.equivFin Jx
  obtain ⟨Rp, hRp⟩ := hEPser
  obtain ⟨Ri, hRi⟩ := hint
  obtain ⟨m, e, O, hO, hOne, hOx⟩ := hfam F G fam I Q n c proj hproj hc hIQ hQI K hKI hKQ hKmax
    hK0 hKlevi rho hsmooth hcalc hrho (fun j => φ (eI.symm j)) (fun j => b (eI.symm j)) Db
    (fun j => hφ _) (fun j => hb _) EP DP hEP
    ⟨Rp, fun lam hlam g => by
      rw [hRp lam hlam g]
      exact (eI.symm.sum_comp (fun x => b x lam * hKI.eisensteinSeries (φ x) lam g)).symm⟩
    (Fintype.card Jx) (fun j => ψ (eJ.symm j)) (fun j => coeff (eJ.symm j)) D (fun j => hψ _)
    (fun j => hcoeff _)
    ⟨Ri, fun lam hlam g => by
      rw [eI.symm.sum_comp (fun x => b x lam *
          hKI.intertwiningOperator hKQ (fam.iU I) (fam.l I) (fam.iU Q) c proj n.val (φ x) lam g),
        hRi lam hlam g]
      exact (eJ.symm.sum_comp (fun i => coeff i lam * ψ i g)).symm⟩ R
  refine ⟨m, e, O, hO, hOne, fun x hx => ⟨(hOx x hx).1, fun g => ?_⟩⟩
  rw [(hOx x hx).2 g]
  exact eJ.symm.sum_comp (fun i => coeff i (e x) *
    hKQ.eisensteinSeries (ψ i) (weylParameter (fam.l I) c proj (e x)) g)

end Langlands.Global
