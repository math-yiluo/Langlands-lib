import Langlands.Global.AdelicEisensteinFiniteCompactChangeProof
import Langlands.Global.AdelicEisensteinTwistComparison
import Langlands.Global.AdelicIntertwiningIntegrability
import Langlands.Global.AdelicMaximalCompactFactors

/-! # Eisenstein operators under a finite change of compact -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Normal convergence supplies summability of the actual terms at every adelic
argument above one regularity threshold. -/
theorem EisensteinAbsoluteConvergenceStatement.exists_summable_eisensteinTerm
    (hconv : EisensteinAbsoluteConvergenceStatement.{u})
    {F : Type u} [Field F] [NumberField F]
    {G P M U : GroupScheme (Spec (CommRingCat.of F))}
    {A : CommGroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [IsAffine P.X.left]
    {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {iU : U ⟶ P} {l : M ⟶ P}
    {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (hG : IsConnectedReductive G) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (hmax : IsMaximalCompactSubgroup F G K) (hrho : IsClosedSubgroup rho)
    {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
      (K.comap (ofInfinite F G).toMonoidHom) rho φ) :
    ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
      ∀ g, Summable (hK.eisensteinTerm φ lam g) := by
  obtain ⟨R, hR⟩ := hconv F G P M U A p iU l a r hA hT hG hU K hK rho hsmooth hcalc φ hmax hrho hφ
  obtain ⟨n, ⟨e⟩⟩ := exists_complexParameterEquiv hG r.isCompatible.parabolic
  refine ⟨R, fun lam hlam g => ?_⟩
  have hsingle : ∀ s ∈ ({e.symm lam} : Set (Fin n → ℂ)), r.IsRegularParameter hA hT R (e s) := by
    intro s hs
    rw [Set.mem_singleton_iff.mp hs, e.apply_symm_apply]
    exact hlam
  obtain ⟨b, hb, hbound⟩ := hR {g} isCompact_singleton n e {e.symm lam} isCompact_singleton hsingle
  apply hb.of_norm_bounded
  intro x
  simpa only [e.apply_symm_apply] using
    hbound x g (Set.mem_singleton g) (e.symm lam) (Set.mem_singleton (e.symm lam))

/-- Maximal Iwasawa compacts with the same infinite projection give the same finite
comparison for both the actual Eisenstein series and the twisted intertwining operator.
One regularity threshold works for the fixed finite family of inducing functions. -/
def EisensteinFiniteCompactOperatorComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine Q.X.left] [IsAffine V.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (q : Q ⟶ G) [IsClosedImmersion q.hom.hom.left]
    (iV : V ⟶ Q) (l' : M' ⟶ Q) [IsClosedImmersion (iV ≫ q).hom.hom.left]
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M) (π' : Q ⟶ M'),
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    IsParabolicSubgroup q → LeviSubgroup.IsGeometricUnipotentRadical iV →
    IsRationalLeviSubgroup l' → IsIso (subgroupMultiplication l' iV) →
    IsWeylConjugation p l q l' w c →
    ∀ (K L : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
      (hL : IsIwasawaCompact p L) (hKQ : IsIwasawaCompact q K) (hLQ : IsIwasawaCompact q L),
      IsMaximalCompactSubgroup F G K → IsMaximalCompactSubgroup F G L →
      K.map (infinite F G).toMonoidHom = L.map (infinite F G).toMonoidHom →
      ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
        (hsmooth : SmoothOfRelativeDimension d G.X.hom)
        (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
        IsClosedSubgroup rho →
        IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
          (K.comap (ofInfinite F G).toMonoidHom) rho φ →
        ∃ (S : Finset (RealCharacterDual F P)) (cut : RealCharacterDual F P → AdelicGroupPoints F G → ℂ),
          (∀ v ∈ S, IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
            (L.comap (ofInfinite F G).toMonoidHom) rho (cut v)) ∧
          ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
            (hK.eisensteinSeries φ lam g =
              ∑ v ∈ S, Complex.exp (complexParameterPairing F P lam v) *
                hL.eisensteinSeries (cut v) lam g) ∧
            (hKQ.parameterTwist (hK.intertwiningOperator hKQ iU l iV c π' w φ lam)
                (weylParameter l c π' lam) g =
              ∑ v ∈ S, Complex.exp (complexParameterPairing F P lam v) *
                hLQ.parameterTwist (hL.intertwiningOperator hLQ iU l iV c π' w (cut v) lam)
                  (weylParameter l c π' lam) g)

/-- The cutoffs for a finite change of compact are automorphic for the common
infinite subgroup. Their regular-region convergence upgrades the twist identity
to identities of both actual operators. -/
theorem eisensteinFiniteCompactOperatorComparison :
    EisensteinFiniteCompactOperatorComparisonStatement.{u} := by
  classical
  intro F _ _ G P M U Q M' V A _ _ _ _ _ _ p _ iU l a r _ _ _ hA hT q _ iV l' _ w c π'
    hG hU hq hV hl' hmul hw K L hK hL hKQ hLQ hmaxK hmaxL hinf N d rho hsmooth hcalc φ hrho hφ
  have hfactor (H : Subgroup (AdelicGroupPoints F G)) (hH : IsMaximalCompactSubgroup F G H) :
      H.comap (ofInfinite F G).toMonoidHom = H.map (infinite F G).toMonoidHom := by
    ext k
    constructor
    · intro hk
      exact ⟨_, hk, infinite_ofInfinite F G k⟩
    · rintro ⟨x, hx, rfl⟩
      exact ((hH.mem_iff x).mp hx).1
  have hArch : K.comap (ofInfinite F G).toMonoidHom = L.comap (ofInfinite F G).toMonoidHom := by
    rw [hfactor K hmaxK, hfactor L hmaxL, hinf]
  obtain ⟨S, cut, hcut, htwist⟩ := hφ.exists_parameterTwist_of_infinite_eq iU l hK hL hmaxK hmaxL hinf
  rw [hArch] at hcut
  have hconv (v : S) : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
      Summable (hL.eisensteinTerm (cut v) lam g) ∧
      Integrable (hL.intertwiningIntegrand iU (iV ≫ q) w (cut v) lam g)
        (intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w)) := by
    obtain ⟨Rs, hs⟩ := eisensteinAbsoluteConvergence.exists_summable_eisensteinTerm r hA hT hG hU
      hL rho hsmooth hcalc hmaxL hrho (hcut v v.2)
    obtain ⟨Ri, hi⟩ := intertwiningIntegrability F G P M U Q M' V A p iU l a r hA hT
      q iV l' w c hG hU hq hV hl' hmul hw L hL rho hsmooth hcalc (cut v) hmaxL hrho (hcut v v.2)
    exact ⟨max Rs Ri, fun lam hreg g =>
      ⟨hs lam (fun α hα => (le_max_left _ _).trans_lt (hreg α hα)) g,
        hi lam (fun α hα => (le_max_right _ _).trans_lt (hreg α hα)) g⟩⟩
  choose R hR using hconv
  let B : ℝ := ∑ v : S, max (R v) 0
  have hB (v : S) : R v ≤ B :=
    (le_max_left (R v) 0).trans
      (Finset.single_le_sum (f := fun x => max (R x) 0)
        (fun x _ => le_max_right (R x) 0) (Finset.mem_univ v))
  refine ⟨S, cut, hcut, B, fun lam hlam g => ?_⟩
  have hregular (v : S) : r.IsRegularParameter hA hT (R v) lam :=
    fun α hα => (hB v).trans_lt (hlam α hα)
  let coeff (v : RealCharacterDual F P) := Complex.exp (complexParameterPairing F P lam v)
  exact ⟨hK.eisensteinSeries_eq_finset_sum_of_twist hL S coeff φ cut lam (htwist lam) g
      (fun v hv => (hR ⟨v, hv⟩ lam (hregular ⟨v, hv⟩) g).1),
    hK.parameterTwist_intertwiningOperator_eq_finset_sum_of_twist hL hKQ hLQ S coeff φ cut lam
      (htwist lam) iU l iV c π' w g (fun v hv => (hR ⟨v, hv⟩ lam (hregular ⟨v, hv⟩) g).2)⟩

end Langlands.Global
