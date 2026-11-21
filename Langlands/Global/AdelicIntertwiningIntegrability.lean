import Langlands.Global.AdelicIntertwiningConvergenceProof
import Langlands.Global.EisensteinConstantTerm.Height

/-! # Integrability on the rational intertwining quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

namespace AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G P U V : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}

/-- The integrand on the rational quotient can be evaluated at any representative. -/
theorem IsIwasawaCompact.intertwiningIntegrand_mk (hK : IsIwasawaCompact p K)
    (iU : U ⟶ P) (j : V ⟶ G) (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (hU : IsUnipotent U) {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ)
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G)
    (v : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) :
    hK.intertwiningIntegrand iU j w φ lam g
        (LeftCosetSpace.mk (intertwiningRationalSubgroup F p iU j (innerAdelicPoint F G w)) v) =
      hK.parameterTwist φ lam ((innerAdelicPoint F G w)⁻¹ * (v : AdelicGroupPoints F G) * g) := by
  let wA := innerAdelicPoint F G w
  let Γ := intertwiningRationalSubgroup F p iU j wA
  let x := (LeftCosetSpace.mk Γ v).out
  have hs : x * v⁻¹ ∈ Γ :=
    (LeftCosetSpace.mk_eq_mk_iff Γ v x).mp (LeftCosetSpace.mk_out Γ _).symm
  obtain ⟨u₀, hu₀⟩ := ((mem_intertwiningRationalSubgroup_iff F p iU j wA _).mp hs).2
  change map F U G (iU ≫ p) u₀ =
    wA⁻¹ * ((x : AdelicGroupPoints F G) * (v : AdelicGroupPoints F G)⁻¹) * wA at hu₀
  have hrearr : wA⁻¹ * (x : AdelicGroupPoints F G) * g =
      map F U G (iU ≫ p) u₀ * (wA⁻¹ * (v : AdelicGroupPoints F G) * g) := by
    rw [hu₀]
    group
  change hK.parameterTwist φ lam (wA⁻¹ * (x : AdelicGroupPoints F G) * g) = _
  rw [hrearr]
  unfold IsIwasawaCompact.parameterTwist
  have hmem : map F U G (iU ≫ p) u₀ ∈ parabolicUnipotentImage F p iU := ⟨u₀, rfl⟩
  rw [hφ _ hmem, hK.heightPower_unipotent_mul hU]

/-- A continuous inducing function invariant under the source radical gives a continuous
intertwining integrand on the rational quotient. -/
theorem IsIwasawaCompact.continuous_intertwiningIntegrand (hK : IsIwasawaCompact p K)
    (iU : U ⟶ P) (j : V ⟶ G) (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (hU : IsUnipotent U) {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ)
    (hφc : Continuous φ) (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    Continuous (hK.intertwiningIntegrand iU j w φ lam g) := by
  apply (LeftCosetSpace.continuous_iff _).mpr
  change Continuous (fun v => hK.intertwiningIntegrand iU j w φ lam g (LeftCosetSpace.mk _ v))
  simp_rw [hK.intertwiningIntegrand_mk iU j w hU hφ]
  exact (hK.continuous_parameterTwist hφc lam).comp
    ((continuous_const.mul continuous_subtype_val).mul continuous_const)

end AdelicGroupPoints

open AdelicGroupPoints

/-- In the regular region of the adelic intertwining convergence theorem, the actual
intertwining integrand is Bochner integrable for every adelic argument. -/
def IntertwiningIntegrabilityStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine V.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (q : Q ⟶ G) (iV : V ⟶ Q) (l' : M' ⟶ Q) [IsClosedImmersion (iV ≫ q).hom.hom.left]
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M),
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    IsParabolicSubgroup q → LeviSubgroup.IsGeometricUnipotentRadical iV →
    IsRationalLeviSubgroup l' → IsIso (subgroupMultiplication l' iV) →
    IsWeylConjugation p l q l' w c →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
        (K.comap (ofInfinite F G).toMonoidHom) rho φ →
      ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
        ∀ g, Integrable (hK.intertwiningIntegrand iU (iV ≫ q) w φ lam g)
          (intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w))

/-- Continuity on the quotient gives measurability, so the published integrable
majorant implies integrability at each sufficiently regular parameter. -/
theorem intertwiningIntegrability : IntertwiningIntegrabilityStatement.{u} := by
  intro F _ _ G P M U Q M' V A _ _ _ _ _ p _ iU l a r _ _ _ hA hT q iV l' _ w c
    hG hU hq hV hl' hmul hw K hK N d rho hsmooth hcalc φ hmax hrho hφ
  obtain ⟨R, hR⟩ := intertwiningAbsoluteConvergence F G P M U Q M' V A p iU l a r hA hT
    q iV l' w c hG hU hq hV hl' hmul hw K hK rho hsmooth hcalc φ hmax hrho hφ
  obtain ⟨n, ⟨e⟩⟩ := exists_complexParameterEquiv hG r.isCompatible.parabolic
  let j := iV ≫ q
  let Γ := intertwiningRationalSubgroup F p iU j (innerAdelicPoint F G w)
  have hclosed := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : LocallyCompactSpace (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) :=
    hclosed.locallyCompactSpace
  let : PolishSpace (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) :=
    hclosed.polishSpace
  let : BorelSpace (LeftCosetSpace Γ) :=
    LeftCosetSpace.discreteQuotientBorelSpace Γ
      (isDiscrete_intertwiningRationalSubgroup F p iU j (innerAdelicPoint F G w))
  have hinv : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ :=
    fun x hx g => hφ.1 x (Subgroup.mem_sup_left hx) g
  refine ⟨R, fun lam hlam g => ?_⟩
  have hsingle : ∀ s ∈ ({e.symm lam} : Set (Fin n → ℂ)),
      r.IsRegularParameter hA hT R (e s) := by
    intro s hs
    rw [Set.mem_singleton_iff.mp hs, e.apply_symm_apply]
    exact hlam
  obtain ⟨b, hb, hbound⟩ := hR {g} isCompact_singleton n e {e.symm lam} isCompact_singleton hsingle
  refine hb.mono' (hK.continuous_intertwiningIntegrand iU j w hU.1.isUnipotent
    hinv hφ.2.1.1 lam g).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  simpa only [e.apply_symm_apply] using
    hbound x g (Set.mem_singleton g) (e.symm lam) (Set.mem_singleton (e.symm lam))

end Langlands.Global
