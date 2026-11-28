import Langlands.Global.AdelicEisensteinFamilyCompactChange
import Langlands.Global.AdelicIntertwiningConjugateTarget
import Langlands.Global.AdelicEisensteinConjugateParabolicSeries
import Langlands.Global.AdelicEisensteinRegularityAmbientTransport
import Langlands.Automorphic.GroupSchemeAutomorphicLeftTranslation

/-! # The family comparison under rational conjugation of the target parabolic -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

variable {F : Type u} [Field F] [NumberField F]
  {G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F))}
  {A A' : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [IsAffine Q.X.left] [IsAffine V.X.left]

/-- **Rational conjugation of the target parabolic.** For a rational point `s`, conjugate `Q`
by `s` (with the transported presentation `r'.compAmbientIso (innerIso s)`) and replace `w`
by `s w`. The family comparison for the conjugated target implies the family comparison for
`Q`. The target forms are translated on the left by `s⁻¹`; the series and the intertwining
operators change by the height factors of `s` for the conjugated target. -/
theorem FamilyRegularComparison.of_conjugateTarget
    {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {iU : U ⟶ P} {l : M ⟶ P}
    {a : A.toGrp ⟶ M} {r : ParabolicRootPresentation p l a}
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    {hA : IsSplitTorus A.toGrp} {hT : IsSplitTorus r.data.T.toGrp}
    {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left] {iV : V ⟶ Q} {l' : M' ⟶ Q}
    [IsClosedImmersion (iV ≫ q).hom.hom.left]
    {a' : A'.toGrp ⟶ M'} {r' : ParabolicRootPresentation q l' a'}
    [Mono r'.data.i.hom.hom.left] [Fintype (relativeWeylGroup r'.data.i)]
    [Mono (CommGroupScheme.groupHom r'.data.f).hom.hom.left]
    {hA' : IsSplitTorus A'.toGrp} {hT' : IsSplitTorus r'.data.T.toGrp} {π' : Q ⟶ M'}
    {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c : M' ⟶ M}
    (s : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    [IsClosedImmersion (q ≫ (G.innerIso s).hom).hom.hom.left]
    [IsClosedImmersion (iV ≫ q ≫ (G.innerIso s).hom).hom.hom.left]
    [Mono (r'.compAmbientIso (G.innerIso s)).data.i.hom.hom.left]
    [Fintype (relativeWeylGroup (r'.compAmbientIso (G.innerIso s)).data.i)]
    [Mono (CommGroupScheme.groupHom (r'.compAmbientIso (G.innerIso s)).data.f).hom.hom.left]
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) (hV : LeviSubgroup.IsGeometricUnipotentRadical iV)
    (hl' : IsRationalLeviSubgroup l') (hw : IsWeylConjugation p l q l' w c)
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
    (hKQ : IsIwasawaCompact q K) (hKQ' : IsIwasawaCompact (q ≫ (G.innerIso s).hom) K)
    {N d : ℕ} {rho : MatrixRepresentation G (Fin N)}
    {hsmooth : SmoothOfRelativeDimension d G.X.hom}
    {hcalc : AdelicDifferentialCommutator F G hsmooth}
    (h : FamilyRegularComparison.{u, v, w} iU l r hA hT iV l' (r'.compAmbientIso (G.innerIso s))
      hA' hT' π' (s * w) c hK hKQ' rho hsmooth hcalc) :
    FamilyRegularComparison.{u, v, w} iU l r hA hT iV l' r' hA' hT' π' w c hK hKQ rho hsmooth
      hcalc := by
  classical
  intro Ix _ φ b Db hφ hb EP DP hEP hEPser Jx _ ψ coeff D hψ hcoeff hint R
  let t := innerAdelicPoint F G s
  have hIt := fun x => intertwiningConjugateTarget F G P M U Q M' V p iU l q iV l' π' w s c hw
    hU.1.isUnipotent K hK hKQ (φ x) (fun y hy g => (hφ x).1 y (Subgroup.mem_sup_left hy) g)
  have hEt := fun i => eisensteinConjugateParabolicSeries F G Q M' V q iV l' s hl' hV K hKQ (ψ i)
    (hψ i).1
  let W := weylParameter l c π'
  let ℓ : ComplexCharacterParameter F P →ₗ[ℂ] ℂ :=
    (complexParameterPairingAt (hKQ'.height t)).comp (-W)
  have hℓ (lam : ComplexCharacterParameter F P) :
      Complex.exp (ℓ lam) = hKQ'.heightPower (-W lam) t := rfl
  have hℓinv (lam : ComplexCharacterParameter F P) :
      hKQ'.heightPower (-W lam) t * hKQ'.heightPower (W lam) t = 1 := by
    simp only [IsIwasawaCompact.heightPower, map_neg, LinearMap.neg_apply, Complex.exp_neg]
    exact inv_mul_cancel₀ (Complex.exp_ne_zero _)
  let ψ' (i : Jx) : AdelicGroupPoints F G → ℂ := fun y => ψ i (t⁻¹ * y)
  let coeff' (i : Jx) (lam : ComplexCharacterParameter F P) : ℂ :=
    coeff i lam * Complex.exp (ℓ lam)
  have hψ' : ∀ i, IsAutomorphicFunctionOn F G hsmooth hcalc
      (parabolicQuotientSubgroup F (q ≫ (G.innerIso s).hom) iV l')
      (K.comap (ofInfinite F G).toMonoidHom) rho (ψ' i) := fun i => by
    have h1 := IsAutomorphicFunctionOn.leftTranslate hcalc (hψ i) t⁻¹
    rw [inv_inv] at h1
    rw [parabolicQuotientSubgroup_conjugate s]
    exact h1
  have hcoeff' : ∀ i, IsMeromorphicInCoordinatesOn (coeff' i) D :=
    fun i => (hcoeff i).mul_exp ℓ
  have hint' : ∃ R₀ : ℝ, ∀ lam, r.IsRegularParameter hA hT R₀ lam → ∀ g,
      ∑ x, b x lam * hK.intertwiningOperator hKQ' iU l iV c π' (s * w) (φ x) lam g =
        ∑ i, coeff' i lam * ψ' i g := by
    obtain ⟨R₁, hR₁⟩ := hint
    refine ⟨R₁, fun lam hlam g => ?_⟩
    have hg : g = t * (t⁻¹ * g) := by group
    calc
      ∑ x, b x lam * hK.intertwiningOperator hKQ' iU l iV c π' (s * w) (φ x) lam g
          = hKQ'.heightPower (-W lam) t *
              ∑ x, b x lam * hK.intertwiningOperator hKQ iU l iV c π' w (φ x) lam (t⁻¹ * g) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => ?_
            obtain ⟨-, hQ', hM⟩ := hIt x
            conv_lhs => rw [hg]
            rw [hM lam (t⁻¹ * g)]
            ring
      _ = hKQ'.heightPower (-W lam) t * ∑ i, coeff i lam * ψ i (t⁻¹ * g) := by
            rw [hR₁ lam hlam (t⁻¹ * g)]
      _ = ∑ i, coeff' i lam * ψ' i g := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [coeff', ψ', hℓ]
            ring
  obtain ⟨m, e, O, hO, hOne, hOx⟩ := h φ b Db hφ hb EP DP hEP hEPser ψ' coeff' D hψ' hcoeff'
    hint' R
  refine ⟨m, e, O, hO, hOne, fun x hx => ⟨?_, fun g => ?_⟩⟩
  · exact (eisensteinRegularityAmbientTransport F G G Q M' A' q l' a' r' (G.innerIso s) hA' hT' R
      (W (e x))).mp (hOx x hx).1
  · rw [(hOx x hx).2 g]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨hK', hE⟩ := hEt i
    rw [hE (W (e x)) g]
    simp only [coeff', hℓ]
    linear_combination (coeff i (e x) * hKQ.eisensteinSeries (ψ i) (W (e x)) g) * hℓinv (e x)

end Langlands.Global
