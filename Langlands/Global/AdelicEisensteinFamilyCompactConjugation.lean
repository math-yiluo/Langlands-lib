import Langlands.Global.AdelicEisensteinFamilyCompactChange
import Langlands.Global.AdelicEisensteinConjugateCompactProof
import Langlands.Automorphic.GroupSchemeAutomorphicRightTranslation

/-! # The family comparison under archimedean conjugation of the Iwasawa compact -/

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

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left] [IsAffine Q.X.left]
  [IsAffine V.X.left] in
/-- Conjugating an adelic subgroup by an archimedean point `a⁻¹` and then conjugating its
archimedean part back by `a` recovers the archimedean part. -/
theorem comap_ofInfinite_map_conj (K : Subgroup (AdelicGroupPoints F G))
    (a : InfiniteAdelicGroupPoints F G) :
    ((K.map (MulAut.conj (ofInfinite F G a)⁻¹).toMonoidHom).comap
        (ofInfinite F G).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      K.comap (ofInfinite F G).toMonoidHom := by
  ext y
  simp only [Subgroup.mem_map_equiv, Subgroup.mem_comap, MulAut.conj_symm_apply, map_mul,
    map_inv, ContinuousMonoidHom.coe_toMonoidHom]
  constructor
  · intro h
    simpa [mul_assoc] using h
  · intro h
    simpa [mul_assoc] using h

/-- **Archimedean conjugation of the Iwasawa compact.** Let `t = ofInfinite a` be an archimedean
point and `K' = t⁻¹ K t`. The family comparison for `K` implies the family comparison for `K'`.
Right translation by `t` carries the data for `K'` to data for `K`. The series and operators
for `K'` at `g t` are those for `K` at `g`, up to the height factors at `t`, which are
exponentials of linear forms in the parameter. -/
theorem FamilyRegularComparison.of_conjugateCompact
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
    {K : Subgroup (AdelicGroupPoints F G)} (hKP : IsIwasawaCompact p K)
    (hKQ : IsIwasawaCompact q K) (s : InfiniteAdelicGroupPoints F G)
    (hKP' : IsIwasawaCompact p (K.map (MulAut.conj (ofInfinite F G s)⁻¹).toMonoidHom))
    (hKQ' : IsIwasawaCompact q (K.map (MulAut.conj (ofInfinite F G s)⁻¹).toMonoidHom))
    {N d : ℕ} {rho : MatrixRepresentation G (Fin N)}
    {hsmooth : SmoothOfRelativeDimension d G.X.hom}
    {hcalc : AdelicDifferentialCommutator F G hsmooth}
    (h : FamilyRegularComparison.{u, v, w} iU l r hA hT iV l' r' hA' hT' π' w c hKP hKQ rho
      hsmooth hcalc) :
    FamilyRegularComparison.{u, v, w} iU l r hA hT iV l' r' hA' hT' π' w c hKP' hKQ' rho
      hsmooth hcalc := by
  classical
  intro Ix _ φ b Db hφ hb EP DP hEP hEPser Jx _ ψ coeff D hψ hcoeff hint R
  let t := ofInfinite F G s
  obtain ⟨hP₁, hQ₁, hid⟩ := eisensteinConjugateCompactTransport F G P M U Q M' V p iU l q iV c π' w
    K hKP hKQ t
  have hKinf := comap_ofInfinite_map_conj K s
  -- the translated data
  let φ' (x : Ix) : AdelicGroupPoints F G → ℂ := fun y => φ x (y * t)
  let ψ' (i : Jx) : AdelicGroupPoints F G → ℂ := fun y => ψ i (y * t)
  let ℓP : ComplexCharacterParameter F P →ₗ[ℂ] ℂ := -complexParameterPairingAt (hKP'.height t)
  let ℓQ : ComplexCharacterParameter F P →ₗ[ℂ] ℂ :=
    (complexParameterPairingAt (hKQ'.height t)).comp (weylParameter l c π')
  let EP' (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) : ℂ :=
    EP lam (g * t) * Complex.exp (ℓP lam)
  let coeff' (i : Jx) (lam : ComplexCharacterParameter F P) : ℂ :=
    coeff i lam * Complex.exp (ℓQ lam) * Complex.exp (ℓP lam)
  have hP'eq (lam : ComplexCharacterParameter F P) :
      hKP'.heightPower lam t * Complex.exp (ℓP lam) = 1 := by
    simp only [IsIwasawaCompact.heightPower, ℓP, LinearMap.neg_apply, complexParameterPairingAt,
      LinearMap.coe_mk, AddHom.coe_mk, Complex.exp_neg]
    exact mul_inv_cancel₀ (Complex.exp_ne_zero _)
  have hQ'eq (lam : ComplexCharacterParameter F P) :
      hKQ'.heightPower (-weylParameter l c π' lam) t * Complex.exp (ℓQ lam) = 1 := by
    simp only [IsIwasawaCompact.heightPower, ℓQ, LinearMap.comp_apply, complexParameterPairingAt,
      LinearMap.coe_mk, AddHom.coe_mk, map_neg, LinearMap.neg_apply, Complex.exp_neg]
    exact inv_mul_cancel₀ (Complex.exp_ne_zero _)
  have hQ'pos (lam : ComplexCharacterParameter F P) :
      Complex.exp (ℓQ lam) = hKQ'.heightPower (weylParameter l c π' lam) t := rfl
  have hφ' : ∀ x, IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
      (K.comap (ofInfinite F G).toMonoidHom) rho (φ' x) := fun x => by
    rw [← hKinf]
    exact IsAutomorphicFunctionOn.infiniteRightTranslate hcalc (hφ x) s
  have hψ' : ∀ i, IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F q iV l')
      (K.comap (ofInfinite F G).toMonoidHom) rho (ψ' i) := fun i => by
    rw [← hKinf]
    exact IsAutomorphicFunctionOn.infiniteRightTranslate hcalc (hψ i) s
  have hEP' : ∀ g, IsMeromorphicInCoordinatesOn (fun lam => EP' lam g) DP :=
    fun g => (hEP (g * t)).mul_exp ℓP
  have hcoeff' : ∀ i, IsMeromorphicInCoordinatesOn (coeff' i) D :=
    fun i => ((hcoeff i).mul_exp ℓQ).mul_exp ℓP
  have hEPser' : ∃ R₀ : ℝ, ∀ lam, r.IsRegularParameter hA hT R₀ lam → ∀ g,
      EP' lam g = ∑ x, b x lam * hKP.eisensteinSeries (φ' x) lam g := by
    obtain ⟨R₁, hR₁⟩ := hEPser
    refine ⟨R₁, fun lam hlam g => ?_⟩
    change EP lam (g * t) * Complex.exp (ℓP lam) = _
    rw [hR₁ lam hlam (g * t), Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [(hid (φ x) lam g).1, mul_assoc, mul_comm (hKP'.heightPower lam t), mul_assoc, hP'eq,
      mul_one]
  have hint' : ∃ R₀ : ℝ, ∀ lam, r.IsRegularParameter hA hT R₀ lam → ∀ g,
      ∑ x, b x lam * hKP.intertwiningOperator hKQ iU l iV c π' w (φ' x) lam g =
        ∑ i, coeff' i lam * ψ' i g := by
    obtain ⟨R₁, hR₁⟩ := hint
    refine ⟨R₁, fun lam hlam g => ?_⟩
    have h1 := hR₁ lam hlam (g * t)
    have hM (x : Ix) := (hid (φ x) lam g).2.2
    have hc : (hKQ'.heightPower (-weylParameter l c π' lam) t * hKP'.heightPower lam t) *
        (Complex.exp (ℓQ lam) * Complex.exp (ℓP lam)) = 1 := by
      rw [show (hKQ'.heightPower (-weylParameter l c π' lam) t * hKP'.heightPower lam t) *
          (Complex.exp (ℓQ lam) * Complex.exp (ℓP lam)) =
        (hKQ'.heightPower (-weylParameter l c π' lam) t * Complex.exp (ℓQ lam)) *
          (hKP'.heightPower lam t * Complex.exp (ℓP lam)) by ring, hQ'eq, hP'eq, mul_one]
    calc
      ∑ x, b x lam * hKP.intertwiningOperator hKQ iU l iV c π' w (φ' x) lam g
          = (∑ x, b x lam * hKP'.intertwiningOperator hKQ' iU l iV c π' w (φ x) lam (g * t)) *
              (Complex.exp (ℓQ lam) * Complex.exp (ℓP lam)) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [hM x]
            change _ = b x lam * (_ * hKP.intertwiningOperator hKQ iU l iV c π' w (φ' x) lam g) *
              _
            rw [show b x lam * ((hKQ'.heightPower (-weylParameter l c π' lam) t *
                hKP'.heightPower lam t) * hKP.intertwiningOperator hKQ iU l iV c π' w (φ' x) lam g) *
                (Complex.exp (ℓQ lam) * Complex.exp (ℓP lam)) =
              b x lam * hKP.intertwiningOperator hKQ iU l iV c π' w (φ' x) lam g *
                ((hKQ'.heightPower (-weylParameter l c π' lam) t * hKP'.heightPower lam t) *
                  (Complex.exp (ℓQ lam) * Complex.exp (ℓP lam))) by ring, hc, mul_one]
      _ = (∑ i, coeff i lam * ψ i (g * t)) * (Complex.exp (ℓQ lam) * Complex.exp (ℓP lam)) := by
            rw [h1]
      _ = ∑ i, coeff' i lam * ψ' i g := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [coeff', ψ']
            ring
  obtain ⟨m, e, O, hO, hOne, hOx⟩ := h φ' b Db hφ' hb EP' DP hEP' hEPser' ψ' coeff' D hψ' hcoeff'
    hint' R
  refine ⟨m, e, O, hO, hOne, fun x hx => ⟨(hOx x hx).1, fun g => ?_⟩⟩
  have h2 := (hOx x hx).2 (g * t⁻¹)
  change EP (e x) (g * t⁻¹ * t) * Complex.exp (ℓP (e x)) = _ at h2
  rw [inv_mul_cancel_right] at h2
  have hEP'' : EP (e x) g = hKP'.heightPower (e x) t * (EP (e x) g * Complex.exp (ℓP (e x))) := by
    rw [← mul_assoc, mul_comm (hKP'.heightPower (e x) t), mul_assoc, hP'eq, mul_one]
  rw [hEP'', h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hQs := (hid (ψ i) (e x) (g * t⁻¹)).2.1
  rw [inv_mul_cancel_right] at hQs
  rw [hQs, ← hQ'pos]
  simp only [coeff', ψ']
  linear_combination (coeff i (e x) * Complex.exp (ℓQ (e x)) *
    hKQ.eisensteinSeries (fun y => ψ i (y * t)) (weylParameter l c π' (e x)) (g * t⁻¹)) *
      hP'eq (e x)

end Langlands.Global
