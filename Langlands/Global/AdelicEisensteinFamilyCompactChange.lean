import Langlands.Global.AdelicEisensteinFamilyRegularComparison
import Langlands.Global.AdelicEisensteinFiniteCompactOperatorComparison

/-! # The family comparison under a finite change of the Iwasawa compact -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

section Meromorphic

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

/-- Multiplying a scalar function meromorphic in linear coordinates by the exponential of a
linear form keeps it meromorphic, with the same domain of holomorphy. -/
theorem _root_.Langlands.Analysis.Meromorphic.IsMeromorphicInCoordinatesOn.mul_exp {b : X → ℂ} {D : Set X}
    (hb : IsMeromorphicInCoordinatesOn b D) (ℓ : X →ₗ[ℂ] ℂ) :
    IsMeromorphicInCoordinatesOn (fun x => b x * Complex.exp (ℓ x)) D := by
  refine ⟨hb.1, fun n e => ?_⟩
  have hlin : Differentiable ℂ (fun z : Fin n → ℂ => ℓ (e z)) :=
    (LinearMap.toContinuousLinearMap (ℓ.comp e.toLinearMap)).differentiable
  have hdiff : DifferentiableOn ℂ (fun z : Fin n → ℂ => Complex.exp (ℓ (e z))) Set.univ :=
    (Complex.differentiable_exp.comp hlin).differentiableOn
  have h1 : DifferentiableOn ℂ (fun _ : Fin n → ℂ => (1 : ℂ)) Set.univ := differentiableOn_const 1
  have hE : IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (fun z : Fin n → ℂ => Complex.exp (ℓ (e z)))
      Set.univ :=
    ⟨isOpen_univ, dense_univ, isHolomorphicOn_iff_differentiableOn_scalar.mpr hdiff,
      fun x => ⟨Set.univ, isOpen_univ, isConnected_univ, Set.mem_univ x, fun _ => 1,
        fun z => Complex.exp (ℓ (e z)), h1.mdifferentiableOn, ⟨x, Set.mem_univ x, one_ne_zero⟩,
        isHolomorphicOn_iff_differentiableOn_scalar.mpr hdiff, fun _ _ => one_smul _ _⟩⟩
  have h := (hb.2 n e).mul hE
  rw [Set.inter_univ] at h
  exact h

end Meromorphic

/-- Evaluation of the complex parameter pairing at a fixed real dual vector, as a complex
linear form on the parameters. -/
def complexParameterPairingAt {F : Type u} [Field F] {H : GroupScheme (Spec (CommRingCat.of F))}
    (v : RealCharacterDual F H) : ComplexCharacterParameter F H →ₗ[ℂ] ℂ where
  toFun lam := complexParameterPairing F H lam v
  map_add' a b := by simp only [map_add, LinearMap.add_apply]
  map_smul' c a := by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]

variable {F : Type u} [Field F] [NumberField F]
  {G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F))}
  {A A' : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [IsAffine Q.X.left] [IsAffine V.X.left]

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left] [IsAffine Q.X.left]
  [IsAffine V.X.left] in
/-- Maximal compacts with the same infinite projection have the same archimedean part. -/
theorem IsMaximalCompactSubgroup.comap_ofInfinite_eq_of_infinite_eq
    {K L : Subgroup (AdelicGroupPoints F G)} (hKmax : IsMaximalCompactSubgroup F G K)
    (hLmax : IsMaximalCompactSubgroup F G L)
    (hinf : K.map (infinite F G).toMonoidHom = L.map (infinite F G).toMonoidHom) :
    K.comap (ofInfinite F G).toMonoidHom = L.comap (ofInfinite F G).toMonoidHom := by
  have hfactor (H : Subgroup (AdelicGroupPoints F G)) (hH : IsMaximalCompactSubgroup F G H) :
      H.comap (ofInfinite F G).toMonoidHom = H.map (infinite F G).toMonoidHom := by
    ext k
    constructor
    · intro hk
      exact ⟨_, hk, infinite_ofInfinite F G k⟩
    · rintro ⟨x, hx, rfl⟩
      exact ((hH.mem_iff x).mp hx).1
  rw [hfactor K hKmax, hfactor L hLmax, hinf]

/-- **Finite change of the Iwasawa compact.** Let `K` and `L` be maximal compact subgroups with
the same infinite projection, both Iwasawa for `P` and for `Q`. The family comparison for `L`
implies the family comparison for `K`. The twists for `K` of the inducing forms are finite
sums `∑ u, exp⟨λ, u⟩ · (cut u)_λ` of twists for `L`, both on the `P`-side and on the `Q`-side,
so the data for `K` become data for `L` with the exponential coefficients absorbed into the
meromorphic coefficients. -/
theorem FamilyRegularComparison.of_finiteCompactChange
    (hG : IsConnectedReductive G)
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
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) (hq : IsParabolicSubgroup q)
    (hV : LeviSubgroup.IsGeometricUnipotentRadical iV) (hl' : IsRationalLeviSubgroup l')
    (hmul : IsIso (subgroupMultiplication l' iV)) (hw : IsWeylConjugation p l q l' w c)
    {K L : Subgroup (AdelicGroupPoints F G)} (hKP : IsIwasawaCompact p K)
    (hKQ : IsIwasawaCompact q K) (hLP : IsIwasawaCompact p L) (hLQ : IsIwasawaCompact q L)
    (hKmax : IsMaximalCompactSubgroup F G K) (hLmax : IsMaximalCompactSubgroup F G L)
    (hinf : K.map (infinite F G).toMonoidHom = L.map (infinite F G).toMonoidHom)
    {N d : ℕ} {rho : MatrixRepresentation G (Fin N)} (hrho : IsClosedSubgroup rho)
    {hsmooth : SmoothOfRelativeDimension d G.X.hom}
    {hcalc : AdelicDifferentialCommutator F G hsmooth}
    (h : FamilyRegularComparison.{u, max v u, max w u} iU l r hA hT iV l' r' hA' hT' π' w c
      hLP hLQ rho hsmooth hcalc) :
    FamilyRegularComparison.{u, v, w} iU l r hA hT iV l' r' hA' hT' π' w c hKP hKQ rho
      hsmooth hcalc := by
  classical
  intro Ix _ φ b Db hφ hb EP DP hEP hEPser Jx _ ψ coeff D hψ hcoeff hint R
  have hArch := IsMaximalCompactSubgroup.comap_ofInfinite_eq_of_infinite_eq hKmax hLmax hinf
  -- the `P`-side comparison for each inducing form
  have hcmp := fun x => eisensteinFiniteCompactOperatorComparison F G P M U Q M' V A p iU l a r
    hA hT q iV l' w c π' hG hU hq hV hl' hmul hw K L hKP hLP hKQ hLQ hKmax hLmax hinf rho
    hsmooth hcalc (φ x) hrho (hφ x)
  choose S cut hcut Rc hRc using hcmp
  -- the `Q`-side twist decomposition for each target form
  have hQch := fun i => eisensteinFiniteCompactChange F G Q M' V q iV l' K L hKQ hLQ hKmax hLmax
    hinf rho hsmooth hcalc (K.comap (ofInfinite F G).toMonoidHom) (ψ i) (hψ i)
  choose S' cut' hcut' htw' using hQch
  -- the new families
  let φ' (y : (x : Ix) × S x) : AdelicGroupPoints F G → ℂ := cut y.1 y.2.val
  let b' (y : (x : Ix) × S x) (lam : ComplexCharacterParameter F P) : ℂ :=
    b y.1 lam * Complex.exp (complexParameterPairing F P lam y.2.val)
  let ψ' (z : (i : Jx) × S' i) : AdelicGroupPoints F G → ℂ := cut' z.1 z.2.val
  let coeff' (z : (i : Jx) × S' i) (lam : ComplexCharacterParameter F P) : ℂ :=
    coeff z.1 lam * Complex.exp (complexParameterPairing F Q (weylParameter l c π' lam) z.2.val)
  have hφ' : ∀ y, IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
      (L.comap (ofInfinite F G).toMonoidHom) rho (φ' y) := fun y => hcut y.1 y.2.val y.2.2
  have hψ' : ∀ z, IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F q iV l')
      (L.comap (ofInfinite F G).toMonoidHom) rho (ψ' z) := fun z => by
    rw [← hArch]
    exact hcut' z.1 z.2.val z.2.2
  have hb' : ∀ y, IsMeromorphicInCoordinatesOn (b' y) Db := fun y =>
    (hb y.1).mul_exp (complexParameterPairingAt y.2.val)
  have hcoeff' : ∀ z, IsMeromorphicInCoordinatesOn (coeff' z) D := fun z =>
    (hcoeff z.1).mul_exp ((complexParameterPairingAt z.2.val).comp (weylParameter l c π'))
  -- summability of the `Q`-series of the cut target forms
  have hsum := fun z : (i : Jx) × S' i =>
    eisensteinAbsoluteConvergence.exists_summable_eisensteinTerm r' hA' hT' hG hV hLQ rho hsmooth
      hcalc hLmax hrho (hψ' z)
  choose RQ hRQ using hsum
  let RQall : ℝ := ∑ z, |RQ z|
  have hRQle : ∀ z, RQ z ≤ RQall := fun z =>
    (le_abs_self _).trans (Finset.single_le_sum (fun z _ => abs_nonneg (RQ z)) (Finset.mem_univ z))
  let Rcall : ℝ := ∑ x, |Rc x|
  have hRcle : ∀ x, Rc x ≤ Rcall := fun x =>
    (le_abs_self _).trans (Finset.single_le_sum (fun x _ => abs_nonneg (Rc x)) (Finset.mem_univ x))
  -- the hypotheses for `L`
  have hEPser' : ∃ R₀ : ℝ, ∀ lam, r.IsRegularParameter hA hT R₀ lam → ∀ g,
      EP lam g = ∑ y, b' y lam * hLP.eisensteinSeries (φ' y) lam g := by
    obtain ⟨R₁, hR₁⟩ := hEPser
    refine ⟨max R₁ Rcall, fun lam hlam g => ?_⟩
    rw [hR₁ lam (fun α hα => (le_max_left _ _).trans_lt (hlam α hα)) g, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [(hRc x lam (fun α hα => ((hRcle x).trans (le_max_right _ _)).trans_lt (hlam α hα)) g).1,
      Finset.mul_sum, ← Finset.sum_coe_sort (S x)]
    exact Finset.sum_congr rfl fun u _ => by simp only [b', φ']; ring
  have hint' : ∃ R₀ : ℝ, ∀ lam, r.IsRegularParameter hA hT R₀ lam → ∀ g,
      ∑ y, b' y lam * hLP.intertwiningOperator hLQ iU l iV c π' w (φ' y) lam g =
        ∑ z, coeff' z lam * ψ' z g := by
    obtain ⟨R₁, hR₁⟩ := hint
    refine ⟨max R₁ Rcall, fun lam hlam g => ?_⟩
    let mu := weylParameter l c π' lam
    have hne : hLQ.heightPower mu g ≠ 0 := Complex.exp_ne_zero _
    apply mul_right_cancel₀ hne
    have hK' : (∑ x, b x lam * hKP.intertwiningOperator hKQ iU l iV c π' w (φ x) lam g) *
        hKQ.heightPower mu g = (∑ i, coeff i lam * ψ i g) * hKQ.heightPower mu g := by
      rw [hR₁ lam (fun α hα => (le_max_left _ _).trans_lt (hlam α hα)) g]
    calc
      (∑ y, b' y lam * hLP.intertwiningOperator hLQ iU l iV c π' w (φ' y) lam g) *
          hLQ.heightPower mu g
          = ∑ x, b x lam * ∑ u ∈ S x, Complex.exp (complexParameterPairing F P lam u) *
              hLQ.parameterTwist (hLP.intertwiningOperator hLQ iU l iV c π' w (cut x u) lam)
                mu g := by
            rw [Finset.sum_mul, Fintype.sum_sigma]
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Finset.mul_sum, ← Finset.sum_coe_sort (S x)]
            refine Finset.sum_congr rfl fun u _ => ?_
            simp only [b', φ', IsIwasawaCompact.parameterTwist]
            ring
      _ = ∑ x, b x lam * hKQ.parameterTwist
            (hKP.intertwiningOperator hKQ iU l iV c π' w (φ x) lam) mu g := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [(hRc x lam (fun α hα => ((hRcle x).trans (le_max_right _ _)).trans_lt
              (hlam α hα)) g).2]
      _ = (∑ x, b x lam * hKP.intertwiningOperator hKQ iU l iV c π' w (φ x) lam g) *
            hKQ.heightPower mu g := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun x _ => ?_
            simp only [IsIwasawaCompact.parameterTwist]
            ring
      _ = (∑ i, coeff i lam * ψ i g) * hKQ.heightPower mu g := hK'
      _ = ∑ i, coeff i lam * hKQ.parameterTwist (ψ i) mu g := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [IsIwasawaCompact.parameterTwist]
            ring
      _ = ∑ i, coeff i lam * ∑ u ∈ S' i, Complex.exp (complexParameterPairing F Q mu u) *
            hLQ.parameterTwist (cut' i u) mu g := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [htw' i mu g]
      _ = (∑ z, coeff' z lam * ψ' z g) * hLQ.heightPower mu g := by
            rw [Finset.sum_mul, Fintype.sum_sigma]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum, ← Finset.sum_coe_sort (S' i)]
            refine Finset.sum_congr rfl fun u _ => ?_
            simp only [coeff', ψ', mu, IsIwasawaCompact.parameterTwist]
            ring
  -- apply the comparison for `L`
  obtain ⟨m, e, O, hO, hOne, hOx⟩ := h φ' b' Db hφ' hb' EP DP hEP hEPser' ψ' coeff' D hψ'
    hcoeff' hint' (max R RQall)
  refine ⟨m, e, O, hO, hOne, fun x hx => ⟨fun α hα =>
    (le_max_left _ _).trans_lt ((hOx x hx).1 α hα), fun g => ?_⟩⟩
  have hreg : ∀ z, r'.IsRegularParameter hA' hT' (RQ z) (weylParameter l c π' (e x)) :=
    fun z α hα => ((hRQle z).trans (le_max_right _ _)).trans_lt ((hOx x hx).1 α hα)
  rw [(hOx x hx).2 g, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hKQ.eisensteinSeries_eq_finset_sum_of_twist hLQ (S' i)
      (fun u => Complex.exp (complexParameterPairing F Q (weylParameter l c π' (e x)) u))
      (ψ i) (cut' i) (weylParameter l c π' (e x)) (fun y => htw' i _ y) g
      (fun u hu => hRQ ⟨i, ⟨u, hu⟩⟩ _ (hreg ⟨i, ⟨u, hu⟩⟩) g),
    Finset.mul_sum, ← Finset.sum_coe_sort (S' i)]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [coeff', ψ']
  ring

end Langlands.Global
