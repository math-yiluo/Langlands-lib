import Langlands.Global.AdelicImaginaryIntertwiningFiniteFamilies
import Langlands.Global.AdelicIntertwiningConvolution
import Langlands.Global.AdelicEisensteinRegularRegion
import Langlands.Analysis.Meromorphic.ScalarIdentity
import Langlands.Analysis.Meromorphic.CoordinateGluing

/-! # Covariance of finite intertwining expansions under convolution -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions Langlands.Analysis.Meromorphic

private theorem isMeromorphicInCoordinatesOn_sum_apply {X : Type*} [AddCommGroup X] [Module ℂ X]
    [FiniteDimensional ℂ X] {m : ℕ} {D : Fin m → Set X} {f : Fin m → X → ℂ}
    (hD : ∀ i, IsOpenDenseInCoordinates (D i)) (hf : ∀ i, IsMeromorphicInCoordinatesOn (f i) (D i)) :
    IsMeromorphicInCoordinatesOn (fun lam => ∑ i, f i lam) (⋂ i, D i) := by
  have hsD := isOpenDenseInCoordinates_iInter hD
  have h := IsMeromorphicInCoordinatesOn.sum Finset.univ hsD (fun i _ =>
    (hf i).congr_mono hsD (iInter_subset D i) (fun _ _ => rfl))
  have hsum : (∑ i, f i) = fun s => ∑ i, f i s := by
    funext s
    simp only [Finset.sum_apply]
  rwa [hsum] at h

section Linearity

variable {F : Type} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

local notation "Ad" => AdelicGroupPoints F G
local notation "dh" => (Measure.haar : Measure Ad)

omit [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- An expansion of the integrated normalized translate into a fixed finite family of functions,
with scalar coefficients holomorphic on the whole complex parameter space. -/
def IsFiniteNormalizedConvolutionExpansion (kernel v : Ad → ℂ) {m : ℕ}
    (u : Fin m → Ad → ℂ) (b : Fin m → ComplexCharacterParameter F P → ℂ) : Prop :=
  (∀ j, IsMeromorphicInCoordinatesOn (b j) Set.univ) ∧
  ∀ lam g, (∫ h, kernel h * hK.inducedRightTranslate lam h v g ∂dh) = ∑ j, b j lam * u j g

/-- Finite linear combinations of continuous inducing functions commute with compactly
supported averaging of the normalized right translate. -/
theorem IsIwasawaCompact.integral_translate_sum_mul
    {a : Ad → ℂ} (ha : Continuous a) (has : HasCompactSupport a)
    (lam : ComplexCharacterParameter F P) {m : ℕ} (v : Fin m → Ad → ℂ)
    (hv : ∀ j, Continuous (v j)) (b : Fin m → ℂ) (g : Ad) :
    (∫ h, a h * hK.inducedRightTranslate lam h (fun x => ∑ j, b j * v j x) g ∂dh) =
      ∑ j, b j * ∫ h, a h * hK.inducedRightTranslate lam h (v j) g ∂dh := by
  have hpoint (h : Ad) : a h * hK.inducedRightTranslate lam h (fun x => ∑ j, b j * v j x) g =
      ∑ j, b j * (a h * hK.inducedRightTranslate lam h (v j) g) := by
    simp only [IsIwasawaCompact.inducedRightTranslate, IsIwasawaCompact.parameterTwist,
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp_rw [hpoint]
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · intro j _
    apply Continuous.integrable_of_hasCompactSupport
    · exact continuous_const.mul (ha.mul (continuous_const.mul
        ((hK.continuous_parameterTwist (hv j) lam).comp (continuous_const.mul continuous_id))))
    · exact has.mul_right.mul_left

end Linearity

section Continued

variable {F : Type} [Field F] [NumberField F]
  {G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom]
  [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom]
  [IsAffine V.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K) (hQ : IsIwasawaCompact q K)
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (iU : U ⟶ P) (l : M ⟶ P)
  {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
  (iV : V ⟶ Q) (l' : M' ⟶ Q) [IsClosedImmersion (iV ≫ q).hom.hom.left]
  (π' : Q ⟶ M') (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (cw : M' ⟶ M)

local notation "Ad" => AdelicGroupPoints F G
local notation "Fun" => Ad → ℂ
local notation "SourceParam" => ComplexCharacterParameter F P
local notation "TargetParam" => ComplexCharacterParameter F Q
local notation "W" => weylParameter l cw π'
local notation "Expn" => IsRegularIntertwiningExpansion hK hQ rho hsmooth hcalc iU l r hA hT iV l' π' w cw
local notation "Aut" => IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
  (Subgroup.comap (ContinuousMonoidHom.toMonoidHom (ofInfinite F G)) K) rho

omit [LocallyOfFiniteType P.X.hom] in
set_option maxHeartbeats 800000 in
/-- Continue the regular convolution identity for a single vector when all the indicated
finite expansions are supplied. Each coefficient of an averaged inducing form is meromorphic
on the whole parameter space with holomorphy domain `univ`. -/
theorem continuedIntertwining_integral_translate
    (hG : IsConnectedReductive G) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (hq : IsParabolicSubgroup q) (hV : LeviSubgroup.IsGeometricUnipotentRadical iV)
    (hl' : IsRationalLeviSubgroup l') (hmul : IsIso (subgroupMultiplication l' iV))
    (hπ' : l' ≫ π' = 𝟙 M') (hw : IsWeylConjugation p l q l' w cw)
    (hmax : IsMaximalCompactSubgroup F G K) (hrho : IsClosedSubgroup rho)
    {kernel : Fun} (hk : Continuous kernel) (hks : HasCompactSupport kernel)
    {v : Fun} (hv : Aut v)
    {m : ℕ} {ψ : Fin m → Fun} {a₀ : Fin m → SourceParam → ℂ} {D : Set SourceParam}
    (hExp : Expn v ψ a₀ D)
    {k : ℕ} {u : Fin k → Fun} {b : Fin k → SourceParam → ℂ} (hu : ∀ j, Aut (u j))
    (hcu : IsFiniteNormalizedConvolutionExpansion hK kernel v u b)
    {k' : Fin k → ℕ} {ξ : ∀ j, Fin (k' j) → Fun}
    {d₀ : ∀ j, Fin (k' j) → SourceParam → ℂ} {D' : Fin k → Set SourceParam}
    (hExp' : ∀ j, Expn (u j) (ξ j) (d₀ j) (D' j))
    {m' : Fin m → ℕ} {υ : ∀ i, Fin (m' i) → Fun} {c₀ : ∀ i, Fin (m' i) → TargetParam → ℂ}
    (hcv : ∀ i, IsFiniteNormalizedConvolutionExpansion hQ kernel (ψ i) (υ i) (c₀ i))
    (mu : RealCharacterParameter F P) (g : Ad) :
    let lam := imaginaryParameter F P mu
    ∑ j, b j lam * ∑ t, d₀ j t lam * ξ j t g =
      ∑ i, a₀ i lam * ∑ t, c₀ i t (W lam) * υ i t g := by
  classical
  dsimp only
  let lam := imaginaryParameter F P mu
  obtain ⟨n, ⟨e⟩⟩ := exists_complexParameterEquiv hG r.isCompatible.parabolic
  let : FiniteDimensional ℂ SourceParam := FiniteDimensional.of_surjective e.toLinearMap e.surjective
  obtain ⟨hψ, hD, hma, R, hR⟩ := hExp
  obtain ⟨hb, hcu⟩ := hcu
  have hc := fun i => (hcv i).1
  have hcform := fun i => (hcv i).2
  choose R' hR' using fun j => (hExp' j).2.2.2
  let : IsIso cw := hw.isIso
  obtain ⟨wE, hwE⟩ := exists_weylParameter_linearEquiv l l' r.isCompatible.levi hl' cw π' hπ'
  have hm_left (j : Fin k) : IsMeromorphicInCoordinatesOn
      (fun s => b j s * ∑ t, d₀ j t s * ξ j t g)
      (Set.univ ∩ (⋂ _ : Fin (k' j), D' j ∩ Set.univ)) := by
    have hterm (t : Fin (k' j)) := ((hExp' j).2.2.1 t).mul
      (isMeromorphicInCoordinatesOn_const (X := SourceParam) (ξ j t g))
    exact (hb j).mul (isMeromorphicInCoordinatesOn_sum_apply
      (fun t => (hterm t).isOpenDenseInCoordinates) hterm)
  have hm_right (i : Fin m) : IsMeromorphicInCoordinatesOn
      (fun s => a₀ i s * ∑ t, c₀ i t (W s) * υ i t g)
      (D ∩ (⋂ _ : Fin (m' i), Set.univ ∩ Set.univ)) := by
    have hterm (t : Fin (m' i)) : IsMeromorphicInCoordinatesOn
        (fun s => c₀ i t (W s) * υ i t g) (Set.univ ∩ Set.univ) := by
      have hcomp := (hc i t).comp_linearEquiv wE
      change IsMeromorphicInCoordinatesOn (fun s => c₀ i t (wE.toLinearMap s)) (wE ⁻¹' Set.univ) at hcomp
      rw [hwE, preimage_univ] at hcomp
      exact hcomp.mul (isMeromorphicInCoordinatesOn_const (X := SourceParam) (υ i t g))
    exact (hma i).mul (isMeromorphicInCoordinatesOn_sum_apply
      (fun t => (hterm t).isOpenDenseInCoordinates) hterm)
  have hL := isMeromorphicInCoordinatesOn_sum_apply (fun j => (hm_left j).isOpenDenseInCoordinates) hm_left
  have hR₀ := isMeromorphicInCoordinatesOn_sum_apply (fun i => (hm_right i).isOpenDenseInCoordinates) hm_right
  have hlam : lam ∈ _ ∩ _ := show lam ∈
      (⋂ j : Fin k, Set.univ ∩ (⋂ _ : Fin (k' j), D' j ∩ Set.univ)) ∩
      (⋂ i : Fin m, D ∩ (⋂ _ : Fin (m' i), Set.univ ∩ Set.univ)) from by
    refine ⟨mem_iInter.mpr fun j => ⟨mem_univ _, mem_iInter.mpr fun _ => ?_⟩,
      mem_iInter.mpr fun _ => ⟨hD ⟨mu, rfl⟩, mem_iInter.mpr fun _ => ⟨mem_univ _, mem_univ _⟩⟩⟩
    exact ⟨(hExp' j).2.1 ⟨mu, rfl⟩, mem_univ _⟩
  obtain ⟨Rc, hRc⟩ := intertwiningConvolutionCovariance F G P M U Q M' V A p iU l a r hA hT
    q iV l' π' w cw hG hU hq hV hl' hmul hw K hK hQ rho hsmooth hcalc v hmax hrho hv
  choose Ri hRi using fun j => intertwiningIntegrability F G P M U Q M' V A p iU l a r hA hT
    q iV l' w cw hG hU hq hV hl' hmul hw K hK rho hsmooth hcalc (u j) hmax hrho (hu j)
  let threshold := max R (max Rc (∑ j, (|R' j| + |Ri j|)))
  have hR'le (j : Fin k) : R' j ≤ threshold := calc
    R' j ≤ |R' j| + |Ri j| := (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
    _ ≤ ∑ j, (|R' j| + |Ri j|) := Finset.single_le_sum (f := fun i => |R' i| + |Ri i|)
      (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ j)
    _ ≤ threshold := (le_max_right _ _).trans (le_max_right _ _)
  have hRile (j : Fin k) : Ri j ≤ threshold := calc
    Ri j ≤ |R' j| + |Ri j| := (le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))
    _ ≤ ∑ j, (|R' j| + |Ri j|) := Finset.single_le_sum (f := fun i => |R' i| + |Ri i|)
      (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ j)
    _ ≤ threshold := (le_max_right _ _).trans (le_max_right _ _)
  have hreg : ∀ s, r.IsRegularParameter hA hT threshold s →
      (∑ j, b j s * ∑ t, d₀ j t s * ξ j t g) = ∑ i, a₀ i s * ∑ t, c₀ i t (W s) * υ i t g := by
    intro s hs
    have hsrc := funext (hcu s)
    have htgt := funext (hR s (fun α hα => (le_max_left _ _).trans_lt (hs α hα)))
    have hleft (j : Fin k) := hR' j s (fun α hα => (hR'le j).trans_lt (hs α hα)) g
    simp_rw [← hleft, ← hK.intertwiningOperator_sum_mul hQ iU l iV cw π' w u (fun j => b j s) s g
      (fun j => hRi j s (fun α hα => (hRile j).trans_lt (hs α hα)) g), ← hsrc,
      hRc s (fun α hα => ((le_max_left _ _).trans (le_max_right _ _)).trans_lt (hs α hα)) kernel hk hks g,
      htgt]
    rw [hQ.integral_translate_sum_mul hk hks (W s) ψ (fun i => (hψ i).1.2.1.1) (fun i => a₀ i s) g]
    simp_rw [hcform]
  exact (hL.eqOn_of_eqOn_open hR₀ e (r.isOpen_regularParameter_inCoordinates hA hT threshold e)
    (r.nonempty_regularParameter_inCoordinates hA hT threshold e)
    (fun s hs => hreg (e s) hs.1)) hlam

end Continued

end Langlands.Global.AdelicGroupPoints
