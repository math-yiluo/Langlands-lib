import Langlands.Global.AdelicContinuedIntertwiningConvolution
import Langlands.Global.AdelicFiniteSpectralFamily

/-! # Weyl symmetry of finite normalized convolution families -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

private theorem sum_fin_reindex {k : ℕ} {m : Fin k → ℕ} {V : Type*} [AddCommMonoid V]
    (f : ∀ j, Fin (m j) → V) :
    ∑ q : Fin (Fintype.card (Σ j : Fin k, Fin (m j))),
        f ((Fintype.equivFin _).symm q).1 ((Fintype.equivFin _).symm q).2 = ∑ j, ∑ q, f j q := by
  rw [← Fintype.sum_sigma']
  exact Fintype.sum_equiv (Fintype.equivFin (Σ j : Fin k, Fin (m j))).symm _ _ (fun _ => rfl)

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {I : Type} [Fintype I] {P M U : I → GroupScheme (Spec (CommRingCat.of F))}
  {A : I → CommGroupScheme (Spec (CommRingCat.of F))}
  [∀ i, IsAffine (P i).X.left] [∀ i, IsAffine (M i).X.left]
  [∀ i, LocallyOfFiniteType (M i).X.hom] [∀ i, IsAffine (U i).X.left]
  {p : ∀ i, P i ⟶ G} [∀ i, IsClosedImmersion (p i).hom.hom.left] {iU : ∀ i, U i ⟶ P i}
  {l : ∀ i, M i ⟶ P i} [∀ i, IsClosedImmersion (iU i ≫ p i).hom.hom.left]
  {a : ∀ i, (A i).toGrp ⟶ M i} {r : ∀ i, ParabolicRootPresentation (p i) (l i) (a i)}
  [∀ i, Mono (r i).data.i.hom.hom.left] [∀ i, Fintype (relativeWeylGroup (r i).data.i)]
  [∀ i, Mono (CommGroupScheme.groupHom (r i).data.f).hom.hom.left]
  {hA : ∀ i, IsSplitTorus (A i).toGrp} {hT : ∀ i, IsSplitTorus (r i).data.T.toGrp}
  {π : ∀ i, P i ⟶ M i} [∀ i, LocallyOfFiniteType (P i).X.hom]
  {K : Subgroup (AdelicGroupPoints F G)} {hK : ∀ i, IsIwasawaCompact (p i) K} {N d : ℕ}
  {rho : MatrixRepresentation G (Fin N)} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
  {hcalc : AdelicDifferentialCommutator F G hsmooth}
  {μM : ∀ i, Measure (AdelicGroupPoints F (M i))} [∀ i, (μM i).IsHaarMeasure]
  {n : I → ℕ} {e : ∀ i, (Fin (n i) → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (P i)}
  {β : ∀ i, (Fin (n i) → ℝ) → ℝ}
  {T : I → I → Type} [∀ i i', Fintype (T i i')]
  {w : ∀ i i', T i i' → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)}
  {cw : ∀ i i', T i i' → (M i' ⟶ M i)}
  {hw : ∀ i i' t, MeasurePreserving
    (fun x => (e i').symm (realWeylParameter (l i) (cw i i' t) (π i') (e i x))) volume volume}
  {nP : I → ℕ}

local notation "A₂" => (fun i => IsSquareIntegrableInducedForm K
  (IsIwasawaCompact.isCompact (hK i)) rho hsmooth hcalc (p i) (iU i) (l i))
local notation "μₕ" => (fun i => inducedL2Measure K (IsIwasawaCompact.isCompact (hK i))
  (l i) (μM i) (e i) (β i))
local notation "Hₕ" => (fun i => inducedHilbertSpace K
  (IsIwasawaCompact.isCompact (hK i)) rho hsmooth hcalc (p i) (iU i) (l i) (μM i) (e i) (β i))
local notation:max "Lhat[" M "]" => symmetricFamilySpace hK rho hsmooth hcalc iU l μM n e β nP T cw π hw M
local notation "Functions" => AdelicGroupPoints F G → ℂ
local notation "imag" => (fun i x => imaginaryParameter F (P i) (e i x))
local notation "weyl" => (fun i i' t => weylParameter (l i) (cw i i' t) (π i'))
local notation "τ" => (fun i i' t x => (LinearEquiv.symm (e i')) (realWeylParameter (l i) (cw i i' t) (π i') (e i x)))
local notation "Expansion" => (fun i i' t => IsRegularIntertwiningExpansion (hK i) (hK i') rho hsmooth
  hcalc (iU i) (l i) (r i) (hA i) (hT i) (iU i') (l i') (π i') (w i i' t) (cw i i' t))

omit [Fintype I] [∀ i i', Fintype (T i i')] in
set_option maxHeartbeats 750000 in
/-- If the normalized convolutions of the inducing forms admit finite entire expansions in
square-integrable inducing forms, the resulting smooth presentation is Weyl symmetric. The
same finite expansion hypothesis is used on the target forms of the intertwining expansions. -/
theorem exists_symmetricFamily_of_finiteConvolutionExpansions
    {Mop : ∀ i i', T i i' → (Fin (n i) → ℝ) → Hₕ i →L[ℂ] Hₕ i'}
    (hG : IsConnectedReductive G)
    (hU : ∀ i, LeviSubgroup.IsGeometricUnipotentRadical (iU i))
    (hmul : ∀ i, IsIso (subgroupMultiplication (l i) (iU i))) (hπ : ∀ i, l i ≫ π i = 𝟙 (M i))
    (hmax : IsMaximalCompactSubgroup F G K) (hrho : IsClosedSubgroup rho)
    (hW : ∀ i i' t, IsWeylConjugation (p i) (l i) (p i') (l i') (w i i' t) (cw i i' t))
    (hMop : ∀ i i' t, IsImaginaryIntertwiningOperator (hK i) (hK i') rho hsmooth hcalc (iU i)
      (l i) (a i) (r i) (hA i) (hT i) (iU i') (l i') (π i') (w i i' t) (cw i i' t) (μM i) (μM i')
      (e i) (e i') (β i) (β i') (Mop i i' t))
    (hβ : ∀ i, Continuous (β i) ∧ HasCompactSupport (β i) ∧ (∀ x, 0 ≤ β i x) ∧ ∫ x, β i x = 1)
    (hnP : ∀ i, nP i ≠ 0)
    (hL : ∀ i v, A₂ i v → MemLp (inducedRestriction K (p i) (l i) v) 2 (μₕ i))
    (hEx : ∀ i i' t v, A₂ i v → ∃ (m : ℕ) (ψ : Fin m → Functions)
      (b : Fin m → ComplexCharacterParameter F (P i) → ℂ) (D : Set (ComplexCharacterParameter F (P i))),
      Expansion i i' t v ψ b D)
    {kernel : Functions} (hk : Continuous kernel) (hks : HasCompactSupport kernel)
    (hConv : ∀ i v, A₂ i v → ∃ (m : ℕ) (u : Fin m → Functions)
      (b : Fin m → ComplexCharacterParameter F (P i) → ℂ),
      (∀ j, A₂ i (u j)) ∧ IsFiniteNormalizedConvolutionExpansion (hK i) kernel v u b)
    {Φ : Lhat[Mop]} {k : I → ℕ} {v : ∀ i, Fin (k i) → Functions}
    {c : ∀ i, Fin (k i) → (Fin (n i) → ℝ) → ℂ}
    (hΦ : IsSmoothCompactFamily hK rho hsmooth hcalc iU l μM n e β nP k v c Φ.1)
    {m : ∀ i, Fin (k i) → ℕ} {u : ∀ i j, Fin (m i j) → Functions}
    {b : ∀ i j, Fin (m i j) → ComplexCharacterParameter F (P i) → ℂ}
    (hu : ∀ i j t, A₂ i (u i j t))
    (hcu : ∀ i j, IsFiniteNormalizedConvolutionExpansion (hK i) kernel (v i j) (u i j) (b i j)) :
    let J (i : I) := Σ j : Fin (k i), Fin (m i j)
    let k' (i : I) := Fintype.card (J i)
    let v' (i : I) (q : Fin (k' i)) := u i ((Fintype.equivFin (J i)).symm q).1
      ((Fintype.equivFin (J i)).symm q).2
    let c' (i : I) (q : Fin (k' i)) (x : Fin (n i) → ℝ) :=
      c i ((Fintype.equivFin (J i)).symm q).1 x * b i ((Fintype.equivFin (J i)).symm q).1
        ((Fintype.equivFin (J i)).symm q).2 (imag i x)
    ∃ Ψ : Lhat[Mop], IsSmoothCompactFamily hK rho hsmooth hcalc iU l μM n e β nP k' v' c' Ψ.1 := by
  classical
  intro J k' v' c'
  have hv' : ∀ i q, A₂ i (v' i q) := fun i q => hu i _ _
  have hc' : ∀ i q, ContDiff ℝ (⊤ : ℕ∞) (c' i q) ∧ HasCompactSupport (c' i q) := by
    intro i q
    let j : J i := (Fintype.equivFin (J i)).symm q
    exact ⟨(hΦ.2.1 i j.1).1.mul (contDiff_comp_imaginaryParameter (e i) ((hcu i j.1).1 j.2)
      (Set.subset_univ _)), (hΦ.2.1 i j.1).2.mul_right⟩
  have hLnew (i : I) (q : Fin (k' i)) :
      MemLp (inducedRestriction K (p i) (l i) (v' i q)) 2 (μₕ i) := hL i (v' i q) (hv' i q)
  have hex := exists_smoothCompactFamily_of_finite_forms
    (F := F) (G := G) (I := I) (P := P) (M := M) (U := U) (p := p) (iU := iU) (l := l)
    (K := K) (hK := hK) (rho := rho) (hsmooth := hsmooth) (hcalc := hcalc) (μM := μM)
    (n := n) (e := e) (β := β) (nP := nP) (k := k') (v := v') (c := c') hnP hv' hLnew hc'
  obtain ⟨Ψ, hΨ⟩ := hex
  refine ⟨⟨Ψ, ?_⟩, hΨ⟩
  intro i i' t
  have hτ : Filter.Tendsto (τ i i' t) (ae (spectralMeasure (n i))) (ae (spectralMeasure (n i'))) := by
    rw [ae_spectralMeasure_eq, ae_spectralMeasure_eq]
    exact (hw i i' t).quasiMeasurePreserving.tendsto_ae
  choose q₀ ψ a₀ D hE using fun j => hEx i i' t (v i j) (hΦ.1 i j)
  choose q₁ ξ d₀ D' hE' using fun j q => hEx i i' t (u i j q) (hu i j q)
  choose lv υ ec _ hcv using fun j q => hConv i' (ψ j q) ((hE j).1 q)
  have hExpNew (q : Fin (k' i)) : Expansion i i' t (v' i q)
      (ξ ((Fintype.equivFin (J i)).symm q).1 ((Fintype.equivFin (J i)).symm q).2)
      (d₀ ((Fintype.equivFin (J i)).symm q).1 ((Fintype.equivFin (J i)).symm q).2)
      (D' ((Fintype.equivFin (J i)).symm q).1 ((Fintype.equivFin (J i)).symm q).2) :=
    hE' _ _
  filter_upwards [hΦ.2.2 i, hτ.eventually (hΦ.2.2 i'), Φ.2 i i' t,
    hΨ.2.2 i, hτ.eventually (hΨ.2.2 i')] with x hx hy hsym hxr hyr
  let y := τ i i' t x
  let lam := imag i x
  let mu := imag i' y
  have hmu : weyl i i' t lam = mu := by
    rw [weylParameter_imaginaryParameter]
    simp only [mu, y, LinearEquiv.apply_symm_apply]
  have hy' : ⇑(Mop i i' t x (Φ.1 i x) : Lp ℂ 2 (μₕ i')) =ᵐ[μₕ i']
      inducedRestriction K (p i') (l i') (fun g => ∑ j, c i' j y * v i' j g) := by
    rw [← hsym]
    exact hy
  have hforms := IsImaginaryIntertwiningOperator.pointwise_eq_of_finite_sum (hK i) (hK i') rho
    hsmooth hcalc (iU i) (l i) (r i) (hA i) (hT i) (iU i') (l i') (π i') (w i i' t) (cw i i' t)
    (μM i) (μM i') (e i) (e i') (β i) (β i') hG (r i').isCompatible.parabolic (hU i')
    (r i').isCompatible.levi (hmul i') (hβ i').1 (hβ i').2.1 (hβ i').2.2.1 (hβ i').2.2.2
    (hMop i i' t) (hΦ.1 i) (hΦ.1 i') (fun j => hL i _ (hΦ.1 i j)) hE
    x (fun j => c i j x) (fun j => c i' j y) (Φ.1 i x) hx hy'
  have hOut := IsImaginaryIntertwiningOperator.ae_apply_finite_sum (hK i) (hK i') rho
    hsmooth hcalc (iU i) (l i) (r i) (hA i) (hT i) (iU i') (l i') (π i') (w i i' t) (cw i i' t)
    (μM i) (μM i') (e i) (e i') (β i) (β i') (hMop i i' t) (hv' i)
    (fun j => hL i _ (hv' i j)) hExpNew x (fun j => c' i j x) (Ψ i x) hxr
  have hpoint (g : AdelicGroupPoints F G) :
      ∑ j, c' i' j y * v' i' j g =
        ∑ q : Fin (k' i), c' i q x * ∑ j,
          d₀ ((Fintype.equivFin (J i)).symm q).1 ((Fintype.equivFin (J i)).symm q).2 j lam *
            ξ ((Fintype.equivFin (J i)).symm q).1 ((Fintype.equivFin (J i)).symm q).2 j g := by
    change (∑ q : Fin (k' i'),
        (c i' ((Fintype.equivFin (J i')).symm q).1 y *
          b i' ((Fintype.equivFin (J i')).symm q).1 ((Fintype.equivFin (J i')).symm q).2 mu) *
          u i' ((Fintype.equivFin (J i')).symm q).1 ((Fintype.equivFin (J i')).symm q).2 g) = _
    rw [sum_fin_reindex (fun j q => (c i' j y * b i' j q mu) * u i' j q g)]
    change _ = ∑ q : Fin (k' i),
      (c i ((Fintype.equivFin (J i)).symm q).1 x *
        b i ((Fintype.equivFin (J i)).symm q).1 ((Fintype.equivFin (J i)).symm q).2 lam) * _
    rw [sum_fin_reindex (fun j q => (c i j x * b i j q lam) * ∑ s, d₀ j q s lam * ξ j q s g)]
    simp_rw [mul_assoc (c _ _ _), ← Finset.mul_sum]
    simp_rw [← (hcu i' _).2 mu g]
    rw [← (hK i').integral_translate_sum_mul hk hks mu (v i')
      (fun j => (hΦ.1 i' j).1.2.1.1) (fun j => c i' j y) g, hforms]
    rw [(hK i').integral_translate_sum_mul hk hks mu
      (fun j z => ∑ q, a₀ j q lam * ψ j q z)
      (fun j => continuous_finsetSum _ fun q _ => continuous_const.mul ((hE j).1 q).1.2.1.1)
      (fun j => c i j x) g]
    refine Finset.sum_congr rfl fun j _ => congrArg (c i j x * ·) ?_
    rw [(hK i').integral_translate_sum_mul hk hks mu (ψ j)
      (fun q => ((hE j).1 q).1.2.1.1) (fun q => a₀ j q lam) g]
    simp_rw [fun q => (hcv j q).2 mu g, ← hmu]
    exact (continuedIntertwining_integral_translate (hK i) (hK i') rho hsmooth hcalc (iU i)
      (l i) (r i) (hA i) (hT i) (iU i') (l i') (π i') (w i i' t) (cw i i' t) hG (hU i)
      (r i').isCompatible.parabolic (hU i') (r i').isCompatible.levi (hmul i') (hπ i')
      (hW i i' t) hmax hrho hk hks (hΦ.1 i j).1 (hE j) (fun q => (hu i j q).1)
      (hcu i j) (hE' j) (hcv j) (e i x) g).symm
  apply Subtype.ext
  apply Lp.ext
  refine hyr.trans ?_
  rw [funext hpoint]
  exact hOut.symm

end Langlands.Global
