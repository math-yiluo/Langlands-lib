import Langlands.Global.AdelicSpectralDecompositionReduction
import Langlands.Global.AdelicEisensteinFunctionalEquationStatement
import Langlands.Global.AdelicRelativeAmbientParameterProduct
import Langlands.Global.AdelicSymmetricFamilyDensity
import Langlands.Global.AdelicWeylParameterEquivalence
import Langlands.GroupScheme.Rational.CentralTorusFixedness
import Langlands.GroupScheme.Rational.ParabolicCharacterLattice
import Langlands.Representation.Plancherel.UnramifiedRationalJacquetGeometryFiniteness

/-! # Relative wave packets under Weyl conjugation -/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Global

open GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

section Parameters

variable {F : Type} [Field F] [NumberField F]
  {G P M Q M' : GroupScheme (Spec (CommRingCat.of F))}
  {A A' : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [IsAffine Q.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left]
  {l : M ⟶ P} {l' : M' ⟶ Q} {a : A.toGrp ⟶ M} {a' : A'.toGrp ⟶ M'}
  (r : ParabolicRootPresentation p l a) (r' : ParabolicRootPresentation q l' a')
  {π' : Q ⟶ M'} (hπ' : l' ≫ π' = 𝟙 M')
  {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c : M' ⟶ M}
  (hw : IsWeylConjugation p l q l' w c)

include hπ' hw in
omit [NumberField F] [IsAffine P.X.left] [IsAffine Q.X.left]
    [IsClosedImmersion p.hom.hom.left] [IsClosedImmersion q.hom.hom.left] in
private theorem splitCentreParabolicLift_weyl :
    splitCentreParabolicLift r' ≫ π' ≫ c ≫ l = splitCentreParabolicLift r := by
  have hp : Mono p.hom.hom := r.isCompatible.parabolic.isClosedSubgroup.mono_overHom
  let : Mono p := (Grp.forget _).mono_of_mono_map (f := p) hp
  have hretract : splitCentreParabolicLift r' ≫ π' ≫ l' = splitCentreParabolicLift r' := by
    unfold splitCentreParabolicLift
    rw [Category.assoc, reassoc_of% hπ']
  apply (cancel_mono p).mp
  calc
    (splitCentreParabolicLift r' ≫ π' ≫ c ≫ l) ≫ p =
        (splitCentreParabolicLift r' ≫ π' ≫ l') ≫ q ≫ (G.innerIso w).inv := by
      simp only [Category.assoc, hw.comp_eq]
    _ = RestrictionSplitCentre.canonicalComponent F G ≫ (G.innerIso w).inv := by
      rw [hretract, ← Category.assoc, splitCentreParabolicLift_comp]
    _ = splitCentreParabolicLift r ≫ p := by
      rw [splitCentreParabolicLift_comp, ← innerIso_inv_hom]
      exact (RestrictionSplitCentre.isSplitComponent_canonicalComponent F G).isCentralSplitTorus.isCentral.comp_innerIso_hom _

include r r' hπ' hw in
/-- The real Weyl map restricts to a linear equivalence of the actual split-centre annihilators. -/
theorem exists_relativeWeylParameter_linearEquiv :
    ∃ e : relativeParameterSpace (F := F) p ≃ₗ[ℝ] relativeParameterSpace (F := F) q,
      ∀ x, (e x : RealCharacterParameter F Q) = realWeylParameter l c π' x := by
  have rightInverse {H L : GroupScheme (Spec (CommRingCat.of F))}
      {i : L ⟶ H} {pr : H ⟶ L} (hi : i ≫ pr = 𝟙 L) :
      Function.RightInverse (characterRestrict pr) (characterRestrict i) := by
    intro χ
    change ((characterRestrict i).comp (characterRestrict pr)) χ = χ
    rw [← characterRestrict_comp, hi, characterRestrict_id]
    rfl
  let : IsIso c := hw.isIso
  have hc : Function.Bijective (characterRestrict c) :=
    ⟨(rightInverse (IsIso.inv_hom_id c)).injective,
      (rightInverse (IsIso.hom_inv_id c)).surjective⟩
  have hπ : Function.Bijective (characterRestrict π') :=
    ⟨(rightInverse hπ').injective, fun χ => ⟨characterRestrict l' χ,
      r'.isCompatible.levi.characterRestrict_bijective.injective (rightInverse hπ' _)⟩⟩
  let eZ := AddEquiv.ofBijective (characterRestrict (π' ≫ c ≫ l)) (by
    rw [characterRestrict_comp, characterRestrict_comp]
    exact hπ.comp (hc.comp r.isCompatible.levi.characterRestrict_bijective))
  let e := AlgebraTensorModule.congr (LinearEquiv.refl ℝ ℝ) eZ.toIntLinearEquiv
  have he : e.toLinearMap = realWeylParameter l c π' := by
    apply AlgebraTensorModule.ext
    intro s χ
    simp [e, eZ, realWeylParameter]
  have hspace (x : RealCharacterParameter F P) :
      e x ∈ relativeParameterSpace (F := F) q ↔ x ∈ relativeParameterSpace (F := F) p := by
    rw [relativeParameterSpace_eq_ker_centralRestriction r',
      relativeParameterSpace_eq_ker_centralRestriction r, LinearMap.mem_ker, LinearMap.mem_ker]
    change realCharacterParameterPullback (splitCentreParabolicLift r') (e.toLinearMap x) = 0 ↔ _
    rw [he]
    change (realCharacterParameterPullback (splitCentreParabolicLift r')).comp
      (realCharacterParameterPullback (π' ≫ c ≫ l)) x = 0 ↔ _
    rw [← realCharacterParameterPullback_comp, splitCentreParabolicLift_weyl r r' hπ' hw]
  have hmap : (relativeParameterSpace (F := F) p).map e.toLinearMap = relativeParameterSpace (F := F) q := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [hspace, Submodule.mem_map]
    exact ⟨fun ⟨z, hz, heq⟩ => e.injective heq ▸ hz, fun hx => ⟨x, hx, rfl⟩⟩
  exact ⟨e.ofSubmodules _ _ hmap, fun x => DFunLike.congr_fun he x.val⟩

end Parameters

/-- The actual functional equation, holomorphic finite intertwining expansions and
target Eisenstein continuation imply the one-way association of relative wave packets. -/
def RelativeWavePacketAssociationReductionStatement : Prop :=
  EisensteinFunctionalEquationStatement.{0} →
    IntertwiningSquareIntegrableExpansionStatement →
    EisensteinImaginaryContinuationStatement →
    RelativeWavePacketAssociationStatement

/-- The functional equation transports relative wave packets using finite square-integrable
intertwining expansions and target Eisenstein continuations on the imaginary axis. -/
theorem relativeWavePacketAssociation_of_inputs : RelativeWavePacketAssociationReductionStatement := by
  classical
  intro hFE hExpansion hContinue
    F _ _ G _ _ _ hG K N d rho hsmooth hcalc hKmax hrho P₀ _ p₀ _ _ _
    P M U A _ _ _ _ p _ iU l a r _ _ _ hA hT _ hU hK
    Q M' V A' _ _ _ _ q _ iV l' a' r' _ _ _ hA' hT' _ hV hK' w c hw Θ hΘ f hf
  obtain ⟨n, e, k, v, b, E, D, hv, hb, hD, hE, hreg, hΘeq⟩ := hΘ
  let : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  let : LocallyOfFiniteType Q.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := q) ‹IsClosedImmersion q.hom.hom.left›
  let : IsClosedImmersion (iU ≫ p).hom.hom.left :=
    IsClosedSubgroup.comp hU.1.isClosedSubgroup ‹IsClosedImmersion p.hom.hom.left›
  let : IsClosedImmersion (iV ≫ q).hom.hom.left :=
    IsClosedSubgroup.comp hV.1.isClosedSubgroup ‹IsClosedImmersion q.hom.hom.left›
  obtain ⟨-, -, π', -, -, hπ', -⟩ := r'.isCompatible.levi.exists_unipotentRadical_retraction
  let : Smooth G.X.hom := hG.smooth
  have hmul := r'.isIso_subgroupMultiplication_of_radical hV
  obtain ⟨eW, heW⟩ := exists_relativeWeylParameter_linearEquiv r r' hπ' hw
  let e' := e.trans eW
  have himag (x : Fin n → ℝ) :
      weylParameter l c π' (imaginaryParameter F P (e x : RealCharacterParameter F P)) =
        imaginaryParameter F Q (e' x : RealCharacterParameter F Q) := by
    rw [weylParameter_imaginaryParameter, ← heW]
    rfl
  have hexp (j : Fin k) := hExpansion F G P M U Q M' V A A' p iU l a r hA hT q iV l' a' r' π' w c
    hG hU hV hmul hπ' hw K hK hK' rho hsmooth hcalc (v j) hKmax hrho (hv j)
  choose m ψ coeff Dm hψ hDm hcoeff R hR using hexp
  let J := (j : Fin k) × Fin (m j)
  let index := Fintype.equivFin J
  let v' (i : Fin (Fintype.card J)) := ψ (index.symm i).1 (index.symm i).2
  have hv' (i : Fin (Fintype.card J)) := hψ (index.symm i).1 (index.symm i).2
  obtain ⟨E', D', hD', hE', hreg'⟩ :=
    hContinue F G Q M' V A' q iV l' a' r' hA' hT' hG hV K hK' rho hsmooth hcalc hKmax hrho _ v' hv'
  let b' (i : Fin (Fintype.card J)) (x : Fin n → ℝ) :=
    b (index.symm i).1 x *
      coeff (index.symm i).1 (index.symm i).2 (imaginaryParameter F P (e x : RealCharacterParameter F P))
  let : Module.Finite ℤ (rationalCharacters P) := (r.rationalCharacters_free_finite hG).2
  let : FiniteDimensional ℝ (RealCharacterParameter F P) := Module.Finite.base_change ℤ ℝ _
  let fullChart := (Module.finBasis ℝ (RealCharacterParameter F P)).equivFun.symm
  let toFull := fullChart.symm.toLinearMap.comp ((relativeParameterSpace p).subtype.comp e.toLinearMap)
  have hChart (x : Fin n → ℝ) : fullChart (toFull x) = (e x : RealCharacterParameter F P) :=
    fullChart.apply_symm_apply _
  have hSmooth (j : Fin k) (i : Fin (m j)) :
      ContDiff ℝ (⊤ : ℕ∞) fun x => coeff j i (imaginaryParameter F P (e x : RealCharacterParameter F P)) := by
    have h := (contDiff_comp_imaginaryParameter fullChart (hcoeff j i) (hDm j)).comp
      toFull.toContinuousLinearMap.contDiff
    simpa only [Function.comp_def, LinearMap.coe_toContinuousLinearMap', hChart] using h
  have hb' (i : Fin (Fintype.card J)) : ContDiff ℝ (⊤ : ℕ∞) (b' i) ∧ HasCompactSupport (b' i) :=
    ⟨(hb (index.symm i).1).1.mul (hSmooth (index.symm i).1 (index.symm i).2),
      (hb (index.symm i).1).2.mul_right⟩
  have hfun (j : Fin k) (x : Fin n → ℝ) (g : AdelicGroupPoints F G) :
      E j (imaginaryParameter F P (e x : RealCharacterParameter F P)) g =
        ∑ i : Fin (m j), coeff j i (imaginaryParameter F P (e x : RealCharacterParameter F P)) *
          E' (index ⟨j, i⟩) (imaginaryParameter F Q (e' x : RealCharacterParameter F Q)) g := by
    have hregJ (i : Fin (m j)) : ∃ R' : ℝ, ∀ lam, r'.IsRegularParameter hA' hT' R' lam →
        E' (index ⟨j, i⟩) lam = hK'.eisensteinSeries (ψ j i) lam := by
      have hV' : v' (index ⟨j, i⟩) = ψ j i :=
        congrArg (fun z : J => ψ z.1 z.2) (index.symm_apply_apply ⟨j, i⟩)
      simpa only [hV'] using hreg' (index ⟨j, i⟩)
    have heq := hFE F G P M U Q M' V A A' p iU l a r hA hT q iV l' a' r' hA' hT' π' w c
      hG hU hV hπ' hw K hK hK' rho hsmooth hcalc (v j) hKmax hrho (hv j).1
      (E j) D (hE j) (hreg j) (m j) (ψ j) (coeff j) (Dm j) (fun i => (hψ j i).1)
      (hcoeff j) ⟨R j, hR j⟩ (fun i => E' (index ⟨j, i⟩)) D'
      (fun i => hE' (index ⟨j, i⟩)) hregJ _ ⟨hD ⟨_, rfl⟩, hDm j ⟨_, rfl⟩⟩
      (by rw [himag x]; exact hD' ⟨_, rfl⟩) g
    simpa only [himag x] using heq
  apply Submodule.le_topologicalClosure _
  apply Submodule.subset_span
  refine ⟨Θ, ⟨n, e', Fintype.card J, v', b', E', D', hv', hb', hD', hE', hreg', ?_⟩, hf⟩
  rw [hΘeq]
  funext g
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [hfun, Finset.mul_sum]
  rw [← Fintype.sum_sigma', ← index.sum_comp]
  refine Finset.sum_congr rfl ?_
  rintro ⟨j, i⟩ _
  have hbIndex : b' (index ⟨j, i⟩) x =
      b j x * coeff j i (imaginaryParameter F P (e x : RealCharacterParameter F P)) :=
    congrArg (fun z : J => b z.1 x *
      coeff z.1 z.2 (imaginaryParameter F P (e x : RealCharacterParameter F P)))
      (index.symm_apply_apply ⟨j, i⟩)
  rw [hbIndex, mul_assoc]

end Langlands.Global
