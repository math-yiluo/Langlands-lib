import Langlands.Global.AdelicLeviCuspFormMajorantStatement
import Langlands.Global.AdelicEisensteinCuspidalTestRootHyperplaneStatement
import Langlands.Global.AdelicRootHyperplaneContinuationStatement
import Langlands.Global.AdelicLeadingCuspidalInjectivityStatement
import Langlands.Global.AdelicLocalRootClearing
import Langlands.Global.AdelicRootHyperplaneReduction
import Langlands.Global.AdelicPositiveChamberProof
import Langlands.Global.AdelicEisensteinContinuationStatement
import Langlands.Automorphic.GroupSchemePositiveMatrixEmbedding
import Langlands.Automorphic.GroupSchemeUniformGrowthEvaluation
import Langlands.Global.EisensteinConstantTerm.Height

/-! # Root-hyperplane singularities of Eisenstein series from their cuspidal tests

For a compact subgroup in good position with respect to a standard parabolic family, the
Eisenstein continuation with root-hyperplane singularities
(`EisensteinGoodPositionRootHyperplaneContinuationStatement`) follows from the
function-valued meromorphic continuation (`EisensteinMeromorphicContinuationStatement`),
the injectivity of leading cuspidal components (`LeadingCuspidalInjectivityStatement`), the
weighted majorants of cusp forms (`LeviCuspFormPairingMajorantStatement`) and the
root-hyperplane form of the cuspidal tests (`EisensteinCuspidalTestRootHyperplaneStatement`).
This is the pole-detection step of Bernstein–Lapid, §8.6. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Set
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G) (J : StandardIndex F G 𝓕.i 𝓕.ν)
  (ψ : AdelicGroupPoints F (𝓕.M J) → ℂ)
  (hψ : IsLeftInvariantUnder F (𝓕.M J) (rationalSubgroup F (𝓕.M J)) ψ)
  (hψc : Continuous ψ) (g : AdelicGroupPoints F G)
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)
  (hrho : IsClosedSubgroup rho) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth) (R : ℝ)
  (L : Subgroup (FiniteAdelicGroupPoints F G))
  (hbound : 𝓕.HasLeviPairingMajorant J ψ g rho R)
  {m : ℕ} {W : TopologicalSpace.Opens (Fin m → ℂ)}
  {f : W → UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L} {D : Set W}
  (E : (Fin m → ℂ) → AdelicGroupPoints F G → ℂ)
  (hE : ∀ t ∈ D, UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L (f t) = E t)

include hψ hψc hbound hE in
/-- The Levi pairing of the constant term of a family with a local uniform-growth
meromorphic presentation has local meromorphic data at every point of the presentation. -/
theorem hasLocalMeromorphicData_leviPairing_constantTerm
    (hf : IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) f D) {s : Fin m → ℂ} (hs : s ∈ W) :
    HasLocalMeromorphicData
      (fun (_ : Unit) t => 𝓕.leviPairing J (𝓕.constantTerm J (E t)) g ψ) s :=
  hasLocalMeromorphicData_of_isMeromorphicOn hf
    (fun _ => 𝓕.constantTermLeviPairingCLM J ψ hψ g rho hN hrho hsmooth hcalc R L hψc hbound)
    (fun t ht _ => by rw [constantTermLeviPairingCLM_apply, hE t ht]) hs

include hψ hψc hbound hE in
/-- The Levi pairing of the constant term of a family with a local uniform-growth
meromorphic presentation is holomorphic on the domain of the presentation. -/
theorem differentiableOn_leviPairing_constantTerm
    (hf : IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) f D) :
    DifferentiableOn ℂ (fun t => 𝓕.leviPairing J (𝓕.constantTerm J (E t)) g ψ)
      (Subtype.val '' D) := by
  refine (differentiableOn_extendOpens hf.1 (hf.2.2.1
    (𝓕.constantTermLeviPairingCLM J ψ hψ g rho hN hrho hsmooth hcalc R L hψc hbound))).congr ?_
  rintro _ ⟨t, ht, rfl⟩
  rw [extendOpens_coe, constantTermLeviPairingCLM_apply, hE t ht]

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- `EisensteinRootHyperplaneContinuationStatement` for a compact subgroup in good position.
It has the binders and hypotheses of that statement, a standard parabolic family `𝓕`, and
the hypotheses that `P₀(𝔸)K = G(𝔸)` for the minimal standard parabolic `P₀` of `𝓕` and that
`K ∩ M_J(𝔸)` is maximal compact in every standard Levi `M_J(𝔸)`; its conclusion is the same:
one pointwise meromorphic continuation of `E(φ, λ)`, equal to the series for `Re λ`
sufficiently regular, whose singularities near every point are cleared by a power of one
product of root forms, uniformly in `g`. -/
def EisensteinGoodPositionRootHyperplaneContinuationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    ∀ (𝓕 : StandardParabolicFamily F G) (K : Subgroup (AdelicGroupPoints F G))
      (hK : IsIwasawaCompact p K),
      IsIwasawaCompact (𝓕.p ⟨∅, Set.empty_subset _⟩) K →
      (∀ J : StandardIndex F G 𝓕.i 𝓕.ν, IsMaximalCompactSubgroup F (𝓕.M J)
        (K.comap (AdelicGroupPoints.map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)).toMonoidHom)) →
      ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
        (hsmooth : SmoothOfRelativeDimension d G.X.hom)
        (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
        IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
        IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
          (K.comap (ofInfinite F G).toMonoidHom) rho φ →
        ∃ (EP : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
          (DP : Set (ComplexCharacterParameter F P)),
          (∀ g, IsMeromorphicInCoordinatesOn (fun lam => EP lam g) DP) ∧
          (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
            EP lam = hK.eisensteinSeries φ lam) ∧
          ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) (s₀ : Fin n → ℂ),
            ∃ (S : Finset (characterLattice A)) (m : ℕ) (W : Set (Fin n → ℂ)),
              (S : Set (characterLattice A)) ⊆ r.unipotentRoots ∧ IsOpen W ∧ s₀ ∈ W ∧
              ∀ g : AdelicGroupPoints F G, ∃ h : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ h W ∧
                ∀ s ∈ W, e s ∈ DP →
                  h s = (∏ β ∈ S, r.rootFunctional hA hT β (e s - e s₀)) ^ m * EP (e s) g

/-- The reduction of `EisensteinGoodPositionRootHyperplaneContinuationStatement` to the
function-valued continuation, the injectivity of leading cuspidal components, the weighted
majorants of cusp forms and the root-hyperplane form of the cuspidal tests. -/
def EisensteinGoodPositionRootHyperplaneReductionStatement : Prop :=
  EisensteinMeromorphicContinuationStatement.{u} → LeadingCuspidalInjectivityStatement.{u} →
    LeviCuspFormPairingMajorantStatement.{u} → EisensteinCuspidalTestRootHyperplaneStatement.{u} →
      EisensteinGoodPositionRootHyperplaneContinuationStatement.{u}

/-- **Pole detection by cuspidal tests** (Bernstein–Lapid §8.6). The Eisenstein continuation
with root-hyperplane singularities for compact subgroups in good position follows from the
function-valued continuation, the injectivity of leading cuspidal components, the weighted
majorants of cusp forms and the root-hyperplane form of the cuspidal tests. -/
theorem eisensteinGoodPositionRootHyperplaneReduction :
    EisensteinGoodPositionRootHyperplaneReductionStatement.{u} := by
  classical
  intro hCont hinj hmaj htest F _ _ G P M U A _ _ _ _ p _ iU l a r _ _ _ hA hT hG hU 𝓕 K hK hKmin hKlevi N d rho
    hsmooth hcalc φ hKmax hrho hφ
  obtain ⟨m, ⟨e₀⟩⟩ := exists_complexParameterEquiv hG r.isCompatible.parabolic
  have : FiniteDimensional ℂ (ComplexCharacterParameter F P) :=
    FiniteDimensional.of_injective e₀.symm.toLinearMap e₀.symm.injective
  obtain ⟨N', rho', hN', hrho', htransfer⟩ :=
    exists_positiveMatrixEmbedding_of_isClosedSubgroup rho hrho hsmooth hcalc
  have hφ' := (htransfer _ _ _).mp hφ
  obtain ⟨E', ⟨R₀, hR₀⟩, hLocal⟩ := hCont F G P M U A p iU l a r hA hT hG hU K hK rho' hN'
    hrho' hsmooth hcalc φ hKmax hφ'
  obtain ⟨Γ, D', hΓ, hclear⟩ := htest F G P M U A p iU l a r hA hT hG hU 𝓕 K hK hKmin hKlevi
    rho' hsmooth hcalc φ hKmax hrho' hφ'
  have hweight := hmaj F G 𝓕 K hKmax hKmin hKlevi rho' hrho'
  obtain ⟨lam₀, h₀⟩ := positiveChamberNonempty F G P M A p l a r hA hT hG
  -- Local meromorphy of the point evaluations.
  have hEloc : ∀ s, HasLocalMeromorphicData (fun y t => E' (e₀ t) y) s := by
    intro s
    obtain ⟨W, hsW, R, L, -, f, D, hf, hE⟩ := hLocal m e₀ s
    exact hasLocalMeromorphicData_of_isMeromorphicOn hf
      (UniformGrowthFrechetSpace.evaluation F G rho' hsmooth hcalc hN' hrho' R L)
      (φ := fun y t => E' (e₀ t) y)
      (fun t ht y => by rw [UniformGrowthFrechetSpace.evaluation_apply, (hE t ht).1]) hsW
  -- Root clearing at every point, from the cuspidal tests.
  have hrc : ∀ s₀, HasLocalRootClearing r.unipotentRoots (r.rootFunctional hA hT) E' e₀ s₀ := by
    intro s₀
    obtain ⟨W, hsW, R, L, hL, f, D, hf, hE⟩ := hLocal m e₀ s₀
    obtain ⟨S, k, Wc, hS, hWc, hs₀c, hh⟩ := hclear m e₀ s₀
    refine UniformGrowthFrechetSpace.hasLocalRootClearing_of_cuspidal_pairings F G rho' hsmooth
      hcalc hN' hrho' R L 𝓕 K hinj hKmax hKmin hKlevi hL (fun J ψ hψ g => hweight J ψ hψ g R)
      r.unipotentRoots (r.rootFunctional hA hT) E' e₀ s₀ hsW hf
      (fun t ht => ⟨(hE t ht).1, by rw [(hE t ht).1]; exact (hE t ht).2⟩)
      ⟨S, k, Wc, hS, hWc, hs₀c, ?_⟩
    intro J ψ hψ g
    -- The test of the continuation is meromorphic on the whole coordinate space.
    let τ : (Fin m → ℂ) → ℂ := fun t => 𝓕.leviPairing J (𝓕.constantTerm J (E' (e₀ t))) g ψ
    have hτloc : ∀ s, HasLocalMeromorphicData (fun (_ : Unit) => τ) s := by
      intro s
      obtain ⟨W₁, hsW₁, R₁, L₁, -, f₁, D₁, hf₁, hE₁⟩ := hLocal m e₀ s
      exact 𝓕.hasLocalMeromorphicData_leviPairing_constantTerm J ψ hψ.1.1 hψ.1.2.1.1 g rho' hN'
        hrho' hsmooth hcalc R₁ L₁ (hweight J ψ hψ g R₁) (fun t => E' (e₀ t))
        (fun t ht => (hE₁ t ht).1) hf₁ hsW₁
    obtain ⟨Dτ, hDτ⟩ := exists_isMeromorphicOn_of_local hτloc
    have hτm : IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) τ Dτ := hDτ ()
    obtain ⟨h, hhd, hheq⟩ := hh J ψ hψ g
    obtain ⟨hΓm, Rγ, hRγ⟩ := hΓ J ψ hψ g
    obtain ⟨O, hOo, hOne, hOreg⟩ := exists_isOpen_isRegularParameter r hA hT h₀ (max R₀ Rγ) e₀
    let pr : (Fin m → ℂ) → ℂ := fun s => (∏ β ∈ S, r.rootFunctional hA hT β (e₀ s - e₀ s₀)) ^ k
    have hpr : Continuous pr :=
      (differentiable_centeredLinearProduct (r.rootFunctional hA hT) e₀ s₀ S k).continuous
    obtain ⟨h', hh'd, hh'eq⟩ := exists_eq_mul_of_eqOn_isOpen (f₁ := τ)
      (f₂ := fun s => Γ J ψ g (e₀ s)) (Or.inl hτm) (Or.inl (hΓm.2 m e₀)) hOo hOne
      (fun s hs => by
        have h1 := hR₀ (e₀ s) ((hOreg s hs).mono r hA hT (le_max_left _ _))
        have h2 := hRγ (e₀ s) ((hOreg s hs).mono r hA hT (le_max_right _ _))
        change 𝓕.leviPairing J (𝓕.constantTerm J (E' (e₀ s))) g ψ = Γ J ψ g (e₀ s)
        rw [h1, h2])
      hWc hpr hhd (fun s hs hs' => hheq s hs hs')
    -- The test of the presentation is holomorphic on its domain.
    have hτD : DifferentiableOn ℂ τ (Subtype.val '' D) :=
      𝓕.differentiableOn_leviPairing_constantTerm J ψ hψ.1.1 hψ.1.2.1.1 g rho' hN' hrho' hsmooth
        hcalc R L (hweight J ψ hψ g R) (fun t => E' (e₀ t)) (fun t ht => (hE t ht).1) hf
    have hDo : IsOpen (Subtype.val '' D) := W.isOpen.isOpenMap_subtype_val _ hf.1
    have hO' : IsOpen (Wc ∩ Subtype.val '' D) := hWc.inter hDo
    have heqO : EqOn h' (fun s => pr s * τ s) (Wc ∩ Subtype.val '' D) := by
      apply EqOn.of_subset_closure (s := (Wc ∩ Subtype.val '' D) ∩ Dτ)
      · exact fun s hs => hh'eq s hs.1.1 hs.2
      · exact (hh'd.mono inter_subset_left).continuousOn
      · exact hpr.continuousOn.mul (hτD.mono inter_subset_right).continuousOn
      · exact inter_subset_left
      · intro s hs
        exact hO'.inter_closure ⟨hs, hτm.2.1 s⟩
    refine ⟨h', hh'd, fun t ht htW => ?_⟩
    have hval := heqO ⟨htW, t, ht, rfl⟩
    change h' t = pr t * 𝓕.leviPairing J (𝓕.constantTerm J
      (UniformGrowthFrechetSpace.toFun F G rho' hsmooth hcalc hN' hrho' R L (f t))) g ψ
    rw [(hE t ht).1]
    exact hval
  obtain ⟨DP, hDP, hroot⟩ := exists_meromorphicInCoordinatesOn_of_local_rootClearing
    r.unipotentRoots (r.rootFunctional hA hT) E' e₀ hEloc hrc
  exact ⟨E', DP, hDP, ⟨R₀, hR₀⟩, hroot⟩

end Langlands.Global
