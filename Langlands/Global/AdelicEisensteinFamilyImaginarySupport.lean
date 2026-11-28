import Langlands.Global.AdelicEisensteinFamilyRegularity

/-! # Continuity and split-centre covariance on the imaginary support -/

noncomputable section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Set Module
open scoped CategoryTheory.MonObj

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Langlands.Analysis.Meromorphic
  Langlands.Automorphic.GroupSchemeFunctions

local notation "Z[" n "]" => (Fin n → ℝ)

section CentralInducingFamily

variable {F : Type} [Field F] [NumberField F] {G P M : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  {A Z : CommGroupScheme (Spec (CommRingCat.of F))}
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem centralInducingFamily
    [IsAffineHom G.X.hom] (r : ParabolicRootPresentation p l a)
    (j : Z.toGrp ⟶ M) (hj : IsCentral (j ≫ l ≫ p)) (hZ : IsSplitTorus Z.toGrp)
    {q : ℕ} {v : Fin q → AdelicGroupPoints F G → ℂ}
    (hv : ∀ j₀, IsSplitComponentEquivariant p l (v j₀))
    (y : PositiveRealTorus.intrinsicSubgroup F Z) :
    let z := map F P G p (map F Z.toGrp P (j ≫ l) y)
    (∀ g, z * g = g * z) ∧ (∀ j₀ g, v j₀ (z * g) = 1 * v j₀ g) := by
  intro z
  let : IsAffineHom Z.toGrp.X.hom := hZ.isAffineHom
  let : IsAffine Z.toGrp.X.left := isAffine_of_isAffineHom Z.toGrp.X.hom
  have hpcl := r.isCompatible.parabolic.isClosedSubgroup
  have hlcl := r.isCompatible.levi.isClosedSubgroup.comp hpcl
  let : Mono p.hom.hom.left := hpcl.mono
  let : Mono (l ≫ p).hom.hom.left := hlcl.mono
  let : Mono p.hom.hom := Over.mono_of_mono_left _
  let : Mono (l ≫ p).hom.hom := Over.mono_of_mono_left _
  have hjc := CoverPreimage.isCentral_of_comp_mono hj (l ≫ p) j rfl
  obtain ⟨k, hk⟩ := r.isCompatible.splitComponent.exists_factor hZ hjc
  have hy : map F Z.toGrp M j y ∈ RestrictionSplitCentre.canonicalSubgroup F M := by
    rw [← RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup r.isCompatible.splitComponent]
    refine ⟨PositiveRealTorus.pointMap F Z.toGrp A.toGrp (Adeles F) k y,
      PositiveRealTorus.map_intrinsicSubgroup_le F Z A (Additive.ofMul k) ⟨y, y.2, rfl⟩, ?_⟩
    rw [← hk]
    rfl
  have hjP : IsCentral ((j ≫ l) ≫ p) := by rwa [Category.assoc]
  have hp : map F M P l (map F Z.toGrp M j y) = map F Z.toGrp P (j ≫ l) y := rfl
  refine ⟨fun g => (PositiveRealTorus.positivePointMap_commute F G Z ((j ≫ l) ≫ p) hjP y g).eq, ?_⟩
  intro j₀ g
  change v j₀ (map F P G p (map F Z.toGrp P (j ≫ l) y) * g) = 1 * v j₀ g
  rw [← hp, hv j₀ _ hy g, hp, parameterPower_halfModulus_map_of_isCentral hjP y]

/-- Restrict a continued Eisenstein family to a real chart of its imaginary support and obtain
its covariance under the rational subgroup and a split centre that factors through the Levi. -/
def EisensteinFamilyImaginarySupportStatement
    [IsAffineHom G.X.hom] [IsClosedImmersion p.hom.hom.left] : Prop :=
  EisensteinPointwiseContinuationStatement.{0} → EisensteinJointRootHyperplaneStatement.{0} →
  ∀ {U : GroupScheme (Spec (CommRingCat.of F))} (iU : U ⟶ P)
    (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (_hG : IsConnectedReductive G) (_hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
    (_hKmax : IsMaximalCompactSubgroup F G K)
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (_hrho : IsClosedSubgroup rho)
    {q n m : ℕ} (v : Fin q → AdelicGroupPoints F G → ℂ)
    (b : Fin q → ComplexCharacterParameter F P → ℂ)
    (E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ) (DE : Set (ComplexCharacterParameter F P))
    (_hv : ∀ j, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (v j))
    (_hb : ∀ j, IsMeromorphicInCoordinatesOn (b j) univ)
    (_hE : ∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) DE)
    (ec : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P)
    (_hPatch : ∀ R : ℝ, ∃ V : Set (Fin m → ℂ), IsOpen V ∧ V.Nonempty ∧
      ∀ t ∈ V, r.IsRegularParameter hA hT R (ec t) ∧
        ∀ g, E (ec t) g = ∑ j, b j (ec t) * hK.eisensteinSeries (v j) (ec t) g)
    (e : Z[n] ≃ₗ[ℝ] RealCharacterParameter F P) (C : Set Z[n])
    (_hC : ∀ x ∈ C, imaginaryParameter F P (e x) ∈ DE)
    (j : Z.toGrp ⟶ M) (_hj : IsCentral (j ≫ l ≫ p)) (_hZ : IsSplitTorus Z.toGrp),
    ContinuousOn (fun z : Z[n] × AdelicGroupPoints F G => E (imaginaryParameter F P (e z.1)) z.2)
      (C ×ˢ univ) ∧
    (∀ x ∈ C, IsLeftInvariantUnder F G (rationalSubgroup F G) (E (imaginaryParameter F P (e x)))) ∧
    ∀ x ∈ C, ∀ (y : PositiveRealTorus.intrinsicSubgroup F Z) (g : AdelicGroupPoints F G),
      E (imaginaryParameter F P (e x)) (g * map F P G p (map F Z.toGrp P (j ≫ l) y)) =
        parameterPower F P (imaginaryParameter F P (e x)) (map F Z.toGrp P (j ≫ l) y) *
          E (imaginaryParameter F P (e x)) g

set_option maxHeartbeats 1000000 in
/-- Use the imaginary linear chart and triviality of the half-modulus on the split centre. -/
theorem eisensteinFamily_regularOn_imaginarySupport
    [IsAffineHom G.X.hom] [IsClosedImmersion p.hom.hom.left] :
    EisensteinFamilyImaginarySupportStatement (p := p) (l := l) (a := a) (Z := Z) := by
  intro hPt hJoint U iU r _ _ _ hA hT hG hU K hK hKmax N d rho hsmooth hcalc hrho q n m
    v b E DE hv hb hE ec hPatch e C hC j hj hZ
  obtain ⟨hcont, hinv, hcent⟩ :=
    eisensteinFamilyRegularity hPt hJoint F G P M U A p iU l a r hA hT hG hU
      K hK rho hsmooth hcalc hKmax hrho q v b E DE (fun j => (hv j).1) hb hE ec hPatch
  refine ⟨?_, fun x hx => hinv _ (hC x hx), ?_⟩
  · let θ : Z[n] →ₗ[ℝ] (Fin m → ℂ) :=
      (ec.symm.toLinearMap.restrictScalars ℝ).comp ((imaginaryParameter F P).comp e.toLinearMap)
    have hθ (x : Z[n]) : ec (θ x) = imaginaryParameter F P (e x) := ec.apply_symm_apply _
    let L (z : Z[n] × AdelicGroupPoints F G) := (θ z.1, z.2)
    have hL : Continuous L := (θ.continuous_of_finiteDimensional.comp continuous_fst).prodMk continuous_snd
    have hmap : MapsTo L (C ×ˢ univ) ((ec ⁻¹' DE) ×ˢ univ) :=
      fun z hz => ⟨show ec (θ z.1) ∈ DE from hθ z.1 ▸ hC z.1 hz.1, mem_univ _⟩
    convert hcont.comp hL.continuousOn hmap using 1
    funext z
    change E (imaginaryParameter F P (e z.1)) z.2 = E (ec (θ z.1)) z.2
    rw [hθ]
  · intro x hx y g
    obtain ⟨hcomm, hfixed⟩ := centralInducingFamily r j hj hZ (fun j₀ => (hv j₀).2.1) y
    simpa only [one_mul] using hcent 1 hcomm hfixed _ (hC x hx) g

end CentralInducingFamily

end Langlands.Global
