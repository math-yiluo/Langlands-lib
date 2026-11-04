import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.Representation.Plancherel.ParabolicIntertwiningRegion
import Langlands.Representation.Plancherel.UnramifiedOperatorTransport

/-! # Canonical character regions on the literal supplied Levi subgroup -/

noncomputable section

universe u uV uW

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {M G P P' Q U V : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {p' : P' ⟶ G} {l' : M ⟶ P'}
  {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance parabolicPointIntertwiningRegionAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance parabolicPointIntertwiningRegionAmbientPointTopology : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
local instance parabolicPointIntertwiningRegionLeviPointTopology : TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X

/-- The actual image of the specified Levi in the identity-test point group. -/
abbrev parabolicLeviPointSubgroup (p : P ⟶ G) (l : M ⟶ P) :
    Subgroup (rationalPoints G) :=
  (SubgroupFunctor.range (l ≫ p)).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))

include r

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffine M.X.left] in
private theorem leviComposite_closed : IsClosedSubgroup (l ≫ p) :=
  r.isCompatible.levi.isClosedSubgroup.comp r.isCompatible.parabolic.isClosedSubgroup

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffine M.X.left] in
private theorem leviComposite_represented :
    (SubgroupFunctor.range (l ≫ p)).IsRepresentedBy (l ≫ p) := by
  have : IsClosedImmersion (l ≫ p).hom.hom.left := leviComposite_closed r
  exact ⟨Over.mono_of_mono_left _, rfl⟩

/-- The canonical topology on the specified Levi scheme agrees with the
inherited topology of its literal ambient point subgroup. -/
def parabolicLeviPointHomeomorph :
    rationalPoints M ≃ₜ* parabolicLeviPointSubgroup p l :=
  rationalPointSubgroupHomeomorph F (SubgroupFunctor.range (l ≫ p)) (l ≫ p)
    (leviComposite_represented r) (leviComposite_closed r)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
@[simp]
theorem parabolicLeviPointHomeomorph_apply_coe (m : rationalPoints M) :
    (parabolicLeviPointHomeomorph r m : rationalPoints G) =
      rationalPoints.map (l ≫ p) m := rfl

omit [IsAffine M.X.left] in
theorem isClosed_parabolicLeviPointSubgroup :
    IsClosed (parabolicLeviPointSubgroup p l : Set (rationalPoints G)) := by
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  exact isClosed_rationalPoint_subgroup F (SubgroupFunctor.range (l ≫ p)) (l ≫ p)
    (leviComposite_represented r) (leviComposite_closed r)

/-- All actual rational-character norms on the literal Levi point subgroup. -/
def parabolicLeviRationalNormCharacters :
    rationalCharacters M → (parabolicLeviPointSubgroup p l →* ℝ≥0ˣ) :=
  fun χ => (rationalNormCharacters M χ).toMul.comp
    (parabolicLeviPointHomeomorph r).symm.toMulEquiv.toMonoidHom

theorem continuous_parabolicLeviRationalNormCharacters (χ : rationalCharacters M) :
    Continuous (parabolicLeviRationalNormCharacters r χ) :=
  (rationalNormContinuousCharacter M χ).continuous.comp
    (parabolicLeviPointHomeomorph r).symm.continuous

@[simp]
theorem parabolicLeviRationalNormCharacters_apply_points (χ : rationalCharacters M)
    (m : rationalPoints M) :
    parabolicLeviRationalNormCharacters r χ (parabolicLeviPointHomeomorph r m) =
      (rationalNormCharacters M χ).toMul m := by
  change (rationalNormCharacters M χ).toMul
    ((parabolicLeviPointHomeomorph r).symm (parabolicLeviPointHomeomorph r m)) = _
  rw [(parabolicLeviPointHomeomorph r).symm_apply_apply]

/-- Transport the existing canonical characters through the actual Levi
point homeomorphism, preserving the full indexed rational norm family. -/
def parabolicLeviUnramifiedCharactersHomeomorph :
    unramifiedCharacters (fun χ => (rationalNormCharacters M χ).toMul) ≃ₜ*
      unramifiedCharacters (parabolicLeviRationalNormCharacters r) :=
  unramifiedCharactersHomeomorph (parabolicLeviPointHomeomorph r)
    (fun χ => (rationalNormCharacters M χ).toMul)

@[simp]
theorem parabolicLeviUnramifiedCharactersHomeomorph_apply
    (χ : unramifiedCharacters (fun ψ => (rationalNormCharacters M ψ).toMul))
    (m : parabolicLeviPointSubgroup p l) :
    (parabolicLeviUnramifiedCharactersHomeomorph r χ).val m =
      χ.val ((parabolicLeviPointHomeomorph r).symm m) := rfl

@[simp]
theorem parabolicLeviUnramifiedCharactersHomeomorph_symm_apply
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r))
    (m : rationalPoints M) :
    ((parabolicLeviUnramifiedCharactersHomeomorph r).symm χ).val m =
      χ.val (parabolicLeviPointHomeomorph r m) := rfl

/-- The actual split-component map into the literal Levi point subgroup. -/
def parabolicSplitComponentPointHom :
    rationalPoints A.toGrp →* parabolicLeviPointSubgroup p l :=
  (parabolicLeviPointHomeomorph r).toMulEquiv.toMonoidHom.comp (rationalPoints.map a)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
@[simp]
theorem parabolicSplitComponentPointHom_apply_coe (x : rationalPoints A.toGrp) :
    (parabolicSplitComponentPointHom r x : rationalPoints G) =
      rationalPoints.map (a ≫ l ≫ p) x := rfl

/-- The same strict full-root region, now on the literal Levi point subgroup. -/
def parabolicPointUnramifiedIntertwiningRegion
    (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A))
    (n : U ⟶ P) (q : Q ⟶ G) (v : V ⟶ Q) (R : ℝ) :
    Set (unramifiedCharacters (parabolicLeviRationalNormCharacters r)) :=
  (parabolicLeviUnramifiedCharactersHomeomorph r).symm ⁻¹'
    parabolicUnramifiedIntertwiningRegion r B n q v R

@[simp]
theorem parabolicPointUnramifiedIntertwiningRegion_preimage
    (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A))
    (n : U ⟶ P) (q : Q ⟶ G) (v : V ⟶ Q) (R : ℝ) :
    (parabolicLeviUnramifiedCharactersHomeomorph r) ⁻¹'
        parabolicPointUnramifiedIntertwiningRegion r B n q v R =
      parabolicUnramifiedIntertwiningRegion r B n q v R := by
  ext χ
  simp only [Set.mem_preimage, parabolicPointUnramifiedIntertwiningRegion,
    (parabolicLeviUnramifiedCharactersHomeomorph r).symm_apply_apply]

/-- The exact corresponding threshold-region subtypes. -/
def parabolicIntertwiningParameterEquiv
    (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A))
    (n : U ⟶ P) (q : Q ⟶ G) (v : V ⟶ Q) (R : ℝ) :
    parabolicUnramifiedIntertwiningRegion r B n q v R ≃
      parabolicPointUnramifiedIntertwiningRegion r B n q v R :=
  (parabolicLeviUnramifiedCharactersHomeomorph r).toEquiv.subtypeEquiv (fun χ => by
    change χ ∈ parabolicUnramifiedIntertwiningRegion r B n q v R ↔
      (parabolicLeviUnramifiedCharactersHomeomorph r).symm
        (parabolicLeviUnramifiedCharactersHomeomorph r χ) ∈
          parabolicUnramifiedIntertwiningRegion r B n q v R
    rw [(parabolicLeviUnramifiedCharactersHomeomorph r).symm_apply_apply])

@[simp]
theorem parabolicIntertwiningParameterEquiv_apply
    (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A))
    (n : U ⟶ P) (q : Q ⟶ G) (v : V ⟶ Q) (R : ℝ)
    (χ : parabolicUnramifiedIntertwiningRegion r B n q v R) :
    (parabolicIntertwiningParameterEquiv r B n q v R χ).val =
      parabolicLeviUnramifiedCharactersHomeomorph r χ.val := rfl

@[simp]
theorem parabolicIntertwiningParameterEquiv_symm_apply
    (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A))
    (n : U ⟶ P) (q : Q ⟶ G) (v : V ⟶ Q) (R : ℝ)
    (χ : parabolicPointUnramifiedIntertwiningRegion r B n q v R) :
    ((parabolicIntertwiningParameterEquiv r B n q v R).symm χ).val =
      (parabolicLeviUnramifiedCharactersHomeomorph r).symm χ.val := rfl

/-- Restrict the evaluation-generated regular-function equivalence to the
actual scheme-Levi and literal-point character spaces. -/
def parabolicLeviRegularFunctionsEquiv :
    unramifiedRegularFunctions (fun χ => (rationalNormCharacters M χ).toMul) ≃ₐ[ℂ]
      unramifiedRegularFunctions (parabolicLeviRationalNormCharacters r) :=
  unramifiedRegularFunctionsEquiv (parabolicLeviPointHomeomorph r)
    (fun χ => (rationalNormCharacters M χ).toMul)

@[simp]
theorem parabolicLeviRegularFunctionsEquiv_apply
    (b : unramifiedRegularFunctions (fun χ => (rationalNormCharacters M χ).toMul))
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r)) :
    (parabolicLeviRegularFunctionsEquiv r b).val χ =
      b.val ((parabolicLeviUnramifiedCharactersHomeomorph r).symm χ) := rfl

@[simp]
theorem parabolicLeviRegularFunctionsEquiv_symm_apply
    (b : unramifiedRegularFunctions (parabolicLeviRationalNormCharacters r))
    (χ : unramifiedCharacters (fun ψ => (rationalNormCharacters M ψ).toMul)) :
    ((parabolicLeviRegularFunctionsEquiv r).symm b).val χ =
      b.val (parabolicLeviUnramifiedCharactersHomeomorph r χ) :=
  unramifiedRegularFunctionsEquiv_symm_apply _ _ b χ

@[simp]
theorem parabolicLeviRegularFunctionsEquiv_evaluation (m : rationalPoints M) :
    parabolicLeviRegularFunctionsEquiv r
        (unramifiedEvaluationRegular (fun χ => (rationalNormCharacters M χ).toMul) m) =
      unramifiedEvaluationRegular (parabolicLeviRationalNormCharacters r)
        (parabolicLeviPointHomeomorph r m) :=
  unramifiedRegularFunctionsEquiv_evaluation _ _ m

section OperatorFamilies

variable {E₁ : Type uV} [AddCommGroup E₁] [Module ℂ E₁]
  {E₂ : Type uW} [AddCommGroup E₂] [Module ℂ E₂]
  (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A))
  (n : U ⟶ P) (q : Q ⟶ G) (v : V ⟶ Q) (R : ℝ)

theorem isPolynomialOn_parabolicIntertwiningParameterEquiv_iff
    (f : parabolicPointUnramifiedIntertwiningRegion r B n q v R → E₂) :
    UnramifiedOperatorFamily.IsPolynomialOn
        (parabolicUnramifiedIntertwiningRegion r B n q v R)
        (fun χ => f (parabolicIntertwiningParameterEquiv r B n q v R χ)) ↔
      UnramifiedOperatorFamily.IsPolynomialOn
        (parabolicPointUnramifiedIntertwiningRegion r B n q v R) f := by
  constructor
  · rintro ⟨k, b, w, hf⟩
    refine ⟨k, fun i => parabolicLeviRegularFunctionsEquiv r (b i), w, ?_⟩
    intro χ
    have h := hf ((parabolicIntertwiningParameterEquiv r B n q v R).symm χ)
    simp only [Equiv.apply_symm_apply] at h
    simpa only [parabolicLeviRegularFunctionsEquiv_apply,
      parabolicIntertwiningParameterEquiv_symm_apply] using h
  · rintro ⟨k, b, w, hf⟩
    refine ⟨k, fun i => (parabolicLeviRegularFunctionsEquiv r).symm (b i), w, ?_⟩
    intro χ
    simpa only [parabolicLeviRegularFunctionsEquiv_symm_apply,
      parabolicIntertwiningParameterEquiv_apply] using
        hf (parabolicIntertwiningParameterEquiv r B n q v R χ)

theorem isPolynomialOperatorOn_parabolicIntertwiningParameterEquiv_iff
    (T : parabolicPointUnramifiedIntertwiningRegion r B n q v R → E₁ →ₗ[ℂ] E₂) :
    UnramifiedOperatorFamily.IsPolynomialOperatorOn
        (parabolicUnramifiedIntertwiningRegion r B n q v R)
        (fun χ => T (parabolicIntertwiningParameterEquiv r B n q v R χ)) ↔
      UnramifiedOperatorFamily.IsPolynomialOperatorOn
        (parabolicPointUnramifiedIntertwiningRegion r B n q v R) T :=
  forall_congr' (fun x =>
    isPolynomialOn_parabolicIntertwiningParameterEquiv_iff r B n q v R (fun χ => T χ x))

/-- One common regular denominator transports on these exact regions. -/
theorem isRationalOperatorOn_parabolicIntertwiningParameterEquiv_iff
    (T : parabolicPointUnramifiedIntertwiningRegion r B n q v R → E₁ →ₗ[ℂ] E₂) :
    UnramifiedOperatorFamily.IsRationalOperatorOn
        (parabolicUnramifiedIntertwiningRegion r B n q v R)
        (fun χ => T (parabolicIntertwiningParameterEquiv r B n q v R χ)) ↔
      UnramifiedOperatorFamily.IsRationalOperatorOn
        (parabolicPointUnramifiedIntertwiningRegion r B n q v R) T := by
  constructor
  · rintro ⟨b, hb, hT⟩
    refine ⟨parabolicLeviRegularFunctionsEquiv r b, ?_, ?_⟩
    · intro χ
      simpa only [parabolicLeviRegularFunctionsEquiv_apply,
        parabolicIntertwiningParameterEquiv_symm_apply] using
          hb ((parabolicIntertwiningParameterEquiv r B n q v R).symm χ)
    · apply (isPolynomialOperatorOn_parabolicIntertwiningParameterEquiv_iff
        r B n q v R _).mp
      simpa only [parabolicLeviRegularFunctionsEquiv_apply, parabolicIntertwiningParameterEquiv_apply,
        (parabolicLeviUnramifiedCharactersHomeomorph r).symm_apply_apply] using hT
  · rintro ⟨b, hb, hT⟩
    refine ⟨(parabolicLeviRegularFunctionsEquiv r).symm b, ?_, ?_⟩
    · intro χ
      simpa only [parabolicLeviRegularFunctionsEquiv_symm_apply,
        parabolicIntertwiningParameterEquiv_apply] using
          hb (parabolicIntertwiningParameterEquiv r B n q v R χ)
    · simpa only [parabolicLeviRegularFunctionsEquiv_symm_apply,
        parabolicIntertwiningParameterEquiv_apply]
        using (isPolynomialOperatorOn_parabolicIntertwiningParameterEquiv_iff
          r B n q v R (fun χ => b.val χ.val • T χ)).mpr hT

end OperatorFamilies

section RootLaws

variable [Smooth G.X.hom] [LocallyOfFiniteType M.X.hom]
  (r' : ParabolicRootPresentation p' l' a) (hM : l ≫ p = l' ≫ p')
  {n : U ⟶ P} (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
  {q : Q ⟶ G}
  (hQ : (Dynamic.parabolic
    (CommGroupScheme.groupHom (-r'.splitComponentCocharacter) ≫ a ≫ l' ≫ p')).IsRepresentedBy q)
  {v : V ⟶ Q} (hv : LeviSubgroup.IsGeometricUnipotentRadical v)

include r r' hM hn hQ hv

omit [LocallyOfFiniteType M.X.hom] in
theorem mem_parabolicPointUnramifiedIntertwiningRegion
    (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A)) (R : ℝ)
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r)) :
    χ ∈ parabolicPointUnramifiedIntertwiningRegion r B n q v R ↔
      ∀ α ∈ relativeRoots (a ≫ l ≫ p),
        0 < latticePairing A α r.splitComponentCocharacter →
          latticePairing A α r'.splitComponentCocharacter < 0 →
            R < B (SplitTorus.normalizedRealPart
              r.isCompatible.splitComponent.1.isSplitSubtorus.1
              (χ.val.toMonoidHom.comp (parabolicSplitComponentPointHom r)))
                ((1 : ℝ) ⊗ₜ[ℤ] α) :=
  mem_parabolicUnramifiedIntertwiningRegion r r' hM hn hQ hv B R
    ((parabolicLeviUnramifiedCharactersHomeomorph r).symm χ)

theorem parabolicPointUnramifiedIntertwiningRegion_nonempty
    (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A)) (hB : B.Nondegenerate)
    (R : ℝ) :
    (parabolicPointUnramifiedIntertwiningRegion r B n q v R).Nonempty := by
  obtain ⟨χ, hχ⟩ :=
    parabolicUnramifiedIntertwiningRegion_nonempty r r' hM hn hQ hv B hB R
  refine ⟨parabolicLeviUnramifiedCharactersHomeomorph r χ, ?_⟩
  change (parabolicLeviUnramifiedCharactersHomeomorph r).symm
    (parabolicLeviUnramifiedCharactersHomeomorph r χ) ∈
      parabolicUnramifiedIntertwiningRegion r B n q v R
  rwa [(parabolicLeviUnramifiedCharactersHomeomorph r).symm_apply_apply]

omit r' hM hn hQ hv

section AmbientForm

local instance parabolicPointIntertwiningRegionRootInclusionMono : Mono r.data.i.hom.hom.left :=
  r.isCompatible.maximalSplit.isSplitSubtorus.mono

local instance parabolicPointIntertwiningRegionRootCharacterMono : Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left := by
  let := r.isCompatible.splitComponent.1.isSplitSubtorus.mono
  let := r.isCompatible.levi.isClosedSubgroup.mono
  let := r.isCompatible.parabolic.isClosedSubgroup.mono
  have : Mono (a ≫ l ≫ p).hom.hom.left := by
    change Mono (a.hom.hom.left ≫ l.hom.hom.left ≫ p.hom.hom.left)
    infer_instance
  exact mono_of_mono_fac
    (congrArg (fun z => z.hom.hom.left) r.isCompatible.factor_comp)

variable [Fintype (relativeWeylGroup r.data.i)]

include r' hM hn hQ hv

omit [LocallyOfFiniteType M.X.hom] in
/-- The literal-point region uses precisely the single ambient Weyl form
and the same orthogonal lift as the canonical scheme-character region. -/
theorem parabolicPointUnramifiedIntertwiningRegion_eq_ambient (R : ℝ) :
    parabolicPointUnramifiedIntertwiningRegion r
        (weylInducedCharacterForm r.isCompatible.splitComponent.1.isSplitSubtorus.1
          r.isCompatible.maximalSplit.isSplitSubtorus.1 r.data.f r.data.i) n q v R =
      (parabolicLeviUnramifiedCharactersHomeomorph r).symm ⁻¹'
        weylAmbientUnramifiedIntertwiningRegion
          r.isCompatible.splitComponent.1.isSplitSubtorus.1
          r.isCompatible.maximalSplit.isSplitSubtorus.1 r.data.f r.data.i a
          r.splitComponentCocharacter r'.splitComponentCocharacter R := by
  exact congrArg
    (fun Ω => (parabolicLeviUnramifiedCharactersHomeomorph r).symm ⁻¹' Ω)
    (parabolicWeylUnramifiedIntertwiningRegion_eq_ambient r r' hM hn hQ hv R)

end AmbientForm
end RootLaws

end Langlands.Plancherel
