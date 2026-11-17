import Langlands.Representation.Plancherel.DynamicCommonLeviContinuationStatement
import Langlands.Representation.Plancherel.ParabolicIntertwiningStatement
import Langlands.Representation.Plancherel.SplitTorusCompactKernel
import Langlands.Representation.CompactCoefficient.GroupTransport

/-! # Canonical maps from complete presentations to actual common-Levi data -/

noncomputable section

set_option maxHeartbeats 400000

universe u uV uW uA uB uI uJ

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.DynamicCommonLeviPresentationComparison

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2

section EqualityMaps

variable {H : Type u} [Group H] [TopologicalSpace H]

/-- The identity on ambient elements between equal literal subgroups. -/
def subgroupHomeomorphOfEq {M N : Subgroup H} (h : M = N) : M ≃ₜ* N := by
  subst N
  exact ContinuousMulEquiv.refl M

@[simp]
theorem subgroupHomeomorphOfEq_coe {M N : Subgroup H} (h : M = N) (m : M) :
    (subgroupHomeomorphOfEq h m : H) = (m : H) := by
  subst N
  rfl

/-- Pull back the action along the actual identity of ambient subgroup elements.
The inducing vector space is unchanged. -/
def representationOfEq {M N : Subgroup H} [NonarchimedeanGroup H]
    (h : M = N) (A : SmoothRep.{0, u, uV} ℂ N) : SmoothRep.{0, u, uV} ℂ M :=
  SmoothRep.pullback (subgroupHomeomorphOfEq h) A

@[simp]
theorem representationOfEq_apply {M N : Subgroup H} [NonarchimedeanGroup H]
    (h : M = N) (A : SmoothRep.{0, u, uV} ℂ N) (m : M) (a : A) :
    (representationOfEq h A).representation m a =
      A.representation (subgroupHomeomorphOfEq h m) a := rfl

end EqualityMaps

section KernelTransport

variable {A : Type uA} {B : Type uB} [Group A] [TopologicalSpace A]
  [Group B] [TopologicalSpace B] {I : Type uI} {J : Type uJ}

private def characterOfKernelComparison (e : A ≃ₜ* B)
    (ν : I → (A →* ℝ≥0ˣ)) (νB : J → (B →* ℝ≥0ˣ))
    (hk : ∀ b, b ∈ commonNormKernel νB ↔ e.symm b ∈ commonNormKernel ν)
    (z : unramifiedCharacters ν) : unramifiedCharacters νB :=
  ⟨z.val.comp (e.symm : B →ₜ* A), by
    intro b hb
    change z.val (e.symm b) = 1
    exact z.property ((hk b).mp hb)⟩

private def characterOfKernelComparisonInverse (e : A ≃ₜ* B)
    (ν : I → (A →* ℝ≥0ˣ)) (νB : J → (B →* ℝ≥0ˣ))
    (hk : ∀ b, b ∈ commonNormKernel νB ↔ e.symm b ∈ commonNormKernel ν)
    (z : unramifiedCharacters νB) : unramifiedCharacters ν :=
  ⟨z.val.comp (e : A →ₜ* B), by
    intro a ha
    change z.val (e a) = 1
    apply z.property
    apply (hk (e a)).mpr
    simpa only [e.symm_apply_apply] using ha⟩

private def charactersOfKernelComparison (e : A ≃ₜ* B)
    (ν : I → (A →* ℝ≥0ˣ)) (νB : J → (B →* ℝ≥0ˣ))
    (hk : ∀ b, b ∈ commonNormKernel νB ↔ e.symm b ∈ commonNormKernel ν) :
    unramifiedCharacters ν ≃ₜ* unramifiedCharacters νB where
  toFun := characterOfKernelComparison e ν νB hk
  invFun := characterOfKernelComparisonInverse e ν νB hk
  left_inv z := by
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro a
    change z.val (e.symm (e a)) = z.val a
    rw [e.symm_apply_apply]
  right_inv z := by
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro b
    change z.val (e (e.symm b)) = z.val b
    rw [e.apply_symm_apply]
  map_mul' z w := by
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro b
    rfl
  continuous_toFun :=
    ((e.symm : B →ₜ* A).continuous_comp_left.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((e : A →ₜ* B).continuous_comp_left.comp continuous_subtype_val).subtype_mk _

end KernelTransport

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {M P U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine M.X.left]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {p : P ⟶ G} {l : M ⟶ P} {a : T.toGrp ⟶ M} {n : U ⟶ P}

/-- All-test realization conditions. Complete root compatibility is retained
separately by the argument `r : ParabolicRootPresentation p l a`. -/
structure Realizes
    (χ ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (p : P ⟶ G) (l : M ⟶ P) (n : U ⟶ P) : Prop where
  parabolic : SubgroupFunctor.range p = Dynamic.parabolic ψ
  levi : SubgroupFunctor.range (l ≫ p) = Dynamic.centralizer χ
  radical : SubgroupFunctor.range (n ≫ p) = Dynamic.unipotent ψ

variable (χ ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (r : ParabolicRootPresentation p l a) (s : Realizes χ ψ p l n)

include s

/-- Equality of the supplied literal point Levi with the actual common Levi. -/
theorem leviPoints_eq : parabolicLeviPointSubgroup p l = levi χ :=
  congrArg (fun S : SubgroupFunctor G => S.carrier (Over.mk (𝟙 _))) s.levi

theorem parabolicPoints_eq :
    (SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)) = parabolic ψ :=
  congrArg (fun S : SubgroupFunctor G => S.carrier (Over.mk (𝟙 _))) s.parabolic

theorem radicalPoints_eq :
    (SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _)) = radical ψ :=
  congrArg (fun S : SubgroupFunctor G => S.carrier (Over.mk (𝟙 _))) s.radical

/-- The canonical point-Levi map is the identity in the ambient group. -/
def leviPointComparison : parabolicLeviPointSubgroup p l ≃ₜ* levi χ :=
  subgroupHomeomorphOfEq (leviPoints_eq χ ψ s)

@[simp]
theorem leviPointComparison_coe (m : parabolicLeviPointSubgroup p l) :
    (leviPointComparison χ ψ s m : rationalPoints G) = (m : rationalPoints G) :=
  subgroupHomeomorphOfEq_coe _ _

include r in
private theorem leviRepresents :
    (Dynamic.centralizer χ).IsRepresentedBy (l ≫ p) := by
  have hc : IsClosedSubgroup (l ≫ p) :=
    r.isCompatible.levi.isClosedSubgroup.comp r.isCompatible.parabolic.isClosedSubgroup
  have : IsClosedImmersion (l ≫ p).hom.hom.left := hc
  exact ⟨Over.mono_of_mono_left _, s.levi⟩

/-- Uniqueness of closed representatives constructs the scheme comparison;
no group or representation equivalence is supplied as an input. -/
def leviSchemeComparison : M ≅ parameterScheme χ :=
  (leviRepresents χ ψ r s).isoOfIsRepresentedBy
    (Dynamic.Affine.isRepresentedBy_centralizerHom χ)

include r in
theorem leviSchemeComparison_hom_comp :
    (leviSchemeComparison χ ψ r s).hom ≫ Dynamic.Affine.centralizerHom χ = l ≫ p :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

/-- Canonical parameter points map to the supplied literal Levi through the
same ambient Levi elements. -/
def parameterPointComparison :
    rationalPoints (parameterScheme χ) ≃ₜ* parabolicLeviPointSubgroup p l :=
  (parameterHomeomorph χ).trans (leviPointComparison χ ψ s).symm

theorem parameterPointComparison_coe (m : rationalPoints (parameterScheme χ)) :
    (parameterPointComparison χ ψ s m : rationalPoints G) =
      (parameterHomeomorph χ m : rationalPoints G) := by
  change ((leviPointComparison χ ψ s).symm (parameterHomeomorph χ m) : rationalPoints G) = _
  have h := leviPointComparison_coe χ ψ s
    ((leviPointComparison χ ψ s).symm (parameterHomeomorph χ m))
  simpa only [ContinuousMulEquiv.apply_symm_apply] using h.symm

include r in
theorem parameterPointComparison_scheme (m : rationalPoints M) :
    (parameterPointComparison χ ψ s).symm (parabolicLeviPointHomeomorph r m) =
      rationalPoints.map (leviSchemeComparison χ ψ r s).hom m := by
  apply (parameterPointComparison χ ψ s).injective
  rw [(parameterPointComparison χ ψ s).apply_symm_apply]
  apply Subtype.ext
  rw [parameterPointComparison_coe, parabolicLeviPointHomeomorph_apply_coe]
  change m ≫ (l ≫ p).hom.hom =
    (m ≫ (leviSchemeComparison χ ψ r s).hom.hom.hom) ≫
      (Dynamic.Affine.centralizerHom χ).hom.hom
  rw [Category.assoc]
  exact congrArg (fun f => m ≫ f.hom.hom) (leviSchemeComparison_hom_comp χ ψ r s).symm

include r in
/-- All rational-character kernels agree through the constructed map.
Both directions use functoriality of the full rational norm kernel. -/
theorem parameterPointComparison_kernel (m : parabolicLeviPointSubgroup p l) :
    m ∈ commonNormKernel (parabolicLeviRationalNormCharacters r) ↔
      (parameterPointComparison χ ψ s).symm m ∈ commonNormKernel (normCharacters χ) := by
  let x := (parabolicLeviPointHomeomorph r).symm m
  have hx : parabolicLeviPointHomeomorph r x = m :=
    (parabolicLeviPointHomeomorph r).apply_symm_apply m
  rw [← hx, parameterPointComparison_scheme χ ψ r s x]
  simp only [mem_commonNormKernel, parabolicLeviRationalNormCharacters_apply_points]
  have hk : x ∈ rationalCommonNormKernel M ↔
      rationalPoints.map (leviSchemeComparison χ ψ r s).hom x ∈
        rationalCommonNormKernel (parameterScheme χ) := by
    constructor
    · exact SplitTorus.map_mem_commonNormKernel _
    · intro hm
      have h := SplitTorus.map_mem_commonNormKernel (leviSchemeComparison χ ψ r s).inv hm
      change (isoPointsEquiv (leviSchemeComparison χ ψ r s) _).symm
        ((isoPointsEquiv (leviSchemeComparison χ ψ r s) _) x) ∈ rationalCommonNormKernel M at h
      simpa only [MulEquiv.symm_apply_apply] using h
  simpa only [rationalCommonNormKernel, mem_commonNormKernel] using hk

/-- The constructed parameter map induces the character homeomorphism for the
full rational-character families, even though their index types differ. -/
def characterComparison :
    unramifiedCharacters (normCharacters χ) ≃ₜ*
      unramifiedCharacters (parabolicLeviRationalNormCharacters r) :=
  charactersOfKernelComparison
    (A := rationalPoints (parameterScheme χ)) (B := parabolicLeviPointSubgroup p l)
    (I := rationalCharacters (parameterScheme χ)) (J := rationalCharacters M)
    (parameterPointComparison χ ψ s)
    (normCharacters χ) (parabolicLeviRationalNormCharacters r)
    (parameterPointComparison_kernel χ ψ r s)

@[simp]
theorem characterComparison_apply (z : unramifiedCharacters (normCharacters χ))
    (m : parabolicLeviPointSubgroup p l) :
    (characterComparison χ ψ r s z).val m =
      z.val ((parameterPointComparison χ ψ s).symm m) := rfl

@[simp]
theorem characterComparison_symm_apply
    (z : unramifiedCharacters (parabolicLeviRationalNormCharacters r))
    (m : rationalPoints (parameterScheme χ)) :
    ((characterComparison χ ψ r s).symm z).val m =
      z.val (parameterPointComparison χ ψ s m) := rfl

private def functionComparison :
    (unramifiedCharacters (normCharacters χ) → ℂ) ≃ₐ[ℂ]
      (unramifiedCharacters (parabolicLeviRationalNormCharacters r) → ℂ) where
  toFun f z := f ((characterComparison χ ψ r s).symm z)
  invFun f z := f (characterComparison χ ψ r s z)
  left_inv f := by
    funext z
    exact congrArg f ((characterComparison χ ψ r s).symm_apply_apply z)
  right_inv f := by
    funext z
    exact congrArg f ((characterComparison χ ψ r s).apply_symm_apply z)
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

private theorem functionComparison_evaluation (m : rationalPoints (parameterScheme χ)) :
    functionComparison χ ψ r s (unramifiedEvaluation (normCharacters χ) m) =
      unramifiedEvaluation (parabolicLeviRationalNormCharacters r)
        (parameterPointComparison χ ψ s m) := by
  funext z
  rfl

private theorem regularFunctions_map :
    (unramifiedRegularFunctions (normCharacters χ)).map (functionComparison χ ψ r s).toAlgHom =
      unramifiedRegularFunctions (parabolicLeviRationalNormCharacters r) := by
  unfold unramifiedRegularFunctions
  rw [AlgHom.map_adjoin]
  congr 1
  ext f
  constructor
  · rintro ⟨_, ⟨m, rfl⟩, rfl⟩
    exact ⟨parameterPointComparison χ ψ s m, (functionComparison_evaluation χ ψ r s m).symm⟩
  · rintro ⟨m, rfl⟩
    refine ⟨unramifiedEvaluation (normCharacters χ) ((parameterPointComparison χ ψ s).symm m),
      ⟨(parameterPointComparison χ ψ s).symm m, rfl⟩, ?_⟩
    change functionComparison χ ψ r s (unramifiedEvaluation (normCharacters χ)
      ((parameterPointComparison χ ψ s).symm m)) = _
    rw [functionComparison_evaluation, (parameterPointComparison χ ψ s).apply_symm_apply]

/-- Actual parameter transport identifies the algebras generated by every
point evaluation; rationality preservation is derived from this algebra map. -/
def regularFunctionsComparison :
    unramifiedRegularFunctions (normCharacters χ) ≃ₐ[ℂ]
      unramifiedRegularFunctions (parabolicLeviRationalNormCharacters r) :=
  ((functionComparison χ ψ r s).subalgebraMap (unramifiedRegularFunctions (normCharacters χ))).trans
    (Subalgebra.equivOfEq _ _ (regularFunctions_map χ ψ r s))

@[simp]
theorem regularFunctionsComparison_apply (b : unramifiedRegularFunctions (normCharacters χ))
    (z : unramifiedCharacters (parabolicLeviRationalNormCharacters r)) :
    (regularFunctionsComparison χ ψ r s b).val z =
      b.val ((characterComparison χ ψ r s).symm z) := rfl

@[simp]
theorem regularFunctionsComparison_symm_apply
    (b : unramifiedRegularFunctions (parabolicLeviRationalNormCharacters r))
    (z : unramifiedCharacters (normCharacters χ)) :
    ((regularFunctionsComparison χ ψ r s).symm b).val z =
      b.val (characterComparison χ ψ r s z) := by
  have h := congrArg (fun c => c.val (characterComparison χ ψ r s z))
    ((regularFunctionsComparison χ ψ r s).apply_symm_apply b)
  simpa only [regularFunctionsComparison_apply,
    (characterComparison χ ψ r s).symm_apply_apply] using h

@[simp]
theorem regularFunctionsComparison_evaluation (m : rationalPoints (parameterScheme χ)) :
    regularFunctionsComparison χ ψ r s (unramifiedEvaluationRegular (normCharacters χ) m) =
      unramifiedEvaluationRegular (parabolicLeviRationalNormCharacters r)
        (parameterPointComparison χ ψ s m) := by
  apply Subtype.ext
  exact functionComparison_evaluation χ ψ r s m

/-- Corresponding character subsets through the constructed homeomorphism. -/
def parameterPreimageComparison
    (Ω : Set (unramifiedCharacters (parabolicLeviRationalNormCharacters r))) :
    ((characterComparison χ ψ r s) ⁻¹' Ω) ≃ Ω :=
  (characterComparison χ ψ r s).toEquiv.subtypeEquiv (fun _ => Iff.rfl)

@[simp]
theorem parameterPreimageComparison_apply
    (Ω : Set (unramifiedCharacters (parabolicLeviRationalNormCharacters r)))
    (z : (characterComparison χ ψ r s) ⁻¹' Ω) :
    (parameterPreimageComparison χ ψ r s Ω z).val = characterComparison χ ψ r s z.val := rfl

@[simp]
theorem parameterPreimageComparison_symm_apply
    (Ω : Set (unramifiedCharacters (parabolicLeviRationalNormCharacters r))) (z : Ω) :
    ((parameterPreimageComparison χ ψ r s Ω).symm z).val =
      (characterComparison χ ψ r s).symm z.val := rfl

open UnramifiedOperatorFamily

section OperatorTransport

variable {E : Type uV} [AddCommGroup E] [Module ℂ E]
  {E' : Type uW} [AddCommGroup E'] [Module ℂ E']
  (Ω : Set (unramifiedCharacters (parabolicLeviRationalNormCharacters r)))

/-- Finite evaluation-polynomial expansions transport on the exact subsets. -/
theorem isPolynomialOn_comparison_iff (f : Ω → E) :
    IsPolynomialOn ((characterComparison χ ψ r s) ⁻¹' Ω)
        (fun z => f (parameterPreimageComparison χ ψ r s Ω z)) ↔
      IsPolynomialOn Ω f := by
  constructor
  · rintro ⟨n, b, v, hf⟩
    refine ⟨n, fun i => regularFunctionsComparison χ ψ r s (b i), v, ?_⟩
    intro z
    have h := hf ((parameterPreimageComparison χ ψ r s Ω).symm z)
    simp only [Equiv.apply_symm_apply] at h
    simpa only [regularFunctionsComparison_apply,
      parameterPreimageComparison_symm_apply] using h
  · rintro ⟨n, b, v, hf⟩
    refine ⟨n, fun i => (regularFunctionsComparison χ ψ r s).symm (b i), v, ?_⟩
    intro z
    simpa only [regularFunctionsComparison_symm_apply,
      parameterPreimageComparison_apply] using hf (parameterPreimageComparison χ ψ r s Ω z)

theorem isPolynomialOperatorOn_comparison_iff (J : Ω → E →ₗ[ℂ] E') :
    IsPolynomialOperatorOn ((characterComparison χ ψ r s) ⁻¹' Ω)
        (fun z => J (parameterPreimageComparison χ ψ r s Ω z)) ↔
      IsPolynomialOperatorOn Ω J :=
  forall_congr' (fun v => isPolynomialOn_comparison_iff χ ψ r s Ω (fun z => J z v))

/-- A single operator denominator, including nonvanishing on the region,
is transported through the proved evaluation algebra isomorphism. -/
theorem isRationalOperatorOn_comparison_iff (J : Ω → E →ₗ[ℂ] E') :
    IsRationalOperatorOn ((characterComparison χ ψ r s) ⁻¹' Ω)
        (fun z => J (parameterPreimageComparison χ ψ r s Ω z)) ↔
      IsRationalOperatorOn Ω J := by
  constructor
  · rintro ⟨b, hb, hJ⟩
    refine ⟨regularFunctionsComparison χ ψ r s b, ?_, ?_⟩
    · intro z
      simpa only [regularFunctionsComparison_apply,
        parameterPreimageComparison_symm_apply] using
          hb ((parameterPreimageComparison χ ψ r s Ω).symm z)
    · apply (isPolynomialOperatorOn_comparison_iff χ ψ r s Ω _).mp
      simpa only [regularFunctionsComparison_apply, parameterPreimageComparison_apply,
        (characterComparison χ ψ r s).symm_apply_apply] using hJ
  · rintro ⟨b, hb, hJ⟩
    refine ⟨(regularFunctionsComparison χ ψ r s).symm b, ?_, ?_⟩
    · intro z
      simpa only [regularFunctionsComparison_symm_apply,
        parameterPreimageComparison_apply] using hb (parameterPreimageComparison χ ψ r s Ω z)
    · simpa only [regularFunctionsComparison_symm_apply, parameterPreimageComparison_apply] using
        (isPolynomialOperatorOn_comparison_iff χ ψ r s Ω (fun z => b.val z.val • J z)).mpr hJ

end OperatorTransport

end Langlands.Plancherel.DynamicCommonLeviPresentationComparison
