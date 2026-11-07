import Langlands.Representation.Plancherel.CompactIntertwiningContinuation
import Langlands.Representation.Plancherel.CompactIntertwiningScalar
import Langlands.Representation.Plancherel.RationalUnramifiedScalarField

/-! # Scalar of two independently continued actual intertwiners -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

open Aubert.General Induction UnramifiedOperatorFamily

universe u uG uI uV uW

namespace UnramifiedOperatorFamily.RationalOperatorContinuationData

variable {H : Type uG} [Group H] [TopologicalSpace H]
  {I : Type uI} {ν : I → (H →* ℝ≥0ˣ)}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {Ω Λ : Set (unramifiedCharacters ν)}
  {A : Ω → V →ₗ[ℂ] W} {B : Λ → W →ₗ[ℂ] V}
  (p : RationalOperatorContinuationData Ω A)
  (q : RationalOperatorContinuationData Λ B)

/-- Each chosen denominator defines an ambient open regular locus. -/
theorem regularRegion_isOpen : IsOpen p.regularRegion := by
  change IsOpen (p.denominator.val ⁻¹' ({0} : Set ℂ)ᶜ)
  exact isOpen_compl_singleton.preimage (continuous_unramifiedRegularFunction ν _)

/-- Nonemptiness of the original region proves the regular denominator is
not the zero function. -/
theorem denominator_ne_zero (hΩ : Ω.Nonempty) : p.denominator ≠ 0 := by
  obtain ⟨χ, hχ⟩ := hΩ
  intro he
  apply p.denominator_nonzero ⟨χ, hχ⟩
  rw [he]
  rfl

/-- Compose only after continuing both operators, on the intersection of
their full denominator nonzero loci. The original regions may be disjoint. -/
def continuedComposite (χ : ↥(p.regularRegion ∩ q.regularRegion)) :
    Module.End ℂ V :=
  (q.continuedOperator ⟨χ.val, χ.property.2⟩).comp
    (p.continuedOperator ⟨χ.val, χ.property.1⟩)

/-- Restricting the two whole-operator denominators and multiplying them
proves rationality of the continued composite. -/
theorem continuedComposite_rational :
    IsRationalOperatorOn (p.regularRegion ∩ q.regularRegion)
      (p.continuedComposite q) :=
  (q.continuedOperator_rational.restrict Set.inter_subset_right).comp
    (p.continuedOperator_rational.restrict Set.inter_subset_left)

/-- Extract a coefficient from the actual continued compact composite.
It becomes its scalar when generic scalarity is proved. -/
def continuedCompositeScalar (v : V) (ℓ : V →ₗ[ℂ] ℂ)
    (χ : ↥(p.regularRegion ∩ q.regularRegion)) : ℂ :=
  endomorphismScalarCoefficient v ℓ (p.continuedComposite q χ)

end UnramifiedOperatorFamily.RationalOperatorContinuationData

section CommonRegularRegion

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints L)]
  (hp : Continuous (rationalValuationImageProjection L))
  (hL : GroupScheme.IsConnectedReductive L)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {Ω Λ : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  {A : Ω → V →ₗ[ℂ] W} {B : Λ → W →ₗ[ℂ] V}
  (p : RationalOperatorContinuationData Ω A)
  (q : RationalOperatorContinuationData Λ B)

include hp hL

/-- The regular regions of independently continued operators have dense
intersection. No intersection of the original parameter regions is needed. -/
theorem continuedCompositeRegion_dense (hΩ : Ω.Nonempty) (hΛ : Λ.Nonempty) :
    Dense (p.regularRegion ∩ q.regularRegion) := by
  let := rationalUnramifiedRegularFunctions_isDomain L hp hL
  have hd := rationalUnramifiedRegular_dense_nonzero L hp hL
    (p.denominator * q.denominator)
    (mul_ne_zero (p.denominator_ne_zero hΩ) (q.denominator_ne_zero hΛ))
  convert hd using 1
  ext χ
  exact mul_ne_zero_iff.symm

/-- The common full regular region is nonempty, even for disjoint original
convergence regions. -/
theorem continuedCompositeRegion_nonempty (hΩ : Ω.Nonempty) (hΛ : Λ.Nonempty) :
    (p.regularRegion ∩ q.regularRegion).Nonempty :=
  (continuedCompositeRegion_dense L hp hL p q hΩ hΛ).nonempty

/-- The extracted coefficient of the continued composite in the actual
unramified function field. Nonemptiness is proved from the independent
original regions, which need not intersect. -/
def continuedCompositeRationalScalar (hΩ : Ω.Nonempty) (hΛ : Λ.Nonempty)
    (v : V) (ℓ : V →ₗ[ℂ] ℂ) :
    rationalUnramifiedFunctionField L hp hL :=
  rationalUnramifiedOperatorScalar L hp hL
    (p.continuedComposite q) (p.continuedComposite_rational q) v ℓ
    (continuedCompositeRegion_nonempty L hp hL p q hΩ hΛ)

/-- A regular fraction represents the extracted coefficient at every common
regular parameter. No value of a rational function at a pole is asserted. -/
theorem continuedCompositeRationalScalar_spec (hΩ : Ω.Nonempty) (hΛ : Λ.Nonempty)
    (v : V) (ℓ : V →ₗ[ℂ] ℂ) :
    ∃ a b : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters L ψ).toMul),
      b ≠ 0 ∧
      (∀ χ : ↥(p.regularRegion ∩ q.regularRegion), b.val χ.val ≠ 0) ∧
      continuedCompositeRationalScalar L hp hL p q hΩ hΛ v ℓ =
        algebraMap (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters L ψ).toMul))
          (rationalUnramifiedFunctionField L hp hL) a /
        algebraMap (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters L ψ).toMul))
          (rationalUnramifiedFunctionField L hp hL) b ∧
      ∀ χ : ↥(p.regularRegion ∩ q.regularRegion),
        p.continuedCompositeScalar q v ℓ χ = a.val χ.val / b.val χ.val :=
  rationalUnramifiedOperatorScalar_spec L hp hL _ _ v ℓ
    (continuedCompositeRegion_nonempty L hp hL p q hΩ hΛ)

/-- Changing the continuation data for each original operator preserves the
compact composite at every common regular parameter. The two original
families require separate open subsets, with no common point assumed. -/
theorem continuedComposite_unique
    (p' : RationalOperatorContinuationData Ω A)
    (q' : RationalOperatorContinuationData Λ B)
    {D E : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
    (hD : IsOpen D) (hneD : D.Nonempty) (hDΩ : D ⊆ Ω)
    (hE : IsOpen E) (hneE : E.Nonempty) (hEΛ : E ⊆ Λ)
    (χ : ↥((p.regularRegion ∩ q.regularRegion) ∩
      (p'.regularRegion ∩ q'.regularRegion))) :
    p.continuedComposite q ⟨χ.val, χ.property.1⟩ =
      p'.continuedComposite q' ⟨χ.val, χ.property.2⟩ := by
  exact congrArg₂ LinearMap.comp
    (rationalOperatorContinuationData_unique L hp hL B q q' hE hneE hEΛ
      ⟨χ.val, χ.property.1.2, χ.property.2.2⟩)
    (rationalOperatorContinuationData_unique L hp hL A p p' hD hneD hDΩ
      ⟨χ.val, χ.property.1.1, χ.property.2.1⟩)

/-- The extracted fraction is independent of both continuation choices,
including their denominators and their regular regions. This conclusion
uses equality of the continued operators, without a scalarity assumption. -/
theorem continuedCompositeRationalScalar_continuation_independent
    (p' : RationalOperatorContinuationData Ω A)
    (q' : RationalOperatorContinuationData Λ B)
    {D E : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
    (hD : IsOpen D) (hneD : D.Nonempty) (hDΩ : D ⊆ Ω)
    (hE : IsOpen E) (hneE : E.Nonempty) (hEΛ : E ⊆ Λ)
    (v : V) (ℓ : V →ₗ[ℂ] ℂ) :
    continuedCompositeRationalScalar L hp hL p q
        (hneD.mono hDΩ) (hneE.mono hEΛ) v ℓ =
      continuedCompositeRationalScalar L hp hL p' q'
        (hneD.mono hDΩ) (hneE.mono hEΛ) v ℓ := by
  have hΩ := hneD.mono hDΩ
  have hΛ := hneE.mono hEΛ
  have hR := p.regularRegion_isOpen.inter q.regularRegion_isOpen
  have hR' := p'.regularRegion_isOpen.inter q'.regularRegion_isOpen
  have hneR := continuedCompositeRegion_nonempty L hp hL p q hΩ hΛ
  have hneR' := continuedCompositeRegion_nonempty L hp hL p' q' hΩ hΛ
  have hneRR := (continuedCompositeRegion_dense L hp hL p' q' hΩ hΛ).inter_open_nonempty
    (p.regularRegion ∩ q.regularRegion) hR hneR
  apply ScalarPresentation.toFunctionField_eq_of_eqOn_isOpen L hp hL
    _ _ hneR hneR' (hR.inter hR') hneRR Set.inter_subset_left Set.inter_subset_right
  intro χ hχ
  exact congrArg (endomorphismScalarCoefficient v ℓ)
    (continuedComposite_unique L hp hL p q p' q' hD hneD hDΩ hE hneE hEΛ ⟨χ, hχ⟩)

end CommonRegularRegion

section ActualInduction

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints L)]
  (hp : Continuous (rationalValuationImageProjection L))
  (hL : GroupScheme.IsConnectedReductive L)
  {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P₀ P₁ M U₀ U₁ : Subgroup G}
  (h₀ : IsSemidirectDecomposition P₀ M U₀) (hU₀ : IsClosed (U₀ : Set G))
  (hδ₀ : IsUnimodularModulus U₀ hU₀)
  (h₁ : IsSemidirectDecomposition P₁ M U₁) (hU₁ : IsClosed (U₁ : Set G))
  (hδ₁ : IsUnimodularModulus U₁ hU₁)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hP₀ : IsClosed (P₀ : Set G)) (hP₁ : IsClosed (P₁ : Set G))
  (hP₀K : ∀ g : G, ∃ p : P₀, ∃ k : K, g = (p : G) * (k : G))
  (hP₁K : ∀ g : G, ∃ p : P₁, ∃ k : K, g = (p : G) * (k : G))
  (hr₀ : Continuous h₀.projection) (hr₁ : Continuous h₁.projection)
  (e : GroupScheme.rationalPoints L ≃ₜ* M)
  (hν : ∀ ψ, Continuous (rationalNormCharacters L ψ).toMul)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
  {Ω₁₀ Ω₀₁ D₁₀ D₀₁ :
    Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}

local notation "νL" => (fun ψ => Additive.toMul (rationalNormCharacters L ψ))
local notation "νM" => (fun ψ => MonoidHom.comp
  (Additive.toMul (rationalNormCharacters L ψ)) e.symm.toMulEquiv.toMonoidHom)
local notation "χM" => unramifiedCharactersHomeomorph e νL
set_option quotPrecheck false in
local notation "hνM" => (fun ψ => (hν ψ).comp e.symm.continuous)
local notation "T₁₀" => compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K
  νM hνM hr₀ h₁ hU₁ hδ₁ hP₁ hP₁K hr₁
local notation "T₀₁" => compactIntertwiningOperator h₁ hU₁ hδ₁ K hP₁ hK hP₁K
  νM hνM hr₁ h₀ hU₀ hδ₀ hP₀ hP₀K hr₀

variable
  (J₁₀ : ∀ χ : Ω₁₀,
    (UnramifiedLeviInduction h₀ hU₀
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A).representation.IntertwiningMap
    (UnramifiedLeviInduction h₁ hU₁
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A).representation)
  (J₀₁ : ∀ χ : Ω₀₁,
    (UnramifiedLeviInduction h₁ hU₁
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A).representation.IntertwiningMap
    (UnramifiedLeviInduction h₀ hU₀
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A).representation)
  (p : RationalOperatorContinuationData Ω₁₀ (fun χ =>
    compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (fun ψ => (hν ψ).comp e.symm.continuous) hr₀
      h₁ hU₁ hδ₁ hP₁ hP₁K hr₁
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A (J₁₀ χ)))
  (q : RationalOperatorContinuationData Ω₀₁ (fun χ =>
    compactIntertwiningOperator h₁ hU₁ hδ₁ K hP₁ hK hP₁K
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (fun ψ => (hν ψ).comp e.symm.continuous) hr₁
      h₀ hU₀ hδ₀ hP₀ hP₀K hr₀
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A (J₀₁ χ)))
  (hD₁₀ : IsOpen D₁₀) (hne₁₀ : D₁₀.Nonempty) (hD₁₀Ω : D₁₀ ⊆ Ω₁₀)
  (hD₀₁ : IsOpen D₀₁) (hne₀₁ : D₀₁.Nonempty) (hD₀₁Ω : D₀₁ ⊆ Ω₀₁)

local notation "R" => p.regularRegion ∩ q.regularRegion
local notation "Jext₁₀" => continuedInductionIntertwiner L hp hL
  h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
  J₁₀ p hD₁₀ hne₁₀ hD₁₀Ω
local notation "Jext₀₁" => continuedInductionIntertwiner L hp hL
  h₁ hU₁ hδ₁ h₀ hU₀ hδ₀ K hK hP₁ hP₀ hP₁K hP₀K hr₁ hr₀ e hν A
  J₀₁ q hD₀₁ hne₀₁ hD₀₁Ω

/-- The actual ambient composite of the two independent continuations. -/
def continuedInductionComposite (χ : ↥(p.regularRegion ∩ q.regularRegion)) :
    (UnramifiedLeviInduction h₀ hU₀ νM (χM χ.val) A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₀ hU₀ νM (χM χ.val) A).representation :=
  (Jext₀₁ ⟨χ.val, χ.property.2⟩).comp (Jext₁₀ ⟨χ.val, χ.property.1⟩)

local notation "C" => continuedInductionComposite L hp hL
  h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
  J₁₀ J₀₁ p q hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω

/-- Compact conjugation of the actual composite is exactly the rational
composite of the two continued polynomial numerator families. -/
theorem continuedInductionComposite_compact (χ : ↥(p.regularRegion ∩ q.regularRegion)) :
    compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K νM hνM hr₀
      h₀ hU₀ hδ₀ hP₀ hP₀K hr₀ (χM χ.val) A (C χ) =
        p.continuedComposite q χ := by
  rw [continuedInductionComposite,
    compactIntertwiningOperator_comp h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK
      hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ νM hνM (χM χ.val) A
      h₀ hU₀ hδ₀ hP₀ hP₀K hr₀]
  exact congrArg₂ LinearMap.comp
    (continuedInductionIntertwiner_compact L hp hL
      h₁ hU₁ hδ₁ h₀ hU₀ hδ₀ K hK hP₁ hP₀ hP₁K hP₀K hr₁ hr₀ e hν A
      J₀₁ q hD₀₁ hne₀₁ hD₀₁Ω ⟨χ.val, χ.property.2⟩)
    (continuedInductionIntertwiner_compact L hp hL
      h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
      J₁₀ p hD₁₀ hne₁₀ hD₁₀Ω ⟨χ.val, χ.property.1⟩)

section GenericIrreducibility

variable [TopologicalSpace.SeparableSpace G]
  {D : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  (hD : IsOpen D) (hne : D.Nonempty)
  (hi : ∀ χ ∈ D,
    (UnramifiedLeviInduction h₀ hU₀
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ)
      A).IsIrreducible)

include hp hL hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω hi
/-- Schur is used only where the actual induced representation is
irreducible. The irreducibility locus need not avoid either denominator. -/
theorem continuedInductionComposite_generic_scalar
    (χ : ↥(D ∩ (p.regularRegion ∩ q.regularRegion))) :
    ∃ c : ℂ, p.continuedComposite q ⟨χ.val, χ.property.2⟩ =
      c • LinearMap.id := by
  obtain ⟨c, hc, -⟩ := Langlands.Schur.separableSmooth_scalarEndomorphism
    (UnramifiedLeviInduction h₀ hU₀ νM (χM χ.val) A).representation
    (UnramifiedLeviInduction h₀ hU₀ νM (χM χ.val) A).isSmooth
    (hi χ.val χ.property.1) (C ⟨χ.val, χ.property.2⟩)
  refine ⟨c, ?_⟩
  exact (continuedInductionComposite_compact L hp hL
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
    J₁₀ J₀₁ p q hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω
    ⟨χ.val, χ.property.2⟩).symm.trans
      ((compactIntertwiningOperator_scalar_iff h₀ hU₀ hδ₀ K hK hP₀ hP₀K hr₀
        νM hνM (χM χ.val) A _ c).mpr hc)

local notation "SC" => continuedInductionComposite_generic_scalar L hp hL
  h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
  J₁₀ J₀₁ p q hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω hi

include hD hne

/-- Generic induced irreducibility implies scalarity on the entire common
regular locus, including its reducible parameters. The scalar is extracted
from these continued operators. -/
theorem continuedInductionComposite_compact_eq_scalar
    (v : CompactInductionPicture h₀ K A)
    (ℓ : CompactInductionPicture h₀ K A →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1) :
    ∀ χ : ↥(p.regularRegion ∩ q.regularRegion),
      p.continuedComposite q χ =
        p.continuedCompositeScalar q v ℓ χ • LinearMap.id := by
  have hΩ := hne₁₀.mono hD₁₀Ω
  have hΛ := hne₀₁.mono hD₀₁Ω
  have hopen := hD.inter (p.regularRegion_isOpen.inter q.regularRegion_isOpen)
  have hnonempty := (continuedCompositeRegion_dense L hp hL p q hΩ hΛ).inter_open_nonempty
    D hD hne
  exact rationalUnramifiedScalarContinuation L hp hL hopen hnonempty
    Set.inter_subset_right (p.continuedComposite q) (p.continuedComposite_rational q)
    v ℓ hℓ (fun χ hχ => SC ⟨χ, hχ⟩)

/-- The scalar equation holds for the actual ambient composite on every
common regular parameter, without irreducibility there. -/
theorem continuedInductionComposite_eq_scalar
    (v : CompactInductionPicture h₀ K A)
    (ℓ : CompactInductionPicture h₀ K A →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1)
    (χ : ↥(p.regularRegion ∩ q.regularRegion)) :
    C χ = p.continuedCompositeScalar q v ℓ χ •
      Representation.IntertwiningMap.id
        (UnramifiedLeviInduction h₀ hU₀ νM (χM χ.val) A).representation := by
  apply (compactIntertwiningOperator_scalar_iff h₀ hU₀ hδ₀ K hK hP₀ hP₀K hr₀
    νM hνM (χM χ.val) A _ _).mp
  exact (continuedInductionComposite_compact L hp hL
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
    J₁₀ J₀₁ p q hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω χ).trans
      (continuedInductionComposite_compact_eq_scalar L hp hL
        h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
        J₁₀ J₀₁ p q hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω hD hne hi
        v ℓ hℓ χ)

/-- The scalar fraction and a regular presentation of its actual ambient
composition identity are constructed together. -/
theorem continuedInductionCompositeRationalScalar_spec
    (v : CompactInductionPicture h₀ K A)
    (ℓ : CompactInductionPicture h₀ K A →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1) :
    ∃ a b : unramifiedRegularFunctions νL,
      b ≠ 0 ∧ (∀ χ : ↥(p.regularRegion ∩ q.regularRegion), b.val χ.val ≠ 0) ∧
      continuedCompositeRationalScalar L hp hL p q
          (hne₁₀.mono hD₁₀Ω) (hne₀₁.mono hD₀₁Ω) v ℓ =
        algebraMap (unramifiedRegularFunctions νL)
          (rationalUnramifiedFunctionField L hp hL) a /
        algebraMap (unramifiedRegularFunctions νL)
          (rationalUnramifiedFunctionField L hp hL) b ∧
      ∀ χ : ↥(p.regularRegion ∩ q.regularRegion),
        C χ = (a.val χ.val / b.val χ.val) • Representation.IntertwiningMap.id
          (UnramifiedLeviInduction h₀ hU₀ νM (χM χ.val) A).representation := by
  let s := scalarCoefficientPresentation
    (p.continuedComposite q) (p.continuedComposite_rational q) v ℓ
  have hR := continuedCompositeRegion_nonempty L hp hL p q
    (hne₁₀.mono hD₁₀Ω) (hne₀₁.mono hD₀₁Ω)
  refine ⟨s.numerator, s.denominator, s.denominator_ne_zero hR,
    s.denominator_nonzero, s.toFunctionField_eq_div L hp hL hR, fun χ => ?_⟩
  exact (continuedInductionComposite_eq_scalar L hp hL
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
    J₁₀ J₀₁ p q hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω hD hne hi
    v ℓ hℓ χ).trans
      (congrArg (fun c : ℂ => c • Representation.IntertwiningMap.id
        (UnramifiedLeviInduction h₀ hU₀ νM (χM χ.val) A).representation) (s.value_eq_div χ))

/-- Both normalized vector/functional choices give the same scalar at every
common regular parameter, including reducible parameters. -/
theorem continuedInductionCompositeScalar_independent
    (v w : CompactInductionPicture h₀ K A)
    (ℓ m : CompactInductionPicture h₀ K A →ₗ[ℂ] ℂ)
    (hℓ : ℓ v = 1) (hm : m w = 1)
    (χ : ↥(p.regularRegion ∩ q.regularRegion)) :
    p.continuedCompositeScalar q v ℓ χ = p.continuedCompositeScalar q w m χ := by
  have he := congrArg (endomorphismScalarCoefficient w m)
    (continuedInductionComposite_compact_eq_scalar L hp hL
      h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
      J₁₀ J₀₁ p q hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω hD hne hi
      v ℓ hℓ χ)
  exact (he.trans (endomorphismScalarCoefficient_smul_id w m hm _)).symm

/-- The function-field scalar is independent of the two normalized
extraction choices. Presentation independence is inherited from the
underlying actual function-field construction. -/
theorem continuedInductionCompositeRationalScalar_independent
    (v w : CompactInductionPicture h₀ K A)
    (ℓ m : CompactInductionPicture h₀ K A →ₗ[ℂ] ℂ)
    (hℓ : ℓ v = 1) (hm : m w = 1) :
    continuedCompositeRationalScalar L hp hL p q
        (hne₁₀.mono hD₁₀Ω) (hne₀₁.mono hD₀₁Ω) v ℓ =
      continuedCompositeRationalScalar L hp hL p q
        (hne₁₀.mono hD₁₀Ω) (hne₀₁.mono hD₀₁Ω) w m := by
  have hΩ := hne₁₀.mono hD₁₀Ω
  have hΛ := hne₀₁.mono hD₀₁Ω
  have hopen := hD.inter (p.regularRegion_isOpen.inter q.regularRegion_isOpen)
  have hnonempty := (continuedCompositeRegion_dense L hp hL p q hΩ hΛ).inter_open_nonempty
    D hD hne
  exact rationalUnramifiedOperatorScalar_independent L hp hL
    (p.continuedComposite q) (p.continuedComposite_rational q) (p.continuedComposite_rational q)
    v w ℓ m hℓ hm (continuedCompositeRegion_nonempty L hp hL p q hΩ hΛ)
    hopen hnonempty Set.inter_subset_right (fun χ hχ => SC ⟨χ, hχ⟩)

end GenericIrreducibility

end ActualInduction

end Langlands.Plancherel
