import Langlands.Representation.Aubert.General.AlternatingOperator

/-!
# Conjugation compatibility of normalized induction and Jacquet restriction

Let `P = M ⋉ U` and `P' = M' ⋉ U'` be actual semidirect decompositions with
`P' = g P g⁻¹`, `M' = g M g⁻¹` and `U' = g U g⁻¹`. This file proves:

* the Haar modulus of conjugation on `U'` at `x` equals the Haar modulus of
  conjugation on `U` at `g⁻¹ x g`, so the normalizing characters correspond;
* the Levi projections correspond under conjugation by `g`;
* `r_{P'} ≅ ᵍ(-) ∘ r_P`, by `[v] ↦ [g v]` on coinvariants;
* `i_P ≅ i_{P'} ∘ ᵍ(-)`, by `f ↦ f(g⁻¹ ·)` on induced functions;
* the corresponding identities of the exact-K0 maps.

These are intrinsic laws of the generic layer. No reductive structure is used.
-/

noncomputable section

open CategoryTheory

open Langlands.SmoothRep

namespace Langlands.Aubert.General

universe uG uV

section Modulus

open MeasureTheory

/-- The Haar scaling factor is invariant under transport by a topological group
isomorphism: `mulEquivHaarChar (e⁻¹ ∘ φ ∘ e) = mulEquivHaarChar φ`. -/
theorem mulEquivHaarChar_trans_symm {H K : Type*} [Group H] [TopologicalSpace H]
    [MeasurableSpace H] [BorelSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
    [Group K] [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [IsTopologicalGroup K]
    [LocallyCompactSpace K] (e : H ≃ₜ* K) (φ : K ≃ₜ* K) :
    mulEquivHaarChar ((e.trans φ).trans e.symm) = mulEquivHaarChar φ := by
  set μ : Measure K := Measure.haar
  set ν : Measure H := μ.map e.symm
  have : ν.IsHaarMeasure := e.symm.isHaarMeasure_map μ
  have : ν.Regular := Measure.Regular.map e.symm.toHomeomorph
  have : (μ.map φ).IsHaarMeasure := φ.isHaarMeasure_map μ
  have hback : ∀ X : Measure K, (X.map e.symm).map e = X := by
    intro X
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    simp [Function.comp_def]
  have h1 := mulEquivHaarChar_smul_map ν ((e.trans φ).trans e.symm)
  have hmap : ν.map ((e.trans φ).trans e.symm) = (μ.map φ).map e.symm := by
    simp only [ν]
    rw [Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    ext x
    simp
  rw [hmap] at h1
  have he : Measurable e := by fun_prop
  have h3 : mulEquivHaarChar ((e.trans φ).trans e.symm) • μ.map φ = μ := by
    have h4 := congrArg (Measure.map e) h1
    rwa [Measure.map_smul _ he.aemeasurable, hback, hback] at h4
  have h2 := mulEquivHaarChar_smul_map μ φ
  have key : ∀ c : NNReal, Measure.haarScalarFactor (c • μ.map φ) (μ.map φ) = c := by
    intro c
    rw [Measure.haarScalarFactor_smul, Measure.haarScalarFactor_self, smul_eq_mul, mul_one]
  have h6 := h3.trans h2.symm
  calc mulEquivHaarChar ((e.trans φ).trans e.symm)
      = Measure.haarScalarFactor (mulEquivHaarChar ((e.trans φ).trans e.symm) • μ.map φ)
          (μ.map φ) := (key _).symm
    _ = Measure.haarScalarFactor (mulEquivHaarChar φ • μ.map φ) (μ.map φ) := by
        simp only [h6]
    _ = mulEquivHaarChar φ := key _

end Modulus

section Characters

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [IsTopologicalGroup G]

/-- The Haar modulus of conjugation on `U' = g U g⁻¹` by `x` equals the Haar
modulus of conjugation on `U` by `g⁻¹ x g`. -/
theorem closedNormalizerCharacter_conj (g : G) {U U' : Subgroup G}
    (hUU' : ∀ x : G, x ∈ U' ↔ g⁻¹ * x * g ∈ U) (hU : IsClosed (U : Set G))
    (hU' : IsClosed (U' : Set G)) (x : Subgroup.normalizer (U' : Set G))
    (hx : g⁻¹ * (x : G) * g ∈ Subgroup.normalizer (U : Set G)) :
    HaarModulus.closedNormalizerCharacter U' hU' x =
      HaarModulus.closedNormalizerCharacter U hU ⟨g⁻¹ * (x : G) * g, hx⟩ := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let : LocallyCompactSpace U' := hU'.locallyCompactSpace
  let : MeasurableSpace U := borel U
  have : BorelSpace U := ⟨rfl⟩
  let : MeasurableSpace U' := borel U'
  have : BorelSpace U' := ⟨rfl⟩
  apply Units.ext
  change MeasureTheory.mulEquivHaarChar (HaarModulus.normalizerConj U' x) =
    MeasureTheory.mulEquivHaarChar (HaarModulus.normalizerConj U ⟨g⁻¹ * (x : G) * g, hx⟩)
  have hconj : HaarModulus.normalizerConj U' x =
      ((conjugationEquiv g hUU').trans
        (HaarModulus.normalizerConj U ⟨g⁻¹ * (x : G) * g, hx⟩)).trans
        (conjugationEquiv g hUU').symm := by
    ext u
    change (x : G) * u * (x : G)⁻¹ =
      g * ((g⁻¹ * (x : G) * g) * (g⁻¹ * u * g) * (g⁻¹ * (x : G) * g)⁻¹) * g⁻¹
    group
  rw [hconj, mulEquivHaarChar_trans_symm]

variable {U U' M M' : Subgroup G}

/-- The restricted modulus character corresponds under conjugation. -/
theorem closedRestrictCharacter_conj (g : G) (hUU' : ∀ x : G, x ∈ U' ↔ g⁻¹ * x * g ∈ U)
    (hMM' : ∀ x : G, x ∈ M' ↔ g⁻¹ * x * g ∈ M) (hU : IsClosed (U : Set G))
    (hU' : IsClosed (U' : Set G)) (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (hM'U' : M' ≤ Subgroup.normalizer (U' : Set G)) (m : M') :
    HaarModulus.closedRestrictCharacter U' hU' M' hM'U' m =
      HaarModulus.closedRestrictCharacter U hU M hMU (conjugationEquiv g hMM' m) :=
  closedNormalizerCharacter_conj g hUU' hU hU' (Subgroup.inclusion hM'U' m)
    (hMU ((hMM' m).mp m.2))

/-- The half modulus `δ^{1/2}` corresponds under conjugation. -/
theorem closedHalfCharacter_conj (g : G) (hUU' : ∀ x : G, x ∈ U' ↔ g⁻¹ * x * g ∈ U)
    (hMM' : ∀ x : G, x ∈ M' ↔ g⁻¹ * x * g ∈ M) (hU : IsClosed (U : Set G))
    (hU' : IsClosed (U' : Set G)) (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (hM'U' : M' ≤ Subgroup.normalizer (U' : Set G)) (m : M') :
    HaarModulus.closedHalfCharacter U' hU' M' hM'U' m =
      HaarModulus.closedHalfCharacter U hU M hMU (conjugationEquiv g hMM' m) := by
  unfold HaarModulus.closedHalfCharacter Jacquet.complexCharacter Jacquet.positiveHalfCharacter
  simp only [MonoidHom.comp_apply]
  rw [closedRestrictCharacter_conj g hUU' hMM' hU hU' hMU hM'U' m]

/-- The inverse half modulus `δ^{-1/2}` corresponds under conjugation. -/
theorem closedInverseHalfCharacter_conj (g : G) (hUU' : ∀ x : G, x ∈ U' ↔ g⁻¹ * x * g ∈ U)
    (hMM' : ∀ x : G, x ∈ M' ↔ g⁻¹ * x * g ∈ M) (hU : IsClosed (U : Set G))
    (hU' : IsClosed (U' : Set G)) (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (hM'U' : M' ≤ Subgroup.normalizer (U' : Set G)) (m : M') :
    HaarModulus.closedInverseHalfCharacter U' hU' M' hM'U' m =
      HaarModulus.closedInverseHalfCharacter U hU M hMU (conjugationEquiv g hMM' m) := by
  unfold HaarModulus.closedInverseHalfCharacter Jacquet.inverseHalfCharacter
    Jacquet.complexCharacter Jacquet.positiveHalfCharacter
  simp only [MonoidHom.inv_apply, MonoidHom.comp_apply]
  rw [closedRestrictCharacter_conj g hUU' hMM' hU hU' hMU hM'U' m]

end Characters

section Projection

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {P M U P' M' U' : Subgroup G}

/-- The Levi projections correspond under conjugation by `g`. -/
theorem projection_conj (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (g : G)
    (hPP' : ∀ x : G, x ∈ P' ↔ g⁻¹ * x * g ∈ P) (hMM' : ∀ x : G, x ∈ M' ↔ g⁻¹ * x * g ∈ M)
    (hUU' : ∀ x : G, x ∈ U' ↔ g⁻¹ * x * g ∈ U) (p : P') :
    conjugationEquiv g hMM' (h'.projection p) = h.projection (conjugationEquiv g hPP' p) := by
  symm
  rw [h.projection_eq_iff]
  have hmem := (hUU' _).mp (h'.projection_inv_mul_mem p)
  simp only [conjugationEquiv_apply]
  convert hmem using 1
  group

end Projection

section Functors

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {P M U P' M' U' : Subgroup G}

section Jacquet

/-- `[v] ↦ [g v]` from the `U`-coinvariants to the `U'`-coinvariants, for
`U' = g U g⁻¹`. -/
def coinvariantsTranslate (g : G) (hUU' : ∀ x : G, x ∈ U' ↔ g⁻¹ * x * g ∈ U)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) :
    Jacquet.Localization.Coinvariants ρ U 1 →ₗ[ℂ] Jacquet.Localization.Coinvariants ρ U' 1 :=
  Jacquet.Localization.lift ρ U 1 (Jacquet.Localization.mk ρ U' 1 ∘ₗ ρ g) (fun u v => by
    have hu : g * (u : G) * g⁻¹ ∈ U' := (hUU' _).mpr (by simp [mul_assoc])
    have key : ρ g (ρ u v) = ρ (g * (u : G) * g⁻¹) (ρ g v) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
        inv_mul_cancel_right]
    change Jacquet.Localization.mk ρ U' 1 (ρ g (ρ u v)) =
      (((1 : U →* ℂˣ) u : ℂˣ) : ℂ) • Jacquet.Localization.mk ρ U' 1 (ρ g v)
    rw [key]
    have h1 := Jacquet.Localization.mk_apply_subgroup ρ U' 1 ⟨_, hu⟩ (ρ g v)
    simpa using h1)

omit [TopologicalSpace G] [LocallyCompactSpace G] [NonarchimedeanGroup G] in
@[simp]
theorem coinvariantsTranslate_mk (g : G) (hUU' : ∀ x : G, x ∈ U' ↔ g⁻¹ * x * g ∈ U)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V) :
    coinvariantsTranslate g hUU' ρ (Jacquet.Localization.mk ρ U 1 v) =
      Jacquet.Localization.mk ρ U' 1 (ρ g v) :=
  rfl

omit [TopologicalSpace G] [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- The membership relation for the inverse conjugation. -/
theorem conj_inv_iff (g : G) {N N' : Subgroup G} (hNN' : ∀ x : G, x ∈ N' ↔ g⁻¹ * x * g ∈ N) :
    ∀ x : G, x ∈ N ↔ g⁻¹⁻¹ * x * g⁻¹ ∈ N' := by
  intro x
  rw [hNN']
  simp [mul_assoc]

/-- The translation of coinvariants is a linear equivalence, with inverse the
translation by `g⁻¹`. -/
def coinvariantsTranslateEquiv (g : G) (hUU' : ∀ x : G, x ∈ U' ↔ g⁻¹ * x * g ∈ U)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) :
    Jacquet.Localization.Coinvariants ρ U 1 ≃ₗ[ℂ] Jacquet.Localization.Coinvariants ρ U' 1 :=
  LinearEquiv.ofLinearMap (coinvariantsTranslate g hUU' ρ)
    (coinvariantsTranslate g⁻¹ (conj_inv_iff g hUU') ρ)
    (by
      apply Jacquet.Localization.hom_ext
      ext v
      change Jacquet.Localization.mk ρ U' 1 (ρ g (ρ g⁻¹ v)) = Jacquet.Localization.mk ρ U' 1 v
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])
    (by
      apply Jacquet.Localization.hom_ext
      ext v
      change Jacquet.Localization.mk ρ U 1 (ρ g⁻¹ (ρ g v)) = Jacquet.Localization.mk ρ U 1 v
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply])

/-- The component `ᵍ(r_P A) ≅ r_{P'} A`, `[v] ↦ [g v]`. -/
def jacquetConjugationIsoApp (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (g : G)
    (hMM' : ∀ x : G, x ∈ M' ↔ g⁻¹ * x * g ∈ M) (hUU' : ∀ x : G, x ∈ U' ↔ g⁻¹ * x * g ∈ U)
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set G)) (A : SmoothRep.{0, uG, uV} ℂ G) :
    (conjugationFunctor g hMM').obj ((jacquetFunctor h hU).obj A) ≅
      (jacquetFunctor h' hU').obj A :=
  SmoothRep.mkIso (Representation.Equiv.mk (coinvariantsTranslateEquiv g hUU' A.representation)
    (fun x => by
      apply Jacquet.Localization.hom_ext
      ext v
      change coinvariantsTranslate g hUU' A.representation
          (((HaarModulus.closedInverseHalfCharacter U hU M h.levi_le_normalizer
            (conjugationEquiv g hMM' x) : ℂˣ) : ℂ) •
            Jacquet.Localization.mk A.representation U 1
              (A.representation (conjugationEquiv g hMM' x) v)) =
        ((HaarModulus.closedInverseHalfCharacter U' hU' M' h'.levi_le_normalizer x : ℂˣ) : ℂ) •
          Jacquet.Localization.mk A.representation U' 1
            (A.representation x (A.representation g v))
      rw [map_smul, coinvariantsTranslate_mk,
        closedInverseHalfCharacter_conj g hUU' hMM' hU hU' h.levi_le_normalizer
          h'.levi_le_normalizer x]
      congr 2
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
        conjugationEquiv_apply]
      group))

/-- Conjugation compatibility of normalized Jacquet restriction:
`r_{P'} ≅ ᵍ(-) ∘ r_P` on the full smooth category, by `[v] ↦ [g v]`. -/
def jacquetConjugationIso (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (g : G)
    (hMM' : ∀ x : G, x ∈ M' ↔ g⁻¹ * x * g ∈ M) (hUU' : ∀ x : G, x ∈ U' ↔ g⁻¹ * x * g ∈ U)
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set G)) :
    jacquetFunctor.{uG, uV} h hU ⋙ conjugationFunctor g hMM' ≅ jacquetFunctor h' hU' :=
  NatIso.ofComponents (jacquetConjugationIsoApp h h' g hMM' hUU' hU hU') (fun {A B} f => by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply Jacquet.Localization.hom_ext
    ext v
    change Jacquet.Localization.mk B.representation U' 1
        (B.representation g (SmoothRep.hom f v)) =
      Jacquet.Localization.mk B.representation U' 1 (SmoothRep.hom f (A.representation g v))
    rw [(SmoothRep.hom f).isIntertwining])

@[simp]
theorem jacquetConjugationIso_hom_mk (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (g : G)
    (hMM' : ∀ x : G, x ∈ M' ↔ g⁻¹ * x * g ∈ M) (hUU' : ∀ x : G, x ∈ U' ↔ g⁻¹ * x * g ∈ U)
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set G)) (A : SmoothRep.{0, uG, uV} ℂ G)
    (v : A) :
    SmoothRep.hom ((jacquetConjugationIso h h' g hMM' hUU' hU hU').hom.app A)
        (Jacquet.Localization.mk A.representation U 1 v) =
      Jacquet.Localization.mk A.representation U' 1 (A.representation g v) :=
  rfl

end Jacquet

section Induction

/-- Left translation `f ↦ f(g⁻¹ ·)` from `P`-covariant to `P'`-covariant
functions, for `P' = g P g⁻¹` and `σ'(p') = σ(g⁻¹ p' g)`; it commutes with right
translation. -/
def coindTranslate (g : G) (hPP' : ∀ x : G, x ∈ P' ↔ g⁻¹ * x * g ∈ P)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ P V)
    (σ' : Representation ℂ P' V) (hσ : ∀ p : P', σ' p = σ (conjugationEquiv g hPP' p)) :
    (Induction.equivariantAction P σ).IntertwiningMap (Induction.equivariantAction P' σ') where
  toFun f := ⟨fun y => f.1 (g⁻¹ * y), fun p y => by
    have hf := f.2 (conjugationEquiv g hPP' p) (g⁻¹ * y)
    change f.1 (g⁻¹ * ((p : G) * y)) = σ' p (f.1 (g⁻¹ * y))
    rw [hσ, ← hf]
    simp [mul_assoc]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' z := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext y
    change f.1 (g⁻¹ * y * z) = f.1 (g⁻¹ * (y * z))
    rw [mul_assoc]

/-- The inducing representations of `i_P A` and `i_{P'} (ᵍA)` correspond under
conjugation by `g`. -/
theorem inducingRepresentation_conj (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (g : G)
    (hPP' : ∀ x : G, x ∈ P' ↔ g⁻¹ * x * g ∈ P) (hMM' : ∀ x : G, x ∈ M' ↔ g⁻¹ * x * g ∈ M)
    (hUU' : ∀ x : G, x ∈ U' ↔ g⁻¹ * x * g ∈ U) (hU : IsClosed (U : Set G))
    (hU' : IsClosed (U' : Set G)) (A : SmoothRep.{0, uG, uV} ℂ M) (p : P') :
    inducingRepresentation h' hU' ((conjugationFunctor g hMM').obj A) p =
      inducingRepresentation h hU A (conjugationEquiv g hPP' p) := by
  change ((HaarModulus.closedHalfCharacter U' hU' P' h'.le_normalizer p : ℂˣ) : ℂ) •
      A.representation (conjugationEquiv g hMM' (h'.projection p)) =
    ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer (conjugationEquiv g hPP' p) : ℂˣ) :
        ℂ) • A.representation (h.projection (conjugationEquiv g hPP' p))
  rw [closedHalfCharacter_conj g hUU' hPP' hU hU' h.le_normalizer h'.le_normalizer p,
    projection_conj h h' g hPP' hMM' hUU' p]

/-- The component `i_P A ≅ i_{P'} (ᵍA)`, `f ↦ f(g⁻¹ ·)`. -/
def inductionConjugationIsoApp (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (g : G)
    (hPP' : ∀ x : G, x ∈ P' ↔ g⁻¹ * x * g ∈ P) (hMM' : ∀ x : G, x ∈ M' ↔ g⁻¹ * x * g ∈ M)
    (hUU' : ∀ x : G, x ∈ U' ↔ g⁻¹ * x * g ∈ U) (hU : IsClosed (U : Set G))
    (hU' : IsClosed (U' : Set G)) (A : SmoothRep.{0, uG, uV} ℂ M) :
    (normalizedInductionFunctor h hU).obj A ≅
      (normalizedInductionFunctor h' hU').obj ((conjugationFunctor g hMM').obj A) :=
  let σ := inducingRepresentation h hU A
  let σ' := inducingRepresentation h' hU' ((conjugationFunctor g hMM').obj A)
  have hσ : ∀ p : P', σ' p = σ (conjugationEquiv g hPP' p) :=
    inducingRepresentation_conj h h' g hPP' hMM' hUU' hU hU' A
  have hσ' : ∀ p : P, σ p = σ' (conjugationEquiv g⁻¹ (conj_inv_iff g hPP') p) := by
    intro p
    rw [hσ]
    congr 1
    ext
    simp [mul_assoc]
  let T := smoothMap (coindTranslate g hPP' σ σ' hσ)
  let T' := smoothMap (coindTranslate g⁻¹ (conj_inv_iff g hPP') σ' σ hσ')
  SmoothRep.mkIso (Representation.Equiv.mk
    (LinearEquiv.ofLinearMap T.toLinearMap T'.toLinearMap
      (by
        apply LinearMap.ext
        intro f
        apply Subtype.ext
        apply Subtype.ext
        funext y
        change f.1.1 (g⁻¹⁻¹ * (g⁻¹ * y)) = f.1.1 y
        simp)
      (by
        apply LinearMap.ext
        intro f
        apply Subtype.ext
        apply Subtype.ext
        funext y
        change f.1.1 (g⁻¹ * (g⁻¹⁻¹ * y)) = f.1.1 y
        simp))
    (fun z => by
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      apply Subtype.ext
      funext y
      change f.1.1 (g⁻¹ * y * z) = f.1.1 (g⁻¹ * (y * z))
      rw [mul_assoc]))

/-- Conjugation compatibility of normalized parabolic induction:
`i_P ≅ i_{P'} ∘ ᵍ(-)` on the full smooth category, by `f ↦ f(g⁻¹ ·)`. -/
def inductionConjugationIso (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (g : G)
    (hPP' : ∀ x : G, x ∈ P' ↔ g⁻¹ * x * g ∈ P) (hMM' : ∀ x : G, x ∈ M' ↔ g⁻¹ * x * g ∈ M)
    (hUU' : ∀ x : G, x ∈ U' ↔ g⁻¹ * x * g ∈ U) (hU : IsClosed (U : Set G))
    (hU' : IsClosed (U' : Set G)) :
    normalizedInductionFunctor.{uG, uV} h hU ≅
      conjugationFunctor g hMM' ⋙ normalizedInductionFunctor h' hU' :=
  NatIso.ofComponents (inductionConjugationIsoApp h h' g hPP' hMM' hUU' hU hU') (fun {A B} f => by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro F
    apply Subtype.ext
    apply Subtype.ext
    funext y
    rfl)

@[simp]
theorem inductionConjugationIso_hom_eval (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (g : G)
    (hPP' : ∀ x : G, x ∈ P' ↔ g⁻¹ * x * g ∈ P) (hMM' : ∀ x : G, x ∈ M' ↔ g⁻¹ * x * g ∈ M)
    (hUU' : ∀ x : G, x ∈ U' ↔ g⁻¹ * x * g ∈ U) (hU : IsClosed (U : Set G))
    (hU' : IsClosed (U' : Set G)) (A : SmoothRep.{0, uG, uV} ℂ M)
    (f : (normalizedInductionFunctor h hU).obj A) (y : G) :
    Induction.eval P' (inducingRepresentation h' hU' ((conjugationFunctor g hMM').obj A))
        (SmoothRep.hom ((inductionConjugationIso h h' g hPP' hMM' hUU' hU hU').hom.app A) f) y =
      Induction.eval P (inducingRepresentation h hU A) f (g⁻¹ * y) :=
  rfl

end Induction

section K0

/-- On exact K0, induction from `P'` after conjugation is induction from `P`. -/
theorem inductionK0_comp_conjugationK0 (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (g : G)
    (hPP' : ∀ x : G, x ∈ P' ↔ g⁻¹ * x * g ∈ P) (hMM' : ∀ x : G, x ∈ M' ↔ g⁻¹ * x * g ∈ M)
    (hUU' : ∀ x : G, x ∈ U' ↔ g⁻¹ * x * g ∈ U) (hU : IsClosed (U : Set G))
    (hU' : IsClosed (U' : Set G))
    (hl : PreservesFiniteLength (normalizedInductionFunctor.{uG, max uG uV} h hU))
    (hx : PreservesFiniteLengthShortExact (normalizedInductionFunctor.{uG, max uG uV} h hU))
    (hl' : PreservesFiniteLength (normalizedInductionFunctor.{uG, max uG uV} h' hU'))
    (hx' : PreservesFiniteLengthShortExact (normalizedInductionFunctor.{uG, max uG uV} h' hU')) :
    (inductionK0 h' hU' hl' hx').comp (conjugationK0.{uG, max uG uV} g hMM') =
      inductionK0 h hU hl hx :=
  calc (inductionK0 h' hU' hl' hx').comp (conjugationK0.{uG, max uG uV} g hMM')
      = SmoothRep.FiniteLengthGrothendieckGroup.map
          (conjugationFunctor.{uG, max uG uV} g hMM' ⋙ normalizedInductionFunctor h' hU')
          ((SmoothRep.pullbackFunctor_preservesFiniteLength _).comp hl')
          (SmoothRep.PreservesFiniteLengthShortExact.comp
            (SmoothRep.pullbackFunctor_preservesFiniteLength _)
            (SmoothRep.pullbackFunctor_preservesShortExact _) hx') :=
        (SmoothRep.FiniteLengthGrothendieckGroup.map_comp _ _
          (SmoothRep.pullbackFunctor_preservesFiniteLength _)
          (SmoothRep.pullbackFunctor_preservesShortExact _) hl' hx' _ _).symm
    _ = inductionK0 h hU hl hx :=
        SmoothRep.FiniteLengthGrothendieckGroup.map_eq_of_iso
          (inductionConjugationIso.{uG, max uG uV} h h' g hPP' hMM' hUU' hU hU').symm _ _ _ _

/-- On exact K0, conjugation after Jacquet restriction to `M` is Jacquet
restriction to `M'`. -/
theorem conjugationK0_comp_jacquetK0 (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (g : G)
    (hMM' : ∀ x : G, x ∈ M' ↔ g⁻¹ * x * g ∈ M) (hUU' : ∀ x : G, x ∈ U' ↔ g⁻¹ * x * g ∈ U)
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set G))
    (hl : PreservesFiniteLength (jacquetFunctor.{uG, max uG uV} h hU))
    (hx : PreservesFiniteLengthShortExact (jacquetFunctor.{uG, max uG uV} h hU))
    (hl' : PreservesFiniteLength (jacquetFunctor.{uG, max uG uV} h' hU'))
    (hx' : PreservesFiniteLengthShortExact (jacquetFunctor.{uG, max uG uV} h' hU')) :
    (conjugationK0.{uG, max uG uV} g hMM').comp (jacquetK0 h hU hl hx) =
      jacquetK0 h' hU' hl' hx' :=
  calc (conjugationK0.{uG, max uG uV} g hMM').comp (jacquetK0 h hU hl hx)
      = SmoothRep.FiniteLengthGrothendieckGroup.map
          (jacquetFunctor.{uG, max uG uV} h hU ⋙ conjugationFunctor g hMM')
          (hl.comp (SmoothRep.pullbackFunctor_preservesFiniteLength _))
          (SmoothRep.PreservesFiniteLengthShortExact.comp hl hx
            (SmoothRep.pullbackFunctor_preservesShortExact _)) :=
        (SmoothRep.FiniteLengthGrothendieckGroup.map_comp _ _ hl hx
          (SmoothRep.pullbackFunctor_preservesFiniteLength _)
          (SmoothRep.pullbackFunctor_preservesShortExact _) _ _).symm
    _ = jacquetK0 h' hU' hl' hx' :=
        SmoothRep.FiniteLengthGrothendieckGroup.map_eq_of_iso
          (jacquetConjugationIso.{uG, max uG uV} h h' g hMM' hUU' hU hU') _ _ _ _

end K0

end Functors

end Langlands.Aubert.General
