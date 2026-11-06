import Langlands.Representation.Aubert.General.RationalInductionDualityAssembly
import Langlands.Representation.Unitary.HermitianDual
import Langlands.Representation.Unitary.SquareIntegrableProof
import Langlands.Representation.Category.Twist

/-! # Hermitian duality for normalized induction

Renard IV.2.1.2 identifies the hermitian dual of `i_P^G (σ ⊗ χ)` with
`i_P^G (σ^h ⊗ conj(χ)⁻¹)`, and IV.2.1, Remark 1, identifies an admissible
unitarizable representation with its hermitian dual. This module combines the
published natural smooth-dual isomorphism `exists_natural_of_compactSpace` with the
conjugate-linear identifications `InvariantPositiveForm.smoothDualEquiv`. No
conjugate representation is constructed: the hermitian dual is replaced by the
smooth dual together with conjugate-linear equivariant maps, and two such maps
around a linear intertwiner compose to a linear intertwiner.
-/

noncomputable section

universe uG uV uW uX uY

open CategoryTheory MeasureTheory
open scoped NNReal ComplexConjugate

namespace Langlands

section ConjugateSandwich

variable {G : Type uG} [Group G]
  {V₁ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] {V₂ : Type uW} [AddCommGroup V₂] [Module ℂ V₂]
  {V₃ : Type uX} [AddCommGroup V₃] [Module ℂ V₃] {V₄ : Type uY} [AddCommGroup V₄] [Module ℂ V₄]
  {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂}
  {ρ₃ : Representation ℂ G V₃} {ρ₄ : Representation ℂ G V₄}

/-- A linear intertwiner between two equivariant conjugate-linear maps: the composite
`C ∘ B ∘ A` is linear, since conjugation is an involution, and it is equivariant. -/
def conjugateSandwich (A : V₁ →ₗ⋆[ℂ] V₂) (hA : ∀ (g : G) (v : V₁), A (ρ₁ g v) = ρ₂ g (A v))
    (B : ρ₂.IntertwiningMap ρ₃) (C : V₃ →ₗ⋆[ℂ] V₄)
    (hC : ∀ (g : G) (v : V₃), C (ρ₃ g v) = ρ₄ g (C v)) :
    ρ₁.IntertwiningMap ρ₄ :=
  LinearMap.intertwiningMap_of_isIntertwiningMap ρ₁ ρ₄ (C.comp (B.toLinearMap.comp A))
    (fun g v => by
      change C (B (A (ρ₁ g v))) = ρ₄ g (C (B (A v)))
      rw [hA, B.isIntertwining, hC])

@[simp]
theorem conjugateSandwich_apply (A : V₁ →ₗ⋆[ℂ] V₂)
    (hA : ∀ (g : G) (v : V₁), A (ρ₁ g v) = ρ₂ g (A v))
    (B : ρ₂.IntertwiningMap ρ₃) (C : V₃ →ₗ⋆[ℂ] V₄)
    (hC : ∀ (g : G) (v : V₃), C (ρ₃ g v) = ρ₄ g (C v)) (v : V₁) :
    conjugateSandwich A hA B C hC v = C (B (A v)) :=
  rfl

end ConjugateSandwich

namespace Induction

section ConjugateLinear

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (P : Subgroup G) {ρ : Representation ℂ P V} {τ : Representation ℂ P W}

/-- Pointwise postcomposition of smooth induced functions with a conjugate-linear map
intertwining the inducing representations. -/
def smoothFunctionsConjMap (T : V →ₗ⋆[ℂ] W)
    (hT : ∀ (p : P) (v : V), T (ρ p v) = τ p (T v)) :
    SmoothFunctions P ρ →ₗ⋆[ℂ] SmoothFunctions P τ where
  toFun f := ⟨⟨fun x => T (f.1.1 x), fun p x => by
      change T (f.1.1 ((p : G) * x)) = τ p (T (f.1.1 x))
      exact (congrArg T (f.1.2 p x)).trans (hT p _)⟩, by
    obtain ⟨K, hK⟩ := f.property
    refine ⟨K, fun k => ?_⟩
    apply Subtype.ext
    funext x
    change T (f.1.1 (x * (k : G))) = T (f.1.1 x)
    exact congrArg T (congrArg (fun F : EquivariantFunctions P ρ => F.1 x) (hK k))⟩
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact map_add T (f.1.1 x) (g.1.1 x)
  map_smul' c f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact map_smulₛₗ T c (f.1.1 x)

omit [IsTopologicalGroup G] in
@[simp]
theorem eval_smoothFunctionsConjMap (T : V →ₗ⋆[ℂ] W)
    (hT : ∀ (p : P) (v : V), T (ρ p v) = τ p (T v)) (f : SmoothFunctions P ρ) (x : G) :
    eval P τ (smoothFunctionsConjMap P T hT f) x = T (eval P ρ f x) :=
  rfl

/-- Pointwise postcomposition commutes with right translation. -/
theorem smoothFunctionsConjMap_smoothInduced (T : V →ₗ⋆[ℂ] W)
    (hT : ∀ (p : P) (v : V), T (ρ p v) = τ p (T v)) (g : G) (f : SmoothFunctions P ρ) :
    smoothFunctionsConjMap P T hT (smoothInduced P ρ g f) =
      smoothInduced P τ g (smoothFunctionsConjMap P T hT f) :=
  rfl

/-- A conjugate-linear equivalence intertwining the inducing representations induces a
conjugate-linear equivalence of smooth induced functions. -/
def smoothFunctionsConjEquiv (T : V ≃ₗ⋆[ℂ] W)
    (hT : ∀ (p : P) (v : V), T (ρ p v) = τ p (T v)) :
    SmoothFunctions P ρ ≃ₗ⋆[ℂ] SmoothFunctions P τ :=
  have hT' : ∀ (p : P) (w : W), T.symm (τ p w) = ρ p (T.symm w) := by
    intro p w
    apply T.injective
    rw [LinearEquiv.apply_symm_apply, hT, LinearEquiv.apply_symm_apply]
  { smoothFunctionsConjMap P T.toLinearMap hT with
    invFun := smoothFunctionsConjMap P T.symm.toLinearMap hT'
    left_inv := fun f => by
      apply Subtype.ext
      apply Subtype.ext
      funext x
      exact T.symm_apply_apply (f.1.1 x)
    right_inv := fun f => by
      apply Subtype.ext
      apply Subtype.ext
      funext x
      exact T.apply_symm_apply (f.1.1 x) }

omit [IsTopologicalGroup G] in
@[simp]
theorem smoothFunctionsConjEquiv_apply (T : V ≃ₗ⋆[ℂ] W)
    (hT : ∀ (p : P) (v : V), T (ρ p v) = τ p (T v)) (f : SmoothFunctions P ρ) :
    smoothFunctionsConjEquiv P T hT f = smoothFunctionsConjMap P T.toLinearMap hT f :=
  rfl

end ConjugateLinear

end Induction

namespace SmoothRep

variable {R : Type uX} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]

/-- The inverse of an isomorphism undoes it on vectors. -/
theorem hom_inv_hom_apply {A B : SmoothRep.{uX, uG, uV} R G} (e : A ≅ B) (x : A) :
    hom e.inv (hom e.hom x) = x := by
  have := congrArg (fun φ : A ⟶ A => hom φ x) e.hom_inv_id
  simp only [hom_comp, hom_id] at this
  exact this

end SmoothRep

namespace Aubert.General

section HermitianDuality

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G))

/-- The identification `v ↦ b(v, -)` intertwines the inducing representation of
`σ ⊗ χ'` with that of `σ^∨ ⊗ χ⁻¹` when `χ'(m) · conj(χ(m)) = 1`: the half modulus is
real and `conj(χ'(m)) = χ(m)⁻¹`. -/
theorem smoothDualEquiv_inducingRepresentation (σ : SmoothRep.{0, uG, uV} ℂ M)
    (b : InvariantPositiveForm σ.representation) (hcof : CompactOpenCofinal M)
    (hσ : σ.IsAdmissible) (χ χ' : M →* ℂˣ) (hχ : IsOpen (χ.ker : Set M))
    (hχ' : IsOpen (χ'.ker : Set M))
    (hconj : ∀ m : M, (χ' m : ℂ) * starRingEnd ℂ (χ m : ℂ) = 1) (p : P) (v : σ) :
    b.smoothDualEquiv hcof hσ (inducingRepresentation h hU (σ.twist χ' hχ') p v) =
      inducingRepresentation h hU (σ.contragredient.twist χ⁻¹ (isOpen_ker_inv hχ)) p
        (b.smoothDualEquiv hcof hσ v) := by
  have hreal :
      conj ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂˣ) : ℂ) =
        ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂˣ) : ℂ) := by
    simp only [HaarModulus.closedHalfCharacter, Jacquet.complexCharacter_apply,
      Complex.conj_ofReal]
  have hχc : conj ((χ' (h.projection p) : ℂˣ) : ℂ) =
      (((χ⁻¹) (h.projection p) : ℂˣ) : ℂ) := by
    have h1 := congrArg (starRingEnd ℂ) (hconj (h.projection p))
    rw [map_mul, Complex.conj_conj, map_one] at h1
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    exact eq_inv_of_mul_eq_one_left h1
  change b.smoothDualEquiv hcof hσ
      (((HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂˣ) : ℂ) •
        (((χ' (h.projection p) : ℂˣ) : ℂ) • σ.representation (h.projection p) v)) =
    ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂˣ) : ℂ) •
      ((((χ⁻¹) (h.projection p) : ℂˣ) : ℂ) •
        smoothContragredient σ.representation (h.projection p)
          (b.smoothDualEquiv hcof hσ v))
  rw [map_smulₛₗ, map_smulₛₗ, hreal, hχc]
  exact congrArg _ (congrArg _ (b.toSmoothDual_apply_action hσ.1 _ v))

variable [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- **Hermitian duality for normalized induction** (Renard IV.2.1.2 with IV.2.1,
Remark 1). Let `G` be unimodular with `P \ G` compact and the modular character of `P`
the restricted Haar modulus on `U`. Let `σ` be an admissible unitarizable
representation of `M` and `χ, χ'` open-kernel characters with
`χ'(m) · conj(χ(m)) = 1`. For a nonzero admissible unitarizable `W`, a subrepresentation
`W ↪ i(σ ⊗ χ)` gives a nonzero morphism `i(σ ⊗ χ') → W`, and a quotient
`i(σ ⊗ χ) ↠ W` gives a nonzero morphism `W → i(σ ⊗ χ')`. -/
theorem normalizedInduction_hermitianDuality (hP : IsClosed (P : Set G))
    (hm : Continuous h.projection)
    [CompactSpace (Induction.LeftQuotient P)] [LocallyCompactSpace P]
    (hG : ∀ g : G, Measure.modularCharacter g = 1)
    (hδ : ∀ q : P, Measure.modularCharacter q =
      (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
    (σ : SmoothRep.{0, uG, uV} ℂ M) (hσ : σ.IsAdmissible)
    (hσu : IsUnitarizable σ.representation)
    (χ χ' : M →* ℂˣ) (hχ : IsOpen (χ.ker : Set M)) (hχ' : IsOpen (χ'.ker : Set M))
    (hconj : ∀ m : M, (χ' m : ℂ) * starRingEnd ℂ (χ m : ℂ) = 1)
    (W : SmoothRep.{0, uG, max uG uV} ℂ G) (hW : W.IsAdmissible)
    (hWu : IsUnitarizable W.representation) (hWn : Nontrivial W) :
    ((∃ f : W ⟶ (normalizedInductionFunctor h hU).obj (σ.twist χ hχ),
        Function.Injective (SmoothRep.hom f)) →
      ∃ f : (normalizedInductionFunctor h hU).obj (σ.twist χ' hχ') ⟶ W,
        ∃ x, SmoothRep.hom f x ≠ 0) ∧
    ((∃ f : (normalizedInductionFunctor h hU).obj (σ.twist χ hχ) ⟶ W,
        Function.Surjective (SmoothRep.hom f)) →
      ∃ f : W ⟶ (normalizedInductionFunctor h hU).obj (σ.twist χ' hχ'),
        ∃ x, SmoothRep.hom f x ≠ 0) := by
  obtain ⟨E, -⟩ := exists_natural_of_compactSpace h hU hP hm hG hδ
  obtain ⟨b⟩ := hσu
  obtain ⟨bW⟩ := hWu
  have hcofM : CompactOpenCofinal M := compactOpenCofinal_of_isClosed (h.isClosed_levi hP hm)
  have hcofG : CompactOpenCofinal G := compactOpenCofinal_of_nonarchimedean G
  let I := normalizedInductionFunctor h hU
  have hA : (σ.twist χ hχ).IsAdmissible := (SmoothRep.isAdmissible_twist_iff χ hχ σ).mpr hσ
  let D := I.obj (σ.contragredient.twist χ⁻¹ (isOpen_ker_inv hχ))
  let J := I.obj (σ.twist χ' hχ')
  let E' : (I.obj (σ.twist χ hχ)).contragredient ≅ D :=
    E _ hA ≪≫ I.mapIso (SmoothRep.contragredientTwistIso χ hχ σ)
  let Φ : J ≃ₗ⋆[ℂ] D := Induction.smoothFunctionsConjEquiv P (b.smoothDualEquiv hcofM hσ)
    (smoothDualEquiv_inducingRepresentation h hU σ b hcofM hσ χ χ' hχ hχ' hconj)
  have hΦ : ∀ (g : G) (x : J), Φ (J.representation g x) = D.representation g (Φ x) :=
    fun g x => rfl
  have hΦs : ∀ (g : G) (y : D), Φ.symm (D.representation g y) = J.representation g (Φ.symm y) := by
    intro g y
    apply Φ.injective
    rw [LinearEquiv.apply_symm_apply, hΦ, LinearEquiv.apply_symm_apply]
  let TW := bW.smoothDualEquiv hcofG hW
  have hTW : ∀ (g : G) (w : W),
      TW (W.representation g w) = smoothContragredient W.representation g (TW w) :=
    fun g w => bW.toSmoothDual_apply_action hW.1 g w
  have hTWs : ∀ (g : G) (ℓ : SmoothDual W.representation),
      TW.symm (smoothContragredient W.representation g ℓ) = W.representation g (TW.symm ℓ) := by
    intro g ℓ
    apply TW.injective
    rw [LinearEquiv.apply_symm_apply, hTW, LinearEquiv.apply_symm_apply]
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  constructor
  · rintro ⟨f, hf⟩
    have hfw : SmoothRep.hom f w ≠ 0 := fun h0 => hw (hf (h0.trans (map_zero _).symm))
    obtain ⟨ℓ, hℓ⟩ := exists_smoothDual_apply_ne_zero_of_compact_cofinal hcofG _
      (I.obj (σ.twist χ hχ)).isSmooth hfw
    let F : J.representation.IntertwiningMap W.representation :=
      conjugateSandwich Φ.toLinearMap hΦ
        ((contragredientMap (SmoothRep.hom f)).comp (SmoothRep.hom E'.inv))
        TW.symm.toLinearMap hTWs
    refine ⟨SmoothRep.ofHom F, Φ.symm (SmoothRep.hom E'.hom ℓ), fun h0 => hℓ ?_⟩
    have hzero : contragredientMap (SmoothRep.hom f) ℓ = 0 := by
      apply TW.symm.injective
      rw [map_zero]
      refine Eq.trans ?_ h0
      change TW.symm (contragredientMap (SmoothRep.hom f) ℓ) =
        TW.symm (contragredientMap (SmoothRep.hom f)
          (SmoothRep.hom E'.inv (Φ (Φ.symm (SmoothRep.hom E'.hom ℓ)))))
      rw [LinearEquiv.apply_symm_apply]
      exact congrArg _ (congrArg _ (SmoothRep.hom_inv_hom_apply E' ℓ).symm)
    exact congrArg (fun φ : SmoothDual W.representation => φ.1 w) hzero
  · rintro ⟨f, hf⟩
    let F : W.representation.IntertwiningMap J.representation :=
      conjugateSandwich TW.toLinearMap hTW
        ((SmoothRep.hom E'.hom).comp (contragredientMap (SmoothRep.hom f)))
        Φ.symm.toLinearMap hΦs
    refine ⟨SmoothRep.ofHom F, w, fun h0 => hw ?_⟩
    have h1 : SmoothRep.hom E'.hom (contragredientMap (SmoothRep.hom f) (TW w)) = 0 := by
      apply Φ.symm.injective
      rw [map_zero]
      exact h0
    have h2 : contragredientMap (SmoothRep.hom f) (TW w) = 0 := by
      rw [← SmoothRep.hom_inv_hom_apply E' (contragredientMap (SmoothRep.hom f) (TW w)), h1]
      exact map_zero _
    have h3 : TW w = 0 := by
      apply Subtype.ext
      apply LinearMap.ext
      intro y
      obtain ⟨x, rfl⟩ := hf y
      exact congrArg (fun φ : SmoothDual (I.obj (σ.twist χ hχ)).representation => φ.1 x) h2
    exact TW.injective (h3.trans (map_zero TW).symm)

end HermitianDuality

end Aubert.General

end Langlands
