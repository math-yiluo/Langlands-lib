import Langlands.GroupScheme.Reductive.FiniteFieldFormClassificationStatement
import Langlands.GroupScheme.Reductive.FiniteFieldFormExistenceStatement
import Langlands.GroupScheme.Reductive.InnerFormStarActionStatement
import Langlands.GroupScheme.Reductive.StarActionContinuityProof
import Langlands.GroupScheme.Reductive.AlgebraicExtensionReflectionProof
import Langlands.GroupScheme.Adjoint.ExistenceProof
import Langlands.GroupScheme.Rational.FiniteFieldCocycleTorusReduction
import Langlands.GroupScheme.Rational.InnerDiscrepancy
import Langlands.GroupScheme.RelativeInnerForm
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Forms over a finite field: reduction to inner forms and to the existence clause -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace FiniteFieldFormClassification

section RootPairingAlgebra

variable {R : Type*} [CommRing R]
  {ι M N ι₁ M₁ N₁ ι₂ M₂ N₂ : Type*}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup N₁] [Module R N₁]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} {Q : RootPairing ι₁ R M₁ N₁} {Q' : RootPairing ι₂ R M₂ N₂}

/-- The inverse of an equivalence of root pairings, composed after it, is the identity. -/
theorem symm_comp_self (f : RootPairing.Equiv P Q) :
    RootPairing.Equiv.comp (RootPairing.Equiv.symm P Q f) f = RootPairing.Equiv.id P := by
  ext x
  · change f.weightEquiv.symm (f.toHom.weightMap x) = x
    exact RootPairing.Equiv.weightEquiv_symm_weightMap f x
  · change f.toHom.coweightMap (f.coweightEquiv.symm x) = x
    exact RootPairing.Equiv.coweightMap_coweightEquiv_symm f x
  · change f.indexEquiv.symm (f.indexEquiv x) = x
    exact Equiv.symm_apply_apply _ x

/-- An equivalence of root pairings, composed after its inverse, is the identity. -/
theorem self_comp_symm (f : RootPairing.Equiv P Q) :
    RootPairing.Equiv.comp f (RootPairing.Equiv.symm P Q f) = RootPairing.Equiv.id Q := by
  ext x
  · change f.toHom.weightMap (f.weightEquiv.symm x) = x
    exact RootPairing.Equiv.weightMap_weightEquiv_symm f x
  · change f.coweightEquiv.symm (f.toHom.coweightMap x) = x
    exact RootPairing.Equiv.coweightEquiv_symm_coweightMap f x
  · change f.indexEquiv (f.indexEquiv.symm x) = x
    exact Equiv.apply_symm_apply _ x

/-- If `f ∘ θ = μ ∘ f`, then `f⁻¹ ∘ μ = θ ∘ f⁻¹`. -/
theorem symm_comp_of_comp_eq {f : RootPairing.Equiv P Q} {θ : RootPairing.Aut P}
    {μ : RootPairing.Aut Q}
    (h : RootPairing.Equiv.comp f θ = RootPairing.Equiv.comp μ f) :
    RootPairing.Equiv.comp (RootPairing.Equiv.symm P Q f) μ =
      RootPairing.Equiv.comp θ (RootPairing.Equiv.symm P Q f) := by
  calc RootPairing.Equiv.comp (RootPairing.Equiv.symm P Q f) μ
      = RootPairing.Equiv.comp (RootPairing.Equiv.symm P Q f)
          (RootPairing.Equiv.comp (RootPairing.Equiv.comp μ f)
            (RootPairing.Equiv.symm P Q f)) := by
        rw [RootPairing.Equiv.comp_assoc μ f, self_comp_symm, RootPairing.Equiv.id_comp]
    _ = RootPairing.Equiv.comp (RootPairing.Equiv.symm P Q f)
          (RootPairing.Equiv.comp (RootPairing.Equiv.comp f θ)
            (RootPairing.Equiv.symm P Q f)) := by
        rw [h]
    _ = RootPairing.Equiv.comp θ (RootPairing.Equiv.symm P Q f) := by
        rw [RootPairing.Equiv.comp_assoc f θ,
          ← RootPairing.Equiv.comp_assoc (RootPairing.Equiv.symm P Q f) f, symm_comp_self,
          RootPairing.Equiv.comp_id]

/-- If `f ∘ θ = μ ∘ f`, `f' ∘ θ' = μ' ∘ f'` and `c ∘ θ = θ' ∘ c`, then
`F = f' ∘ c ∘ f⁻¹` satisfies `F ∘ μ = μ' ∘ F`. -/
theorem comp_intertwine_of_conj {f : RootPairing.Equiv P Q} {f' : RootPairing.Equiv P Q'}
    {θ θ' c : RootPairing.Aut P} {μ : RootPairing.Aut Q} {μ' : RootPairing.Aut Q'}
    (hθ : RootPairing.Equiv.comp f θ = RootPairing.Equiv.comp μ f)
    (hθ' : RootPairing.Equiv.comp f' θ' = RootPairing.Equiv.comp μ' f')
    (hc : RootPairing.Equiv.comp c θ = RootPairing.Equiv.comp θ' c) :
    RootPairing.Equiv.comp
        (RootPairing.Equiv.comp f' (RootPairing.Equiv.comp c (RootPairing.Equiv.symm P Q f))) μ =
      RootPairing.Equiv.comp μ'
        (RootPairing.Equiv.comp f' (RootPairing.Equiv.comp c (RootPairing.Equiv.symm P Q f))) := by
  rw [RootPairing.Equiv.comp_assoc f', RootPairing.Equiv.comp_assoc c,
    symm_comp_of_comp_eq hθ, ← RootPairing.Equiv.comp_assoc c θ, hc,
    RootPairing.Equiv.comp_assoc θ' c, ← RootPairing.Equiv.comp_assoc f' θ', hθ',
    RootPairing.Equiv.comp_assoc μ' f']

/-- If `f ∘ θ = μ ∘ f`, `f' ∘ θ' = μ' ∘ f'` and `F ∘ μ = μ' ∘ F`, then
`c = f'⁻¹ ∘ F ∘ f` satisfies `c ∘ θ = θ' ∘ c`. -/
theorem conj_of_comp_intertwine {f : RootPairing.Equiv P Q} {f' : RootPairing.Equiv P Q'}
    {θ θ' : RootPairing.Aut P} {μ : RootPairing.Aut Q} {μ' : RootPairing.Aut Q'}
    {F : RootPairing.Equiv Q Q'}
    (hθ : RootPairing.Equiv.comp f θ = RootPairing.Equiv.comp μ f)
    (hθ' : RootPairing.Equiv.comp f' θ' = RootPairing.Equiv.comp μ' f')
    (hF : RootPairing.Equiv.comp F μ = RootPairing.Equiv.comp μ' F) :
    RootPairing.Equiv.comp
        (RootPairing.Equiv.comp (RootPairing.Equiv.symm P Q' f') (RootPairing.Equiv.comp F f)) θ =
      RootPairing.Equiv.comp θ'
        (RootPairing.Equiv.comp (RootPairing.Equiv.symm P Q' f') (RootPairing.Equiv.comp F f)) := by
  rw [RootPairing.Equiv.comp_assoc (RootPairing.Equiv.symm P Q' f'),
    RootPairing.Equiv.comp_assoc F f, hθ, ← RootPairing.Equiv.comp_assoc F μ, hF,
    RootPairing.Equiv.comp_assoc μ' F,
    ← RootPairing.Equiv.comp_assoc (RootPairing.Equiv.symm P Q' f') μ',
    symm_comp_of_comp_eq hθ', RootPairing.Equiv.comp_assoc θ']

/-- An intertwining relation `F ∘ x = y ∘ F` passes to all natural powers. -/
theorem comp_pow_of_comp_eq {F : RootPairing.Equiv Q Q'} {x : RootPairing.Aut Q}
    {y : RootPairing.Aut Q'} (h : RootPairing.Equiv.comp F x = RootPairing.Equiv.comp y F)
    (n : ℕ) : RootPairing.Equiv.comp F (x ^ n) = RootPairing.Equiv.comp (y ^ n) F := by
  induction n with
  | zero =>
    change RootPairing.Equiv.comp F (RootPairing.Equiv.id Q) =
      RootPairing.Equiv.comp (RootPairing.Equiv.id Q') F
    rw [RootPairing.Equiv.id_comp, RootPairing.Equiv.comp_id]
  | succ n ih =>
    change RootPairing.Equiv.comp F (RootPairing.Equiv.comp (x ^ n) x) =
      RootPairing.Equiv.comp (RootPairing.Equiv.comp (y ^ n) y) F
    rw [← RootPairing.Equiv.comp_assoc F, ih, RootPairing.Equiv.comp_assoc (y ^ n) F, h,
      RootPairing.Equiv.comp_assoc (y ^ n) y]

end RootPairingAlgebra

section Frobenius

variable {k : Type u} [Field k] [Fintype k]

/-- On a finite-dimensional intermediate field of `k_s / k`, every element of `Gal(k_s / k)`
agrees with a natural power of the arithmetic Frobenius. -/
theorem exists_frobenius_pow_eq (L : IntermediateField k (SeparableClosure k))
    [FiniteDimensional k L] (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) :
    ∃ n : ℕ, ∀ x ∈ L,
      σ x = (FiniteField.frobeniusAlgEquivOfAlgebraic k (SeparableClosure k) ^ n) x := by
  have : Finite L := Module.finite_of_finite k
  obtain ⟨n, hn⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k L).2 (σ.restrictNormal L)
  refine ⟨n.1, fun x hx => ?_⟩
  have h1 := AlgEquiv.restrictNormal_commutes σ L ⟨x, hx⟩
  rw [← hn] at h1
  change _ = σ x at h1
  rw [← h1, AlgEquiv.coe_pow, AlgEquiv.coe_pow,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, map_pow]
  rfl

variable {G G' : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom G'.X.hom] [LocallyOfFiniteType G'.X.hom]

/-- For two Galois pinning data over `k_s` of groups over a finite field `k`, the star actions
of any `σ ∈ Gal(k_s / k)` are the same natural power of the star actions of Frobenius. -/
theorem exists_starAction_eq_pow (d : GaloisPinningData k (SeparableClosure k) G)
    (d' : GaloisPinningData k (SeparableClosure k) G')
    (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) :
    ∃ n : ℕ,
      d.starAction σ =
          d.starAction (FiniteField.frobeniusAlgEquivOfAlgebraic k (SeparableClosure k)) ^ n ∧
        d'.starAction σ =
          d'.starAction (FiniteField.frobeniusAlgEquivOfAlgebraic k (SeparableClosure k)) ^ n := by
  obtain ⟨L₁, hL₁, h₁⟩ := starActionContinuity k (SeparableClosure k) G d
  obtain ⟨L₂, hL₂, h₂⟩ := starActionContinuity k (SeparableClosure k) G' d'
  have : FiniteDimensional k ↥(L₁ ⊔ L₂) := IntermediateField.finiteDimensional_sup L₁ L₂
  obtain ⟨n, hn⟩ := exists_frobenius_pow_eq (L₁ ⊔ L₂) σ
  let φ := FiniteField.frobeniusAlgEquivOfAlgebraic k (SeparableClosure k) ^ n
  have hfix : ∀ x ∈ L₁ ⊔ L₂, (φ⁻¹ * σ) x = x := by
    intro x hx
    rw [AlgEquiv.mul_apply, hn x hx, AlgEquiv.aut_inv]
    exact φ.symm_apply_apply x
  have hσ : σ = φ * (φ⁻¹ * σ) := (mul_inv_cancel_left φ σ).symm
  refine ⟨n, ?_, ?_⟩
  · have h := (h₁ (φ⁻¹ * σ) fun x hx => hfix x (le_sup_left (a := L₁) hx)).2
    calc d.starAction σ = d.starAction (φ * (φ⁻¹ * σ)) := congrArg _ hσ
      _ = _ := by rw [map_mul, h, mul_one, map_pow]
  · have h := (h₂ (φ⁻¹ * σ) fun x hx => hfix x (le_sup_right (b := L₂) hx)).2
    calc d'.starAction σ = d'.starAction (φ * (φ⁻¹ * σ)) := congrArg _ hσ
      _ = _ := by rw [map_mul, h, mul_one, map_pow]

end Frobenius

end FiniteFieldFormClassification

open FiniteFieldFormClassification in
/-- **Reduction.** The classification of forms of a split reductive group over a finite field
follows from the detection of inner forms by the star action
(`InnerFormStarActionStatement`) and from the existence clause
(`FiniteFieldFormExistenceStatement`). -/
theorem finiteFieldFormClassification_of_innerFormStarAction
    (hinner : InnerFormStarActionStatement.{u})
    (hexist : FiniteFieldFormExistenceStatement.{u}) :
    FiniteFieldFormClassificationStatement.{u} := by
  intro k _ _ G₀ _ p
  dsimp only
  refine ⟨fun θ hθ => hexist k G₀ p θ hθ, ?_⟩
  intro G G' _ _ _ _ d d' θ θ' hG hG'
  obtain ⟨f, hf, hθ⟩ := hG
  obtain ⟨f', hf', hθ'⟩ := hG'
  have hred : IsConnectedReductive G :=
    connectedReductiveAlgebraicExtensionReflection k (SeparableClosure k) G
      d.isConnectedReductive
  obtain ⟨A, q, hq⟩ := adjointQuotientExistence k G hred
  constructor
  · rintro ⟨φ⟩
    obtain ⟨F, hFb, hF⟩ := (hinner k G G' A q hq d d').mp
      ⟨k, inferInstance, inferInstance, inferInstance, inferInstance,
        LocalGroupIso.ofIso φ _, LocalGroupIso.ofIso_hasInnerDiscrepancy φ hq.innerAction _⟩
    have hc := conj_of_comp_intertwine hθ hθ'
      (hF (FiniteField.frobeniusAlgEquivOfAlgebraic k (SeparableClosure k)))
    let c : RootPairing.Aut p.rootDatum :=
      RootPairing.Equiv.comp (RootPairing.Equiv.symm _ _ f') (RootPairing.Equiv.comp F f)
    have hcb : c ∈ p.basedRootDatumAut := by
      intro a
      change a ∈ p.base.support ↔
        f'.indexEquiv.symm (F.indexEquiv (f.indexEquiv a)) ∈ p.base.support
      rw [hf a, hFb, hf', Equiv.apply_symm_apply]
    refine isConj_iff.mpr ⟨⟨c, hcb⟩, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact mul_inv_eq_iff_eq_mul.mpr hc
  · intro hconj
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    have hc' : RootPairing.Equiv.comp c.val θ.val = RootPairing.Equiv.comp θ'.val c.val := by
      have h := congrArg Subtype.val hc
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h
      exact mul_inv_eq_iff_eq_mul.mp h
    have hcb : ∀ a, a ∈ p.base.support ↔ c.val.indexEquiv a ∈ p.base.support := c.property
    let F := RootPairing.Equiv.comp f' (RootPairing.Equiv.comp c.val (RootPairing.Equiv.symm _ _ f))
    have hFb : ∀ a, a ∈ d.toSplitPinning.base.support ↔
        F.indexEquiv a ∈ d'.toSplitPinning.base.support := by
      intro a
      change _ ↔ f'.indexEquiv (c.val.indexEquiv (f.indexEquiv.symm a)) ∈ _
      rw [← hf', ← hcb, hf, Equiv.apply_symm_apply]
    have hFrob := comp_intertwine_of_conj hθ hθ' hc'
    have hall : ∀ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
        RootPairing.Equiv.comp F (d.starAction σ).val =
          RootPairing.Equiv.comp (d'.starAction σ).val F := by
      intro σ
      obtain ⟨n, h1, h2⟩ := exists_starAction_eq_pow d d' σ
      rw [h1, h2, Subgroup.coe_pow, Subgroup.coe_pow]
      exact comp_pow_of_comp_eq hFrob n
    obtain ⟨L, _, _, _, _, e, he⟩ := (hinner k G G' A q hq d d').mpr ⟨F, hFb, hall⟩
    have hA := hq.isAdjoint.isSemisimple.isConnectedReductive
    have := hA.smooth
    have := hA.isAffineHom
    have := hA.connectedSpace
    have hξ : (e.innerCocycle hq.innerAction hq.innerAction_isFaithful he).IsTrivial :=
      Cocycle.isTrivial_of_finite A (L := L) _
    obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc k L
    have : Surjective (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L)))).hom := hsurj
    have : Flat (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L)))).hom := hflat
    have : QuasiCompact (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L)))).hom := hqc
    exact ⟨e.descendOfTrivial hq.innerAction _
      (e.innerCocycle_hasDiscrepancy hq.innerAction hq.innerAction_isFaithful he) hξ⟩

/-- **Reduction statement.** The detection of inner forms by the star action
(`InnerFormStarActionStatement`) and the existence clause (`FiniteFieldFormExistenceStatement`)
together imply the classification of forms of a split reductive group over a finite field
(`FiniteFieldFormClassificationStatement`). -/
def FiniteFieldFormClassificationReductionStatement : Prop :=
  InnerFormStarActionStatement.{u} → FiniteFieldFormExistenceStatement.{u} →
    FiniteFieldFormClassificationStatement.{u}

/-- Proof of `FiniteFieldFormClassificationReductionStatement`. -/
theorem finiteFieldFormClassificationReduction :
    FiniteFieldFormClassificationReductionStatement.{u} :=
  fun hinner hexist => finiteFieldFormClassification_of_innerFormStarAction hinner hexist

end Langlands.GroupScheme
