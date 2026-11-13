import Langlands.LocalFactor.BrauerKernel.GlobalRelation
import Langlands.LocalFactor.BrauerKernel.PlaceNorm
import Langlands.ClassField.Global.RelativeWeilTransferNormProof
import Langlands.ClassField.Global.RelativeWeilCharacterFactorization
import Langlands.LocalFactor.BrauerKernel.ArchimedeanTrivial

/-! # The Hecke characters of a Galois type decomposition and their global relation -/

noncomputable section

set_option autoImplicit false

universe uF uV

namespace Langlands.LocalFactor.NonabelianBrauer

open CommonClosure VirtualRepresentation ClassField.Global ClassField.Global.RelativeWeilGroup
open Langlands.Global
open scoped NumberField

attribute [local instance] relativeGaloisTopology

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {e : ReciprocityFamily F}
  {z : Presentation F (Correspondence.baseExtension F)}
  (D : GaloisTypeDecomposition F e z)
  (c : FundamentalClass.ClassFamily.{0}) (k K' : Type) [Field k] [NumberField k] [Field K']
  [NumberField K'] [Algebra k K'] [IsGalois k K']
  (θ : (K' ≃ₐ[k] K') ≃* (D.K.field ≃ₐ[F.Carrier] D.K.field))
  (h : FundamentalClass.Restriction c)

/-- The Hecke character `(α ∘ N) · ‖·‖^t · Θ` of the global field of a generator. -/
def generatorHecke (g : Generator F (Correspondence.baseExtension F)) (α : HeckeCharacter k)
    (t : ℂ) (Θ : HeckeCharacter (globalField D k K' θ g)) :
    HeckeCharacter (globalField D k K' θ g) :=
  HeckeCharacter.normComp α * HeckeCharacter.normPower (globalField D k K' θ g) t * Θ

/-- With the norm compatibility of the transfer, the restriction of the reciprocity character of
`α · ‖·‖^t` times the reciprocity character of `Θ` is the reciprocity character of
`(α ∘ N) · ‖·‖^t · Θ`. -/
theorem comp_restrictionInclusion_mul_eq (g : Generator F (Correspondence.baseExtension F))
    (α : HeckeCharacter k) (t : ℂ) (Θ : HeckeCharacter (globalField D k K' θ g)) :
    (continuousReciprocityCharacter c k K' (α * HeckeCharacter.normPower k t)).comp
        (restrictionInclusion c k K' (globalField D k K' θ g) h) *
      continuousReciprocityCharacter c (globalField D k K' θ g) K' Θ =
    continuousReciprocityCharacter c (globalField D k K' θ g) K'
      (generatorHecke D k K' θ g α t Θ) := by
  rw [continuousReciprocityCharacter_comp_restrictionInclusion (globalField D k K' θ g) h
    (transferNormCompatibilityStatement c k (globalField D k K' θ g) K' h), ←
    continuousReciprocityCharacter_mul]
  congr 1
  change HeckeCharacter.normComp (α * HeckeCharacter.normPower k t) * Θ = _
  unfold generatorHecke
  rw [← normComp_normPower (k := k) (M := globalField D k K' θ g) t]
  rfl

/-- **The global relation in Hecke form.** If `Θ₁ g`, `Θ₂ g` are Hecke characters whose
reciprocity characters are the inflated characters of `θ₁ g`, `θ₂ g`, then for every Hecke
character `α` of `k` the characters `(α ∘ N) · ‖·‖^{t_i g} · Θ_i g` satisfy the relation
`Σ_g z(g) Ind ([·] - [·]) = 0`, indexed by any enumeration of the support of `z`. -/
theorem globalRelation_generatorHecke {n : ℕ} (gs : Fin n ≃ z.support) (α : HeckeCharacter k)
    (Θ₁ Θ₂ : ∀ g, HeckeCharacter (globalField D k K' θ g))
    (hΘ₁ : ∀ g, continuousReciprocityCharacter c (globalField D k K' θ g) K' (Θ₁ g) =
      globalCharacter D c k K' θ h g (D.θ₁ g))
    (hΘ₂ : ∀ g, continuousReciprocityCharacter c (globalField D k K' θ g) K' (Θ₂ g) =
      globalCharacter D c k K' θ h g (D.θ₂ g)) :
    ∑ i : Fin n, z (gs i).1 • ExactGrothendieckGroup.continuousInduceAlong
        (restrictionInclusion c k K' (globalField D k K' θ (gs i).1) h)
        (isOpenEmbedding_restrictionInclusion c k K' (globalField D k K' θ (gs i).1) h)
        (ExactGrothendieckGroup.characterClass.{0, uV}
            (continuousReciprocityCharacter c (globalField D k K' θ (gs i).1) K'
              (generatorHecke D k K' θ (gs i).1 α (D.t₁ (gs i).1) (Θ₁ (gs i).1))) -
          ExactGrothendieckGroup.characterClass.{0, uV}
            (continuousReciprocityCharacter c (globalField D k K' θ (gs i).1) K'
              (generatorHecke D k K' θ (gs i).1 α (D.t₂ (gs i).1) (Θ₂ (gs i).1)))) =
      (0 : ContinuousVirtual.{0, uV} c k K') := by
  classical
  let Ω : ℂ → (RelativeWeilGroup c k K' →ₜ* ℂˣ) := fun τ =>
    continuousReciprocityCharacter c k K' (α * HeckeCharacter.normPower k τ)
  let f : Generator F (Correspondence.baseExtension F) → ContinuousVirtual.{0, uV} c k K' :=
    fun g => z g • ExactGrothendieckGroup.continuousInduceAlong
      (restrictionInclusion c k K' (globalField D k K' θ g) h)
      (isOpenEmbedding_restrictionInclusion c k K' (globalField D k K' θ g) h)
      (ExactGrothendieckGroup.characterClass.{0, uV}
          (continuousReciprocityCharacter c (globalField D k K' θ g) K'
            (generatorHecke D k K' θ g α (D.t₁ g) (Θ₁ g))) -
        ExactGrothendieckGroup.characterClass.{0, uV}
          (continuousReciprocityCharacter c (globalField D k K' θ g) K'
            (generatorHecke D k K' θ g α (D.t₂ g) (Θ₂ g))))
  have hsum : ∑ i : Fin n, f (gs i).1 = ∑ g ∈ z.support, f g :=
    (Fintype.sum_equiv gs _ (fun j : z.support => f j.1) fun _ => rfl).trans
      (Finset.sum_coe_sort z.support f)
  refine hsum.trans (Eq.trans ?_ (globalRelation.{uF, uV, 0} D c k K' θ h Ω))
  refine Finset.sum_congr rfl fun g _ => ?_
  have e₁ : (Ω (D.t₁ g)).comp (restrictionInclusion c k K' (globalField D k K' θ g) h) *
      globalCharacter D c k K' θ h g (D.θ₁ g) =
      continuousReciprocityCharacter c (globalField D k K' θ g) K'
        (generatorHecke D k K' θ g α (D.t₁ g) (Θ₁ g)) := by
    rw [← hΘ₁ g]
    exact comp_restrictionInclusion_mul_eq D c k K' θ h g α (D.t₁ g) (Θ₁ g)
  have e₂ : (Ω (D.t₂ g)).comp (restrictionInclusion c k K' (globalField D k K' θ g) h) *
      globalCharacter D c k K' θ h g (D.θ₂ g) =
      continuousReciprocityCharacter c (globalField D k K' θ g) K'
        (generatorHecke D k K' θ g α (D.t₂ g) (Θ₂ g)) := by
    rw [← hΘ₂ g]
    exact comp_restrictionInclusion_mul_eq D c k K' θ h g α (D.t₂ g) (Θ₂ g)
  change f g = _
  simp only [f]
  rw [e₁, e₂]

/-- The inflated character of a generator is trivial on the idele classes of `K'`. -/
theorem globalCharacter_inclusion (g : Generator F (Correspondence.baseExtension F))
    (χ : @galoisImage p _ F D.K D.normal g.extension →* ℂˣ)
    (a : NumberField.IdeleClassGroup (𝓞 K') K') :
    globalCharacter D c k K' θ h g χ (inclusion c (globalField D k K' θ g) K' a) = 1 := by
  have h1 : projection c k K' (restrictionInclusion c k K' (globalField D k K' θ g) h
      (inclusion c (globalField D k K' θ g) K' a)) = 1 := by
    rw [restrictionInclusion_inclusion]
    have : inclusion c k K' a ∈ (projection c k K').ker := exact c k K' ▸ ⟨a, rfl⟩
    exact this
  change globalSubgroupCharacter D k K' θ g χ
    ((projection c k K').subgroupComap (globalSubgroup D k K' θ g) _) = 1
  rw [← map_one (globalSubgroupCharacter D k K' θ g χ)]
  congr 1

/-- The value of the inflated character of a generator: `χ` at the image under `θ` of the Galois
projection of `x`. -/
theorem globalCharacter_apply (g : Generator F (Correspondence.baseExtension F))
    (χ : @galoisImage p _ F D.K D.normal g.extension →* ℂˣ)
    (x : RelativeWeilGroup c (globalField D k K' θ g) K') :
    ∃ hx : θ ((projection c (globalField D k K' θ g) K' x).restrictScalars k) ∈
        @galoisImage p _ F D.K D.normal g.extension,
      globalCharacter D c k K' θ h g χ x = χ ⟨_, hx⟩ := by
  have hp := projection_restrictionInclusion c k K' (globalField D k K' θ g) h x
  have hmem : restrictionInclusion c k K' (globalField D k K' θ g) h x ∈
      galoisPreimage c k K' (globalSubgroup D k K' θ g) := by
    rw [← range_restrictionInclusion_fixedField c k K' h (globalSubgroup D k K' θ g)]
    exact ⟨x, rfl⟩
  have hx : θ ((projection c (globalField D k K' θ g) K' x).restrictScalars k) ∈
      @galoisImage p _ F D.K D.normal g.extension := by
    rw [← hp]
    exact hmem
  refine ⟨hx, ?_⟩
  change χ ⟨θ (projection c k K' (restrictionInclusion c k K' (globalField D k K' θ g) h x)),
    _⟩ = _
  exact congrArg χ (Subtype.ext (congrArg θ hp))

/-- For a totally real `K'`, if `α` is trivial at infinity and the reciprocity character of `Θ` is
an inflated character, then `generatorHecke D k K' θ g α t Θ` has the archimedean components of
`‖·‖^t`. -/
theorem generatorHecke_infiniteComponent [NumberField.IsTotallyReal K']
    (g : Generator F (Correspondence.baseExtension F)) (α : HeckeCharacter k)
    (hα : α.HasPrescribedInfinityComponent 1) (t : ℂ)
    (Θ : HeckeCharacter (globalField D k K' θ g))
    (χ : @galoisImage p _ F D.K D.normal g.extension →* ℂˣ)
    (hΘ : continuousReciprocityCharacter c (globalField D k K' θ g) K' Θ =
      globalCharacter D c k K' θ h g χ)
    (v : NumberField.InfinitePlace (globalField D k K' θ g)) :
    (generatorHecke D k K' θ g α t Θ).infiniteComponent v =
      (HeckeCharacter.normPower (globalField D k K' θ g) t).infiniteComponent v := by
  have : IsGalois (globalField D k K' θ g) K' :=
    IsGalois.tower_top_of_isGalois k (globalField D k K' θ g) K'
  unfold generatorHecke
  rw [HeckeCharacter.infiniteComponent_mul, HeckeCharacter.infiniteComponent_mul,
    HeckeCharacter.normComp_infiniteComponent_eq_one α hα v,
    infiniteComponent_eq_one_of_isTotallyReal (c := c) Θ (fun a => by
      rw [hΘ]
      exact globalCharacter_inclusion D c k K' θ h g χ a) v]
  refine DFunLike.ext _ _ fun x => ?_
  change (1 : ℂˣ) * (HeckeCharacter.normPower (globalField D k K' θ g) t).infiniteComponent v x *
    1 = _
  rw [one_mul, mul_one]

end Langlands.LocalFactor.NonabelianBrauer
