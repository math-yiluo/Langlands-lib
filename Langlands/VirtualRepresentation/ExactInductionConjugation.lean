import Langlands.Automorphic.InducedReciprocityBasic
import Langlands.Global.Factors.RelativeWeilBrauer

/-!
# Induction along conjugate embeddings

If `ψ h = g * φ h * g⁻¹` for all `h`, then induction along `ψ` and along `φ` give
equivalent representations: an equivariant function `f` for the range of `ψ` is sent
to `x ↦ f (g * x)`, equivariant for the range of `φ`.

Consequently, if conjugation by `g` carries the range of an open embedding `φ` onto a
subgroup `S`, then inducing a character `θ` of `S` from `S` agrees with inducing
`θ ∘ (g φ g⁻¹)` along `φ`.
-/

noncomputable section

set_option autoImplicit false

universe uK uG uH uV

namespace Langlands.FiniteRepresentation

open InductionAlong

variable {K : Type uK} [Field K] {G : Type uG} [Group G] {H : Type uH} [Group H]

/-- Induction along two conjugate injective homomorphisms `ψ = g φ g⁻¹`: left
translation by `g` identifies the two spaces of equivariant functions. -/
def induceAlongConjEquiv (φ ψ : H →* G) (hφ : Function.Injective φ)
    (hψ : Function.Injective ψ) [φ.range.FiniteIndex] [ψ.range.FiniteIndex] (g : G)
    (hg : ∀ h, ψ h = g * φ h * g⁻¹) (A : FiniteRepresentation.{uK, uH, uV} K H) :
    Equiv (induceAlong ψ hψ A) (induceAlong φ hφ A) where
  toFun f := ⟨fun x => f.val (g * x), by
    rintro ⟨_, h, rfl⟩ x
    have key := f.property ⟨ψ h, h, rfl⟩ (g * x)
    have hx : ψ h * (g * x) = g * (φ h * x) := by rw [hg]; group
    change f.val (g * (φ h * x)) = A.representation (rangeInverse φ hφ ⟨φ h, h, rfl⟩)
      (f.val (g * x))
    rw [rangeInverse_apply, ← hx]
    refine key.trans ?_
    change A.representation (rangeInverse ψ hψ ⟨ψ h, h, rfl⟩) _ = _
    rw [rangeInverse_apply]⟩
  invFun f := ⟨fun x => f.val (g⁻¹ * x), by
    rintro ⟨_, h, rfl⟩ x
    have key := f.property ⟨φ h, h, rfl⟩ (g⁻¹ * x)
    have hx : φ h * (g⁻¹ * x) = g⁻¹ * (ψ h * x) := by rw [hg]; group
    change f.val (g⁻¹ * (ψ h * x)) = A.representation (rangeInverse ψ hψ ⟨ψ h, h, rfl⟩)
      (f.val (g⁻¹ * x))
    rw [rangeInverse_apply, ← hx]
    refine key.trans ?_
    change A.representation (rangeInverse φ hφ ⟨φ h, h, rfl⟩) _ = _
    rw [rangeInverse_apply]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := Subtype.ext (funext fun x => by
    change f.val (g * (g⁻¹ * x)) = f.val x
    rw [mul_inv_cancel_left])
  right_inv f := Subtype.ext (funext fun x => by
    change f.val (g⁻¹ * (g * x)) = f.val x
    rw [inv_mul_cancel_left])
  isIntertwining' y := by
    ext f
    refine Subtype.ext (funext fun x => ?_)
    change f.val (g * x * y) = f.val (g * (x * y))
    rw [mul_assoc]

end Langlands.FiniteRepresentation

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

variable {G : Type uG} {H : Type uH} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G]

/-- Continuous induction along conjugate open embeddings `ψ = g φ g⁻¹` agrees on
continuous exact virtual groups. -/
theorem continuousInduceAlong_eq_of_conj (φ ψ : H →ₜ* G) (hφ : Topology.IsOpenEmbedding φ)
    (hψ : Topology.IsOpenEmbedding ψ) [φ.toMonoidHom.range.FiniteIndex]
    [ψ.toMonoidHom.range.FiniteIndex] (g : G) (hg : ∀ h, ψ h = g * φ h * g⁻¹) :
    continuousInduceAlong.{uG, uH, uV} ψ hψ = continuousInduceAlong.{uG, uH, uV} φ hφ := by
  apply hom_ext _
  intro c
  induction c using Quotient.inductionOn with
  | h A =>
    change continuousInduceAlong ψ hψ (ofRepresentation _ A) =
      continuousInduceAlong φ hφ (ofRepresentation _ A)
    obtain ⟨A, hA⟩ := A
    rw [continuousInduceAlong_ofRepresentationWithProof,
      continuousInduceAlong_ofRepresentationWithProof]
    exact ofRepresentation_eq_of_equiv _
      (FiniteRepresentation.induceAlongConjEquiv φ.toMonoidHom ψ.toMonoidHom hφ.injective
        hψ.injective g hg A)

/-- The conjugate `h ↦ g * φ h * g⁻¹` of a continuous homomorphism. -/
def conjAlong (φ : H →ₜ* G) (g : G) : H →ₜ* G where
  toMonoidHom := (MulAut.conj g).toMonoidHom.comp φ.toMonoidHom
  continuous_toFun := (continuous_const.mul φ.continuous).mul continuous_const

@[simp] theorem conjAlong_apply (φ : H →ₜ* G) (g : G) (h : H) :
    conjAlong φ g h = g * φ h * g⁻¹ := rfl

theorem isOpenEmbedding_conjAlong (φ : H →ₜ* G) (hφ : Topology.IsOpenEmbedding φ) (g : G) :
    Topology.IsOpenEmbedding (conjAlong φ g) :=
  ((Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)).isOpenEmbedding.comp hφ

/-- If conjugation by `g` carries the range of `φ` exactly onto `S`, then `S` is the
range of the conjugate homomorphism. -/
theorem range_conjAlong (φ : H →ₜ* G) (S : Subgroup G) (g : G)
    (hg : ∀ y, y ∈ φ.toMonoidHom.range ↔ g * y * g⁻¹ ∈ S) :
    (conjAlong φ g).toMonoidHom.range = S := by
  ext y
  constructor
  · rintro ⟨h, rfl⟩
    exact (hg _).mp ⟨h, rfl⟩
  · intro hy
    obtain ⟨h, hh⟩ := (hg (g⁻¹ * y * g)).mpr (by group; exact hy)
    refine ⟨h, ?_⟩
    change g * φ.toMonoidHom h * g⁻¹ = y
    rw [hh]
    group

/-- The conjugate `h ↦ g * φ h * g⁻¹`, corestricted to a subgroup `S` onto which
conjugation by `g` carries the range of `φ`. -/
def conjCodRestrict (φ : H →ₜ* G) (S : Subgroup G) (g : G)
    (hg : ∀ y, y ∈ φ.toMonoidHom.range ↔ g * y * g⁻¹ ∈ S) : H →ₜ* S :=
  codRestrictOfRange (conjAlong φ g) S (range_conjAlong φ S g hg)

@[simp] theorem conjCodRestrict_apply (φ : H →ₜ* G) (S : Subgroup G) (g : G)
    (hg : ∀ y, y ∈ φ.toMonoidHom.range ↔ g * y * g⁻¹ ∈ S) (h : H) :
    (conjCodRestrict φ S g hg h : G) = g * φ h * g⁻¹ := rfl

/-- If conjugation by `g` carries the range of an open embedding `φ` onto `S`, then
inducing a character `θ` from `S` agrees with inducing `θ ∘ (g φ g⁻¹)` along `φ`. -/
theorem continuousInduce_characterClass_eq_along_conj (φ : H →ₜ* G)
    (hφ : Topology.IsOpenEmbedding φ) [φ.toMonoidHom.range.FiniteIndex]
    (S : Subgroup G) [S.FiniteIndex] (hSo : IsOpen (S : Set G)) (g : G)
    (hg : ∀ y, y ∈ φ.toMonoidHom.range ↔ g * y * g⁻¹ ∈ S) (θ : S →ₜ* ℂˣ) :
    continuousInduce S hSo (characterClass.{uG, uV} θ) =
      continuousInduceAlong φ hφ
        (characterClass.{uH, uV} (θ.comp (conjCodRestrict φ S g hg))) := by
  have hψ := isOpenEmbedding_conjAlong φ hφ g
  have hS := range_conjAlong φ S g hg
  have : (conjAlong φ g).toMonoidHom.range.FiniteIndex := by
    rw [hS]
    infer_instance
  rw [continuousInduce_characterClass_eq_along (conjAlong φ g) hψ S hSo hS θ,
    continuousInduceAlong_eq_of_conj φ (conjAlong φ g) hφ hψ g (fun _ => rfl)]
  rfl

end Langlands.VirtualRepresentation.ExactGrothendieckGroup
