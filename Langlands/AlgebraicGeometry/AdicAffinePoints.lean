import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.RingTheory.AdicCompletion.RingHom

/-! # Affine points over an adically complete ring -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AdicAffinePoints

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The spectrum of the quotient by `I^(n+1)`. -/
abbrev quotientSpec (n : ℕ) : Scheme.{u} :=
  Spec (CommRingCat.of (A ⧸ I ^ (n + 1)))

/-- The inclusion of the `n`th adic thickening. -/
def quotientMap (n : ℕ) : quotientSpec I n ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))

/-- The inclusion of one adic thickening in the next. -/
def transition (n : ℕ) : quotientSpec I n ⟶ quotientSpec I (n + 1) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPow I (n + 1).le_succ))

@[simp]
lemma transition_quotientMap (n : ℕ) :
    transition I n ≫ quotientMap I (n + 1) = quotientMap I n := by
  unfold transition quotientMap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1

/-- Reduction to an adic thickening as a morphism over `Spec A`. -/
def reduction (n : ℕ) :
    Over.mk (quotientMap I n) ⟶ Over.mk (𝟙 (Spec (CommRingCat.of A))) :=
  Over.homMk (quotientMap I n)

/-- Successive adic thickenings as a morphism over `Spec A`. -/
def transitionOver (n : ℕ) :
    Over.mk (quotientMap I n) ⟶ Over.mk (quotientMap I (n + 1)) :=
  Over.homMk (transition I n) (transition_quotientMap I n)

@[simp]
lemma transitionOver_reduction (n : ℕ) :
    transitionOver I n ≫ reduction I (n + 1) = reduction I n := by
  apply Over.OverMorphism.ext
  exact transition_quotientMap I n

lemma strictMono_add_one : StrictMono (fun n : ℕ ↦ n + 1) :=
  fun _ _ h ↦ Nat.add_lt_add_right h 1

/-- Morphisms from `Spec A` to an affine scheme are determined by their reductions. -/
theorem adic_ext [IsHausdorff I A] {X : Scheme.{u}} [IsAffine X]
    {g₁ g₂ : Spec (CommRingCat.of A) ⟶ X}
    (h : ∀ n : ℕ, quotientMap I n ≫ g₁ = quotientMap I n ≫ g₂) :
    g₁ = g₂ := by
  rw [← cancel_mono X.isoSpec.hom]
  suffices Spec.preimage (g₁ ≫ X.isoSpec.hom) =
      Spec.preimage (g₂ ≫ X.isoSpec.hom) by
    simpa using congrArg Spec.map this
  apply CommRingCat.hom_ext
  apply DFunLike.coe_injective
  refine IsHausdorff.StrictMono.funext' I strictMono_add_one fun n x ↦ ?_
  have hn : quotientMap I n ≫ Spec.map (Spec.preimage (g₁ ≫ X.isoSpec.hom)) =
      quotientMap I n ≫ Spec.map (Spec.preimage (g₂ ≫ X.isoSpec.hom)) := by
    simpa only [Spec.map_preimage, ← Category.assoc] using
      congrArg (fun f ↦ f ≫ X.isoSpec.hom) (h n)
  unfold quotientMap at hn
  rw [← Spec.map_comp, ← Spec.map_comp] at hn
  exact congrArg (fun f ↦ f.hom x) (Spec.map_injective hn)

/-- Compatible points of an affine scheme over the adic quotients come from a point over
the complete ring. -/
theorem exists_adic_lift [IsAdicComplete I A] {X : Scheme.{u}} [IsAffine X]
    (f : ∀ n : ℕ, quotientSpec I n ⟶ X)
    (hf : ∀ n : ℕ, transition I n ≫ f (n + 1) = f n) :
    ∃ g : Spec (CommRingCat.of A) ⟶ X,
      ∀ n : ℕ, quotientMap I n ≫ g = f n := by
  let ψ : ∀ n : ℕ, Γ(X, ⊤) →+* A ⧸ I ^ (n + 1) :=
    fun n ↦ (Spec.preimage (f n ≫ X.isoSpec.hom)).hom
  have hψ' : ∀ n, Spec.map (CommRingCat.ofHom (ψ n)) = f n ≫ X.isoSpec.hom :=
    fun n ↦ by
      change Spec.map (Spec.preimage (f n ≫ X.isoSpec.hom)) = _
      exact Spec.map_preimage _
  have hψ : ∀ {n}, (Ideal.Quotient.factorPow I
      (strictMono_add_one.monotone n.le_succ)).comp (ψ (n + 1)) = ψ n := by
    intro n
    have hn : Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.factorPow I (strictMono_add_one.monotone n.le_succ)).comp
          (ψ (n + 1)))) = Spec.map (CommRingCat.ofHom (ψ n)) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, hψ', hψ']
      change transition I n ≫ (f (n + 1) ≫ X.isoSpec.hom) = _
      rw [← Category.assoc, hf]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hn)
  refine ⟨Spec.map (CommRingCat.ofHom
    (IsAdicComplete.StrictMono.liftRingHom I strictMono_add_one ψ hψ)) ≫ X.isoSpec.inv,
    fun n ↦ ?_⟩
  have key := IsAdicComplete.StrictMono.mk_comp_liftRingHom I strictMono_add_one ψ hψ
    (n := n)
  beta_reduce at key
  rw [← Category.assoc, quotientMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    key, hψ', Category.assoc,
    X.isoSpec.hom_inv_id, Category.comp_id]

/-- The lift of a compatible family of affine points is unique. -/
theorem existsUnique_adic_lift [IsAdicComplete I A] {X : Scheme.{u}} [IsAffine X]
    (f : ∀ n : ℕ, quotientSpec I n ⟶ X)
    (hf : ∀ n : ℕ, transition I n ≫ f (n + 1) = f n) :
    ∃! g : Spec (CommRingCat.of A) ⟶ X,
      ∀ n : ℕ, quotientMap I n ≫ g = f n := by
  obtain ⟨g, hg⟩ := exists_adic_lift I f hf
  exact ⟨g, hg, fun g' hg' ↦ adic_ext I (fun n ↦ (hg' n).trans (hg n).symm)⟩

/-- Equality of sections of an affine `Spec A`-scheme can be checked on adic quotients. -/
theorem over_adic_ext [IsHausdorff I A] {X : Over (Spec (CommRingCat.of A))}
    [IsAffine X.left]
    {g₁ g₂ : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ X}
    (h : ∀ n : ℕ, reduction I n ≫ g₁ = reduction I n ≫ g₂) :
    g₁ = g₂ := by
  apply Over.OverMorphism.ext
  exact adic_ext I (fun n ↦ congrArg CommaMorphism.left (h n))

/-- A compatible family of sections of an affine `Spec A`-scheme algebraizes uniquely. -/
theorem existsUnique_over_adic_lift [IsAdicComplete I A]
    {X : Over (Spec (CommRingCat.of A))} [IsAffine X.left]
    (f : ∀ n : ℕ, Over.mk (quotientMap I n) ⟶ X)
    (hf : ∀ n : ℕ, transitionOver I n ≫ f (n + 1) = f n) :
    ∃! g : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ X,
      ∀ n : ℕ, reduction I n ≫ g = f n := by
  obtain ⟨g, hg⟩ := exists_adic_lift I (fun n ↦ (f n).left)
    (fun n ↦ congrArg CommaMorphism.left (hf n))
  have hgS : g ≫ X.hom = 𝟙 _ := by
    apply adic_ext I
    intro n
    rw [← Category.assoc, hg n, Over.w (f n), Category.comp_id]
    rfl
  refine ⟨Over.homMk g hgS, ?_, ?_⟩
  · intro n
    exact Over.OverMorphism.ext (hg n)
  · intro g' hg'
    apply over_adic_ext I
    intro n
    exact (hg' n).trans (Over.OverMorphism.ext (hg n)).symm

end Langlands.AlgebraicGeometry.AdicAffinePoints
