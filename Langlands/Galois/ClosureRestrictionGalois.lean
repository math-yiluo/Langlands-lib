import Langlands.Galois.HeckeInduction.RestrictionIndex
import Langlands.Galois.ClosureRestriction

/-!
# Galois theory of restriction along closure embeddings

For a field extension `E/K` and a `K`-algebra embedding `ι` of algebraic closures,
`restrictionAlongClosure ι g` is the unique automorphism `h` of `K̄` with `ι ∘ h = g ∘ ι`.
This gives the composition and conjugation rules of these restrictions. When `E/K` is
algebraic, `ι` is bijective and the image of the restriction is the group fixing the
transported copy of `E`.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.GaloisRepresentation

section Basic

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

/-- The restriction is characterized by its intertwining property. -/
theorem eq_restrictionAlongClosure (ι : AlgebraicClosure K →ₐ[K] AlgebraicClosure E)
    (g : Field.absoluteGaloisGroup E) (h : Field.absoluteGaloisGroup K)
    (hh : ∀ x, ι (AlgEquiv.toRingEquiv h x) = AlgEquiv.toRingEquiv g (ι x)) :
    h = restrictionAlongClosure ι g := by
  apply AlgEquiv.ext
  intro x
  apply ι.injective
  exact (hh x).trans (restrictionAlongClosure_commutes ι g x).symm

/-- Restricting along `ι ∘ c` conjugates the restriction along `ι` by `c`. -/
theorem restrictionAlongClosure_comp_aut (ι : AlgebraicClosure K →ₐ[K] AlgebraicClosure E)
    (c : Field.absoluteGaloisGroup K) (g : Field.absoluteGaloisGroup E) :
    restrictionAlongClosure (ι.comp (AlgEquiv.toAlgHom c)) g =
      c⁻¹ * restrictionAlongClosure ι g * c := by
  symm
  apply eq_restrictionAlongClosure
  intro x
  change ι (AlgEquiv.toRingEquiv c (AlgEquiv.toRingEquiv c⁻¹
      (AlgEquiv.toRingEquiv (restrictionAlongClosure ι g) (AlgEquiv.toRingEquiv c x)))) =
    AlgEquiv.toRingEquiv g (ι (AlgEquiv.toRingEquiv c x))
  rw [← restrictionAlongClosure_commutes ι g]
  congr 1
  change AlgEquiv.toRingEquiv (c * c⁻¹) _ = _
  rw [mul_inv_cancel]
  rfl

/-- Two closure embeddings that agree pointwise give the same restriction. -/
theorem restrictionAlongClosure_congr {ι κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure E}
    (h : ∀ x, ι x = κ x) (g : Field.absoluteGaloisGroup E) :
    restrictionAlongClosure ι g = restrictionAlongClosure κ g := by
  have : ι = κ := AlgHom.ext h
  rw [this]

/-- The ring isomorphism underlying a closure embedding of an algebraic extension. -/
def closureEmbeddingRingEquiv [Algebra.IsAlgebraic K E]
    (ι : AlgebraicClosure K →ₐ[K] AlgebraicClosure E) :
    AlgebraicClosure K ≃+* AlgebraicClosure E :=
  (closureEmbeddingEquiv ι).toRingEquiv

@[simp]
theorem closureEmbeddingRingEquiv_apply [Algebra.IsAlgebraic K E]
    (ι : AlgebraicClosure K →ₐ[K] AlgebraicClosure E) (x : AlgebraicClosure K) :
    closureEmbeddingRingEquiv ι x = ι x := rfl

/-- For an algebraic extension, the image of the restriction along `ι` is the subgroup fixing
every element that `ι` sends into `E`. -/
theorem mem_range_restrictionAlongClosure_iff_fixes_preimages [Algebra.IsAlgebraic K E]
    (ι : AlgebraicClosure K →ₐ[K] AlgebraicClosure E) (g : Field.absoluteGaloisGroup K) :
    g ∈ (restrictionAlongClosure ι).toMonoidHom.range ↔
      ∀ (x : E) (y : AlgebraicClosure K), ι y = algebraMap E (AlgebraicClosure E) x →
        AlgEquiv.toRingEquiv g y = y := by
  let e := closureEmbeddingRingEquiv ι
  constructor
  · rintro ⟨σ, rfl⟩ x y hy
    apply ι.injective
    change ι (AlgEquiv.toRingEquiv (restrictionAlongClosure ι σ) y) = ι y
    rw [restrictionAlongClosure_commutes, hy]
    exact σ.commutes x
  · intro hg
    let t : AlgebraicClosure E ≃+* AlgebraicClosure E :=
      (e.symm.trans (AlgEquiv.toRingEquiv g)).trans e
    have ht (x : E) : t (algebraMap E (AlgebraicClosure E) x) =
        algebraMap E (AlgebraicClosure E) x := by
      have h1 : ι (e.symm (algebraMap E (AlgebraicClosure E) x)) =
          algebraMap E (AlgebraicClosure E) x := e.apply_symm_apply _
      change e (AlgEquiv.toRingEquiv g (e.symm (algebraMap E (AlgebraicClosure E) x))) = _
      rw [hg x _ h1]
      exact e.apply_symm_apply _
    let σ : Field.absoluteGaloisGroup E := AlgEquiv.ofRingEquiv (f := t) ht
    refine ⟨σ, ?_⟩
    symm
    apply eq_restrictionAlongClosure
    intro y
    change e (AlgEquiv.toRingEquiv g y) = e (AlgEquiv.toRingEquiv g (e.symm (e y)))
    rw [e.symm_apply_apply]

end Basic

section Composition

variable {K E F : Type*} [Field K] [Field E] [Field F] [Algebra K E] [Algebra E F] [Algebra K F]

/-- Restriction along a composite of closure embeddings is the composite of restrictions. -/
theorem restrictionAlongClosure_comp
    (ι₁ : AlgebraicClosure K →ₐ[K] AlgebraicClosure E)
    (ι₂ : AlgebraicClosure E →ₐ[E] AlgebraicClosure F)
    (ι : AlgebraicClosure K →ₐ[K] AlgebraicClosure F) (hι : ∀ x, ι x = ι₂ (ι₁ x))
    (g : Field.absoluteGaloisGroup F) :
    restrictionAlongClosure ι g =
      restrictionAlongClosure ι₁ (restrictionAlongClosure ι₂ g) := by
  symm
  apply eq_restrictionAlongClosure
  intro x
  rw [hι, hι, restrictionAlongClosure_commutes, restrictionAlongClosure_commutes]

end Composition

section RingHom

variable {K E : Type*} [Field K] [Field E]

/-- Restriction along a closure embedding compatible with a field homomorphism `f`, for the
algebra structure induced by `f`. -/
def restrictionAlongClosureHom (f : K →+* E) (ι : ClosureEmbedding f) :
    Field.absoluteGaloisGroup E →ₜ* Field.absoluteGaloisGroup K := by
  letI : Algebra K E := f.toAlgebra
  exact restrictionAlongClosure ι

/-- The restriction compatible with `f` is characterized by its intertwining property. -/
theorem eq_restrictionAlongClosureHom (f : K →+* E) (ι : ClosureEmbedding f)
    (g : Field.absoluteGaloisGroup E) (h : Field.absoluteGaloisGroup K)
    (hh : letI : Algebra K E := f.toAlgebra
      ∀ x, ι (AlgEquiv.toRingEquiv h x) = AlgEquiv.toRingEquiv g (ι x)) :
    h = restrictionAlongClosureHom f ι g := by
  letI : Algebra K E := f.toAlgebra
  exact eq_restrictionAlongClosure ι g h hh

/-- A closure embedding compatible with `f`, from a ring homomorphism of algebraic closures. -/
def closureEmbeddingOfRingHom (f : K →+* E)
    (φ : AlgebraicClosure K →+* AlgebraicClosure E)
    (hφ : ∀ a, φ (algebraMap K (AlgebraicClosure K) a) = algebraMap E (AlgebraicClosure E) (f a)) :
    ClosureEmbedding f := by
  letI : Algebra K E := f.toAlgebra
  exact { toRingHom := φ
          commutes' := fun a => (hφ a).trans
            (IsScalarTower.algebraMap_apply K E (AlgebraicClosure E) a).symm }

/-- The restriction along `closureEmbeddingOfRingHom` is characterized by the ring map. -/
theorem eq_restrictionAlongClosureHom_ofRingHom (f : K →+* E)
    (φ : AlgebraicClosure K →+* AlgebraicClosure E)
    (hφ : ∀ a, φ (algebraMap K (AlgebraicClosure K) a) = algebraMap E (AlgebraicClosure E) (f a))
    (g : Field.absoluteGaloisGroup E) (h : Field.absoluteGaloisGroup K)
    (hh : ∀ x, φ (AlgEquiv.toRingEquiv h x) = AlgEquiv.toRingEquiv g (φ x)) :
    h = restrictionAlongClosureHom f (closureEmbeddingOfRingHom f φ hφ) g := by
  letI : Algebra K E := f.toAlgebra
  exact eq_restrictionAlongClosure _ g h hh

end RingHom

end Langlands.GaloisRepresentation
