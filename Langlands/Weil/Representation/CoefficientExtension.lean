import Langlands.Weil.Representation.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Coefficient extension and descent for finite representations -/

noncomputable section

open scoped TensorProduct MonoidAlgebra

universe uk ue ug uv uw

namespace Langlands.FiniteRepresentation

variable {k : Type uk} [Field k] (E : Type ue) [Field E] [Algebra k E]
  {G : Type ug} [Monoid G]

/-- Extend the action to the actual scalar-extension tensor product. -/
abbrev extendCoefficients (A : FiniteRepresentation.{uk, ug, uv} k G) :
    FiniteRepresentation.{ue, ug, max ue uv} E G :=
  of ((Module.End.baseChangeHom k E A).toMonoidHom.comp A.representation)

@[simp] theorem extendCoefficients_apply_tmul
    (A : FiniteRepresentation.{uk, ug, uv} k G) (g : G) (a : E) (v : A) :
    (A.extendCoefficients E).representation g (a ⊗ₜ[k] v) =
      a ⊗ₜ[k] A.representation g v := rfl

@[simp] theorem rank_extendCoefficients (A : FiniteRepresentation.{uk, ug, uv} k G) :
    (A.extendCoefficients E).rank = A.rank :=
  Module.finrank_baseChange

/-- Irreducibility after coefficient extension implies irreducibility over the base field. -/
theorem irreducible_of_extendCoefficients (A : FiniteRepresentation.{uk, ug, uv} k G)
    (hA : Representation.IsIrreducible (A.extendCoefficients E).representation) :
    Representation.IsIrreducible A.representation := by
  let := hA
  let extend (S : Subrepresentation A.representation) :
      Subrepresentation (A.extendCoefficients E).representation :=
    ⟨S.toSubmodule.baseChange E, by
      intro g x hx
      obtain ⟨z, rfl⟩ := hx
      refine ⟨(S.toRepresentation g).baseChange E z, ?_⟩
      change S.toSubmodule.subtype.baseChange E ((S.toRepresentation g).baseChange E z) =
        (A.representation g).baseChange E (S.toSubmodule.subtype.baseChange E z)
      induction z using TensorProduct.inductionOn with
      | tmul a s => rfl
      | add x y hx hy => simp only [map_add, hx, hy]⟩
  have hinj : Function.Injective extend := fun S T h =>
    Subrepresentation.toSubmodule_injective <|
      Submodule.baseChange_injective (congrArg Subrepresentation.toSubmodule h)
  have hbot : extend ⊥ = ⊥ :=
    Subrepresentation.toSubmodule_injective (Submodule.baseChange_bot E)
  have htop : extend ⊤ = ⊤ :=
    Subrepresentation.toSubmodule_injective (Submodule.baseChange_top E)
  have : Nontrivial (Subrepresentation A.representation) :=
    ⟨⊥, ⊤, fun h => bot_ne_top (hbot.symm.trans ((congrArg extend h).trans htop))⟩
  refine ⟨?_⟩
  intro S
  rcases eq_bot_or_eq_top (extend S) with h | h
  · exact Or.inl (hinj (h.trans hbot.symm))
  · exact Or.inr (hinj (h.trans htop.symm))

private def coefficientProjection {W : Type uw} [AddCommGroup W] [Module k W]
    (φ : E →ₗ[k] k) : E ⊗[k] W →ₗ[k] W :=
  (TensorProduct.lid k W).toLinearMap ∘ₗ TensorProduct.map φ LinearMap.id

@[simp] private theorem coefficientProjection_tmul
    {W : Type uw} [AddCommGroup W] [Module k W]
    (φ : E →ₗ[k] k) (a : E) (w : W) :
    coefficientProjection E φ (a ⊗ₜ[k] w) = φ a • w := rfl

private theorem coefficientProjection_comp
    {W : Type uw} [AddCommGroup W] [Module k W]
    (φ : E →ₗ[k] k) (f : Module.End k W) (z : E ⊗[k] W) :
    coefficientProjection E φ (f.baseChange E z) = f (coefficientProjection E φ z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a w => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- An equivalence after extension descends if the source is irreducible over the
original field. A nonzero coefficient of the extended intertwiner gives an
injective base-field intertwiner, and the two original dimensions agree. -/
theorem nonempty_equiv_of_extendCoefficients
    (A : FiniteRepresentation.{uk, ug, uv} k G) (B : FiniteRepresentation.{uk, ug, uw} k G)
    (hA : Representation.IsIrreducible A.representation)
    (h : Nonempty (Equiv (A.extendCoefficients E) (B.extendCoefficients E))) :
    Nonempty (Equiv A B) := by
  let := hA
  let : Nontrivial A := IsSimpleModule.nontrivial k[G] A.representation.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : A)
  obtain ⟨e⟩ := h
  obtain ⟨φ₀, hφ₀⟩ := Module.Projective.exists_dual_eq_one k (one_ne_zero : (1 : E) ≠ 0)
  let e₀ : (E ⊗[k] A) ≃ₗ[E] (E ⊗[k] B) := e.toLinearEquiv
  let z : E ⊗[k] B := e₀ (1 ⊗ₜ[k] v)
  have hz : z ≠ 0 := by
    intro hzero
    have ht : (1 : E) ⊗ₜ[k] v = 0 := e₀.injective (hzero.trans e₀.map_zero.symm)
    have hz' := congrArg (coefficientProjection (W := A) E φ₀) ht
    exact hv (by simpa [hφ₀] using hz')
  let b := Module.finBasis k B
  obtain ⟨i, hi⟩ : ∃ i, (b.baseChange E).repr z i ≠ 0 := by
    by_contra! hz'
    exact hz ((b.baseChange E).repr.injective (DFunLike.ext _ _ fun i => by simp [hz' i]))
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero k hi
  let f : A.representation.IntertwiningMap B.representation :=
    (coefficientProjection E φ ∘ₗ e₀.toLinearMap.restrictScalars k ∘ₗ
      TensorProduct.mk k E A 1).intertwiningMap_of_isIntertwiningMap _ _ (by
        intro g x
        change coefficientProjection E φ (e.toLinearEquiv (1 ⊗ₜ[k] A.representation g x)) =
          B.representation g (coefficientProjection E φ (e.toLinearEquiv (1 ⊗ₜ[k] x)))
        calc
          _ = coefficientProjection E φ ((B.representation g).baseChange E
                (e₀ (1 ⊗ₜ[k] x))) :=
            congrArg (coefficientProjection E φ)
              (Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g
                (1 ⊗ₜ[k] x))
          _ = _ := coefficientProjection_comp E φ _ _)
  have hcoef (x : E ⊗[k] B) : b.repr (coefficientProjection E φ x) i =
      φ ((b.baseChange E).repr x i) := by
    induction x using TensorProduct.inductionOn with
    | tmul a w =>
      simp only [coefficientProjection_tmul, Module.Basis.baseChange_repr_tmul,
        map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact mul_comm _ _
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  have hf : f ≠ 0 := by
    intro hzero
    apply hφ
    rw [← hcoef z]
    change b.repr (f v) i = 0
    simp [hzero]
  have hinj := (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  have hrank : Module.finrank k A = Module.finrank k B := by
    change A.rank = B.rank
    simpa only [rank_extendCoefficients] using rank_eq_of_equiv e
  exact ⟨f.ofBijective ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := f.toLinearMap) hrank).mp hinj⟩⟩

end Langlands.FiniteRepresentation
