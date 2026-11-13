import Langlands.CategoryTheory.Renard.GeneratorTensorEvaluation
import Langlands.Representation.Category.Abelian
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Category.ExactFunctor
import Mathlib.CategoryTheory.ObjectProperty.EpiMono
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.Generator.Preadditive
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Tensor evaluation for a projective separator of a subcategory of smooth representations

Let `p` be a property of smooth representations closed under subobjects, quotients and
finite products, and let `P` be a projective separator of the full subcategory of `p`.
For every object `Y` of that subcategory, the `ℤ`-linear evaluation
`(P ⟶ Y) ⊗[ℤ] P → Y`, `α ⊗ w ↦ α(w)`, is surjective, and its kernel is the span of
the balancing elements `(r ≫ α) ⊗ w - α ⊗ r(w)` for `r : End P`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe uR uG uV

namespace Langlands.SmoothRep

variable {R : Type uR} {G : Type uG} [CommRing R] [Group G] [TopologicalSpace G]
  (p : ObjectProperty (SmoothRep.{uR, uG, uV} R G))

/-- The underlying additive map of a morphism of the full subcategory. -/
abbrev fullSubcategoryAddHom {X Y : p.FullSubcategory} (f : X ⟶ Y) : X.obj →+ Y.obj :=
  (hom f.hom).toLinearMap.toAddMonoidHom

/-- The trace of `P` in `X`: the sum of the images of all morphisms `P ⟶ X`, as an
invariant submodule of `X`. -/
def traceSubrepresentation (P X : p.FullSubcategory) :
    Subrepresentation X.obj.representation where
  toSubmodule := ⨆ α : P ⟶ X, LinearMap.range (hom α.hom).toLinearMap
  apply_mem_toSubmodule g v hv := by
    refine Submodule.iSup_induction
      (motive := fun v => X.obj.representation g v ∈
        ⨆ α : P ⟶ X, LinearMap.range (hom α.hom).toLinearMap) _ hv ?_ ?_ ?_
    · rintro α _ ⟨w, rfl⟩
      refine Submodule.mem_iSup_of_mem α ⟨P.obj.representation g w, ?_⟩
      exact LinearMap.congr_fun ((hom α.hom).isIntertwining' g) w
    · rw [map_zero]
      exact zero_mem _
    · intro a b ha hb
      rw [map_add]
      exact add_mem ha hb

variable {p}

/-- Elementwise kernels: an element killed by a morphism comes from the actual kernel. -/
theorem exists_kernel_element [p.IsClosedUnderSubobjects] {X Z : p.FullSubcategory}
    (f : X ⟶ Z) (x : X.obj) (hx : hom f.hom x = 0) :
    ∃ (K : p.FullSubcategory) (ι : K ⟶ X) (k : K.obj), hom ι.hom k = x ∧ ι ≫ f = 0 := by
  have : Mono (kernelι f.hom) := (mono_iff_injective _).2 (subtype_injective _ _)
  refine ⟨⟨kernel f.hom, p.prop_of_mono (kernelι f.hom) X.2⟩, p.homMk (kernelι f.hom),
    ⟨x, hx⟩, rfl, ?_⟩
  apply ObjectProperty.hom_ext
  apply hom_ext'
  apply Representation.IntertwiningMap.ext
  ext ⟨v, hv⟩
  exact hv

/-- A projective separator generates every object elementwise: every element is a finite
sum of elements `α(w)` with `α : P ⟶ X`. -/
theorem mem_closure_of_projective_isSeparator [p.IsClosedUnderQuotients]
    (P : p.FullSubcategory) [Projective P] (hP : IsSeparator P)
    (X : p.FullSubcategory) (x : X.obj) :
    x ∈ AddSubgroup.closure {y | ∃ (α : P ⟶ X) (w : P.obj), hom α.hom w = y} := by
  let S := traceSubrepresentation p P X
  suffices hx : x ∈ S.toSubmodule by
    refine Submodule.iSup_induction
      (motive := fun v => v ∈ AddSubgroup.closure
        {y | ∃ (α : P ⟶ X) (w : P.obj), hom α.hom w = y}) _ hx ?_ ?_ ?_
    · rintro α _ ⟨w, rfl⟩
      exact AddSubgroup.subset_closure ⟨α, w, rfl⟩
    · exact zero_mem _
    · intro a b ha hb
      exact add_mem ha hb
  have : Epi (mkQ X.obj S) := (epi_iff_surjective _).2 (mkQ_surjective _ _)
  let Q : p.FullSubcategory := ⟨quotient X.obj S, p.prop_of_epi (mkQ X.obj S) X.2⟩
  let q : X ⟶ Q := p.homMk (mkQ X.obj S)
  have : Epi q := p.ι.epi_of_epi_map (show Epi (mkQ X.obj S) from inferInstance)
  have hzero : ∀ β : P ⟶ Q, β = 0 := by
    intro β
    rw [← Projective.factorThru_comp β q]
    apply ObjectProperty.hom_ext
    apply hom_ext'
    apply Representation.IntertwiningMap.ext
    ext w
    exact (Submodule.Quotient.mk_eq_zero _).2
      (Submodule.mem_iSup_of_mem (Projective.factorThru β q) ⟨w, rfl⟩)
  have hq : q = 0 := (Preadditive.isSeparator_iff P).1 hP q (fun h => hzero (h ≫ q))
  have hqx : hom q.hom x = 0 := by
    rw [hq]
    rfl
  exact (Submodule.Quotient.mk_eq_zero _).1 hqx

/-- The `ℤ`-linear evaluation `(P ⟶ Y) ⊗[ℤ] P → Y`, `α ⊗ w ↦ α(w)`, for objects of a
full subcategory of smooth representations: `Langlands.Renard.tensorEvaluation` for the
underlying additive maps of morphisms. -/
def fullSubcategoryTensorEvaluation (P Y : p.FullSubcategory) :
    (P ⟶ Y) ⊗[ℤ] P.obj →ₗ[ℤ] Y.obj :=
  Langlands.Renard.tensorEvaluation
    (V := fun X : p.FullSubcategory => (X.obj : Type uV))
    (u := fun f => fullSubcategoryAddHom p f) (fun _ _ _ => rfl) P Y

@[simp]
theorem fullSubcategoryTensorEvaluation_tmul {P Y : p.FullSubcategory} (α : P ⟶ Y)
    (w : P.obj) : fullSubcategoryTensorEvaluation P Y (α ⊗ₜ w) = hom α.hom w :=
  Langlands.Renard.tensorEvaluation_tmul
    (V := fun X : p.FullSubcategory => (X.obj : Type uV))
    (u := fun f => fullSubcategoryAddHom p f) (fun _ _ _ => rfl) α w

/-- **Tensor evaluation for a projective separator.** In a full subcategory of smooth
representations closed under subobjects, quotients and finite products, for a projective
separator `P` and every object `Y`, the evaluation `(P ⟶ Y) ⊗[ℤ] P → Y`,
`α ⊗ w ↦ α(w)`, is surjective with kernel the span of the balancing elements
`(r ≫ α) ⊗ w - α ⊗ r(w)`. -/
theorem fullSubcategoryTensorEvaluation_surjective_and_ker
    [p.IsClosedUnderSubobjects] [p.IsClosedUnderQuotients] [p.IsClosedUnderFiniteProducts]
    (P : p.FullSubcategory) [Projective P] (hP : IsSeparator P) (Y : p.FullSubcategory) :
    Function.Surjective (fullSubcategoryTensorEvaluation P Y) ∧
      LinearMap.ker (fullSubcategoryTensorEvaluation P Y) = Submodule.span ℤ (Set.range
        (fun q : End P × (P ⟶ Y) × P.obj =>
          (q.1 ≫ q.2.1) ⊗ₜ[ℤ] q.2.2 - q.2.1 ⊗ₜ[ℤ] (hom q.1.hom q.2.2))) := by
  have : HasFiniteBiproducts p.FullSubcategory := HasFiniteBiproducts.of_hasFiniteProducts
  exact Langlands.Renard.tensorEvaluation_surjective_and_ker
    (V := fun X : p.FullSubcategory => (X.obj : Type uV))
    (u := fun f => fullSubcategoryAddHom p f)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) P Y
    (mem_closure_of_projective_isSeparator P hP)
    (fun f x hx => exists_kernel_element f x hx)

/-- Existential packaging of `fullSubcategoryTensorEvaluation_surjective_and_ker`: a
projective separator `P` has, for every object `Y`, a `ℤ`-linear evaluation
`(P ⟶ Y) ⊗[ℤ] P → Y`, `α ⊗ w ↦ α(w)`, that is surjective with kernel the span of the
balancing elements `(r ≫ α) ⊗ w - α ⊗ r(w)`. -/
theorem exists_tensorEvaluation_of_projective_isSeparator
    [p.IsClosedUnderSubobjects] [p.IsClosedUnderQuotients] [p.IsClosedUnderFiniteProducts]
    (P : p.FullSubcategory) [Projective P] (hP : IsSeparator P) (Y : p.FullSubcategory) :
    ∃ ev : (P ⟶ Y) ⊗[ℤ] P.obj →ₗ[ℤ] Y.obj,
      (∀ (α : P ⟶ Y) (w : P.obj), ev (α ⊗ₜ w) = hom α.hom w) ∧
      Function.Surjective ev ∧
      LinearMap.ker ev = Submodule.span ℤ (Set.range
        (fun q : End P × (P ⟶ Y) × P.obj =>
          (q.1 ≫ q.2.1) ⊗ₜ[ℤ] q.2.2 - q.2.1 ⊗ₜ[ℤ] (hom q.1.hom q.2.2))) :=
  ⟨fullSubcategoryTensorEvaluation P Y, fun α w => fullSubcategoryTensorEvaluation_tmul α w,
    fullSubcategoryTensorEvaluation_surjective_and_ker P hP Y⟩

end Langlands.SmoothRep
