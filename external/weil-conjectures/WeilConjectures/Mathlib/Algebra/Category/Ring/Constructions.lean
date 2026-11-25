/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import WeilConjectures.Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered
public import Mathlib.RingTheory.PolynomialAlgebra
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
public import WeilConjectures.Mathlib.Algebra.Polynomial.Laurent

/-!
# Quotients by extended ideals are pushouts

For an ideal `K` of `R` and a ring map `φ : R ⟶ S`, the square formed by the quotient
maps `R ⟶ R ⧸ K`, `S ⟶ S ⧸ K·S` and the induced map `R ⧸ K ⟶ S ⧸ K·S` is a pushout in
`CommRingCat`.

This is not proved by exhibiting the colimit cocone by hand: it is the tensor-product
pushout `CommRingCat.isPushout_tensorProduct` transported along the isomorphism
`Algebra.TensorProduct.quotIdealMapEquivTensorQuot : S ⧸ K·S ≃ₐ[S] S ⊗[R] (R ⧸ K)`.

We also record that the statement "the ranges of two ring maps into `R` generate `R`" is
invariant under an isomorphism of `R` (`CommRingCat.closure_range_union_eq_top_iff_of_iso`).

## Main results

- `CommRingCat.isPushout_quotient`, `CommRingCat.isPushout_quotient_of_map_eq`
- `CommRingCat.IsPushout.closure_range_union_eq_top`: a pushout of commutative rings is generated
  by the images of the two maps into it.
- `CommRingCat.IsPushout.bijective_sum_mul`: a `ℤ`-basis is carried to a basis along a pushout
  square of commutative rings over a quotient of `ℤ`.
- `CommRingCat.polynomialFunctor`, `CommRingCat.laurentFunctor`: the functors `R ↦ R[t]` and
  `R ↦ R[t, t⁻¹]`; their inclusions of constants are coequifibered
  (`CommRingCat.coequifibered_polynomialC`, `CommRingCat.coequifibered_laurentC`).
-/

@[expose] public section

universe u

open CategoryTheory TensorProduct

namespace CommRingCat

/-- Quotients by extended ideals are pushouts in `CommRingCat`: base change of the closed
immersion cut out by `K` along `φ` is the closed immersion cut out by the extended ideal. -/
lemma isPushout_quotient {R S : CommRingCat.{u}} (φ : R ⟶ S) (K : Ideal R) :
    IsPushout (ofHom (Ideal.Quotient.mk K)) φ
      (ofHom (Ideal.quotientMap (K.map φ.hom) φ.hom Ideal.le_comap_map))
      (ofHom (Ideal.Quotient.mk (K.map φ.hom))) := by
  let := φ.hom.toAlgebra
  let e : of (S ⧸ K.map φ.hom) ≅ of (S ⊗[R] (R ⧸ K)) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S K).toRingEquiv.toCommRingCatIso
  refine (isPushout_tensorProduct R S (R ⧸ K)).flip.of_iso' (Iso.refl _) (Iso.refl _)
    (Iso.refl _) e ?_ ?_ ?_ ?_
  · ext r
    simp
  · ext r
    rfl
  · ext r
    simp only [e, Iso.refl_hom, Category.id_comp, RingEquiv.toCommRingCatIso_hom, hom_comp,
      hom_ofHom, RingHom.comp_apply, Ideal.quotientMap_mk, AlgEquiv.coe_toRingEquiv,
      RingEquiv.coe_toRingHom, AlgHom.toRingHom_eq_coe]
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul r).symm
  · ext r
    exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk S K r).symm

/-- A variant of `CommRingCat.isPushout_quotient` with the extended ideal given up to equality. -/
lemma isPushout_quotient_of_map_eq {R S : CommRingCat.{u}} (φ : R ⟶ S) (K : Ideal R)
    {L : Ideal S} (hL : K.map φ.hom = L) :
    IsPushout (ofHom (Ideal.Quotient.mk K)) φ
      (ofHom (Ideal.quotientMap L φ.hom (hL ▸ Ideal.le_comap_map)))
      (ofHom (Ideal.Quotient.mk L)) := by
  subst hL
  exact isPushout_quotient φ K

/-- Transporting "the ranges of `a` and `b` generate" along an isomorphism of the target. -/
lemma closure_range_union_eq_top_of_iso {A B R R' : CommRingCat.{u}}
    {a : A ⟶ R} {b : B ⟶ R} (e : R ⟶ R') [IsIso e]
    (h : Subring.closure (Set.range ⇑a.hom ∪ Set.range ⇑b.hom) = ⊤) :
    Subring.closure (Set.range ⇑(a ≫ e).hom ∪ Set.range ⇑(b ≫ e).hom) = ⊤ := by
  have he : Function.Surjective ⇑e.hom := (ConcreteCategory.bijective_of_isIso e).2
  have := _root_.Subring.closure_image_eq_top e.hom he h
  rwa [Set.image_union, ← Set.range_comp, ← Set.range_comp] at this

/-- "The ranges of `a` and `b` generate" is invariant under an isomorphism of the target. -/
lemma closure_range_union_eq_top_iff_of_iso {A B R R' : CommRingCat.{u}}
    {a : A ⟶ R} {b : B ⟶ R} (e : R ⟶ R') [IsIso e] :
    Subring.closure (Set.range ⇑(a ≫ e).hom ∪ Set.range ⇑(b ≫ e).hom) = ⊤ ↔
      Subring.closure (Set.range ⇑a.hom ∪ Set.range ⇑b.hom) = ⊤ := by
  refine ⟨fun h ↦ ?_, closure_range_union_eq_top_of_iso e⟩
  have := closure_range_union_eq_top_of_iso (a := a ≫ e) (b := b ≫ e) (inv e) h
  simpa using this

end CommRingCat

namespace CommRingCat

set_option backward.isDefEq.respectTransparency false in
/-- **Bases are preserved by pushouts over the integers**: given a pushout square of commutative
rings `R → A, R → B, A → X, B → X` with `R` a quotient of `ℤ`, a `ℤ`-basis `v` of `A` maps to a
`B`-basis of `X`, i.e. every element of `X` is uniquely a finite sum `∑ b(cᵢ) a(vᵢ)`. -/
theorem IsPushout.bijective_sum_mul {R A B X : CommRingCat} {f : R ⟶ A} {g : R ⟶ B}
    {a : A ⟶ X} {b : B ⟶ X} (h : IsPushout f g a b)
    (hR : Function.Surjective (Int.castRingHom R)) {ι : Type*} (v : Module.Basis ι ℤ A) :
    Function.Bijective fun c : ι →₀ B ↦ c.sum fun i r ↦ b r * a (v i) := by
  let := f.hom.toAlgebra
  let := g.hom.toAlgebra
  let := a.hom.toAlgebra
  let := b.hom.toAlgebra
  let : Algebra R X := (f ≫ a).hom.toAlgebra
  have : IsScalarTower R A X := .of_algebraMap_eq' rfl
  have : IsScalarTower R B X := .of_algebraMap_eq' (by
    change (f ≫ a).hom = (g ≫ b).hom
    rw [h.w])
  have hp : Algebra.IsPushout R A B X := CommRingCat.isPushout_iff_isPushout.mp h
  have hli : LinearIndependent R v := by
    rw [linearIndependent_iff']
    intro t c hc i hi
    choose z hz using fun j ↦ hR (c j)
    have h' : ∑ j ∈ t, z j • v j = 0 := by
      rw [← hc]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← hz j, eq_intCast, Int.cast_smul_eq_zsmul]
    rw [← hz i, linearIndependent_iff'.mp v.linearIndependent t z h' i hi, eq_intCast,
      Int.cast_zero]
  have hsp : (⊤ : Submodule R A) ≤ Submodule.span R (Set.range v) := by
    intro x _
    have := Submodule.span_le_restrictScalars ℤ R (Set.range v)
    exact this (v.span_eq.ge Submodule.mem_top)
  let vX := IsBaseChange.basis (Module.Basis.mk hli hsp) hp.symm.out
  have hvX : ∀ i, vX i = a (v i) := fun i ↦ by
    simp [vX, IsBaseChange.basis_apply]
    rfl
  convert vX.repr.symm.bijective using 1
  ext c
  rw [Module.Basis.repr_symm_apply, Finsupp.linearCombination_apply]
  refine Finsupp.sum_congr fun i _ ↦ ?_
  rw [hvX, Algebra.smul_def]
  rfl

/-- **A pushout of commutative rings is generated by the images of the two maps into it**, as
the tensor product is generated by the pure tensors. -/
lemma IsPushout.closure_range_union_eq_top {R A B P : CommRingCat.{u}} {f : R ⟶ A} {g : R ⟶ B}
    {inl : A ⟶ P} {inr : B ⟶ P} (h : IsPushout f g inl inr) :
    Subring.closure (Set.range ⇑inl.hom ∪ Set.range ⇑inr.hom) = ⊤ := by
  let := f.hom.toAlgebra
  let := g.hom.toAlgebra
  have h' : IsPushout f g (ofHom (S := A ⊗[R] B) Algebra.TensorProduct.includeLeftRingHom)
      (ofHom (S := A ⊗[R] B) Algebra.TensorProduct.includeRight.toRingHom) :=
    CommRingCat.isPushout_tensorProduct R A B
  have htop : Subring.closure
      (Set.range ⇑(ofHom (S := A ⊗[R] B) Algebra.TensorProduct.includeLeftRingHom).hom ∪
        Set.range ⇑(ofHom (S := A ⊗[R] B) Algebra.TensorProduct.includeRight.toRingHom).hom) =
      ⊤ := by
    rw [eq_top_iff]
    rintro x -
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      rw [← mul_one a, ← one_mul b, ← Algebra.TensorProduct.tmul_mul_tmul]
      exact mul_mem (Subring.subset_closure (Or.inl ⟨a, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨b, rfl⟩))
    | add x y hx hy => exact add_mem hx hy
  have := closure_range_union_eq_top_of_iso (h'.isoIsPushout _ _ h).hom htop
  have e₁ := h'.inl_isoIsPushout_hom _ _ h
  have e₂ := h'.inr_isoIsPushout_hom _ _ h
  rwa [e₁, e₂] at this

end CommRingCat

noncomputable section

open Polynomial LaurentPolynomial

/-! ### Polynomial and Laurent polynomial functors -/

namespace CommRingCat

/-- The functor `R ↦ R[t]`. -/
@[simps]
noncomputable def polynomialFunctor : CommRingCat.{u} ⥤ CommRingCat.{u} where
  obj R := .of R[X]
  map f := ofHom (mapRingHom f.hom)
  map_id R := by ext : 1; exact mapRingHom_id
  map_comp f g := by ext : 1; exact (mapRingHom_comp _ _).symm

/-- The inclusion of constants `R ⟶ R[t]`. -/
@[simps]
noncomputable def polynomialC : 𝟭 CommRingCat.{u} ⟶ polynomialFunctor where
  app R := ofHom C
  naturality _ _ f := by ext : 1; exact (mapRingHom_comp_C _).symm

lemma coequifibered_polynomialC : polynomialC.{u}.Coequifibered := by
  intro R S f
  algebraize [f.hom]
  let := Polynomial.algebra (R := R) (A := S)
  exact CommRingCat.isPushout_of_isPushout R S R[X] S[X]

/-- The functor `R ↦ R[t, t⁻¹]`. -/
@[simps]
noncomputable def laurentFunctor : CommRingCat.{u} ⥤ CommRingCat.{u} where
  obj R := .of R[T;T⁻¹]
  map f := ofHom (LaurentPolynomial.mapRingHom f.hom)
  map_id R := by ext : 1; exact AddMonoidAlgebra.mapRingHom_id
  map_comp f g := by ext : 1; exact AddMonoidAlgebra.mapRingHom_comp _ _

/-- The inclusion of constants `R ⟶ R[t, t⁻¹]`. -/
@[simps]
noncomputable def laurentC : 𝟭 CommRingCat.{u} ⟶ laurentFunctor where
  app R := ofHom LaurentPolynomial.C
  naturality _ _ f := by
    ext x
    exact (LaurentPolynomial.mapRingHom_C f.hom x).symm

open scoped AlgebraMonoidAlgebra in
lemma coequifibered_laurentC : laurentC.{u}.Coequifibered := by
  intro R S f
  algebraize [f.hom]
  exact CommRingCat.isPushout_of_isPushout R S R[T;T⁻¹] S[T;T⁻¹]

/-- The inclusion `R[t] ⟶ R[t, t⁻¹]`. -/
@[simps]
noncomputable def polynomialToLaurent : polynomialFunctor.{u} ⟶ laurentFunctor where
  app R := ofHom toLaurent
  naturality _ _ f := by
    ext p
    exact (LaurentPolynomial.mapRingHom_toLaurent f.hom p).symm

end CommRingCat

end
