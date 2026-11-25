/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Center.Basic
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The shift endomorphism of a countable power

For an endomorphism `e : A ⟶ A` of an object of a category with countable products, let
`powShift e : ∏ₙ A ⟶ ∏ₙ A` be the map `(xₙ)ₙ ↦ (e x_{n+1})ₙ`
(`CategoryTheory.Limits.powShift`). The invertibility of `1 - powShift e` expresses that `A` is
complete and separated with respect to `e`: if `e` is the multiplication by an element `ϖ` of a
ring, the inverse of `1 - powShift e` is `(yₙ)ₙ ↦ (∑ₖ ϖᵏ y_{n+k})ₙ`.

We show that the invertibility of `1 - powShift e`:
* is invariant under isomorphisms compatible with the endomorphisms
  (`CategoryTheory.Limits.isIso_sub_powShift_iff_of_iso`);
* is preserved and reflected by functors preserving the countable power
  (`CategoryTheory.Limits.isIso_map_sub_powShift_iff`);
* holds for zero objects (`CategoryTheory.Limits.isIso_sub_powShift_of_isZero`).

For an element `z` of the center of a preadditive category, the maps `1 - powShift (z.app A)`
form an endomorphism of the additive functor `A ↦ ∏ₙ A`, so that the objects `A` for which it is
invertible are stable under finite biproducts
(`CategoryTheory.Limits.isIso_sub_powShift_biproduct`). In an abelian category with exact
countable products, they are stable under quotients by subobjects `A' ⊆ A` for which
`1 - powShift (z.app A')` is an epimorphism
(`CategoryTheory.Limits.isIso_sub_powShift_of_shortExact`).
-/

@[expose] public section

namespace CategoryTheory.Limits

open Category

variable {C : Type*} [Category* C]

/-- Two morphisms related by isomorphisms of their sources and targets are simultaneously
isomorphisms. -/
lemma isIso_iff_of_isos_comm {X Y X' Y' : C} {f : X ⟶ Y} {g : X' ⟶ Y'} (e₁ : X ≅ X')
    (e₂ : Y ≅ Y') (w : f ≫ e₂.hom = e₁.hom ≫ g) : IsIso f ↔ IsIso g := by
  have h₁ : g = e₁.inv ≫ f ≫ e₂.hom := by rw [w, Iso.inv_hom_id_assoc]
  have h₂ : f = e₁.hom ≫ g ≫ e₂.inv := by rw [← reassoc_of% w, Iso.hom_inv_id, comp_id]
  exact ⟨fun _ ↦ h₁ ▸ inferInstance, fun _ ↦ h₂ ▸ inferInstance⟩

section Basic

variable {A : C} [HasProduct fun _ : ℕ ↦ A]

/-- The endomorphism `(xₙ)ₙ ↦ (e x_{n+1})ₙ` of the countable power `∏ₙ A`, for an endomorphism
`e` of `A`. -/
noncomputable def powShift (e : A ⟶ A) : (∏ᶜ fun _ : ℕ ↦ A) ⟶ ∏ᶜ fun _ : ℕ ↦ A :=
  Pi.lift fun n ↦ Pi.π _ (n + 1) ≫ e

@[reassoc (attr := simp)]
lemma powShift_π (e : A ⟶ A) (n : ℕ) :
    powShift e ≫ Pi.π (fun _ : ℕ ↦ A) n = Pi.π (fun _ : ℕ ↦ A) (n + 1) ≫ e :=
  Pi.lift_comp_π _ _

/-- `powShift` is natural with respect to morphisms compatible with the endomorphisms. -/
@[reassoc]
lemma powShift_comp_map {B : C} [HasProduct fun _ : ℕ ↦ B] {e : A ⟶ A} {e' : B ⟶ B} (g : A ⟶ B)
    (h : e ≫ g = g ≫ e') :
    powShift e ≫ Pi.map (fun _ ↦ g) = Pi.map (fun _ ↦ g) ≫ powShift e' :=
  Pi.hom_ext _ _ fun n ↦ by simp [h]

variable [Preadditive C]

/-- `1 - powShift` is natural with respect to morphisms compatible with the endomorphisms. -/
@[reassoc]
lemma sub_powShift_comp_map {B : C} [HasProduct fun _ : ℕ ↦ B] {e : A ⟶ A} {e' : B ⟶ B}
    (g : A ⟶ B) (h : e ≫ g = g ≫ e') :
    (𝟙 _ - powShift e) ≫ Pi.map (fun _ ↦ g) = Pi.map (fun _ ↦ g) ≫ (𝟙 _ - powShift e') := by
  rw [Preadditive.sub_comp, Preadditive.comp_sub, powShift_comp_map g h, id_comp, comp_id]

/-- The invertibility of `1 - powShift e` is invariant under isomorphisms compatible with the
endomorphisms. -/
lemma isIso_sub_powShift_iff_of_iso {B : C} [HasProduct fun _ : ℕ ↦ B] {e : A ⟶ A}
    {e' : B ⟶ B} (g : A ≅ B) (h : e ≫ g.hom = g.hom ≫ e') :
    IsIso (𝟙 _ - powShift e) ↔ IsIso (𝟙 _ - powShift e') := by
  let G : (∏ᶜ fun _ : ℕ ↦ A) ≅ ∏ᶜ fun _ : ℕ ↦ B :=
    { hom := Pi.map fun _ ↦ g.hom
      inv := Pi.map fun _ ↦ g.inv
      hom_inv_id := Pi.hom_ext _ _ fun _ ↦ by simp
      inv_hom_id := Pi.hom_ext _ _ fun _ ↦ by simp }
  have hG : (𝟙 _ - powShift e) ≫ G.hom = G.hom ≫ (𝟙 _ - powShift e') :=
    sub_powShift_comp_map g.hom h
  exact isIso_iff_of_isos_comm G G hG

/-- `1 - powShift e` is invertible on a zero object. -/
lemma isIso_sub_powShift_of_isZero (hA : IsZero A) (e : A ⟶ A) :
    IsIso (𝟙 _ - powShift e) := by
  have h : IsZero (∏ᶜ fun _ : ℕ ↦ A) := (IsZero.iff_id_eq_zero _).2
    (Pi.hom_ext _ _ fun _ ↦ hA.eq_of_tgt _ _)
  exact ⟨⟨𝟙 _, h.eq_of_src _ _, h.eq_of_src _ _⟩⟩

/-- A functor preserving the countable power `∏ₙ A` carries `1 - powShift e` to
`1 - powShift (F.map e)`, up to the comparison isomorphism. -/
lemma map_sub_powShift_comp_piComparison {D : Type*} [Category* D] [Preadditive D] (F : C ⥤ D)
    [F.Additive] [HasProduct fun _ : ℕ ↦ F.obj A] (e : A ⟶ A) :
    F.map (𝟙 _ - powShift e) ≫ piComparison F (fun _ : ℕ ↦ A) =
      piComparison F (fun _ : ℕ ↦ A) ≫ (𝟙 _ - powShift (F.map e)) :=
  Pi.hom_ext _ _ fun n ↦ by
    rw [assoc, piComparison_comp_π, ← F.map_comp, Preadditive.sub_comp, id_comp, powShift_π,
      assoc, Preadditive.sub_comp, id_comp, powShift_π, F.map_sub, F.map_comp, Preadditive.comp_sub,
      piComparison_comp_π, ← assoc, piComparison_comp_π]

/-- A functor preserving the countable power `∏ₙ A` preserves and reflects the invertibility of
`1 - powShift e`. -/
lemma isIso_map_sub_powShift_iff {D : Type*} [Category* D] [Preadditive D] (F : C ⥤ D)
    [F.Additive] [HasProduct fun _ : ℕ ↦ F.obj A]
    [PreservesLimit (Discrete.functor fun _ : ℕ ↦ A) F] (e : A ⟶ A) :
    IsIso (F.map (𝟙 _ - powShift e)) ↔ IsIso (𝟙 _ - powShift (F.map e)) :=
  isIso_iff_of_isos_comm (asIso (piComparison F (fun _ : ℕ ↦ A)))
    (asIso (piComparison F (fun _ : ℕ ↦ A))) (map_sub_powShift_comp_piComparison F e)

/-- A family of functors jointly reflecting isomorphisms and preserving the countable power
`∏ₙ A` detects the invertibility of `1 - powShift e`. -/
lemma isIso_sub_powShift_of_jointlyReflectIsomorphisms {I : Type*} {D : I → Type*}
    [∀ i, Category (D i)] [∀ i, Preadditive (D i)] {F : ∀ i, C ⥤ D i}
    (hF : JointlyReflectIsomorphisms F) [∀ i, (F i).Additive]
    [∀ i, HasProduct fun _ : ℕ ↦ (F i).obj A]
    [∀ i, PreservesLimit (Discrete.functor fun _ : ℕ ↦ A) (F i)] (e : A ⟶ A)
    (h : ∀ i, IsIso (𝟙 _ - powShift ((F i).map e))) : IsIso (𝟙 _ - powShift e) := by
  have (i : I) : IsIso ((F i).map (𝟙 _ - powShift e)) :=
    (isIso_map_sub_powShift_iff (F i) e).2 (h i)
  exact hF.isIso _

end Basic

section Functor

variable (C) [HasLimitsOfShape (Discrete ℕ) C]

/-- The countable power functor `A ↦ ∏ₙ A`. -/
@[simps]
noncomputable def powFunctor : C ⥤ C where
  obj A := ∏ᶜ fun _ : ℕ ↦ A
  map g := Pi.map fun _ ↦ g

/-- The countable power functor is the composite of the constant diagram functor and the limit
functor. -/
noncomputable def powFunctorIsoConstCompLim :
    powFunctor C ≅ Functor.const (Discrete ℕ) ⋙ lim :=
  NatIso.ofComponents
    (fun A ↦ HasLimit.isoOfNatIso (Discrete.natIso fun _ ↦ Iso.refl _))
    (fun g ↦ limit.hom_ext fun ⟨n⟩ ↦ by simp)

variable [Preadditive C]

instance : (powFunctor C).Additive where
  map_add := Pi.hom_ext _ _ fun _ ↦ by simp

variable {C}

/-- For an element `z` of the center, the maps `1 - powShift (z.app A)`, as an endomorphism of
the countable power functor. -/
@[simps]
noncomputable def subPowShift (z : CatCenter C) : powFunctor C ⟶ powFunctor C where
  app A := 𝟙 _ - powShift (z.app A)
  naturality _ _ g := (sub_powShift_comp_map g (z.naturality g).symm).symm

/-- For an element `z` of the center, the objects `A` for which `1 - powShift (z.app A)` is
invertible are stable under finite biproducts. -/
lemma isIso_sub_powShift_biproduct (z : CatCenter C) {J : Type} [Finite J] (f : J → C)
    [HasBiproduct f] (h : ∀ j, IsIso (𝟙 _ - powShift (z.app (f j)))) :
    IsIso (𝟙 _ - powShift (z.app (⨁ f))) := by
  have := Fintype.ofFinite J
  let e := (powFunctor C).mapBiproduct f
  have he : (subPowShift z).app (⨁ f) ≫ e.hom =
      e.hom ≫ biproduct.map fun j ↦ (subPowShift z).app (f j) :=
    biproduct.hom_ext _ _ fun j ↦ by
      simp only [e, Functor.mapBiproduct_hom, assoc]
      erw [biproduct.lift_π, biproduct.map_π, biproduct.lift_π_assoc]
      exact ((subPowShift z).naturality _).symm
  exact (isIso_iff_of_isos_comm e e he).2
    (biproduct.mapIso fun j ↦ @asIso _ _ _ _ ((subPowShift z).app (f j)) (h j)).isIso_hom

end Functor

section Abelian

variable [Abelian C]

/-- A morphism of short exact sequences whose first component is an epimorphism and whose second
component is an isomorphism has an invertible third component. -/
lemma ShortComplex.isIso_τ₃_of_shortExact {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) [Epi φ.τ₁] [IsIso φ.τ₂] : IsIso φ.τ₃ := by
  have := h₁.epi_g
  have := h₂.epi_g
  have := h₂.mono_f
  have : Epi φ.τ₃ := by
    have : Epi (S₁.g ≫ φ.τ₃) := by
      rw [← φ.comm₂₃]
      infer_instance
    exact epi_of_epi S₁.g φ.τ₃
  have : Mono φ.τ₃ := by
    refine Preadditive.mono_of_cancel_zero _ fun {A} x hx ↦ ?_
    obtain ⟨A₁, π₁, _, y, hy⟩ := surjective_up_to_refinements_of_epi S₁.g x
    have hy₁ : (y ≫ φ.τ₂) ≫ S₂.g = 0 := by
      rw [assoc, φ.comm₂₃, ← reassoc_of% hy, hx, comp_zero]
    obtain ⟨A₂, π₂, _, w, hw⟩ := h₂.exact.exact_up_to_refinements _ hy₁
    obtain ⟨A₃, π₃, _, v, hv⟩ := surjective_up_to_refinements_of_epi φ.τ₁ w
    have hv₂ : π₃ ≫ π₂ ≫ y = v ≫ S₁.f := by
      rw [← cancel_mono φ.τ₂, assoc, assoc, hw, assoc, ← φ.comm₁₂, ← reassoc_of% hv]
    rw [← cancel_epi π₁, comp_zero, hy, ← cancel_epi π₂, ← cancel_epi π₃, comp_zero, comp_zero,
      ← assoc, ← assoc, assoc π₃, hv₂, assoc, S₁.zero, comp_zero]
  exact isIso_of_mono_of_epi _

variable [HasLimitsOfShape (Discrete ℕ) C] [HasExactLimitsOfShape (Discrete ℕ) C]

instance : PreservesFiniteLimits (powFunctor C) :=
  preservesFiniteLimits_of_natIso (powFunctorIsoConstCompLim C).symm

instance : PreservesFiniteColimits (powFunctor C) :=
  have : PreservesFiniteColimits (lim : (Discrete ℕ ⥤ C) ⥤ C) :=
    HasExactLimitsOfShape.preservesFiniteColimits
  preservesFiniteColimits_of_natIso (powFunctorIsoConstCompLim C).symm

variable (z : CatCenter C)

/-- In an abelian category with exact countable products, if `1 - powShift (z.app B)` is an
epimorphism and `B ⟶ C` is an epimorphism, then `1 - powShift (z.app C)` is an epimorphism. -/
lemma epi_sub_powShift_of_epi {B D : C} (p : B ⟶ D) [Epi p]
    [Epi (𝟙 _ - powShift (z.app B))] : Epi (𝟙 _ - powShift (z.app D)) := by
  have : Epi ((powFunctor C).map p) := (powFunctor C).map_epi p
  have : Epi ((𝟙 _ - powShift (z.app B)) ≫ (powFunctor C).map p) := inferInstance
  rw [powFunctor_map, sub_powShift_comp_map p (z.naturality p).symm] at this
  exact epi_of_epi (Pi.map fun _ ↦ p) _

/-- In an abelian category with exact countable products, let `0 ⟶ A ⟶ B ⟶ D ⟶ 0` be short
exact. If `1 - powShift (z.app A)` is an epimorphism and `1 - powShift (z.app B)` is an
isomorphism, then `1 - powShift (z.app D)` is an isomorphism. -/
lemma isIso_sub_powShift_of_shortExact {S : ShortComplex C} (hS : S.ShortExact)
    [Epi (𝟙 _ - powShift (z.app S.X₁))] [IsIso (𝟙 _ - powShift (z.app S.X₂))] :
    IsIso (𝟙 _ - powShift (z.app S.X₃)) := by
  have : Epi (S.mapNatTrans (subPowShift z)).τ₁ := ‹Epi (𝟙 _ - powShift (z.app S.X₁))›
  have : IsIso (S.mapNatTrans (subPowShift z)).τ₂ := ‹IsIso (𝟙 _ - powShift (z.app S.X₂))›
  exact ShortComplex.isIso_τ₃_of_shortExact (S.mapNatTrans (subPowShift z))
    (hS.map_of_exact (powFunctor C)) (hS.map_of_exact (powFunctor C))

/-- In an abelian category with exact countable products, let `z` be an element of the center and
`U` an object for which `1 - powShift (z.app U)` is an isomorphism. Then so is
`1 - powShift (z.app M)` for the cokernel `M` of any morphism between finite biproducts of copies
of `U`: the image `I` of the morphism is a quotient of a finite biproduct, so that
`1 - powShift (z.app I)` is an epimorphism, and `M` is the quotient of a finite biproduct by `I`. -/
lemma isIso_sub_powShift_cokernel {U : C} (hU : IsIso (𝟙 _ - powShift (z.app U))) {m n : ℕ}
    [HasBiproduct fun _ : Fin m ↦ U] [HasBiproduct fun _ : Fin n ↦ U]
    (f : (⨁ fun _ : Fin m ↦ U) ⟶ ⨁ fun _ : Fin n ↦ U) :
    IsIso (𝟙 _ - powShift (z.app (cokernel f))) := by
  have hm := isIso_sub_powShift_biproduct z (fun _ : Fin m ↦ U) fun _ ↦ hU
  have hn := isIso_sub_powShift_biproduct z (fun _ : Fin n ↦ U) fun _ ↦ hU
  have h₁ := epi_sub_powShift_of_epi z (Abelian.factorThruImage f)
  let S := ShortComplex.mk (kernel.ι (cokernel.π f)) (cokernel.π f) (kernel.condition _)
  have hS : S.ShortExact := { exact := S.exact_of_f_is_kernel (kernelIsKernel _) }
  exact @isIso_sub_powShift_of_shortExact _ _ _ _ _ z S hS h₁ hn

end Abelian

end CategoryTheory.Limits
