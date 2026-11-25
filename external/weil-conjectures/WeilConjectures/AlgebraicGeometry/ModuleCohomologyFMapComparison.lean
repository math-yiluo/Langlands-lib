/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-! # Homotopy comparison of the auxiliary injective complexes

Source: Stacks Project, Derived Categories, Tags 013P and 013S, and Cohomology
of Sheaves, Remark 01FB
(blueprint: lem-weil-pbc-module-cohomology-fmap-comparison).
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

private theorem lift_nat_quasiIso {A : Type*} [Category* A] [Abelian A]
    {K L I : CochainComplex A ℕ} (hI : ∀ n, Injective (I.X n))
    (α : K ⟶ L) [QuasiIso α] (γ : K ⟶ I) :
    ∃ β : L ⟶ I, Nonempty (Homotopy (α ≫ β) γ) := by
  let : ∀ n, Injective (I.X n) := hI
  let := HasDerivedCategory.standard A
  let e := ComplexShape.embeddingUpNat
  let E := e.extendFunctor A
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  have : QuasiIso (E.map α) :=
    (HomologicalComplex.quasiIso_extendMap_iff α e).2 inferInstance
  obtain ⟨b, hb⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    (q.obj (L.extend e)) (I.extend e)).surjective
      ((DerivedCategory.quotientCompQhIso A).hom.app (L.extend e) ≫
        inv (DerivedCategory.Q.map (E.map α)) ≫ DerivedCategory.Q.map (E.map γ) ≫
        (DerivedCategory.quotientCompQhIso A).inv.app (I.extend e))
  obtain ⟨b, rfl⟩ := q.map_surjective b
  obtain ⟨β, rfl⟩ := E.map_surjective b
  have heq : q.map (E.map (α ≫ β)) = q.map (E.map γ) := by
    apply (CochainComplex.IsKInjective.Qh_map_bijective
      (q.obj (K.extend e)) (I.extend e)).injective
    rw [E.map_comp, q.map_comp, DerivedCategory.Qh.map_comp]
    rw [← cancel_mono ((DerivedCategory.quotientCompQhIso A).hom.app (I.extend e))]
    dsimp only [q, E, ComplexShape.Embedding.extendFunctor] at hb ⊢
    simp only [hb, Category.assoc]
    rw [Iso.inv_hom_id_app, Category.comp_id,
      DerivedCategory.quotientCompQhIso_hom_naturality,
      DerivedCategory.quotientCompQhIso_hom_naturality_assoc,
      IsIso.hom_inv_id_assoc]
  refine ⟨β, ⟨?_⟩⟩
  exact Homotopy.ofExtend (e := e) (HomotopyCategory.homotopyOfEq _ _ heq)

private theorem unique_nat_quasiIso {A : Type*} [Category* A] [Abelian A]
    {K L I : CochainComplex A ℕ} (hI : ∀ n, Injective (I.X n))
    (α : K ⟶ L) [QuasiIso α] (β₁ β₂ : L ⟶ I)
    (hβ : Nonempty (Homotopy (α ≫ β₁) (α ≫ β₂))) :
    Nonempty (Homotopy β₁ β₂) := by
  let : ∀ n, Injective (I.X n) := hI
  let e := ComplexShape.embeddingUpNat
  let E := e.extendFunctor A
  have : QuasiIso (E.map α) :=
    (HomologicalComplex.quasiIso_extendMap_iff α e).2 inferInstance
  have hh : Nonempty (Homotopy (E.map α ≫ E.map β₁) (E.map α ≫ E.map β₂)) := by
    rw [← E.map_comp, ← E.map_comp]
    exact ⟨hβ.some.extend e⟩
  obtain ⟨hh⟩ := CochainComplex.homotopy_of_comp_quasiIso_of_injective
    (I := I.extend e)
    ⟨0, fun n hn ↦ CochainComplex.isZero_of_isStrictlyGE _ 0 n hn⟩
    (E.map α) (E.map β₁) (E.map β₂) hh
  exact ⟨hh.ofExtend⟩

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency.types false in
/-- The two auxiliary injective complexes admit a comparison morphism intertwining
both the pushforward comparison and the lifted module map, up to homotopy.
Source: Stacks Project, Derived Categories, Tags 013P and 013S; Cohomology of Sheaves,
Remark 01FB (blueprint: lem-weil-pbc-module-cohomology-fmap-comparison).

Proof: take the identity descents between the two resolutions of F and of G.
Extend all complexes by zero to integer indices. The auxiliary target K' is bounded
below and termwise injective, hence K-injective. In the homotopy category, precomposition
with the quasi-isomorphism lambda induces a bijection on maps into K'. Apply its
surjectivity to the composite of the pushforward identity descent with lambda'. This
produces a map e from K to K' and a homotopy for the first square.
For the second square, precompose its two
routes with the augmentation of J. The compatibility equations for beta and beta',
the augmentation equations for the identity descents, and the first homotopy identify
these routes up to homotopy. Precomposition with the quasi-isomorphism J's augmentation
is injective on homotopy classes of maps into K', so the second routes are homotopic.
Full faithfulness of extension by zero returns the map and homotopies
to natural indices. No cohomology functor or inverse of a sections map is used here. -/
theorem moduleCohomologyFMapData_comparison {X Y : Scheme.{u}} (h : X ⟶ Y)
    {G : Y.Modules} {F : X.Modules} (φ : G ⟶ (pushforward h).obj F)
    (C C' : ModuleCohomologyFMapData h G F φ) :
    ∃ e : C.K ⟶ C'.K,
      Nonempty (Homotopy (C.lambda ≫ e)
        (((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (InjectiveResolution.desc (𝟙 F) C'.I C.I) ≫ C'.lambda)) ∧
      Nonempty (Homotopy (C.β ≫ e)
        (InjectiveResolution.desc (𝟙 G) C'.J C.J ≫ C'.β)) := by
  let P := pushforward h
  have : P.Additive := inferInstanceAs (pushforward h).Additive
  let PP := P.mapHomologicalComplex (ComplexShape.up ℕ)
  let αI := InjectiveResolution.desc (𝟙 F) C'.I C.I
  let αJ := InjectiveResolution.desc (𝟙 G) C'.J C.J
  have : QuasiIso C.lambda := C.quasiIso
  obtain ⟨e, he⟩ := lift_nat_quasiIso C'.injective C.lambda (PP.map αI ≫ C'.lambda)
  refine ⟨e, he, ?_⟩
  let γ₀ := φ ≫ P.map (C.I.ι.f 0)
  have hγ₀ : γ₀ ≫ (PP.obj C.I.cocomplex).d 0 1 = 0 := by
    change (φ ≫ P.map (C.I.ι.f 0)) ≫ P.map (C.I.cocomplex.d 0 1) = 0
    rw [Category.assoc, ← P.map_comp, C.I.ι_f_zero_comp_complex_d,
      P.map_zero, comp_zero]
  let γ := (CochainComplex.fromSingle₀Equiv (PP.obj C.I.cocomplex) G).symm ⟨γ₀, hγ₀⟩
  have hγ : γ.f 0 = γ₀ := CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _
  have hβ : C.J.ι ≫ C.β = γ ≫ C.lambda := by
    apply HomologicalComplex.from_single_hom_ext
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, hγ]
    exact C.compatible
  have hβ' : C'.J.ι ≫ C'.β = γ ≫ PP.map αI ≫ C'.lambda := by
    apply HomologicalComplex.from_single_hom_ext
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      hγ, C'.compatible]
    change φ ≫ P.map (C'.I.ι.f 0) ≫ C'.lambda.f 0 =
      γ₀ ≫ P.map (αI.f 0) ≫ C'.lambda.f 0
    dsimp [γ₀, αI]
    simp only [Category.assoc]
    rw [← P.map_comp_assoc, InjectiveResolution.desc_commutes_zero, Category.id_comp]
  apply unique_nat_quasiIso C'.injective C.J.ι (C.β ≫ e) (αJ ≫ C'.β)
  have hJ : C.J.ι ≫ αJ = C'.J.ι := by simp [αJ]
  have hleft : C.J.ι ≫ (C.β ≫ e) = γ ≫ (C.lambda ≫ e) := by
    rw [← Category.assoc, hβ, Category.assoc]
  have hright : C.J.ι ≫ (αJ ≫ C'.β) = γ ≫ (PP.map αI ≫ C'.lambda) := by
    rw [← Category.assoc, hJ, hβ']
  rw [hleft, hright]
  exact ⟨he.some.compLeft γ⟩

end AlgebraicGeometry.Scheme.Modules
