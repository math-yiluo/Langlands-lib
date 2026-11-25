/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module


public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact

/-!
# Sections with support on a site and their derived triangle

Let `(C, J)` be a site and `A` an abelian category. For an object `U` of `C` the functor of
*sections with support away from `U`* is `Γ_U^c(F) = ker (Γ(F) ⟶ F(U))`
(`CategoryTheory.Sheaf.ΓSupport`). More generally, a *pair* is a morphism `p : U ⟶ V` of `C`,
and its sections with support are `ker (F(V) ⟶ F(U))`; a morphism of pairs is a commutative
square, i.e. a morphism in `Arrow C`.

If `p` is a monomorphism, then for an injective sheaf `I` the restriction `I(V) ⟶ I(U)` is a
split epimorphism (`CategoryTheory.Sheaf.isSplitEpi_map_of_injective`): the presheaf
`W ↦ ⊕_{Hom(W, U)} a` is a subpresheaf of `W ↦ ⊕_{Hom(W, V)} a`, and sheafification preserves
monomorphisms. Similarly `Γ(I) ⟶ I(U)` is a split epimorphism when every `Hom(W, U)` is a
subsingleton (`CategoryTheory.Sheaf.isSplitEpi_ΓRes_of_injective`), e.g. for an open subscheme
on the small étale or pro-étale site. Hence the sequences

`0 ⟶ Γ_Z ⟶ Γ ⟶ Γ(U, -) ⟶ 0`, `0 ⟶ Γ_{V ∖ U}(V, -) ⟶ Γ(V, -) ⟶ Γ(U, -) ⟶ 0`

are short exact on injectives and, by `CategoryTheory.ShortComplex.rightDerivedTriangle`, give
distinguished triangles of derived functors on the bounded below derived category, natural in the
complex and in the pair.

## Main definitions

- `CategoryTheory.Sheaf.ΓSupport`, `CategoryTheory.Sheaf.ΓSupportShortComplex`
- `CategoryTheory.Sheaf.pairShortComplex`, `CategoryTheory.Sheaf.pairShortComplexFunctor`
- `CategoryTheory.Sheaf.ΓSupportShortComplexToPair`
- `CategoryTheory.Sheaf.ΓSupportRightDerivedTriangle`,
  `CategoryTheory.Sheaf.pairRightDerivedTriangle`
  and the morphisms of triangles `CategoryTheory.Sheaf.pairRightDerivedTriangleMap`,
  `CategoryTheory.Sheaf.ΓSupportRightDerivedTriangleToPair`.
-/

@[expose] public section

universe u' u v w

open CategoryTheory Category Limits Opposite

namespace CategoryTheory

/-- The sections of sheaves over an object of the site form an additive functor. -/
instance Sheaf.additive_sheafSections_obj {C : Type*} [Category C] {J : GrothendieckTopology C}
    {A : Type*} [Category A] [Preadditive A] (U : Cᵒᵖ) : ((sheafSections J A).obj U).Additive where
  map_add := rfl

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u') [Category.{w} A] [Abelian A] [HasSheafify J A]

section ΓSupport

variable [HasGlobalSectionsFunctor J A]

/-- The sections with support away from an object `U` of the site: the kernel
`F ↦ ker (Γ(F) ⟶ F(U))` of the restriction from the global sections to the sections on `U`.
For `U` the open complement of a closed subscheme `Z` this is the functor `Γ_Z` of sections
with support in `Z`. -/
noncomputable def Sheaf.ΓSupport (U : Cᵒᵖ) : Sheaf J A ⥤ A :=
  kernel (Sheaf.natTransΓRes J A U)

/-- The inclusion `Γ_Z(F) ⟶ Γ(F)` of the sections with support. -/
noncomputable def Sheaf.ΓSupportι (U : Cᵒᵖ) : Sheaf.ΓSupport J A U ⟶ Sheaf.Γ J A :=
  kernel.ι _

instance (U : Cᵒᵖ) (F : Sheaf J A) : Mono ((Sheaf.ΓSupportι J A U).app F) := by
  have : Mono (Sheaf.ΓSupportι J A U) := by dsimp [Sheaf.ΓSupportι]; infer_instance
  infer_instance

@[reassoc (attr := simp)]
lemma Sheaf.ΓSupportι_app_comp_ΓRes (U : Cᵒᵖ) (F : Sheaf J A) :
    (Sheaf.ΓSupportι J A U).app F ≫ Sheaf.ΓRes F U = 0 := by
  have := congr_app (kernel.condition (Sheaf.natTransΓRes J A U)) F
  rw [NatTrans.comp_app, NatTrans.app_zero] at this
  exact this

instance (U : Cᵒᵖ) : (Sheaf.ΓSupport J A U).Additive where
  map_add {F G f g} := by
    rw [← cancel_mono ((Sheaf.ΓSupportι J A U).app G)]
    simp only [Preadditive.add_comp, NatTrans.naturality, Functor.map_add,
      Preadditive.comp_add]

/-- The short complex of functors `Γ_U^c ⟶ Γ ⟶ Γ(U, -)` of the sections with support away from
`U`, the global sections and the sections over `U`. -/
@[simps]
noncomputable def Sheaf.ΓSupportShortComplex (U : Cᵒᵖ) : ShortComplex (Sheaf J A ⥤ A) :=
  ShortComplex.mk (Sheaf.ΓSupportι J A U) (Sheaf.natTransΓRes J A U) (kernel.condition _)

instance (U : Cᵒᵖ) : (Sheaf.ΓSupportShortComplex J A U).X₁.Additive :=
  inferInstanceAs (Sheaf.ΓSupport J A U).Additive

instance (U : Cᵒᵖ) : (Sheaf.ΓSupportShortComplex J A U).X₂.Additive :=
  inferInstanceAs (Sheaf.Γ J A).Additive

instance (U : Cᵒᵖ) : (Sheaf.ΓSupportShortComplex J A U).X₃.Additive :=
  inferInstanceAs ((sheafSections J A).obj U).Additive

end ΓSupport

section Pair

/-- The sections with support of a pair `p : U ⟶ V`: `F ↦ ker (F(V) ⟶ F(U))`. -/
noncomputable def Sheaf.pairSupport (p : Arrow C) : Sheaf J A ⥤ A :=
  kernel ((sheafSections J A).map p.hom.op)

/-- The inclusion `Γ_{V ∖ U}(V, F) ⟶ F(V)` of the sections with support of a pair. -/
noncomputable def Sheaf.pairSupportι (p : Arrow C) :
    Sheaf.pairSupport J A p ⟶ (sheafSections J A).obj (op p.right) :=
  kernel.ι _

instance (p : Arrow C) : Mono (Sheaf.pairSupportι J A p) := by
  dsimp [Sheaf.pairSupportι]; infer_instance

instance (p : Arrow C) (F : Sheaf J A) : Mono ((Sheaf.pairSupportι J A p).app F) := by
  have : Mono (Sheaf.pairSupportι J A p) := by dsimp [Sheaf.pairSupportι]; infer_instance
  infer_instance

instance (p : Arrow C) : (Sheaf.pairSupport J A p).Additive where
  map_add {F G f g} := by
    rw [← cancel_mono ((Sheaf.pairSupportι J A p).app G)]
    simp only [Preadditive.add_comp, NatTrans.naturality, Functor.map_add,
      Preadditive.comp_add]

/-- The short complex of functors `Γ_{V ∖ U}(V, -) ⟶ Γ(V, -) ⟶ Γ(U, -)` of a pair `p : U ⟶ V`. -/
@[simps]
noncomputable def Sheaf.pairShortComplex (p : Arrow C) : ShortComplex (Sheaf J A ⥤ A) :=
  ShortComplex.mk (Sheaf.pairSupportι J A p) ((sheafSections J A).map p.hom.op)
    (kernel.condition _)

instance (p : Arrow C) : (Sheaf.pairShortComplex J A p).X₁.Additive :=
  inferInstanceAs (Sheaf.pairSupport J A p).Additive

instance (p : Arrow C) : (Sheaf.pairShortComplex J A p).X₂.Additive :=
  inferInstanceAs ((sheafSections J A).obj (op p.right)).Additive

instance (p : Arrow C) : (Sheaf.pairShortComplex J A p).X₃.Additive :=
  inferInstanceAs ((sheafSections J A).obj (op p.left)).Additive

omit [Abelian A] [HasSheafify J A] in
lemma Sheaf.pairShortComplexMap_comm {p q : Arrow C} (φ : p ⟶ q) :
    (sheafSections J A).map q.hom.op ≫ (sheafSections J A).map φ.left.op =
      (sheafSections J A).map φ.right.op ≫ (sheafSections J A).map p.hom.op := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, Arrow.w]

/-- The restriction `S(q) ⟶ S(p)` of the short complexes of a morphism of pairs `p ⟶ q`. -/
@[simps]
noncomputable def Sheaf.pairShortComplexMap {p q : Arrow C} (φ : p ⟶ q) :
    Sheaf.pairShortComplex J A q ⟶ Sheaf.pairShortComplex J A p where
  τ₁ := kernel.map ((sheafSections J A).map q.hom.op) ((sheafSections J A).map p.hom.op)
    ((sheafSections J A).map φ.right.op) ((sheafSections J A).map φ.left.op)
    (Sheaf.pairShortComplexMap_comm J A φ)
  τ₂ := (sheafSections J A).map φ.right.op
  τ₃ := (sheafSections J A).map φ.left.op
  comm₁₂ := by simp [Sheaf.pairSupportι]
  comm₂₃ := (Sheaf.pairShortComplexMap_comm J A φ).symm

/-- The short complexes of pairs, as a contravariant functor of the pair. -/
@[simps]
noncomputable def Sheaf.pairShortComplexFunctor : (Arrow C)ᵒᵖ ⥤ ShortComplex (Sheaf J A ⥤ A) where
  obj p := Sheaf.pairShortComplex J A p.unop
  map φ := Sheaf.pairShortComplexMap J A φ.unop
  map_id p := by
    refine ShortComplex.hom_ext _ _ ?_ (by simp; rfl) (by simp; rfl)
    simp only [unop_id, pairShortComplexMap_τ₁, Arrow.id_right, op_id, Functor.map_id,
      Arrow.id_left, kernel.map_id, ShortComplex.id_τ₁]
    rfl
  map_comp φ ψ := by
    refine ShortComplex.hom_ext _ _ ?_ (by simp) (by simp)
    rw [← cancel_mono (Sheaf.pairSupportι J A _)]
    simp [Sheaf.pairSupportι]

variable [HasGlobalSectionsFunctor J A]

omit [Abelian A] in
lemma Sheaf.ΓSupportShortComplexToPair_comm {U : C} (p : Arrow C) (g : p.left ⟶ U) :
    Sheaf.natTransΓRes J A (op U) ≫ (sheafSections J A).map g.op =
      Sheaf.natTransΓRes J A (op p.right) ≫ (sheafSections J A).map p.hom.op := by
  ext F
  simp [Sheaf.ΓRes_map]

/-- The morphism of short complexes from `Γ_U^c ⟶ Γ ⟶ Γ(U, -)` to the short complex of a pair
`p : U' ⟶ V` with a map `g : U' ⟶ U`: the restriction from the pair `(X, U)` to `(V, U')`. -/
@[simps]
noncomputable def Sheaf.ΓSupportShortComplexToPair {U : C} (p : Arrow C) (g : p.left ⟶ U) :
    Sheaf.ΓSupportShortComplex J A (op U) ⟶ Sheaf.pairShortComplex J A p where
  τ₁ := kernel.map (Sheaf.natTransΓRes J A (op U)) ((sheafSections J A).map p.hom.op)
    (Sheaf.natTransΓRes J A (op p.right)) ((sheafSections J A).map g.op)
    (Sheaf.ΓSupportShortComplexToPair_comm J A p g)
  τ₂ := Sheaf.natTransΓRes J A (op p.right)
  τ₃ := (sheafSections J A).map g.op
  comm₁₂ := by simp [Sheaf.ΓSupportι, Sheaf.pairSupportι]
  comm₂₃ := (Sheaf.ΓSupportShortComplexToPair_comm J A p g).symm

end Pair

section Injective

variable {J A}

/-- A morphism of presheaves from a presheaf `P` into an injective sheaf extends along a
monomorphism of presheaves `P ⟶ Q`: sheafification preserves monomorphisms. -/
lemma Sheaf.exists_comp_eq_of_injective (I : Sheaf J A) [Injective I] {P Q : Cᵒᵖ ⥤ A}
    (m : P ⟶ Q) [Mono m] (g : P ⟶ I.obj) : ∃ h : Q ⟶ I.obj, m ≫ h = g := by
  let adj := sheafificationAdjunction J A
  refine ⟨adj.homEquiv _ _ (Injective.factorThru ((adj.homEquiv _ _).symm g)
    ((presheafToSheaf J A).map m)), ?_⟩
  rw [← Adjunction.homEquiv_naturality_left, Injective.comp_factorThru, Equiv.apply_symm_apply]

omit [HasSheafify J A] in
lemma mono_sigmaDesc_id_of_subsingleton {ι : Type*} [Subsingleton ι] (a : A)
    [HasCoproduct fun _ : ι ↦ a] : Mono (Sigma.desc fun _ : ι ↦ 𝟙 a) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have h : IsZero (∐ fun _ : ι ↦ a) :=
      (IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ fun i ↦ isEmptyElim i)
    exact ⟨fun _ _ _ ↦ h.eq_of_tgt _ _⟩
  · obtain ⟨i⟩ := hι
    have : IsIso (Sigma.desc fun _ : ι ↦ 𝟙 a) :=
      ⟨Sigma.ι (fun _ : ι ↦ a) i, Sigma.hom_ext _ _ fun j ↦ by
        rw [Subsingleton.elim j i]; simp, by simp⟩
    infer_instance
variable [∀ W U : C, HasCoproductsOfShape (W ⟶ U) A]

variable (A) in
/-- The presheaf `W ↦ ⊕_{Hom(W, U)} a`, the left adjoint of the sections over `U` applied to
`a`. -/
@[simps]
noncomputable def sigmaYoneda (U : C) (a : A) : Cᵒᵖ ⥤ A where
  obj W := ∐ fun _ : W.unop ⟶ U ↦ a
  map f := Sigma.desc fun g ↦ Sigma.ι (fun _ : _ ⟶ U ↦ a) (f.unop ≫ g)
  map_id W := by ext g; simp
  map_comp f f' := by ext g; simp

/-- The morphism of presheaves `(W ↦ ⊕_{Hom(W, U)} a) ⟶ (W ↦ ⊕_{Hom(W, V)} a)` induced by a
morphism `p : U ⟶ V`. -/
@[simps]
noncomputable def sigmaYonedaMap {U V : C} (p : U ⟶ V) (a : A) :
    sigmaYoneda A U a ⟶ sigmaYoneda A V a where
  app W := Sigma.desc fun g ↦ Sigma.ι (fun _ : _ ⟶ V ↦ a) (g ≫ p)
  naturality W W' f := Sigma.hom_ext _ _ fun g ↦ by simp

/-- The morphism of presheaves `(W ↦ ⊕_{Hom(W, U)} P(U)) ⟶ P` given by the restrictions of `P`. -/
@[simps]
noncomputable def sigmaYonedaToObj (P : Cᵒᵖ ⥤ A) (U : C) :
    sigmaYoneda A U (P.obj (op U)) ⟶ P where
  app W := Sigma.desc fun g ↦ P.map g.op
  naturality W W' f := by
    refine Sigma.hom_ext _ _ fun g ↦ ?_
    simp only [sigmaYoneda_map, colimit.ι_desc_assoc, Discrete.functor_obj_eq_as,
      Cofan.mk_pt, Cofan.mk_ι_app, colimit.ι_desc, op_comp, Quiver.Hom.op_unop, Functor.map_comp]

/-- The morphism of presheaves `(W ↦ ⊕_{Hom(W, U)} a) ⟶ a` to the constant presheaf. -/
@[simps]
noncomputable def sigmaYonedaToConst (U : C) (a : A) :
    sigmaYoneda A U a ⟶ (Functor.const Cᵒᵖ).obj a where
  app W := Sigma.desc fun _ ↦ 𝟙 a
  naturality W W' f := Sigma.hom_ext _ _ fun g ↦ by simp

instance mono_sigmaYonedaMap {U V : C} (p : U ⟶ V) [Mono p] (a : A) :
    Mono (sigmaYonedaMap p a) := by
  have (W : Cᵒᵖ) : Mono ((sigmaYonedaMap p a).app W) := by
    classical
    refine SplitMono.mono ⟨Sigma.desc fun h ↦
      if hh : ∃ g : W.unop ⟶ U, g ≫ p = h then Sigma.ι (fun _ : W.unop ⟶ U ↦ a) hh.choose
      else 0, Sigma.hom_ext _ _ fun g ↦ ?_⟩
    have hh : ∃ g' : W.unop ⟶ U, g' ≫ p = g ≫ p := ⟨g, rfl⟩
    have hg : hh.choose = g := (cancel_mono p).1 hh.choose_spec
    simp only [sigmaYonedaMap_app, colimit.ι_desc_assoc, Discrete.functor_obj_eq_as,
      Cofan.mk_pt, Cofan.mk_ι_app, colimit.ι_desc, dite_eq_left hh, hg]
    exact (comp_id _).symm
  exact NatTrans.mono_of_mono_app _

/-- For a monomorphism `p : U ⟶ V` of the site and an injective sheaf `I`, the restriction
`I(V) ⟶ I(U)` is a split epimorphism. -/
theorem Sheaf.isSplitEpi_map_of_injective {U V : C} (p : U ⟶ V) [Mono p] (I : Sheaf J A)
    [Injective I] : IsSplitEpi (I.obj.map p.op) := by
  obtain ⟨h, hh⟩ := Sheaf.exists_comp_eq_of_injective I (sigmaYonedaMap p _)
    (sigmaYonedaToObj I.obj U)
  refine ⟨⟨Sigma.ι (fun _ : V ⟶ V ↦ I.obj.obj (op U)) (𝟙 _) ≫ h.app (op V), ?_⟩⟩
  have h₁ := Sigma.ι (fun _ : U ⟶ U ↦ I.obj.obj (op U)) (𝟙 _) ≫= congr_app hh (op U)
  rw [assoc, ← h.naturality]
  simp only [NatTrans.comp_app, sigmaYonedaMap_app, sigmaYonedaToObj_app, colimit.ι_desc_assoc,
    colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app, Discrete.functor_obj_eq_as, id_comp, op_id,
    Functor.map_id] at h₁
  simpa using h₁

/-- If every `Hom(W, U)` is a subsingleton (e.g. `U` is a subobject of a terminal object), then
for an injective sheaf `I` the restriction `Γ(I) ⟶ I(U)` is a split epimorphism. -/
theorem Sheaf.isSplitEpi_ΓRes_of_injective [HasGlobalSectionsFunctor J A] (U : C)
    [∀ W, Subsingleton (W ⟶ U)] (I : Sheaf J A) [Injective I] :
    IsSplitEpi (I.ΓRes (op U)) := by
  have : ∀ W, Mono ((sigmaYonedaToConst U (I.obj.obj (op U))).app W) := fun W ↦
    mono_sigmaDesc_id_of_subsingleton _
  have : Mono (sigmaYonedaToConst U (I.obj.obj (op U))) := NatTrans.mono_of_mono_app _
  obtain ⟨h, hh⟩ := Sheaf.exists_comp_eq_of_injective I (sigmaYonedaToConst U _)
    (sigmaYonedaToObj I.obj U)
  refine ⟨⟨Sheaf.ΓHomEquiv h, ?_⟩⟩
  have h₁ : Sheaf.ΓHomEquiv h ≫ I.ΓRes (op U) = h.app (op U) := by
    have := congr_app (Sheaf.ΓHomEquiv_naturality_left_symm (Sheaf.ΓHomEquiv h) (𝟙 _)) (op U)
    rw [comp_id, Equiv.symm_apply_apply] at this
    rw [this]
    rfl
  rw [h₁]
  have h₂ := Sigma.ι (fun _ : U ⟶ U ↦ I.obj.obj (op U)) (𝟙 _) ≫= congr_app hh (op U)
  simpa using h₂

end Injective

section ShortExact

variable [∀ W U : C, HasCoproductsOfShape (W ⟶ U) A]

/-- The short complex of a pair `p : U ⟶ V` with `p` a monomorphism is short exact on injective
sheaves. -/
theorem Sheaf.shortExactOnInjectives_pairShortComplex (p : Arrow C) [Mono p.hom] :
    (Sheaf.pairShortComplex J A p).ShortExactOnInjectives := by
  intro I _
  have := Sheaf.isSplitEpi_map_of_injective p.hom I
  have hκ := KernelFork.mapIsLimit _ (kernelIsKernel ((sheafSections J A).map p.hom.op))
    ((evaluation _ A).obj I)
  refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ hκ) ?_ ?_
  · have : Mono (kernel.ι ((sheafSections J A).map p.hom.op)) := inferInstance
    change Mono ((kernel.ι ((sheafSections J A).map p.hom.op)).app I)
    infer_instance
  · change Epi (I.obj.map p.hom.op)
    infer_instance

variable [HasGlobalSectionsFunctor J A]

/-- The short complex `Γ_U^c ⟶ Γ ⟶ Γ(U, -)` is short exact on injective sheaves if every
`Hom(W, U)` is a subsingleton. -/
theorem Sheaf.shortExactOnInjectives_ΓSupportShortComplex (U : C) [∀ W, Subsingleton (W ⟶ U)] :
    (Sheaf.ΓSupportShortComplex J A (op U)).ShortExactOnInjectives := by
  intro I _
  have := Sheaf.isSplitEpi_ΓRes_of_injective U I
  have hκ := KernelFork.mapIsLimit _ (kernelIsKernel (Sheaf.natTransΓRes J A (op U)))
    ((evaluation _ A).obj I)
  refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ hκ) ?_ ?_
  · change Mono ((Sheaf.ΓSupportι J A (op U)).app I)
    infer_instance
  · change Epi (I.ΓRes (op U))
    infer_instance

end ShortExact

omit [Abelian A] [HasSheafify J A] in
instance Arrow.mono_mk_hom {X Y : C} (f : X ⟶ Y) [Mono f] : Mono (Arrow.mk f).hom := ‹_›

section Derived

variable [∀ W U : C, HasCoproductsOfShape (W ⟶ U) A] [HasDerivedCategory (Sheaf J A)]
  [HasDerivedCategory A] [Abelian.HasKInjectiveResolutions (Sheaf J A)]
  [EnoughInjectives (Sheaf J A)]

open DerivedCategory

/-- The distinguished triangle `RΓ_{V ∖ U}(V, K) ⟶ RΓ(V, K) ⟶ RΓ(U, K) ⟶ RΓ_{V ∖ U}(V, K)[1]` of
a pair `p : U ⟶ V` with `p` a monomorphism, as a functor of the bounded below complex `K`. -/
noncomputable def Sheaf.pairRightDerivedTriangle (p : Arrow C) [Mono p.hom] :
    Plus (Sheaf J A) ⥤ Pretriangulated.Triangle (DerivedCategory A) :=
  ShortComplex.rightDerivedTriangle (Sheaf.shortExactOnInjectives_pairShortComplex J A p)

lemma Sheaf.pairRightDerivedTriangle_obj_distinguished (p : Arrow C) [Mono p.hom]
    (K : Plus (Sheaf J A)) :
    (Sheaf.pairRightDerivedTriangle J A p).obj K ∈ distTriang _ :=
  ShortComplex.rightDerivedTriangle_obj_distinguished _ K


/-- The functoriality of the triangle of a pair in morphisms of pairs `p ⟶ q`. -/
noncomputable def Sheaf.pairRightDerivedTriangleMap {p q : Arrow C} [Mono p.hom] [Mono q.hom]
    (φ : p ⟶ q) : Sheaf.pairRightDerivedTriangle J A q ⟶ Sheaf.pairRightDerivedTriangle J A p :=
  ShortComplex.rightDerivedTriangleMap _ _ (Sheaf.pairShortComplexMap J A φ)

variable [HasGlobalSectionsFunctor J A]

/-- The distinguished triangle `RΓ_U^c(K) ⟶ RΓ(K) ⟶ RΓ(U, K) ⟶ RΓ_U^c(K)[1]`, as a functor of
the bounded below complex `K`, when every `Hom(W, U)` is a subsingleton. -/
noncomputable def Sheaf.ΓSupportRightDerivedTriangle (U : C) [∀ W, Subsingleton (W ⟶ U)] :
    Plus (Sheaf J A) ⥤ Pretriangulated.Triangle (DerivedCategory A) :=
  ShortComplex.rightDerivedTriangle (Sheaf.shortExactOnInjectives_ΓSupportShortComplex J A U)

lemma Sheaf.ΓSupportRightDerivedTriangle_obj_distinguished (U : C) [∀ W, Subsingleton (W ⟶ U)]
    (K : Plus (Sheaf J A)) :
    (Sheaf.ΓSupportRightDerivedTriangle J A U).obj K ∈ distTriang _ :=
  ShortComplex.rightDerivedTriangle_obj_distinguished _ K

/-- The morphism of triangles from the triangle of `Γ_U^c ⟶ Γ ⟶ Γ(U, -)` to the triangle of a
pair `p : U' ⟶ V` with a map `U' ⟶ U`. -/
noncomputable def Sheaf.ΓSupportRightDerivedTriangleToPair (U : C) [∀ W, Subsingleton (W ⟶ U)]
    (p : Arrow C) [Mono p.hom] (g : p.left ⟶ U) :
    Sheaf.ΓSupportRightDerivedTriangle J A U ⟶ Sheaf.pairRightDerivedTriangle J A p :=
  ShortComplex.rightDerivedTriangleMap _ _ (Sheaf.ΓSupportShortComplexToPair J A p g)

end Derived

end CategoryTheory
