/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.RepresentationTheory.Rep.Basic
public import WeilConjectures.Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Equivariant evaluation of sheaves at a point with a group action

Let `C` be a category, `T` an object of `C` and `a : H →* (End T)ᵐᵒᵖ` a right action of a group
`H` on `T`. For a presheaf `F` of `Λ`-modules on `C`, the group `H` acts (on the left) on
`F(T)` by `h ↦ F(a h)`; this gives the *equivariant evaluation* functor
`CategoryTheory.Presheaf.evaluationRep` from presheaves of `Λ`-modules to `Λ`-linear
representations of `H`. It has a right adjoint `CategoryTheory.Presheaf.coevaluationRep`,
sending a representation `M` to the presheaf `W ↦ Hom_H(Hom(T, W), M)` of equivariant functions.

If every covering sieve of `T` for a Grothendieck topology `J` contains the identity, then
`Hom_H(Hom(T, -), M)` is a sheaf, and the adjunction restricts to sheaves
(`CategoryTheory.Sheaf.evaluationRepAdjunction`). If moreover every object is covered by objects
`W` on which `H` acts freely on `Hom(T, W)`, then the right adjoint is exact
(`CategoryTheory.Sheaf.preservesFiniteColimits_coevaluationRep`).

## Main definitions

- `CategoryTheory.Presheaf.evaluationRep`, `CategoryTheory.Presheaf.coevaluationRep` and the
  adjunction `CategoryTheory.Presheaf.evaluationRepAdjunction` between them.
- `CategoryTheory.Sheaf.evaluationRep`, `CategoryTheory.Sheaf.coevaluationRep` and the
  adjunction `CategoryTheory.Sheaf.evaluationRepAdjunction` between them.

## Main statements

- `CategoryTheory.Sheaf.preservesFiniteColimits_evaluationRep`: the equivariant evaluation is
  exact if evaluation at `T` preserves epimorphisms.
- `CategoryTheory.Sheaf.preservesFiniteColimits_coevaluationRep`: its right adjoint is exact if
  `H` acts freely on `Hom(T, W)` for the objects `W` of a covering of every object.
- `CategoryTheory.Sheaf.evaluationRepConstantSheafIso`: the equivariant evaluation of a constant
  sheaf is a trivial representation, if sheafification is bijective at `T`.
-/

@[expose] public section

universe w' w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {T : C} {H : Type*} [Group H] (a : H →* (End T)ᵐᵒᵖ)
  (Λ : Type w') [CommRing Λ]

lemma End.unop_map_mul (g h : H) :
    (a (g * h)).unop.asHom = (a g).unop.asHom ≫ (a h).unop.asHom := by
  rw [map_mul, MulOpposite.unop_mul, End.mul_asHom]

namespace Presheaf

/-- The representation `h ↦ F(a h)` of `H` on the sections `F(T)` of a presheaf of modules. -/
@[simps]
noncomputable def sectionsRepresentation (F : Cᵒᵖ ⥤ ModuleCat.{w} Λ) :
    Representation Λ H (F.obj (op T)) where
  toFun h := (F.map (Quiver.Hom.op (a h).unop.asHom)).hom
  map_one' := by
    rw [map_one, MulOpposite.unop_one, End.one_asHom]
    exact congrArg ModuleCat.Hom.hom (F.map_id (op T))
  map_mul' g h := by
    rw [End.unop_map_mul, op_comp, F.map_comp, ModuleCat.hom_comp]
    rfl

/-- The equivariant evaluation at `T`: a presheaf `F` of modules is sent to `F(T)`, with the
action `h ↦ F(a h)` of `H`. -/
@[simps obj]
noncomputable def evaluationRep : (Cᵒᵖ ⥤ ModuleCat.{w} Λ) ⥤ Rep.{w} Λ H where
  obj F := Rep.of (sectionsRepresentation a Λ F)
  map {F G} f := Rep.ofHom ⟨(f.app (op T)).hom, fun h ↦
    congrArg ModuleCat.Hom.hom (f.naturality (Quiver.Hom.op (a h).unop.asHom))⟩

@[simp]
lemma evaluationRep_map_hom_apply {F G : Cᵒᵖ ⥤ ModuleCat.{w} Λ} (f : F ⟶ G)
    (x : F.obj (op T)) : ((evaluationRep a Λ).map f).hom x = f.app (op T) x :=
  rfl

/-- The `H`-equivariant functions `Hom(T, W) → M`, for the action `h • t = a h ≫ t` on
`Hom(T, W)`. -/
def equivariantFunctions (M : Rep.{w} Λ H) (W : C) : Submodule Λ ((T ⟶ W) → M) where
  carrier := {s | ∀ h t, s ((a h).unop.asHom ≫ t) = M.ρ h (s t)}
  add_mem' {s s'} hs hs' h t := by simp [hs h t, hs' h t]
  zero_mem' h t := by simp
  smul_mem' c s hs h t := by simp [hs h t]

lemma mem_equivariantFunctions {M : Rep.{w} Λ H} {W : C} {s : (T ⟶ W) → M} :
    s ∈ equivariantFunctions a Λ M W ↔ ∀ h t, s ((a h).unop.asHom ≫ t) = M.ρ h (s t) :=
  Iff.rfl

/-- The presheaf `W ↦ Hom_H(Hom(T, W), M)` of equivariant functions, with restriction given by
precomposition. -/
@[simps obj]
noncomputable def coevaluationRepObj (M : Rep.{max v w} Λ H) : Cᵒᵖ ⥤ ModuleCat.{max v w} Λ where
  obj W := ModuleCat.of Λ (equivariantFunctions a Λ M W.unop)
  map {W W'} f := ModuleCat.ofHom ((LinearMap.funLeft Λ M (· ≫ f.unop)).restrict
    fun s hs h t ↦ by simpa [LinearMap.funLeft] using hs h (t ≫ f.unop))
  map_id W := by
    ext s t
    simp [LinearMap.funLeft]
  map_comp f g := by
    ext s t
    simp [LinearMap.funLeft]

@[simp]
lemma coevaluationRepObj_map_apply (M : Rep.{max v w} Λ H) {W W' : Cᵒᵖ} (f : W ⟶ W')
    (s : equivariantFunctions a Λ M W.unop) (t : T ⟶ W'.unop) :
    ((coevaluationRepObj a Λ M).map f s).1 t = s.1 (t ≫ f.unop) :=
  rfl

/-- The right adjoint of the equivariant evaluation: a representation `M` is sent to the
presheaf `W ↦ Hom_H(Hom(T, W), M)` of equivariant functions. -/
@[simps obj]
noncomputable def coevaluationRep : Rep.{max v w} Λ H ⥤ (Cᵒᵖ ⥤ ModuleCat.{max v w} Λ) where
  obj M := coevaluationRepObj a Λ M
  map {M N} f :=
    { app W := ModuleCat.ofHom ((LinearMap.compLeft f.hom.toLinearMap _).restrict
        fun s hs h t ↦ by simpa [hs h t] using Rep.hom_comm_apply f h (s t))
      naturality W W' g := by
        ext s
        rfl }

@[simp]
lemma coevaluationRep_map_app_apply {M N : Rep.{max v w} Λ H} (f : M ⟶ N) (W : Cᵒᵖ)
    (s : equivariantFunctions a Λ M W.unop) (t : T ⟶ W.unop) :
    (((coevaluationRep a Λ).map f).app W s).1 t = f.hom (s.1 t) :=
  rfl

variable {a Λ} in
/-- The linear map `F(W) → Hom_H(Hom(T, W), M)`, `x ↦ (t ↦ α(F(t) x))`, attached to an
`H`-equivariant map `α : F(T) → M`. -/
noncomputable def evaluationRepHomEquivToFunApp {F : Cᵒᵖ ⥤ ModuleCat.{max v w} Λ}
    {M : Rep.{max v w} Λ H} (α : (evaluationRep a Λ).obj F ⟶ M) (W : Cᵒᵖ) :
    F.obj W →ₗ[Λ] equivariantFunctions a Λ M W.unop :=
  LinearMap.codRestrict _
    (LinearMap.pi fun t : T ⟶ W.unop ↦ α.hom.toLinearMap ∘ₗ (F.map t.op).hom) fun x h t ↦ by
      simp only [LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, op_comp,
        F.map_comp, ModuleCat.hom_comp]
      exact Rep.hom_comm_apply α h _

@[simp]
lemma evaluationRepHomEquivToFunApp_apply {F : Cᵒᵖ ⥤ ModuleCat.{max v w} Λ}
    {M : Rep.{max v w} Λ H} (α : (evaluationRep a Λ).obj F ⟶ M) (W : Cᵒᵖ) (x : F.obj W)
    (t : T ⟶ W.unop) :
    (evaluationRepHomEquivToFunApp α W x).1 t = α.hom (F.map t.op x) :=
  rfl

variable {a Λ} in
/-- The morphism of presheaves `F ⟶ Hom_H(Hom(T, -), M)`, `x ↦ (t ↦ α(F(t) x))`, attached to
an `H`-equivariant map `α : F(T) → M`. -/
noncomputable def evaluationRepHomEquivToFun {F : Cᵒᵖ ⥤ ModuleCat.{max v w} Λ}
    {M : Rep.{max v w} Λ H} (α : (evaluationRep a Λ).obj F ⟶ M) :
    F ⟶ (coevaluationRep a Λ).obj M where
  app W := ModuleCat.ofHom (evaluationRepHomEquivToFunApp α W)
  naturality W W' f := by
    ext x
    exact Subtype.ext (funext fun t ↦
      (congrArg α.hom (ConcreteCategory.congr_hom (F.map_comp f t.op) x)).symm)

variable {a Λ} in
/-- The `H`-equivariant map `F(T) → M`, `x ↦ β(x)(𝟙 T)`, attached to a morphism of presheaves
`β : F ⟶ Hom_H(Hom(T, -), M)`. -/
noncomputable def evaluationRepHomEquivInvFun {F : Cᵒᵖ ⥤ ModuleCat.{max v w} Λ}
    {M : Rep.{max v w} Λ H} (β : F ⟶ (coevaluationRep a Λ).obj M) :
    (evaluationRep a Λ).obj F ⟶ M :=
  Rep.ofHom ⟨(LinearMap.proj (𝟙 T)).comp ((equivariantFunctions a Λ M T).subtype.comp
    (β.app (op T)).hom), fun h ↦ by
      ext x
      have hβ := congrArg (fun s : equivariantFunctions a Λ M T ↦ s.1 (𝟙 T))
        (ConcreteCategory.congr_hom (β.naturality (Quiver.Hom.op (a h).unop.asHom)) x)
      have hx := (β.app (op T) x).2 h (𝟙 T)
      rw [Category.comp_id] at hx
      exact hβ.trans ((congrArg (β.app (op T) x).1 (Category.id_comp _)).trans hx)⟩

@[simp]
lemma evaluationRepHomEquivInvFun_hom_apply {F : Cᵒᵖ ⥤ ModuleCat.{max v w} Λ}
    {M : Rep.{max v w} Λ H} (β : F ⟶ (coevaluationRep a Λ).obj M) (x : F.obj (op T)) :
    (evaluationRepHomEquivInvFun β).hom x = (β.app (op T) x).1 (𝟙 T) :=
  rfl

/-- The adjunction between the equivariant evaluation at `T` and the presheaf of equivariant
functions on `Hom(T, -)`. -/
noncomputable def evaluationRepAdjunction :
    (evaluationRep a Λ : (Cᵒᵖ ⥤ ModuleCat.{max v w} Λ) ⥤ Rep.{max v w} Λ H) ⊣
      coevaluationRep a Λ :=
  Adjunction.mkOfHomEquiv
    { homEquiv F M :=
        { toFun := evaluationRepHomEquivToFun
          invFun := evaluationRepHomEquivInvFun
          left_inv α := by
            ext x
            exact congrArg α.hom (ConcreteCategory.congr_hom (F.map_id (op T)) x)
          right_inv β := by
            ext W x
            refine Subtype.ext (funext fun t ↦ ?_)
            have hβ := congrArg (fun s : equivariantFunctions a Λ M T ↦ s.1 (𝟙 T))
              (ConcreteCategory.congr_hom (β.naturality t.op) x)
            exact hβ.trans (congrArg (β.app W x).1 (Category.id_comp t)) }
      homEquiv_naturality_left_symm f g := by
        ext x
        rfl
      homEquiv_naturality_right f g := by
        ext W x
        rfl }
instance : (evaluationRep a Λ : (Cᵒᵖ ⥤ ModuleCat.{w} Λ) ⥤ Rep.{w} Λ H).Additive where
  map_add := rfl

/-- The equivariant evaluation at `T` followed by the forgetful functor is the evaluation at
`T`. -/
noncomputable def evaluationRepCompForgetIso :
    (evaluationRep a Λ : (Cᵒᵖ ⥤ ModuleCat.{w} Λ) ⥤ Rep.{w} Λ H) ⋙
      forget₂ (Rep.{w} Λ H) (ModuleCat.{w} Λ) ≅ (evaluation _ _).obj (op T) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

instance : PreservesFiniteLimits
    (evaluationRep a Λ : (Cᵒᵖ ⥤ ModuleCat.{w} Λ) ⥤ Rep.{w} Λ H) := by
  have := preservesFiniteLimits_of_natIso (evaluationRepCompForgetIso a Λ).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (forget₂ (Rep.{w} Λ H) (ModuleCat Λ))

instance : PreservesFiniteColimits
    (evaluationRep a Λ : (Cᵒᵖ ⥤ ModuleCat.{w} Λ) ⥤ Rep.{w} Λ H) := by
  have := preservesFiniteColimits_of_natIso (evaluationRepCompForgetIso a Λ).symm
  exact preservesFiniteColimits_of_reflects_of_preserves _ (forget₂ (Rep.{w} Λ H) (ModuleCat Λ))

end Presheaf

namespace Sheaf

variable (J : GrothendieckTopology C)

/-- The equivariant evaluation at `T` of sheaves of modules: a sheaf `F` is sent to `F(T)`, with
the action `h ↦ F(a h)` of `H`. -/
noncomputable abbrev evaluationRep : Sheaf J (ModuleCat.{w} Λ) ⥤ Rep.{w} Λ H :=
  sheafToPresheaf J _ ⋙ Presheaf.evaluationRep a Λ

variable {J} in
/-- If every covering sieve of `T` contains the identity, then the presheaf
`W ↦ Hom_H(Hom(T, W), M)` is a sheaf: a section over `W` is glued from a compatible family on a
covering sieve `S` of `W` by evaluating the member of the family at `t ∈ S`, for each
`t : T ⟶ W`. -/
lemma isSheaf_coevaluationRepObj (hT : ∀ ⦃S : Sieve T⦄, S ∈ J T → S (𝟙 T))
    (M : Rep.{max u v} Λ H) : Presheaf.IsSheaf J (Presheaf.coevaluationRepObj a Λ M) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget J _ (forget (ModuleCat.{max u v} Λ)),
    isSheaf_iff_isSheaf_of_type]
  intro W S hS x hx
  have hmem (t : T ⟶ W) : S t := by simpa using hT (J.pullback_stable t hS)
  rw [Presieve.compatible_iff_sieveCompatible] at hx
  refine ⟨⟨fun t ↦ (x t (hmem t)).1 (𝟙 T), fun h t ↦ ?_⟩, fun Y f hf ↦ ?_, fun y hy ↦ ?_⟩
  · have h₁ := congrArg (fun s : Presheaf.equivariantFunctions a Λ M T ↦ s.1 (𝟙 T))
      (hx t (a h).unop.asHom (hmem t))
    exact h₁.trans ((congrArg (x t (hmem t)).1
      ((Category.id_comp _).trans (Category.comp_id _).symm)).trans ((x t (hmem t)).2 h (𝟙 T)))
  · exact Subtype.ext (funext fun t ↦
      (congrArg (fun s : Presheaf.equivariantFunctions a Λ M T ↦ s.1 (𝟙 T)) (hx f t hf)).trans
        (congrArg (x f hf).1 (Category.id_comp t)))
  · exact Subtype.ext (funext fun t ↦ (congrArg y.1 (Category.id_comp t)).symm.trans
      (congrArg (fun s : Presheaf.equivariantFunctions a Λ M T ↦ s.1 (𝟙 T)) (hy t (hmem t))))

variable {J} in
/-- The right adjoint of the equivariant evaluation at `T` on sheaves, if every covering sieve
of `T` contains the identity: a representation `M` is sent to the sheaf
`W ↦ Hom_H(Hom(T, W), M)` of equivariant functions. -/
noncomputable def coevaluationRep (hT : ∀ ⦃S : Sieve T⦄, S ∈ J T → S (𝟙 T)) :
    Rep.{max u v} Λ H ⥤ Sheaf J (ModuleCat.{max u v} Λ) :=
  ObjectProperty.lift _ (Presheaf.coevaluationRep a Λ) (isSheaf_coevaluationRepObj a Λ hT)

variable {J} in
/-- The adjunction between the equivariant evaluation at `T` and the sheaf of equivariant
functions on `Hom(T, -)`. -/
noncomputable def evaluationRepAdjunction (hT : ∀ ⦃S : Sieve T⦄, S ∈ J T → S (𝟙 T)) :
    evaluationRep a Λ J ⊣ coevaluationRep a Λ hT :=
  (Presheaf.evaluationRepAdjunction a Λ).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf J _) (Functor.FullyFaithful.id _) (Functor.rightUnitor _).symm
    (Functor.leftUnitor _ ≪≫ (ObjectProperty.liftCompιIso _ _ _).symm)

instance (hT : ∀ ⦃S : Sieve T⦄, S ∈ J T → S (𝟙 T)) : (coevaluationRep a Λ hT).Additive where
  map_add {M N f g} := by
    ext W s
    rfl

instance (hT : ∀ ⦃S : Sieve T⦄, S ∈ J T → S (𝟙 T)) :
    PreservesFiniteLimits (coevaluationRep a Λ hT) :=
  have := (evaluationRepAdjunction a Λ hT).isRightAdjoint
  inferInstance

/-- The equivariant evaluation is exact if evaluation at `T` preserves epimorphisms. -/
lemma preservesFiniteColimits_evaluationRep [HasSheafify J (ModuleCat.{w} Λ)]
    [((sheafSections J (ModuleCat.{w} Λ)).obj (op T)).PreservesEpimorphisms] :
    PreservesFiniteColimits (evaluationRep a Λ J : Sheaf J (ModuleCat.{w} Λ) ⥤ _) := by
  have : (evaluationRep a Λ J : Sheaf J (ModuleCat.{w} Λ) ⥤ _).PreservesEpimorphisms :=
    ⟨fun {F G} f _ ↦ (Rep.epi_iff_surjective _).2 ((ModuleCat.epi_iff_surjective _).1
      (((sheafSections J (ModuleCat.{w} Λ)).obj (op T)).map_epi f))⟩
  have := Functor.preservesHomology_of_preservesEpis_and_kernels
    (evaluationRep a Λ J : Sheaf J (ModuleCat.{w} Λ) ⥤ _)
  exact Functor.preservesFiniteColimits_of_preservesHomology _

variable {J a Λ} in
/-- If `H` acts freely on `Hom(T, W)` for the objects `W` of a covering of every object, then the
sheaf of equivariant functions sends epimorphisms to locally surjective morphisms: an
equivariant function on a free `H`-set lifts along a surjection. -/
lemma isLocallySurjective_coevaluationRep_map (hT : ∀ ⦃S : Sieve T⦄, S ∈ J T → S (𝟙 T))
    (hfree : ∀ W : C, ∃ S ∈ J W, ∀ ⦃W' : C⦄ (f : W' ⟶ W), S f →
      ∀ (h : H) (t : T ⟶ W'), (a h).unop.asHom ≫ t = t → h = 1)
    {M N : Rep.{max u v} Λ H} (π : M ⟶ N) [Epi π] :
    Sheaf.IsLocallySurjective ((coevaluationRep a Λ hT).map π) := by
  refine ⟨fun {W} s ↦ ?_⟩
  obtain ⟨S, hS, hSfree⟩ := hfree W
  refine J.superset_covering (fun W' f hf ↦ ?_) hS
  let := MulAction.compHom (T ⟶ W') a
  obtain ⟨s', hs', hπs'⟩ := MulAction.exists_equivariant_lift_of_free (hSfree f hf)
    (fun h m ↦ M.ρ h m) (fun g h m ↦ by rw [map_mul, Module.End.mul_apply])
    (fun h n ↦ N.ρ h n) π.hom ((Rep.epi_iff_surjective π).1 inferInstance)
    (fun h m ↦ Rep.hom_comm_apply π h m) (fun t ↦ s.1 (t ≫ f))
    (fun h t ↦ by
      rw [← s.2 h (t ≫ f), ← Category.assoc]
      rfl)
  exact ⟨⟨s', fun h t ↦ hs' h t⟩, Subtype.ext (funext hπs')⟩

/-- If every covering sieve of `T` contains the identity and `H` acts freely on `Hom(T, W)` for
the objects `W` of a covering of every object, then the sheaf of equivariant functions is
exact. -/
lemma preservesFiniteColimits_coevaluationRep [HasSheafify J (ModuleCat.{max u v} Λ)]
    (hT : ∀ ⦃S : Sieve T⦄, S ∈ J T → S (𝟙 T))
    (hfree : ∀ W : C, ∃ S ∈ J W, ∀ ⦃W' : C⦄ (f : W' ⟶ W), S f →
      ∀ (h : H) (t : T ⟶ W'), (a h).unop.asHom ≫ t = t → h = 1) :
    PreservesFiniteColimits (coevaluationRep a Λ hT) := by
  have : (coevaluationRep a Λ hT).PreservesEpimorphisms :=
    ⟨fun π _ ↦ have := isLocallySurjective_coevaluationRep_map hT hfree π
      inferInstance⟩
  have := Functor.preservesHomology_of_preservesEpis_and_kernels (coevaluationRep a Λ hT)
  exact Functor.preservesFiniteColimits_of_preservesHomology _

/-- The equivariant evaluation of a constant sheaf `X` is the trivial representation on `X`, if
the map from the constant presheaf to its sheafification is bijective at `T`. -/
noncomputable def evaluationRepConstantSheafIso [HasWeakSheafify J (ModuleCat.{w} Λ)]
    (X : ModuleCat.{w} Λ)
    (hX : Function.Bijective ((toSheafify J ((Functor.const Cᵒᵖ).obj X)).app (op T))) :
    (evaluationRep a Λ J).obj ((constantSheaf J _).obj X) ≅ Rep.trivial Λ H X :=
  (Rep.mkIso (Representation.Equiv.mk
    (LinearEquiv.ofBijective ((toSheafify J ((Functor.const Cᵒᵖ).obj X)).app (op T)).hom hX)
    fun h ↦ LinearMap.ext fun x ↦
      ConcreteCategory.congr_hom
        ((toSheafify J _).naturality (Quiver.Hom.op (a h).unop.asHom)) x)).symm

end Sheaf

end CategoryTheory
