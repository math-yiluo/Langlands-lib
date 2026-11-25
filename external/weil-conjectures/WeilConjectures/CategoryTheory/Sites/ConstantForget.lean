/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# Sheaves of modules whose underlying sheaf of sets is constant

Let `F` be a sheaf of `Λ`-modules on a site `(C, J)`, for a finite ring `Λ`, and suppose that the
underlying sheaf of sets of `F` is the constant sheaf at a finite set `X`. Then `F` is constant
locally on a covering sieve of any object `T`
(`CategoryTheory.Sheaf.exists_mem_forall_isConstant_over_of_forget`): the sections `σ_x` of `F`
corresponding to the points `x ∈ X` are closed under the module operations after restriction
to the members of a covering sieve of `T`, because there are only finitely many sums `σ_x + σ_y`
and multiples `c • σ_x` to take care of, each of which is locally of the form `σ_z`. Over a
member `U` of this sieve, the restrictions of the `σ_x` form a submodule `N` of `F(U)`, and the
morphism from the constant sheaf at `N` to `F|_U` adjoint to the inclusion is an isomorphism,
being locally bijective.

The point of the statement is that no connectedness hypothesis is needed: on a disconnected
site a constant sheaf of sets may carry a module structure that is not constant, but it is
locally constant.
-/

@[expose] public section

universe v u w

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A finite intersection of covering sieves is a covering sieve. -/
lemma GrothendieckTopology.finsetInf_mem {T : C} {ι : Type*} (s : Finset ι) (S : ι → Sieve T)
    (h : ∀ i, S i ∈ J T) : s.inf S ∈ J T := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s _ ih =>
    rw [Finset.inf_insert]
    exact J.intersection_covering (h a) ih

namespace Sheaf

variable {J} {Λ : Type w} [Ring Λ] [HasWeakSheafify J (Type w)]
  [J.WEqualsLocallyBijective (Type w)]
  [J.HasSheafCompose (CategoryTheory.forget (ModuleCat.{w} Λ))]
  {F : Sheaf J (ModuleCat.{w} Λ)} {X : Type w}

namespace ConstantForget

variable (e : (sheafCompose J (CategoryTheory.forget (ModuleCat.{w} Λ))).obj F ≅
    (constantSheaf J (Type w)).obj X)

/-- The section of `F` over `T` corresponding to a point `x` of `X`. -/
noncomputable def σ (T : C) (x : X) : F.obj.obj (op T) :=
  e.inv.hom.app (op T) ((toSheafify J ((Functor.const Cᵒᵖ).obj X)).app (op T) x)

omit [J.WEqualsLocallyBijective (Type w)] in
lemma hom_app_map_σ {T U : C} (g : U ⟶ T) (x : X) :
    e.hom.hom.app (op U) (F.obj.map g.op (σ e T x)) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj X)).app (op U) x := by
  have h₁ := NatTrans.naturality_apply e.hom.hom g.op (σ e T x)
  have h₂ : e.hom.hom.app (op T) (σ e T x) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj X)).app (op T) x :=
    ConcreteCategory.congr_hom (Iso.inv_hom_id_app ((sheafToPresheaf J _).mapIso e) (op T)) _
  have h₃ := NatTrans.naturality_apply (toSheafify J ((Functor.const Cᵒᵖ).obj X)) g.op x
  exact h₁.trans ((congrArg _ h₂).trans h₃.symm)

omit [J.WEqualsLocallyBijective (Type w)] in
lemma injective_hom_app (U : C) : Function.Injective (e.hom.hom.app (op U)) := fun a b h ↦ by
  have h' := congrArg (e.inv.hom.app (op U)) h
  have hh : ∀ c, e.inv.hom.app (op U) (e.hom.hom.app (op U) c) = c := fun c ↦
    ConcreteCategory.congr_hom (Iso.hom_inv_id_app ((sheafToPresheaf J _).mapIso e) (op U)) c
  rwa [hh, hh] at h'

omit [J.WEqualsLocallyBijective (Type w)] in
/-- If the image of a section `t` of `F` over `T` lies in the image of `X` after restriction
along `g`, then the restriction of `t` is the restriction of some `σ_z`. -/
lemma exists_eq_map_σ {T U : C} (t : F.obj.obj (op T)) (g : U ⟶ T)
    (hg : Presheaf.imageSieve (toSheafify J ((Functor.const Cᵒᵖ).obj X))
      (e.hom.hom.app (op T) t) g) :
    ∃ z, F.obj.map g.op t = F.obj.map g.op (σ e T z) := by
  obtain ⟨z, hz⟩ := hg
  refine ⟨z, injective_hom_app e U ?_⟩
  rw [hom_app_map_σ]
  exact (NatTrans.naturality_apply e.hom.hom g.op t).trans hz.symm

end ConstantForget

open ConstantForget in
/-- **A sheaf of modules with constant underlying sheaf of sets is locally constant.** Let `F` be
a sheaf of `Λ`-modules over a finite ring `Λ` whose underlying sheaf of sets is the constant sheaf
at a finite set `X`. Then for every object `T` there is a covering sieve of `T` over whose members
`U` the restriction `F|_U` is a constant sheaf of modules. -/
theorem exists_mem_forall_isConstant_over_of_forget [Finite Λ] [Finite X]
    (e : (sheafCompose J (CategoryTheory.forget (ModuleCat.{w} Λ))).obj F ≅
      (constantSheaf J (Type w)).obj X) (T : C)
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
    [∀ U : C, (J.over U).WEqualsLocallyBijective (ModuleCat.{w} Λ)]
    [∀ U : C, (J.over U).HasSheafCompose (CategoryTheory.forget (ModuleCat.{w} Λ))] :
    ∃ S ∈ J T, ∀ ⦃U : C⦄ (f : U ⟶ T), S f → (F.over U).IsConstant (J.over U) := by
  classical
  let : Fintype ((X × X) ⊕ (Λ × X) ⊕ Unit) := Fintype.ofFinite _
  -- the finitely many sections whose restrictions have to be of the form `σ_z`
  let t : (X × X) ⊕ (Λ × X) ⊕ Unit → F.obj.obj (op T)
    | .inl p => σ e T p.1 + σ e T p.2
    | .inr (.inl p) => p.1 • σ e T p.2
    | .inr (.inr _) => 0
  let Si : (X × X) ⊕ (Λ × X) ⊕ Unit → Sieve T := fun i ↦
    Presheaf.imageSieve (toSheafify J ((Functor.const Cᵒᵖ).obj X)) (e.hom.hom.app (op T) (t i))
  have hSi : ∀ i, Si i ∈ J T := fun i ↦ Presheaf.imageSieve_mem J _ _
  refine ⟨Finset.univ.inf Si, J.finsetInf_mem _ _ hSi, fun U f hf ↦ ?_⟩
  have hf' : ∀ i, ∃ z, F.obj.map f.op (t i) = F.obj.map f.op (σ e T z) := fun i ↦
    exists_eq_map_σ e (t i) f (Finset.inf_le (Finset.mem_univ i) (f := Si) _ hf)
  let ρ : F.obj.obj (op T) →ₗ[Λ] F.obj.obj (op U) := (F.obj.map f.op).hom
  -- the restrictions of the `σ_x` form a submodule `N` of `F(U)`
  let N : Submodule Λ (F.obj.obj (op U)) :=
    { carrier := Set.range fun x ↦ ρ (σ e T x)
      add_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        obtain ⟨z, hz⟩ := hf' (.inl (x, y))
        exact ⟨z, by rw [← map_add]; exact hz.symm⟩
      zero_mem' := by
        obtain ⟨z, hz⟩ := hf' (.inr (.inr ()))
        exact ⟨z, by rw [← map_zero ρ]; exact hz.symm⟩
      smul_mem' := by
        rintro c _ ⟨x, rfl⟩
        obtain ⟨z, hz⟩ := hf' (.inr (.inl (c, x)))
        exact ⟨z, by rw [← map_smul]; exact hz.symm⟩ }
  -- the morphism from the constant presheaf at `N` to `F|_U`
  let α : (Functor.const (Over U)ᵒᵖ).obj (ModuleCat.of Λ N) ⟶ (F.over U).obj :=
    { app V := ModuleCat.ofHom ((F.obj.map V.unop.hom.op).hom ∘ₗ N.subtype)
      naturality V W g := by
        ext n
        change F.obj.map W.unop.hom.op n.1 = F.obj.map g.unop.left.op (F.obj.map V.unop.hom.op n.1)
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Over.w] }
  let φ : (constantSheaf (J.over U) (ModuleCat.{w} Λ)).obj (ModuleCat.of Λ N) ⟶ F.over U :=
    ⟨sheafifyLift (J.over U) α (F.over U).property⟩
  have hφ : toSheafify (J.over U) _ ≫ φ.hom = α := toSheafify_sheafifyLift _ _ _
  -- the restriction of the sheafification map of the constant presheaf at `X`
  let τ := Functor.whiskerLeft (Over.forget U).op
    (toSheafify J ((Functor.const Cᵒᵖ).obj X))
  have : Presheaf.IsLocallyInjective J (toSheafify J ((Functor.const Cᵒᵖ).obj X)) :=
    (J.W_toSheafify _).isLocallyInjective
  have : Presheaf.IsLocallySurjective J (toSheafify J ((Functor.const Cᵒᵖ).obj X)) :=
    (J.W_toSheafify _).isLocallySurjective
  have hτi : Presheaf.IsLocallyInjective (J.over U) τ :=
    Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) _
  have hτs : Presheaf.IsLocallySurjective (J.over U) τ :=
    Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) _
  -- the value of `α` on the restriction of `σ_x`
  have hα (V : (Over U)ᵒᵖ) (x : X) :
      e.hom.hom.app (op V.unop.left) (α.app V ⟨ρ (σ e T x), x, rfl⟩) = τ.app V x := by
    change e.hom.hom.app (op V.unop.left)
      (F.obj.map V.unop.hom.op (F.obj.map f.op (σ e T x))) = _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    exact hom_app_map_σ e _ x
  have hαi : Presheaf.IsLocallyInjective (J.over U) α := by
    refine ⟨fun {V} n₁ n₂ h ↦ ?_⟩
    obtain ⟨x₁, hx₁⟩ := n₁.2
    obtain ⟨x₂, hx₂⟩ := n₂.2
    have e₁ : n₁ = ⟨ρ (σ e T x₁), x₁, rfl⟩ := Subtype.ext hx₁.symm
    have e₂ : n₂ = ⟨ρ (σ e T x₂), x₂, rfl⟩ := Subtype.ext hx₂.symm
    have h' : τ.app V x₁ = τ.app V x₂ := by
      rw [← hα, ← hα, ← e₁, ← e₂, h]
    refine J.over U |>.superset_covering ?_ (Presheaf.equalizerSieve_mem _ τ x₁ x₂ h')
    intro W g (hg : x₁ = x₂)
    change ((Functor.const (Over U)ᵒᵖ).obj (ModuleCat.of Λ N)).map g.op n₁ =
      ((Functor.const (Over U)ᵒᵖ).obj (ModuleCat.of Λ N)).map g.op n₂
    rw [e₁, e₂, hg]
  have hαs : Presheaf.IsLocallySurjective (J.over U) α := by
    refine ⟨fun {V} s ↦ ?_⟩
    refine J.over U |>.superset_covering ?_
      (Presheaf.imageSieve_mem _ τ (e.hom.hom.app (op V.left) s))
    rintro W g ⟨x, hx⟩
    refine ⟨⟨ρ (σ e T x), x, rfl⟩, injective_hom_app e W.left ?_⟩
    rw [hα]
    exact hx.trans (NatTrans.naturality_apply e.hom.hom g.left.op s).symm
  have : Presheaf.IsLocallyInjective (J.over U)
      (toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj (ModuleCat.of Λ N))) :=
    ((J.over U).W_toSheafify _).isLocallyInjective
  have : Presheaf.IsLocallySurjective (J.over U)
      (toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj (ModuleCat.of Λ N))) :=
    ((J.over U).W_toSheafify _).isLocallySurjective
  have : IsIso φ := by
    rw [← Sheaf.isLocallyBijective_iff_isIso φ]
    rw [← hφ] at hαi hαs
    exact ⟨(Presheaf.comp_isLocallyInjective_iff _ _ _).mp hαi,
      (Presheaf.comp_isLocallySurjective_iff _ _ _).mp hαs⟩
  exact isConstant_of_iso _ (asIso φ).symm

end Sheaf

end CategoryTheory
