/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Descent
public import WeilConjectures.AlgebraicGeometry.Modules.FpqcSections
public import WeilConjectures.AlgebraicGeometry.Picard.NormalizedDescent
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Descent.IsPrestack
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Homomorphisms and isomorphisms of modules on the small étale site

For quasi-coherent `𝒪_X`-modules `M` and `N`, the presheaf `V ↦ Hom(V^* M, V^* N)` on schemes
over `X` is a sheaf for the fpqc topology; this is the full faithfulness part of fpqc descent
for quasi-coherent modules (`AlgebraicGeometry.bijective_toDescentData_map_of_mem_fpqcTopology`).
Restricting to the small étale site gives the étale sheaves
`AlgebraicGeometry.Scheme.Modules.etaleHom M N` and
`AlgebraicGeometry.Scheme.Modules.etaleIso M N` of homomorphisms and isomorphisms.

## Main statements

- `AlgebraicGeometry.isSheaf_presheafHom`: `Hom(- ^* M, - ^* N)` is an fpqc sheaf.
- `AlgebraicGeometry.Scheme.Modules.isSheaf_etaleHom`,
  `AlgebraicGeometry.Scheme.Modules.isSheaf_etaleIso`: the étale sheaves of homomorphisms and
  isomorphisms.
- `CategoryTheory.Pseudofunctor.isIso_of_isIso_presheafHom_map`: being an isomorphism is local
  for a pseudofunctor whose presheaves of morphisms are separated and glue.
-/

@[expose] public section

universe u

open CategoryTheory Opposite CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry

section

variable {C : Type*} [Category C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat} {S : C}

open Pseudofunctor.LocallyDiscreteOpToCat

lemma _root_.CategoryTheory.Pseudofunctor.presheafHom_map_comp {M N K : F.obj (.mk (op S))}
    {T T' : Over S} (g : T' ⟶ T) (φ : (F.presheafHom M N).obj (op T))
    (ψ : (F.presheafHom N K).obj (op T)) :
    (F.presheafHom M K).map g.op (φ ≫ ψ) =
      (F.presheafHom M N).map g.op φ ≫ (F.presheafHom N K).map g.op ψ :=
  pullHom_comp _ _ _ _ _ _

lemma _root_.CategoryTheory.Pseudofunctor.presheafHom_map_id {M : F.obj (.mk (op S))}
    {T T' : Over S} (g : T' ⟶ T) :
    (F.presheafHom M M).map g.op (𝟙 _) = 𝟙 _ :=
  pullHom_id_eq_id _ _

instance _root_.CategoryTheory.Pseudofunctor.isIso_presheafHom_map {M N : F.obj (.mk (op S))}
    {T T' : Over S} (g : T' ⟶ T) (φ : (F.presheafHom M N).obj (op T)) [IsIso φ] :
    IsIso ((F.presheafHom M N).map g.op φ) :=
  isIso_pullHom _ _ _ _ (Over.w g) (Over.w g)

variable {D : Type*} [Category D] (G : D ⥤ Over S)

lemma _root_.CategoryTheory.Pseudofunctor.isIso_of_isIso_presheafHom_map
    {M N : F.obj (.mk (op S))} {V : D} (φ : (G.op ⋙ F.presheafHom M N).obj (op V))
    {R : Sieve V} (hNM : Presieve.IsSheafFor (G.op ⋙ F.presheafHom N M) R.arrows)
    (hMM : Presieve.IsSheafFor (G.op ⋙ F.presheafHom M M) R.arrows)
    (hNN : Presieve.IsSheafFor (G.op ⋙ F.presheafHom N N) R.arrows)
    (h : ∀ ⦃W : D⦄ (g : W ⟶ V), R g → IsIso ((F.presheafHom M N).map (G.map g).op φ)) :
    IsIso φ := by
  let x : Presieve.FamilyOfElements (G.op ⋙ F.presheafHom N M) R.arrows := fun W g hg ↦
    haveI := h g hg
    inv ((F.presheafHom M N).map (G.map g).op φ)
  have key {W : D} (g : W ⟶ V) [IsIso ((F.presheafHom M N).map (G.map g).op φ)] {Z : D}
      (f : Z ⟶ W) [IsIso ((F.presheafHom M N).map (G.map (f ≫ g)).op φ)] :
      (F.presheafHom N M).map (G.map f).op (inv ((F.presheafHom M N).map (G.map g).op φ)) =
        inv ((F.presheafHom M N).map (G.map (f ≫ g)).op φ) := by
    apply IsIso.eq_inv_of_hom_inv_id
    rw [G.map_comp, op_comp, Functor.map_comp, types_comp_apply,
      ← Pseudofunctor.presheafHom_map_comp, IsIso.hom_inv_id, Pseudofunctor.presheafHom_map_id]
  have hx : x.Compatible := by
    intro W₁ W₂ Z f₁ f₂ g₁ g₂ hg₁ hg₂ fac
    have := h g₁ hg₁
    have := h g₂ hg₂
    have := h (f₁ ≫ g₁) (R.downward_closed hg₁ f₁)
    have := h (f₂ ≫ g₂) (R.downward_closed hg₂ f₂)
    change (F.presheafHom N M).map (G.map f₁).op (inv ((F.presheafHom M N).map (G.map g₁).op φ)) =
      (F.presheafHom N M).map (G.map f₂).op (inv ((F.presheafHom M N).map (G.map g₂).op φ))
    rw [key, key]
    congr 3
    rw [fac]
  obtain ⟨ψ, hψ, -⟩ := hNM x hx
  refine ⟨ψ, hMM.isSeparatedFor.ext fun W g hg ↦ ?_, hNN.isSeparatedFor.ext fun W g hg ↦ ?_⟩
  · have := h g hg
    change (F.presheafHom M M).map (G.map g).op (φ ≫ ψ) =
      (F.presheafHom M M).map (G.map g).op (𝟙 _)
    rw [Pseudofunctor.presheafHom_map_comp, Pseudofunctor.presheafHom_map_id]
    erw [hψ g hg]
    exact IsIso.hom_inv_id _
  · have := h g hg
    change (F.presheafHom N N).map (G.map g).op (ψ ≫ φ) =
      (F.presheafHom N N).map (G.map g).op (𝟙 _)
    rw [Pseudofunctor.presheafHom_map_comp, Pseudofunctor.presheafHom_map_id]
    erw [hψ g hg]
    exact IsIso.inv_hom_id _

/-- The subpresheaf of isomorphisms in `G.op ⋙ F.presheafHom M N`. -/
def _root_.CategoryTheory.Pseudofunctor.presheafIso (M N : F.obj (.mk (op S))) :
    Subfunctor (G.op ⋙ F.presheafHom M N) where
  obj _ := {φ | IsIso φ}
  map {_ _} g φ (_ : IsIso φ) :=
    Pseudofunctor.isIso_presheafHom_map (G.map g.unop) φ

end

/-- Multiplication by a global function, as an endomorphism in `modulesPseudofunctor`. -/
noncomputable def smulMor {Y : Scheme.{u}} (A : modulesPseudofunctor.obj (.mk (op Y)))
    (a : Γ(Y, ⊤)) : A ⟶ A :=
  Scheme.Modules.smulHom (A : Y.Modules) a

lemma smulMor_one {Y : Scheme.{u}} (A : modulesPseudofunctor.obj (.mk (op Y))) :
    smulMor A 1 = 𝟙 A :=
  Scheme.Modules.smulHom_one (A : Y.Modules)

lemma smulMor_mul {Y : Scheme.{u}} (A : modulesPseudofunctor.obj (.mk (op Y))) (a b : Γ(Y, ⊤)) :
    smulMor A (a * b) = smulMor A b ≫ smulMor A a :=
  Scheme.Modules.smulHom_mul (A : Y.Modules) a b

lemma presheafHom_map_smulMor_comp {X : Scheme.{u}} (O L : modulesPseudofunctor.obj (.mk (op X)))
    {T T' : Over X} (g : T' ⟶ T) (a : Γ(T.left, ⊤))
    (t : (modulesPseudofunctor.presheafHom O L).obj (op T)) :
    (modulesPseudofunctor.presheafHom O L).map g.op
        (smulMor ((modulesPseudofunctor.map T.hom.op.toLoc).toFunctor.obj O) a ≫ t) =
      smulMor ((modulesPseudofunctor.map T'.hom.op.toLoc).toFunctor.obj O)
          (g.left.appTop a) ≫
        (modulesPseudofunctor.presheafHom O L).map g.op t := by
  simp only [Pseudofunctor.presheafHom_map, TypeCat.ofHom_apply, Quiver.Hom.unop_op]
  rw [pullHom_comp (smulMor _ a) t g.left T'.hom T'.hom T'.hom (Over.w g) (Over.w g) (Over.w g)]
  unfold smulMor
  rw [pullHom_smulHom]

namespace Scheme

variable {X : Scheme.{u}}

instance : (toProEt X ⋙ ProEt.forget X).IsContinuous (smallEtaleTopology X)
    (proetaleTopology.over X) :=
  Functor.isContinuous_comp _ _ _ (ProEt.topology X) _

/-- The presheaf `V ↦ Hom(V^* M, V^* N)` of homomorphisms between the pullbacks of two
`𝒪_X`-modules, on the small étale site of `X`. -/
noncomputable def Modules.etaleHom (M N : modulesPseudofunctor.obj (.mk (op X))) :
    X.Etaleᵒᵖ ⥤ Type u :=
  (toProEt X ⋙ ProEt.forget X).op ⋙ modulesPseudofunctor.presheafHom (S := X) M N

lemma Modules.isSheaf_etaleHom (M N : modulesPseudofunctor.obj (.mk (op X)))
    [(M : X.Modules).IsQuasicoherent] [(N : X.Modules).IsQuasicoherent] :
    Presheaf.IsSheaf X.smallEtaleTopology (Modules.etaleHom M N) :=
  Functor.op_comp_isSheaf _ _ (proetaleTopology.over X)
    ⟨_, (isSheaf_presheafHom (S := X) M N inferInstance inferInstance).of_le
      fun U R hR ↦ by
        rw [GrothendieckTopology.mem_over_iff] at hR ⊢
        exact proetaleTopology_le_fpqcTopology _ hR⟩

namespace Modules

/-- The presheaf `V ↦ Iso(V^* M, V^* N)` on the small étale site. -/
noncomputable abbrev etaleIso (M N : modulesPseudofunctor.obj (.mk (op X))) :
    Subfunctor (etaleHom M N) :=
  modulesPseudofunctor.presheafIso (toProEt X ⋙ ProEt.forget X) M N

lemma isSheaf_etaleIso (M N : modulesPseudofunctor.obj (.mk (op X)))
    [(M : X.Modules).IsQuasicoherent] [(N : X.Modules).IsQuasicoherent] :
    Presheaf.IsSheaf X.smallEtaleTopology (etaleIso M N).toFunctor := by
  have h (A B : modulesPseudofunctor.obj (.mk (op X))) [(A : X.Modules).IsQuasicoherent]
      [(B : X.Modules).IsQuasicoherent] :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (Modules.isSheaf_etaleHom A B)
  rw [isSheaf_iff_isSheaf_of_type, Subfunctor.isSheaf_iff _ (h M N)]
  intro V φ hφ
  exact Pseudofunctor.isIso_of_isIso_presheafHom_map _ φ (h N M _ hφ) (h M M _ hφ)
    (h N N _ hφ) fun W g hg ↦ hg

instance isIso_smulHom_units {Y : Scheme.{u}} (M : Y.Modules) (a : Γ(Y, ⊤)ˣ) :
    IsIso (M.smulHom (a : Γ(Y, ⊤))) :=
  ⟨M.smulHom (a⁻¹ : Γ(Y, ⊤)ˣ), by rw [← smulHom_mul, Units.inv_mul, smulHom_one], by
    rw [← smulHom_mul, Units.mul_inv, smulHom_one]⟩

instance isIso_smulMor_units {Y : Scheme.{u}} (A : modulesPseudofunctor.obj (.mk (op Y)))
    (a : Γ(Y, ⊤)ˣ) : IsIso (smulMor A a) :=
  isIso_smulHom_units (A : Y.Modules) a

/-- The structure sheaf, as an object of `modulesPseudofunctor`. -/
noncomputable abbrev unitObj (X : Scheme.{u}) : modulesPseudofunctor.obj (.mk (op X)) :=
  Modules.unit X

instance : ((unitObj X : modulesPseudofunctor.obj (.mk (op X))) : X.Modules).IsQuasicoherent :=
  SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)

lemma exists_smulHom_comp_eq {Y : Scheme.{u}} {A B : Y.Modules} [A.IsInvertible]
    (t s : A ⟶ B) [IsIso t] [IsIso s] : ∃ a : Γ(Y, ⊤)ˣ, A.smulHom a ≫ t = s := by
  obtain ⟨c, hc⟩ := exists_eq_smulHom A (s ≫ inv t)
  obtain ⟨d, hd⟩ := exists_eq_smulHom A (t ≫ inv s)
  have h₁ : A.smulHom (c * d) = A.smulHom 1 := by
    rw [smulHom_mul, ← hc, ← hd, smulHom_one]
    simp
  have h₂ : c * d = 1 := eq_of_smulHom_eq A h₁
  refine ⟨⟨c, d, h₂, by rw [mul_comm, h₂]⟩, ?_⟩
  change A.smulHom c ≫ t = s
  rw [← hc]
  simp

lemma smulMor_comp_injective {Y : Scheme.{u}} {A B : modulesPseudofunctor.obj (.mk (op Y))}
    [(A : Y.Modules).IsInvertible] (t : A ⟶ B) (ht : IsIso t) :
    Function.Injective (fun a : Γ(Y, ⊤) ↦ smulMor A a ≫ t) := by
  intro a b h
  exact eq_of_smulHom_eq (A : Y.Modules) ((cancel_mono t).1 h)

lemma exists_smulMor_comp_eq {Y : Scheme.{u}} {A B : modulesPseudofunctor.obj (.mk (op Y))}
    [(A : Y.Modules).IsInvertible] (t s : A ⟶ B) (ht : IsIso t) (hs : IsIso s) :
    ∃ a : Γ(Y, ⊤)ˣ, smulMor A a ≫ t = s :=
  @exists_smulHom_comp_eq Y A B _ t s ht hs

end Modules

end Scheme

end AlgebraicGeometry
