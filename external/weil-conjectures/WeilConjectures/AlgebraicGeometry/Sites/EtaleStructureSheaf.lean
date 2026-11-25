/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtaleHom
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-!
# The structure sheaf on the small étale site

The presheaf `V ↦ Γ(V, 𝒪_V)` on the small étale site of `X` is a sheaf: it is isomorphic to the
presheaf `V ↦ End(V^* 𝒪_X)` of endomorphisms of the pulled back structure sheaf, `a ↦ a ·`,
which is a sheaf by fpqc descent for quasi-coherent modules
(`AlgebraicGeometry.Scheme.Modules.isSheaf_etaleHom`).

## Main statements

- `CategoryTheory.Presheaf.isSheaf_of_isSheaf_forget_commRingCat`: a presheaf of commutative rings
  is a sheaf if its underlying presheaf of sets is.
- `AlgebraicGeometry.Scheme.isSheaf_etaleStructurePresheaf_aux`: `V ↦ Γ(V, 𝒪_V)` is a sheaf on
  the small étale site.
-/

@[expose] public section

universe w v u

open CategoryTheory Opposite

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A presheaf of commutative rings is a sheaf if its underlying presheaf of sets is: compatible
families of ring homomorphisms glue pointwise, and the glued map is a ring homomorphism by
separatedness. -/
lemma isSheaf_of_isSheaf_forget_commRingCat (P : Cᵒᵖ ⥤ CommRingCat.{w})
    (h : Presieve.IsSheaf J (P ⋙ forget CommRingCat)) : Presheaf.IsSheaf J P := by
  intro E V S hS x hx
  have hQ := h S hS
  let y (e : E) : Presieve.FamilyOfElements (P ⋙ forget CommRingCat) S :=
    fun W f hf ↦ (x f hf).hom e
  have hy (e : E) : (y e).Compatible := by
    intro W₁ W₂ Z g₁ g₂ f₁ f₂ h₁ h₂ fac
    have := congrArg (fun φ : E ⟶ P.obj (op Z) ↦ φ.hom e) (hx g₁ g₂ h₁ h₂ fac)
    exact this
  let g (e : E) : P.obj (op V) := hQ.amalgamate (y e) (hy e)
  have hg (e : E) {W : C} (f : W ⟶ V) (hf : S f) : P.map f.op (g e) = (x f hf).hom e :=
    hQ.valid_glue (hy e) f hf
  have ext {a b : P.obj (op V)}
      (hab : ∀ {W : C} (f : W ⟶ V), S f → P.map f.op a = P.map f.op b) :
      a = b :=
    hQ.isSeparatedFor.ext fun _ f hf ↦ hab f hf
  let φ : E ⟶ P.obj (op V) := CommRingCat.ofHom
    { toFun := g
      map_one' := ext fun f hf ↦ by rw [hg _ f hf, map_one, map_one]
      map_mul' := fun a b ↦ ext fun f hf ↦ by rw [map_mul, hg _ f hf, hg _ f hf, hg _ f hf, map_mul]
      map_zero' := ext fun f hf ↦ by rw [hg _ f hf, map_zero, map_zero]
      map_add' := fun a b ↦ ext fun f hf ↦ by
        rw [map_add, hg _ f hf, hg _ f hf, hg _ f hf, map_add] }
  refine ⟨φ, fun W f hf ↦ ?_, fun ψ hψ ↦ ?_⟩
  · change φ ≫ P.map f.op = x f hf
    ext e
    exact hg e f hf
  · refine CommRingCat.hom_ext (RingHom.ext fun e ↦ ?_)
    refine ext fun f hf ↦ ?_
    exact (congrArg (fun χ : E ⟶ P.obj (op _) ↦ χ.hom e) (hψ f hf)).trans (hg e f hf).symm

end CategoryTheory.Presheaf

namespace AlgebraicGeometry.Scheme

open Pseudofunctor.LocallyDiscreteOpToCat Modules

variable (X : Scheme.{u})

-- the defeq checks through the small étale and pro-étale sites are slow
set_option backward.isDefEq.respectTransparency.types false in
/-- **Étale descent for the structure sheaf.** The presheaf `V ↦ Γ(V, 𝒪_V)` is a sheaf on the
small étale site: `a ↦ a ·` identifies it with the étale sheaf `V ↦ End(V^* 𝒪_X)`. -/
theorem isSheaf_etaleStructurePresheaf_aux :
    Presheaf.IsSheaf X.smallEtaleTopology
      ((Scheme.Etale.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ) := by
  apply Presheaf.isSheaf_of_isSheaf_forget_commRingCat
  have h := (isSheaf_iff_isSheaf_of_type _ _).1
    (Modules.isSheaf_etaleHom (unitObj X) (unitObj X))
  let G := toProEt X ⋙ ProEt.forget X
  have : (Modules.unit X).IsInvertible := isInvertible_tensorUnit
  let eqv (V : X.Etaleᵒᵖ) : Γ(V.unop.left, ⊤) ≃ (etaleHom (unitObj X) (unitObj X)).obj V :=
    have hA : ((pullback (G.obj V.unop).hom).obj (Modules.unit X)).IsInvertible := inferInstance
    Equiv.ofBijective (fun a ↦ smulMor
      ((modulesPseudofunctor.map (G.obj V.unop).hom.op.toLoc).toFunctor.obj (unitObj X)) a)
      ⟨fun a b hab ↦ eq_of_smulHom_eq ((pullback (G.obj V.unop).hom).obj (Modules.unit X)) hab,
        fun φ ↦ by
          obtain ⟨c, hc⟩ := exists_eq_smulHom ((pullback (G.obj V.unop).hom).obj (Modules.unit X)) φ
          exact ⟨c, hc.symm⟩⟩
  refine Presieve.isSheaf_iso _ (NatIso.ofComponents (fun V ↦ (eqv V).toIso) ?_).symm h
  intro V W f
  -- Keep the maps as function applications so their composition can be reduced directly.
  apply ConcreteCategory.hom_ext
  intro a
  dsimp only [types_comp_apply, Equiv.toIso_hom_hom_apply, eqv, Equiv.ofBijective_apply,
    etaleHom, Functor.comp_map, Functor.op_map, Pseudofunctor.presheafHom_map,
    TypeCat.ofHom_apply, Quiver.Hom.unop_op, CommRingCat.forget_map_apply, Scheme.Γ_map,
    Over.forget_map, G]
  exact (pullHom_smulHom (unitObj X) V.unop.hom f.unop.left W.unop.hom
    (MorphismProperty.Over.w f.unop) a).symm

end AlgebraicGeometry.Scheme
