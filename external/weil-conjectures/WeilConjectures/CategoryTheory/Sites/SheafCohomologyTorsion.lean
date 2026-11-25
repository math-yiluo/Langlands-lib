/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyBijective

/-!
# Injective abelian sheaves are divisible

Let `I` be an injective abelian sheaf on a site and `n` a positive integer. Multiplication by `n`
on `I` is an epimorphism: a section `s` of `I` over `U` is a morphism from the sheafified free
abelian sheaf on `U`, on which multiplication by `n` is a monomorphism, and extending along it
divides `s` by `n`. Consequently the `n`-torsion subsheaf `I[n]` of `I` has no cohomology in
positive degrees. Since every abelian sheaf embeds into an injective one, every sheaf killed by
`n` embeds into an acyclic sheaf killed by `n`, which allows dimension shifting within sheaves
killed by `n`.

## Main statements

- `CategoryTheory.Sheaf.epi_nsmul_id_of_injective`: multiplication by `n ≠ 0` on an injective
  abelian sheaf is an epimorphism.
- `CategoryTheory.Sheaf.subsingleton_H_kernel_nsmul_of_injective`: the `n`-torsion subsheaf of an
  injective abelian sheaf has no cohomology in positive degrees.
-/

@[expose] public section

universe w' w v u

namespace CategoryTheory

open Abelian Limits Opposite

namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max w v}]

section Free

/-- The morphism from the free abelian presheaf on `U` to `F` determined by a section of `F`
over `U`. -/
noncomputable def freeYonedaPresheafHom (U : C) (F : Cᵒᵖ ⥤ AddCommGrpCat.{max w v})
    (s : F.obj (op U)) : (uliftYoneda.{w}.obj U ⋙ AddCommGrpCat.free) ⟶ F where
  app V := AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun g ↦ F.map g.down.op s)
  naturality V W g := by
    apply AddCommGrpCat.hom_ext
    refine FreeAbelianGroup.lift_ext _ _ fun x ↦ ?_
    change FreeAbelianGroup.lift _ ((AddCommGrpCat.free.map _) (FreeAbelianGroup.of x)) =
      F.map g (FreeAbelianGroup.lift _ (FreeAbelianGroup.of x))
    rw [AddCommGrpCat.free_map_coe, FreeAbelianGroup.map_of, FreeAbelianGroup.lift_apply_of,
      FreeAbelianGroup.lift_apply_of]
    change (F.map ((g.unop ≫ x.down).op)) s = _
    rw [op_comp, F.map_comp]
    rfl

/-- The generator of the free abelian presheaf on `U` over `U`: the identity of `U`. -/
noncomputable def freeYonedaGen (U : C) :
    (uliftYoneda.{w}.obj U ⋙ AddCommGrpCat.free).obj (op U) :=
  FreeAbelianGroup.of (ULift.up (𝟙 U))

lemma freeYonedaPresheafHom_gen (U : C) (F : Cᵒᵖ ⥤ AddCommGrpCat.{max w v})
    (s : F.obj (op U)) :
    (freeYonedaPresheafHom.{w} U F s).app (op U) (freeYonedaGen.{w} U) = s := by
  change FreeAbelianGroup.lift _ (FreeAbelianGroup.of _) = s
  erw [FreeAbelianGroup.lift_apply_of]
  simp

/-- Multiplication by `n ≠ 0` on the free abelian presheaf on `U` is a monomorphism. -/
lemma mono_nsmul_id_freeYonedaPresheaf (U : C) {n : ℕ} (hn : n ≠ 0) :
    Mono (n • 𝟙 ((uliftYoneda.{w}.obj U ⋙ AddCommGrpCat.free))) := by
  have (V : Cᵒᵖ) : Mono ((n • 𝟙 (uliftYoneda.{w}.obj U ⋙ AddCommGrpCat.free)).app V) := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro x y hxy
    simp only [NatTrans.app_nsmul, NatTrans.id_app] at hxy
    let X := (uliftYoneda.{w}.obj U).obj V
    let e := (FreeAbelianGroup.equivFinsupp X).toAddMonoidHom
    have hxy' : n • (x : FreeAbelianGroup X) = n • (y : FreeAbelianGroup X) := hxy
    apply (FreeAbelianGroup.equivFinsupp X).injective
    have := congrArg e hxy'
    have h1 : e (n • (x : FreeAbelianGroup X)) = n • e x := map_nsmul e n x
    have h2 : e (n • (y : FreeAbelianGroup X)) = n • e y := map_nsmul e n y
    rw [h1, h2] at this
    exact nsmul_right_injective hn this
  exact NatTrans.mono_of_mono_app _

end Free

/-- **Injective abelian sheaves are divisible.** Multiplication by `n ≠ 0` on an injective
abelian sheaf `I` is an epimorphism: every section of `I` is `n` times a section. -/
theorem epi_nsmul_id_of_injective (I : Sheaf J AddCommGrpCat.{max w v}) [Injective I] {n : ℕ}
    (hn : n ≠ 0) : Epi (n • 𝟙 I) := by
  let P (U : C) : Sheaf J AddCommGrpCat.{max w v} :=
    (presheafToSheaf J _).obj ((uliftYoneda.{w}.obj U ⋙ AddCommGrpCat.free))
  have hP (U : C) : Mono (n • 𝟙 (P U)) := by
    have := mono_nsmul_id_freeYonedaPresheaf.{w} U hn
    rw [← Functor.map_id, ← Functor.map_nsmul]
    infer_instance
  -- the section of `I` corresponding to a morphism out of `P U`
  let e (U : C) (g : P U ⟶ I) : I.obj.obj (op U) :=
    g.hom.app (op U) ((toSheafify J (uliftYoneda.{w}.obj U ⋙ AddCommGrpCat.free)).app (op U)
      (freeYonedaGen.{w} U))
  have he (U : C) (s : I.obj.obj (op U)) :
      e U ⟨sheafifyLift J (freeYonedaPresheafHom.{w} U I.obj s) I.property⟩ = s := by
    change ((toSheafify J _ ≫ (sheafifyLift J (freeYonedaPresheafHom.{w} U I.obj s)
      I.property)).app (op U)) _ = s
    rw [toSheafify_sheafifyLift]
    exact freeYonedaPresheafHom_gen U I.obj s
  have hsurj (U : C) : Function.Surjective ((n • 𝟙 I).hom.app (op U)) := by
    intro s
    let f : P U ⟶ I := ⟨sheafifyLift J (freeYonedaPresheafHom.{w} U I.obj s) I.property⟩
    let g := Injective.factorThru f (n • 𝟙 (P U))
    refine ⟨e U g, ?_⟩
    have hg : (n • 𝟙 (P U)) ≫ g = f := Injective.comp_factorThru f (n • 𝟙 (P U))
    rw [← he U s]
    change _ = e U f
    rw [← hg, Preadditive.nsmul_comp, Category.id_comp, ← Category.comp_id g,
      ← Preadditive.comp_nsmul]
    rfl
  have : Sheaf.IsLocallySurjective (n • 𝟙 I) :=
    Presheaf.isLocallySurjective_of_surjective J _ fun U ↦ hsurj U.unop
  exact Sheaf.epi_of_isLocallySurjective _

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{max w v})]

/-- Multiplication by `n` on `H⁰` of an injective abelian sheaf is surjective: a morphism out of
the constant sheaf `ℤ` extends along multiplication by `n`, which is a monomorphism. -/
lemma surjective_nsmul_H_zero_of_injective (I : Sheaf J AddCommGrpCat.{max w v}) [Injective I]
    {n : ℕ} (hn : n ≠ 0) : Function.Surjective fun x : H I 0 ↦ n • x := by
  let Z := (constantSheaf J AddCommGrpCat.{max w v}).obj (AddCommGrpCat.of (ULift ℤ))
  have hZ : Mono (n • 𝟙 Z) := by
    have : Mono (n • 𝟙 (AddCommGrpCat.of (ULift.{max w v} ℤ))) := by
      rw [AddCommGrpCat.mono_iff_injective]
      intro x y hxy
      change n • x = n • y at hxy
      have : n • x.down = n • y.down := congrArg ULift.down hxy
      exact ULift.ext (nsmul_right_injective hn this)
    have : Mono ((Functor.const Cᵒᵖ).map (n • 𝟙 (AddCommGrpCat.of (ULift.{max w v} ℤ)))) :=
      NatTrans.mono_of_mono_app _
    have : Mono ((presheafToSheaf J _).map
        ((Functor.const Cᵒᵖ).map (n • 𝟙 (AddCommGrpCat.of (ULift.{max w v} ℤ))))) :=
      inferInstance
    rw [← Functor.map_id, ← Functor.map_nsmul]
    exact this
  intro x
  obtain ⟨f, rfl⟩ := Ext.addEquiv₀.symm.surjective x
  refine ⟨Ext.addEquiv₀.symm (Injective.factorThru f (n • 𝟙 Z)), ?_⟩
  change n • _ = _
  rw [← map_nsmul]
  congr 1
  conv_rhs => rw [← Injective.comp_factorThru f (n • 𝟙 Z)]
  rw [Preadditive.nsmul_comp, Category.id_comp]

/-- **The `n`-torsion of an injective sheaf is acyclic.** For an injective abelian sheaf `I` and
`n ≠ 0`, the kernel `I[n]` of multiplication by `n` on `I` has no cohomology in positive degrees:
`0 → I[n] → I → I → 0` is exact since `I` is divisible, `Hᵠ(I) = 0` for `q ≥ 1`, and
multiplication by `n` on `H⁰(I)` is surjective. -/
theorem subsingleton_H_kernel_nsmul_of_injective (I : Sheaf J AddCommGrpCat.{max w v})
    [Injective I] {n : ℕ} (hn : n ≠ 0) (q : ℕ) :
    Subsingleton (H (kernel (n • 𝟙 I)) (q + 1)) := by
  have := epi_nsmul_id_of_injective I hn
  let S := ShortComplex.mk (kernel.ι (n • 𝟙 I)) (n • 𝟙 I) (kernel.condition _)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel _) inferInstance inferInstance
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨y, rfl⟩ :=
    Ext.covariant_sequence_exact₁ _ hS x (Ext.eq_zero_of_injective _) (zero_add (q + 1))
  cases q with
  | zero =>
    obtain ⟨z, rfl⟩ := surjective_nsmul_H_zero_of_injective I hn y
    have : n • z = H.map S.g 0 z := by
      rw [H.map_nsmul_apply, H.map_id_apply]
    change Ext.comp (n • z) _ _ = 0
    rw [this, H.map_apply, Ext.comp_assoc _ _ _ (add_zero 0) (zero_add 1) (zero_add 1),
      hS.comp_extClass, Ext.comp_zero]
  | succ q => rw [Ext.eq_zero_of_injective y, Ext.zero_comp]

end Sheaf

section Shift

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact)

include hS in
/-- **Dimension shifting.** In a short exact sequence `0 → S.X₁ → S.X₂ → S.X₃ → 0` of abelian
sheaves, `Hᵠ⁺¹(S.X₁) = 0` as soon as `Hᵠ(S.X₃) = 0` and `Hᵠ⁺¹(S.X₂) = 0`. -/
lemma Sheaf.H.subsingleton_X₁_of_shortExact (q : ℕ) [Subsingleton (H S.X₃ q)]
    [Subsingleton (H S.X₂ (q + 1))] : Subsingleton (H S.X₁ (q + 1)) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS x (Subsingleton.elim _ _) rfl
  rw [Subsingleton.elim y 0, Ext.zero_comp]

include hS in
/-- **Dimension shifting.** In a short exact sequence `0 → S.X₁ → S.X₂ → S.X₃ → 0` of abelian
sheaves, `Hᵠ(S.X₃) = 0` as soon as `Hᵠ(S.X₂) = 0` and `Hᵠ⁺¹(S.X₁) = 0`. -/
lemma Sheaf.H.subsingleton_X₃_of_shortExact (q : ℕ) [Subsingleton (H S.X₂ q)]
    [Subsingleton (H S.X₁ (q + 1))] : Subsingleton (H S.X₃ q) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₃ _ hS x rfl (Subsingleton.elim _ _)
  rw [Subsingleton.elim y 0, Ext.zero_comp]

omit hS in
/-- Sheaf cohomology groups of isomorphic sheaves: if `Hⁿ(B) = 0` and `A ≅ B`, then `Hⁿ(A) = 0`. -/
lemma Sheaf.H.subsingleton_of_iso {A B : Sheaf J AddCommGrpCat.{w}} (e : A ≅ B) (n : ℕ)
    [Subsingleton (H B n)] : Subsingleton (H A n) :=
  Function.Injective.subsingleton (f := H.map e.hom n) fun x y h ↦ by
    have h' := congrArg (H.map e.inv n) h
    rwa [← H.map_comp_apply, ← H.map_comp_apply, e.hom_inv_id, H.map_id_apply,
      H.map_id_apply] at h'

end Shift

end CategoryTheory
