/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# Sheaves of `ℤ/n`-modules are the abelian sheaves killed by `n`

An abelian group killed by `n` carries exactly one `ℤ/n`-module structure
(`AddCommGroup.zmodModule`), and additive maps between `ℤ/n`-modules are `ℤ/n`-linear
(`AddMonoidHom.toZModLinearMap`): the forgetful functor from `ℤ/n`-modules to abelian groups
is fully faithful, with essential image the groups killed by `n`. Applying this sectionwise,
the same holds for sheaves on any site: the functor from sheaves of `ℤ/n`-modules to abelian
sheaves is fully faithful, and its essential image consists of the abelian sheaves `F` with
`n • 𝟙 F = 0`.

In the blueprint (`lem-weil-pbc-sheaves-killed-by-n-zmod-modules`) a sheaf of `ℤ/n`-modules is
a module over the constant sheaf of rings `(ℤ/n)_T`, and the comparison with sectionwise
`ℤ/n`-modules goes through the sheafification of the constant presheaf of rings
(`lem-weil-pbc-ring-sheafification-underlying-sets`, which is Mathlib's
`CategoryTheory.sheafifyComposeIso`). Here sheaves of `ℤ/n`-modules are sheaves with values in
`ModuleCat (ZMod n)`, so that this comparison is built in.

## Main statements

- `ModuleCat.fullyFaithfulForget₂ZMod`: additive maps between `ℤ/n`-modules are linear.
- `ModuleCat.mem_essImage_forget₂_zmod_iff`: an abelian group comes from a `ℤ/n`-module if and
  only if it is killed by `n`.
- `CategoryTheory.Sheaf.mem_essImage_sheafCompose_forget₂_zmod_iff`: an abelian sheaf comes from
  a sheaf of `ℤ/n`-modules if and only if it is killed by `n`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace ModuleCat

variable (n : ℕ)

/-- Additive maps between `ℤ/n`-modules are `ℤ/n`-linear: the forgetful functor from
`ℤ/n`-modules to abelian groups is fully faithful (blueprint
`lem-weil-pbc-zmod-module-structure-killed-by-n`, (4)). -/
def fullyFaithfulForget₂ZMod : (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w}).FullyFaithful
    where
  preimage {M N} f := ModuleCat.ofHom (AddMonoidHom.toZModLinearMap n (M := M) (M₁ := N) f.hom)

instance : (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w}).Full :=
  (fullyFaithfulForget₂ZMod n).full

/-- The underlying abelian group of a `ℤ/n`-module is killed by `n`. -/
lemma nsmul_id_forget₂_zmod_eq_zero (M : ModuleCat.{w} (ZMod n)) :
    n • 𝟙 ((forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w}).obj M) = 0 := by
  ext (x : M)
  change n • x = (0 : M)
  rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]

/-- An abelian group is the underlying group of a `ℤ/n`-module if and only if it is killed by
`n` (blueprint `lem-weil-pbc-zmod-module-structure-killed-by-n`, (1)). -/
lemma mem_essImage_forget₂_zmod_iff (A : AddCommGrpCat.{w}) :
    (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w}).essImage A ↔ n • 𝟙 A = 0 := by
  refine ⟨fun ⟨M, ⟨e⟩⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [← cancel_epi e.hom, Preadditive.comp_nsmul, Category.comp_id, comp_zero,
      ← Category.id_comp e.hom, ← Preadditive.nsmul_comp, nsmul_id_forget₂_zmod_eq_zero,
      zero_comp]
  · let _ : Module (ZMod n) A := AddCommGroup.zmodModule fun x ↦ by
      simpa using congrArg (fun f ↦ f x) (congrArg AddCommGrpCat.Hom.hom h)
    exact ⟨ModuleCat.of (ZMod n) A, ⟨Iso.refl _⟩⟩

end ModuleCat

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (n : ℕ)
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})]

/-- The underlying abelian sheaf of a sheaf of `ℤ/n`-modules is killed by `n` (blueprint
`lem-weil-pbc-sheaves-killed-by-n-zmod-modules`, (1)). -/
lemma nsmul_id_sheafCompose_forget₂_zmod_eq_zero (G : Sheaf J (ModuleCat.{w} (ZMod n))) :
    n • 𝟙 ((sheafCompose J (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})).obj G) = 0 :=
  (sheafToPresheaf J _).map_injective (by
    rw [Functor.map_nsmul, Functor.map_id, Functor.map_zero]
    ext U : 2
    exact ModuleCat.nsmul_id_forget₂_zmod_eq_zero n _)

/-- An abelian sheaf is the underlying abelian sheaf of a sheaf of `ℤ/n`-modules if and only if
it is killed by `n` (blueprint `lem-weil-pbc-sheaves-killed-by-n-zmod-modules`, (2)): the
sections of a sheaf killed by `n` are `ℤ/n`-modules, compatibly with restriction, and the sheaf
condition is checked on underlying abelian groups. -/
lemma mem_essImage_sheafCompose_forget₂_zmod_iff (F : Sheaf J AddCommGrpCat.{w}) :
    (sheafCompose J (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})).essImage F ↔
      n • 𝟙 F = 0 := by
  refine ⟨fun ⟨G, ⟨e⟩⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [← cancel_epi e.hom, Preadditive.comp_nsmul, Category.comp_id, comp_zero,
      ← Category.id_comp e.hom, ← Preadditive.nsmul_comp,
      nsmul_id_sheafCompose_forget₂_zmod_eq_zero, zero_comp]
  · have hF (U : Cᵒᵖ) : (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w}).essImage
        (F.obj.obj U) := by
      rw [ModuleCat.mem_essImage_forget₂_zmod_iff]
      have := congrArg (fun φ ↦ ((sheafToPresheaf J _).map φ).app U) h
      simp only [Functor.map_nsmul, NatTrans.app_nsmul, Functor.map_zero, Functor.map_id,
        NatTrans.id_app, NatTrans.app_zero] at this
      exact this
    let e := Functor.essImage.liftFunctorCompIso F.obj _ hF
    refine ⟨⟨_, Presheaf.isSheaf_of_isSheaf_comp J _
      (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})
      ((Presheaf.isSheaf_of_iso_iff e).2 F.property)⟩,
      ⟨(fullyFaithfulSheafToPresheaf J _).preimageIso e⟩⟩

/-- **Abelian sheaves killed by `n` are the sheaves of `ℤ/n`-modules.** On any site, the
functor from sheaves of `ℤ/n`-modules to abelian sheaves forgetting the module structure is full
and faithful — a morphism of abelian sheaves between sheaves of `ℤ/n`-modules is `ℤ/n`-linear,
so that a sheaf killed by `n` carries exactly one structure of sheaf of `ℤ/n`-modules up to
unique isomorphism — and its essential image consists of the abelian sheaves killed by `n`.
(blueprint: `lem-weil-pbc-sheaves-killed-by-n-zmod-modules`) -/
theorem sheafCompose_forget₂_zmod_full_faithful_essImage :
    (sheafCompose J (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})).Full ∧
      (sheafCompose J (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})).Faithful ∧
      ∀ F : Sheaf J AddCommGrpCat.{w},
        (sheafCompose J (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})).essImage F ↔
          n • 𝟙 F = 0 :=
  ⟨inferInstance, inferInstance, mem_essImage_sheafCompose_forget₂_zmod_iff J n⟩

section Constant

variable [HasWeakSheafify J (ModuleCat.{w} (ZMod n))] [HasWeakSheafify J AddCommGrpCat.{w}]
  {T : C} (hT : IsTerminal T)

/-- On a site with a terminal object, the constant abelian sheaf on the underlying group of a
`ℤ/n`-module is the underlying abelian sheaf of the constant sheaf of `ℤ/n`-modules: both
constant sheaf functors are left adjoint to the sections over the terminal object, and the
constant abelian sheaf on a group killed by `n` is killed by `n`. -/
noncomputable def forget₂ZModCompConstantSheafIso :
    forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w} ⋙ constantSheaf J AddCommGrpCat.{w} ≅
      constantSheaf J (ModuleCat.{w} (ZMod n)) ⋙
        sheafCompose J (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w}) :=
  have : ((sheafSections J AddCommGrpCat.{w}).obj (Opposite.op T)).Additive :=
    ⟨fun {_ _ _ _} ↦ rfl⟩
  have := (constantSheafAdj J AddCommGrpCat.{w} hT).left_adjoint_additive
  Adjunction.compIsoOfForallMemEssImage (ModuleCat.fullyFaithfulForget₂ZMod n)
    (fullyFaithfulSheafCompose J (ModuleCat.fullyFaithfulForget₂ZMod n))
    (constantSheafAdj J AddCommGrpCat.{w} hT) (constantSheafAdj J _ hT) (Iso.refl _)
    fun M ↦ (mem_essImage_sheafCompose_forget₂_zmod_iff J n _).2 (by
      rw [← Functor.map_id, ← Functor.map_nsmul, ModuleCat.nsmul_id_forget₂_zmod_eq_zero,
        Functor.map_zero])

include hT in
/-- On a site with a terminal object, a sheaf of `ℤ/n`-modules is constant if and only if its
underlying abelian sheaf is. If the underlying abelian sheaf is the constant sheaf on a group
`A`, it is also the constant sheaf on `A / nA`, which is the underlying group of a
`ℤ/n`-module: the constant sheaf functor preserves cokernels and the constant sheaf on `A` is
killed by `n`. No connectedness of the site is needed. -/
lemma isConstant_sheafCompose_forget₂_zmod_iff (G : Sheaf J (ModuleCat.{w} (ZMod n))) :
    ((sheafCompose J (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})).obj G).IsConstant J ↔
      G.IsConstant J := by
  let Φ := sheafCompose J (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})
  have hΦ := fullyFaithfulSheafCompose J (ModuleCat.fullyFaithfulForget₂ZMod n)
  refine ⟨fun ⟨⟨A, ⟨e⟩⟩⟩ ↦ ?_, fun ⟨⟨M, ⟨e⟩⟩⟩ ↦
    ⟨⟨_, ⟨(forget₂ZModCompConstantSheafIso J n hT).app M ≪≫ Φ.mapIso e⟩⟩⟩⟩
  have : ((sheafSections J AddCommGrpCat.{w}).obj (Opposite.op T)).Additive :=
    ⟨fun {_ _ _ _} ↦ rfl⟩
  have := (constantSheafAdj J AddCommGrpCat.{w} hT).left_adjoint_additive
  let K := constantSheaf J AddCommGrpCat.{w}
  have := (constantSheafAdj J AddCommGrpCat.{w} hT).leftAdjoint_preservesColimits
  have hA : K.map (n • 𝟙 A) = 0 := by
    rw [Functor.map_nsmul, Functor.map_id, ← cancel_epi e.inv, Preadditive.comp_nsmul,
      Category.comp_id, comp_zero, ← Category.id_comp e.inv, ← Preadditive.nsmul_comp,
      nsmul_id_sheafCompose_forget₂_zmod_eq_zero, zero_comp]
  have hQ : n • 𝟙 (cokernel (n • 𝟙 A)) = 0 := by
    rw [← cancel_epi (cokernel.π _), comp_zero, Preadditive.comp_nsmul, Category.comp_id,
      ← Category.id_comp (cokernel.π _), ← Preadditive.nsmul_comp, cokernel.condition]
  obtain ⟨M, ⟨e'⟩⟩ := (ModuleCat.mem_essImage_forget₂_zmod_iff n _).2 hQ
  exact ⟨⟨M, ⟨hΦ.preimageIso ((forget₂ZModCompConstantSheafIso J n hT).symm.app M ≪≫
    K.mapIso e' ≪≫ PreservesCokernel.iso K (n • 𝟙 A) ≪≫ cokernelIsoOfEq hA ≪≫
      cokernelZeroIsoTarget ≪≫ e)⟩⟩⟩

end Constant

end CategoryTheory.Sheaf
