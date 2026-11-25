/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sp.SpEllCoefficientTower
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Sites.EpiMono

/-! # Epic maps between locally trivial rank-one modules -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u c v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private theorem unitEnd_apply (X : Scheme.{u}) (W : X.ProEt)
    (O : Sheaf ((Scheme.ProEt.topology X).over W) CommRingCat.{u + 1})
    (f : End (SheafOfModules.unit ((sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)))
    (U : (Over W)ᵒᵖ) (x : O.obj.obj U) :
    f.asHom.val.app U x = @Mul.mul (O.obj.obj U) inferInstance x
      (f.asHom.val.app U (1 : O.obj.obj U)) := by
  let f' : ModuleCat.of (O.obj.obj U) (O.obj.obj U) ⟶
      ModuleCat.of (O.obj.obj U) (O.obj.obj U) := f.asHom.val.app U
  change f' x = x * f' 1
  simpa only [smul_eq_mul, mul_one] using f'.hom.map_smul x (1 : O.obj.obj U)

private theorem epiUnit_isIso (X : Scheme.{u}) (W : X.ProEt)
    (O : Sheaf ((Scheme.ProEt.topology X).over W) CommRingCat.{u + 1})
    (f : End (SheafOfModules.unit ((sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)))
    [Epi f.asHom] : IsIso f.asHom := by
  let J := (Scheme.ProEt.topology X).over W
  let R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O
  let q := (SheafOfModules.toSheaf.{u + 1} R).map f.asHom
  have : Epi q := inferInstance
  have : Sheaf.IsLocallySurjective q :=
    (Sheaf.isLocallySurjective_iff_epi' _ q).2 inferInstance
  have hinj (U : (Over W)ᵒᵖ) : Function.Injective (f.asHom.val.app U) := by
    intro x y hxy
    have hsheaf : Presieve.IsSheaf J (O.obj ⋙ forget CommRingCat) :=
      (isSheaf_iff_isSheaf_of_type J _).mp
        ((sheafCompose J (forget CommRingCat)).obj O).property
    apply (hsheaf.isSeparated _ (Presheaf.imageSieve_mem J q.hom
      (1 : O.obj.obj U))).ext
    rintro V g ⟨z, hz⟩
    change f.asHom.val.app (op V) z = O.obj.map g.op 1 at hz
    rw [map_one, unitEnd_apply X W O] at hz
    have hu : @IsUnit (O.obj.obj (op V)) inferInstance
        (f.asHom.val.app (op V) (1 : O.obj.obj (op V))) := by
      apply isUnit_iff_exists_inv.mpr
      refine ⟨z, ?_⟩
      change @Mul.mul (O.obj.obj (op V)) inferInstance _ z = 1
      exact (mul_comm _ _).trans hz
    apply hu.mul_right_cancel
    have hn := congrArg (fun z ↦ O.obj.map g.op z) hxy
    have hx := PresheafOfModules.naturality_apply f.asHom.val g.op x
    have hy := PresheafOfModules.naturality_apply f.asHom.val g.op y
    have hh : f.asHom.val.app (op V) (O.obj.map g.op x) =
        f.asHom.val.app (op V) (O.obj.map g.op y) := hx.trans (hn.trans hy.symm)
    exact (unitEnd_apply X W O f (op V) (O.obj.map g.op x)).symm.trans
      (hh.trans (unitEnd_apply X W O f (op V) (O.obj.map g.op y)))
  have : Mono f.asHom := ⟨by
    intro M g h heq
    apply SheafOfModules.hom_ext
    ext U x
    apply hinj U
    exact congrArg (fun z ↦ z.val.app U x) heq⟩
  exact isIso_of_mono_of_epi f.asHom

private theorem isIso_of_epi_bases
    {C : Type c} [Category.{v} C] {M N T : C} (f : M ⟶ N) [Epi f]
    (e : M ≅ T) (d : N ≅ T)
    (hT : ∀ a : End T, Epi a.asHom → IsIso a.asHom) : IsIso f := by
  let a := e.inv ≫ f ≫ d.hom
  have : Epi a := inferInstance
  have : IsIso a := hT (End.of a) inferInstance
  have h : f = e.hom ≫ a ≫ d.inv := by
    simp only [a, Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h]
  infer_instance

private theorem epiOver (X : Scheme.{u})
    (O : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1})
    {M N : SheafOfModules.{u + 1} O} (f : M ⟶ N) [Epi f] (W : X.ProEt) :
    Epi (f.over W) := by
  let U := SheafOfModules.toSheaf.{u + 1} O
  have : Sheaf.IsLocallySurjective (U.map f) :=
    (Sheaf.isLocallySurjective_iff_epi' _ _).2 inferInstance
  have : Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) (U.map f).hom :=
    inferInstance
  have : Presheaf.IsLocallySurjective ((Scheme.ProEt.topology X).over W)
      ((SheafOfModules.toSheaf.{u + 1} (O.over W)).map (f.over W)).hom :=
    show Presheaf.IsLocallySurjective ((Scheme.ProEt.topology X).over W)
      (Functor.whiskerLeft (Over.forget W).op (U.map f).hom) from
      Presheaf.isLocallySurjective_whisker ((Scheme.ProEt.topology X).over W)
        (Scheme.ProEt.topology X) (Over.forget W) (U.map f).hom
  have : Sheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf.{u + 1} (O.over W)).map (f.over W)) :=
    inferInstance
  have : Epi ((SheafOfModules.toSheaf.{u + 1} (O.over W)).map (f.over W)) :=
    (Sheaf.isLocallySurjective_iff_epi' _ _).mp inferInstance
  exact (SheafOfModules.toSheaf.{u + 1} (O.over W)).epi_of_epi_map (f := f.over W) inferInstance

/-- An epic morphism of module sheaves is invertible on a slice where both
modules have specified rank-one bases over the same commutative coefficient ring.

Source: blueprint latest, sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.proof.md, the local rank-one criterion.
(blueprint: lem-diagonal-local-rank-one-iso).

Proof in words. Restrict the epic map to the slice; restriction preserves local
surjectivity and the forgetful functor reflects epimorphisms. Conjugate by the two
bases to obtain an epic regular-module endomorphism. Such an endomorphism is
multiplication by its value on 1. Local surjectivity supplies local preimages of 1,
so that value is locally a unit in the commutative section rings. Cancellation and
sheaf separatedness prove injectivity. The endomorphism is mono and epi in an
abelian category and hence invertible. Undoing the two bases proves the claim.
This includes the zero ring and an empty slice. -/
theorem diagonalLocalRankOne_isIso (X : Scheme.{u})
    (O : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) (W : X.ProEt)
    {M N : SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)}
    (f : M ⟶ N) [Epi f]
    (e : M.over W ≅ (SheafOfModules.unit _).over W)
    (d : N.over W ≅ (SheafOfModules.unit _).over W) : IsIso (f.over W) := by
  have : Epi (f.over W) := epiOver X _ f W
  exact isIso_of_epi_bases (f.over W) e d
    (fun a ha ↦ @epiUnit_isIso X W (O.over W) a ha)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
