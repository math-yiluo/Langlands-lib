/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafConstruction
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafTerms
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs

/-! # Quasi-coherence of affine pushforward Čech terms

Source: Stacks Project, Tags 02KG and 02KH, affine intersections and direct images.
(blueprint: lem-pc-s3-alternating-cech-sheaf-affine-quasicoherent).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped ZeroObject
namespace AlgebraicGeometry

private theorem quasicoherent_product {A : CommRingCat.{u}} {I : Type}
    [Finite I] (M : I → (Spec A).Modules)
    [∀ t, SheafOfModules.IsQuasicoherent.{u} (M t)] :
    SheafOfModules.IsQuasicoherent.{u} (∏ᶜ M) := by
  let N : ModuleCat.{u} A := ∏ᶜ fun t ↦ moduleSpecΓFunctor.obj (M t)
  let e : (tilde.functor A).obj N ≅ ∏ᶜ M :=
    PreservesProduct.iso (tilde.functor A) _ ≪≫
      Pi.mapIso (fun t ↦ asIso (M t).fromTildeΓ)
  exact (SheafOfModules.isQuasicoherent.{u} (Spec A).ringCatSheaf).prop_of_iso e
    (inferInstance : SheafOfModules.IsQuasicoherent.{u} ((tilde.functor A).obj N))

/-- Each pushed-forward extended term is quasi-coherent.
Source: Stacks Project, Tags 02KG and 02KH, separated-case affine intersections.
(blueprint: lem-pc-s3-alternating-cech-sheaf-affine-quasicoherent).

Proof: For nonnegative degree p, use the term comparison to identify the term with
the finite product of j_t* of G restricted to W_t. Every tuple has p+1 entries, so
W_t is an affine open: finite nonempty intersections of affine opens are affine
on a scheme separated over an affine base. The map W_t → Spec A is affine, and
its pushforward takes quasi-coherent modules to quasi-coherent modules. Composition
of pushforwards identifies this with f* j_t*. Pushforward preserves products;
finite products of quasi-coherent modules are quasi-coherent because they are
finite biproducts. Transfer quasi-coherence across the term and extension
isomorphisms. In negative degree the extended term is zero, whose pushforward
is zero and is quasi-coherent. If no tuples exist, the product is likewise zero.
No covering hypothesis is needed. -/
theorem alternatingCechSheafComplex_affineQuasicoherent
    {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A) [IsSeparated f]
    {r : ℕ} (U : Fin r → X.Opens) (haffine : ∀ i, IsAffineOpen (U i))
    (G : X.Modules) [SheafOfModules.IsQuasicoherent.{u} G] (i : ℤ) :
    SheafOfModules.IsQuasicoherent.{u}
      ((((Scheme.Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((alternatingCechSheafComplex U G).extend ComplexShape.embeddingUpNat)).X i) :=
  by
  classical
  let : IsSeparated (Limits.terminal.from X) := by
    have h : IsSeparated (f ≫ Limits.terminal.from (Spec A)) := inferInstance
    convert h using 1
    exact Subsingleton.elim _ _
  by_cases hi : ∃ p : ℕ, ComplexShape.embeddingUpNat.f p = i
  · obtain ⟨p, hp⟩ := hi
    let C := alternatingCechSheafComplex U G
    let F := Scheme.Modules.pushforward f
    obtain ⟨e⟩ := alternatingCechSheafComplex_terms U G p
    let M (t : Fin (p + 1) ↪o Fin r) :=
      (Scheme.Modules.pushforward (alternatingCechIntersection U t).ι).obj
        (G.restrict (alternatingCechIntersection U t).ι)
    have hM (t : Fin (p + 1) ↪o Fin r) :
        SheafOfModules.IsQuasicoherent.{u} (F.obj (M t)) := by
      have ht : IsAffineOpen (alternatingCechIntersection U t) :=
        IsAffineOpen.iInf (fun k ↦ haffine (t k))
      let : IsAffine (alternatingCechIntersection U t).toScheme := ht
      let j := (alternatingCechIntersection U t).ι
      have hqc := Scheme.Modules.isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated (j ≫ f)
        (G.restrict j)
      exact (SheafOfModules.isQuasicoherent.{u} (Spec A).ringCatSheaf).prop_of_iso
        ((Scheme.Modules.pushforwardComp j f).app (G.restrict j)).symm hqc
    let : ∀ t, SheafOfModules.IsQuasicoherent.{u} (F.obj (M t)) := hM
    let e' := F.mapIso (C.extendXIso ComplexShape.embeddingUpNat hp) ≪≫
      F.mapIso e ≪≫ PreservesProduct.iso F M
    exact (SheafOfModules.isQuasicoherent.{u} (Spec A).ringCatSheaf).prop_of_iso e'.symm
      (quasicoherent_product (fun t ↦ F.obj (M t)))
  · let C := alternatingCechSheafComplex U G
    have hz := C.isZero_extend_X ComplexShape.embeddingUpNat i
      (fun p hp ↦ hi ⟨p, hp⟩)
    have hzf := (Scheme.Modules.pushforward f).map_isZero hz
    let Z := (tilde.functor A).obj (0 : ModuleCat.{u} A)
    have hzZ : Limits.IsZero Z := (tilde.functor A).map_isZero (isZero_zero _)
    let e := hzf.isoZero ≪≫ hzZ.isoZero.symm
    exact (SheafOfModules.isQuasicoherent.{u} (Spec A).ringCatSheaf).prop_of_iso e.symm
      (inferInstance : SheafOfModules.IsQuasicoherent.{u} Z)

end AlgebraicGeometry
