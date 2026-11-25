/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.AlgebraicGeometry.ModuleFiniteTypeImageExtension
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import WeilConjectures.AlgebraicGeometry.QuasiCoherentExtensionQcOpen
import WeilConjectures.AlgebraicGeometry.ModuleFiniteTypeApproximation

/-!
# Extension of finite-type quasi-coherent submodules

Source: Stacks Project, Properties, Lemma 01PF.
(blueprint: lem-weil-pbc-module-finite-type-submodule-extension).
-/

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

private theorem finiteType_of_submodule_extension_iso.{u₁, v₁}
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ A, HasSheafify (J.over A) AddCommGrpCat.{u}]
    [∀ A, (J.over A).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} R} (e : M ≅ N) [M.IsFiniteType] : N.IsFiniteType := by
  obtain ⟨q, hq⟩ := IsFiniteType.exists_localGeneratorsData M
  let q' : N.LocalGeneratorsData :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators i := (q.generators i).ofEpi (e.hom.over (q.X i)) }
  refine ⟨q', ⟨fun i ↦ ?_⟩⟩
  exact ⟨(hq.isFiniteType i).finite⟩

private theorem restricted_image_iso.{u₁, v₁, u₂, v₂}
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    (R : C ⥤ D) [R.PreservesEpimorphisms]
    {E F : C} (r : E ⟶ F) {G : D} (ι : G ⟶ R.obj F) [Mono ι]
    (e : R.obj E ≅ G) (hr : R.map r = e.hom ≫ ι) :
    ∃ e' : R.obj (Abelian.image r) ≅ G,
      R.map (Abelian.image.ι r) = e'.hom ≫ ι := by
  have : Mono (R.map r) := by rw [hr]; infer_instance
  have : Mono (R.map (Abelian.factorThruImage r)) :=
    mono_of_mono_fac (by rw [← Functor.map_comp, Abelian.image.fac])
  have : Epi (R.map (Abelian.factorThruImage r)) := R.map_epi _
  have : IsIso (R.map (Abelian.factorThruImage r)) := isIso_of_mono_of_epi _
  refine ⟨(asIso (R.map (Abelian.factorThruImage r))).symm ≪≫ e, ?_⟩
  apply (cancel_epi (R.map (Abelian.factorThruImage r))).mp
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc,
    IsIso.hom_inv_id_assoc]
  rw [← R.map_comp, Abelian.image.fac]
  exact hr

set_option backward.isDefEq.respectTransparency false in
/-- A finite-type quasi-coherent submodule on a quasi-compact open extends to the scheme.

Source: Stacks Project, Properties, Lemma 01PF.
(blueprint: lem-weil-pbc-module-finite-type-submodule-extension).

Proof:
1. Extend the prescribed inclusion using the quasi-coherent extension theorem 01PE(3),
   obtaining H, a map to F, and an isomorphism H restricted to U with G. The open
   immersion is quasi-compact because U is compact and X is quasi-separated.
2. Transport the finite local generators of G along the inverse isomorphism. Apply
   exists_finiteType_global_approximation to H: its finite-affine-cover induction
   uses exists_finiteType_affine_enlargement to obtain a quasi-coherent finite-type
   E with a monomorphism to H which restricts to an isomorphism on U.
3. Take the abelian image of the composite E to H to F. The image is quasi-coherent
   and finite type by quasiCoherent_cokernel_image and finiteType_image_extension.
   Over U the composite is the prescribed monomorphism preceded by an isomorphism.
   Its restricted factorization through the image is therefore monic, and it is
   epic because restriction preserves epimorphisms; hence it is an isomorphism.
4. Compose its inverse with the restriction E to H and the isomorphism to G.
   Cancel the restricted factorization through the image to prove that this
   isomorphism commutes with the inclusions into F restricted to U. -/
theorem exists_quasicoherent_finiteType_submodule_extension
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (U : X.Opens) (hU : IsCompact (U : Set X))
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [F.IsQuasicoherent]
    (G : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    [G.IsQuasicoherent] [G.IsFiniteType]
    (ι : G ⟶ F.over U) [Mono ι] :
    ∃ (G' : SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      G'.IsQuasicoherent ∧ G'.IsFiniteType ∧
        ∃ (ι' : G' ⟶ F), Mono ι' ∧ ∃ (e : G'.over U ≅ G),
          (SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U).map ι' = e.hom ≫ ι := by
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  obtain ⟨H, hH, ψ, α, hψ⟩ :=
    exists_quasiCoherent_extension_of_quasiCompact_open X U inferInstance F G ι
  have : H.IsQuasicoherent := hH
  have : (H.over U).IsFiniteType := finiteType_of_submodule_extension_iso.{u, u, u} α.symm
  obtain ⟨E, hE, hEft, j, hj, hjU⟩ := exists_finiteType_global_approximation X U hU H
  have : E.IsQuasicoherent := hE
  have : E.IsFiniteType := hEft
  let r := j ≫ ψ
  let R := SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U
  have : IsIso (R.map j) := hjU
  have hr : R.map r = (asIso (R.map j) ≪≫ α).hom ≫ ι := by
    change R.map (j ≫ ψ) = _
    rw [Functor.map_comp]
    change R.map j ≫ (SheafOfModules.overFunctor _ U).map ψ = _
    rw [hψ]
    rfl
  have : R.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction
      (SheafOfModules.overPushforwardOverAdj (R := moduleRings X.toRingedSpace) U)
  obtain ⟨e, he⟩ := restricted_image_iso R r ι (asIso (R.map j) ≪≫ α) hr
  have := isQuasicoherent_cokernel r
  have himg := isQuasicoherent_kernel (CategoryTheory.Limits.cokernel.π r)
  exact ⟨Abelian.image r, himg,
    (RingedSpace.finiteType_image_extension X.toRingedSpace).2.1 r,
    Abelian.image.ι r, inferInstance, e, he⟩

end AlgebraicGeometry.Scheme.Modules
