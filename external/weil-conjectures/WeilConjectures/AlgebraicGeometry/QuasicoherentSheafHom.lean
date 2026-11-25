/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.HomLocalKernelOfPresentation
import Mathlib.Data.Fintype.EquivFin

/-! # Quasi-coherence of sheaf Hom from a finitely presented module

Source: Stacks Project, Schemes, Section 01LA, item (10), using Modules, Lemma 01CQ
(blueprint: lem-weil-pbc-sheaf-hom-finite-presentation-quasi-coherent).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory CategoryTheory.Limits TopologicalSpace in
set_option backward.isDefEq.respectTransparency false in
/-- A finite biproduct of copies of a sheaf of modules `A` isomorphic to the unit is
isomorphic to the free sheaf of modules on a finite index type of the same cardinality. -/
noncomputable def finiteFreeIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasFiniteBiproducts (SheafOfModules.{u} R)]
    (A : SheafOfModules.{u} R) (η : A ≅ SheafOfModules.unit R)
    (I : Type u) [Fintype I] :
    (⨁ fun _ : Fin (Fintype.card I) ↦ A) ≅ SheafOfModules.free (R := R) I :=
  biproduct.isoCoproduct _ ≪≫ Sigma.mapIso (fun _ ↦ η) ≪≫
    Sigma.reindex (Fintype.equivFin I).symm (fun _ ↦ SheafOfModules.unit R)

open CategoryTheory CategoryTheory.Limits TopologicalSpace in
private theorem isQuasicoherent_overEquiv_inverse (X : Scheme.{u}) (U : X.Opens)
    (M : U.toScheme.Modules) [M.IsQuasicoherent] :
    ((overEquiv (X := X) U).inverse.obj M).IsQuasicoherent := by
  have (V : CategoryTheory.Over U) :
      (Over.post (X := V) U.overEquivalence.symm.inverse).IsContinuous
        ((Opens.grothendieckTopology ↥X).over U |>.over V)
        ((Opens.grothendieckTopology ↥U).over
          (U.overEquivalence.functor.obj V)) :=
    Functor.isContinuous_of_coverPreserving
      (compatiblePreservingOfFlat _ _)
      (((U.overEquivalence.symm.toAdjunction.isCocontinuous_iff_coverPreserving _ _).mp
        inferInstance).overPost V)
  exact @SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint.{u, u, u, u, u}
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf) _ _ (fun V ↦ this V) _ _ M _

open CategoryTheory CategoryTheory.Limits TopologicalSpace in
private theorem isQuasicoherent_finiteBiproduct {X : Scheme.{u}} (F : X.Modules)
    [HasFiniteBiproducts X.Modules] [F.IsQuasicoherent] (n : ℕ) :
    (⨁ fun _ : Fin n ↦ F).IsQuasicoherent := by
  let e : (⨁ fun _ : Fin n ↦ F) ≅ ∐ (fun _ : ULift.{u} (Fin n) ↦ F) :=
    biproduct.isoCoproduct _ ≪≫
      Sigma.reindex Equiv.ulift.symm (fun _ : ULift.{u} (Fin n) ↦ F)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e.symm
    (isQuasicoherent_sigma (fun _ : ULift.{u} (Fin n) ↦ F))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- On a scheme `X`, sheaf Hom from a finitely presented module `G` into a quasi-coherent
module `F` is quasi-coherent. Its sections over `W` are the `O_W`-linear maps
`G|_W ⟶ F|_W`, as in `SheafOfModules.homObj`.
Source: Stacks Project, Schemes, Section 01LA, item (10), and Modules, Lemma 01CQ
(blueprint: lem-weil-pbc-sheaf-hom-finite-presentation-quasi-coherent).

Proof:
1. At each point choose a finite free cokernel presentation `O_U^m → O_U^n → G|_U`
   using `def-weil-pbc-module-finite-type-presentation`. Restriction preserves that
   cokernel and quasi-coherence of `F`, by
   `lem-weil-pbc-module-restriction-open-immersion-colimits`.
2. Finite direct sums of `F|_U` are quasi-coherent by
   `lem-weil-pbc-quasi-coherent-module-direct-sum`. For rank zero, the zero module is
   the kernel of the identity of `F|_U`, using `lem-weil-pbc-quasi-coherent-module-kernel`.
3. Write the presentation map as a matrix `(a_ik)` of sections of `O_U`. The induced
   map `(F|_U)^n → (F|_U)^m` sends `(s_i)` to `(∑ i, a_ik s_i)_k`. On every open
   `W ⊆ U`, a map from `O_W^n` is determined by the images of the basis sections.
   It factors uniquely through `G|_W` exactly when that tuple is in this matrix
   map's kernel. The identification commutes with restriction, so `def-pur-sheaf-hom`
   identifies the Hom sheaf on `U` with this kernel. The kernel is quasi-coherent by
   `lem-weil-pbc-quasi-coherent-module-kernel`.
4. Every point has such a neighbourhood. Its affine refinements give the required
   local quasi-coherence of the Hom sheaf by `pqf-def-coherent`. -/
theorem isQuasicoherent_homObj_of_isFinitePresentation (X : Scheme.{u}) (G F : X.Modules)
    [G.IsFinitePresentation] [F.IsQuasicoherent] :
    (SheafOfModules.homObj (R := X.sheaf) G F).IsQuasicoherent :=
    open CategoryTheory CategoryTheory.Limits TopologicalSpace in by
  classical
  let : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts
  let J := Opens.grothendieckTopology X
  have : HasSheafify J AddCommGrpCat.{u} := inferInstance
  have : J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  have (U : X.Opens) : HasSheafify (J.over U) AddCommGrpCat.{u} := inferInstance
  have (U : X.Opens) : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  have (U : X.Opens) (V : Over U) :
      HasSheafify ((J.over U).over V) AddCommGrpCat.{u} := inferInstance
  have (U : X.Opens) (V : Over U) :
      ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  obtain ⟨p, hp⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData G
  let H : X.Modules := SheafOfModules.homObj (R := X.sheaf) G F
  have hlocal (i : p.I) : (H.over (p.X i)).IsQuasicoherent := by
    let U : X.Opens := p.X i
    let : HasFiniteBiproducts (SheafOfModules.{u} (X.ringCatSheaf.over U)) :=
      HasFiniteBiproducts.of_hasFiniteProducts
    let : HasFiniteBiproducts U.toScheme.Modules :=
      HasFiniteBiproducts.of_hasFiniteProducts
    let P : (G.over U).Presentation := p.presentation i
    have : P.IsFinite := hp.isFinite_presentation i
    have : Finite P.generators.I := SheafOfModules.GeneratingSections.IsFiniteType.finite
    have : Finite P.relations.I := SheafOfModules.GeneratingSections.IsFiniteType.finite
    let gi : Fintype P.generators.I := Fintype.ofFinite _
    let ri : Fintype P.relations.I := Fintype.ofFinite _
    let n : ℕ := @Fintype.card P.generators.I gi
    let m : ℕ := @Fintype.card P.relations.I ri
    let η : (SheafOfModules.unit X.ringCatSheaf).over U ≅
        SheafOfModules.unit (X.ringCatSheaf.over U) :=
      Iso.refl (SheafOfModules.unit (X.ringCatSheaf.over U))
    let eg := finiteFreeIso (X.ringCatSheaf.over U) _ η P.generators.I
    let er := finiteFreeIso (X.ringCatSheaf.over U) _ η P.relations.I
    let a₀ := CategoryStruct.comp P.relations.π (kernel.ι P.generators.π)
    let a := CategoryStruct.comp er.hom (CategoryStruct.comp a₀ eg.inv)
    let b := CategoryStruct.comp eg.hom P.generators.π
    have hab : CategoryStruct.comp a b = 0 := by simp [a, b, a₀]
    have hc : IsColimit (CokernelCofork.ofπ b hab) :=
      IsCokernel.ofIso _ P.isColimit _ er.symm eg.symm (Iso.refl _)
        (by simp [a, a₀]) (by simp [b])
    let e := (hc.coconePointUniqueUpToIso (cokernelIsCokernel a)).symm
    obtain ⟨α, ⟨eH⟩⟩ := homObj_locally_kernel_of_local_presentation X G F U m n a e
    have : (biproduct (fun _ : Fin n ↦ F.restrict U.ι)).IsQuasicoherent :=
      isQuasicoherent_finiteBiproduct _ n
    have : (biproduct (fun _ : Fin m ↦ F.restrict U.ι)).IsQuasicoherent :=
      isQuasicoherent_finiteBiproduct _ m
    have : (kernel α).IsQuasicoherent := isQuasicoherent_kernel α
    have : (H.restrict U.ι).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso eH.symm
        inferInstance
    have hback := isQuasicoherent_overEquiv_inverse X U (H.restrict U.ι)
    let eback : (overEquiv U).inverse.obj (H.restrict U.ι) ≅ H.over U :=
      ((overEquiv U).inverse.mapIso ((overFunctorEquiv U).app H).symm).trans
        ((overEquiv U).unitIso.app (H.over U)).symm
    exact (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over U)).prop_of_iso eback hback
  exact @SheafOfModules.IsQuasicoherent.of_coversTop _ _ _ _ _ _ _ _
    H p.I p.X p.coversTop hlocal

end AlgebraicGeometry.Scheme.Modules
