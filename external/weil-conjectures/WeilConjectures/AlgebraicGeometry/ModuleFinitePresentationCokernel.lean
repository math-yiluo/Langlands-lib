/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.ModuleFinitePresentationCokernelKernel
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

/-!
# Finite presentation of cokernels on a ringed space

Source: Stacks Project, Modules, Lemma 0H96
(blueprint: lem-weil-pbc-module-finite-presentation-cokernel).

## Main statements

- `AlgebraicGeometry.RingedSpace.isFinitePresentation_cokernel_of_isFiniteType`:
  finite-type source and finitely presented target give a finitely presented cokernel.
- `AlgebraicGeometry.RingedSpace.isFinitePresentation_cokernel_of_both_isFinitePresentation`:
  the special case where both source and target are finitely presented.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.RingedSpace

-- Stacks 0H96, final step: refine the cover using finite generators of the kernel.
-- Reuses the proved construction from CoherentFiniteTypeLocallyNoetherian.lean.
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem isFinitePresentation_of_generators_kernel
    {C : Type u} [SmallCategory C] [HasBinaryProducts C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ V, HasSheafify (J.over V) AddCommGrpCat.{u}]
    [∀ V, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (M : SheafOfModules.{u} R) (G : M.GeneratingSections)
    [G.IsFiniteType] [(kernel G.π).IsFiniteType] : M.IsFinitePresentation := by
  classical
  obtain ⟨r, hr⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData (kernel G.π)
  let H (j : r.I) := SheafOfModules.overFunctor R (r.X j)
  have (j : r.I) : PreservesColimitsOfSize.{u, u} (H j) :=
    inferInstanceAs (PreservesColimitsOfSize.{u, u}
      (SheafOfModules.pushforward (F := Over.forget (r.X j)) (𝟙 (R.over (r.X j)))))
  let e (j : r.I) := SheafOfModules.mapFreeIso (H j) G.I (Iso.refl _)
  let a (j : r.I) := (r.generators j).π ≫ (H j).map (kernel.ι G.π) ≫ (e j).inv
  let b (j : r.I) := (G.map (H j) (Iso.refl _)).π
  have hab (j : r.I) : a j ≫ b j = 0 := by
    dsimp only [a, b]
    rw [SheafOfModules.GeneratingSections.map_π_eq]
    simp only [e, Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp,
      kernel.condition, Functor.map_zero, comp_zero]
  have hcol (j : r.I) : IsColimit (CokernelCofork.ofπ (b j) (hab j)) := by
    let c := CokernelCofork.ofπ G.π (kernel.condition G.π)
    have hc : IsColimit c := Abelian.epiIsCokernelOfKernel
      (KernelFork.ofι (kernel.ι G.π) (kernel.condition G.π))
      (kernelIsKernel _)
    have hh : ((H j).map (kernel.ι G.π) ≫ (e j).inv) ≫ b j = 0 := by
      dsimp only [b]
      rw [SheafOfModules.GeneratingSections.map_π_eq]
      simp only [e, Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp,
        kernel.condition, Functor.map_zero]
    let c' := CokernelCofork.ofπ (b j) hh
    have hc' : IsColimit c' := IsCokernel.ofIso _ (c.mapIsColimit hc (H j)) c'
      (Iso.refl _) (e j).symm (Iso.refl _) (by simp)
      (by
        simp only [c', CokernelCofork.π_ofπ, b, e,
          SheafOfModules.GeneratingSections.map_π_eq, Iso.symm_hom,
          Iso.refl_hom, Category.comp_id, Iso.inv_hom_id_assoc]
        rfl)
    exact isCokernelEpiComp hc' (r.generators j).π rfl
  let D : M.QuasicoherentData :=
    { I := r.I
      X := r.X
      coversTop := r.coversTop
      presentation j := SheafOfModules.presentationOfIsCokernelFree (a j) (b j)
        (hab j) (hcol j) }
  have : D.IsFinitePresentation := ⟨fun j ↦ by
    have := hr.isFiniteType j
    exact ⟨⟨inferInstanceAs (Finite G.I)⟩,
      ⟨inferInstanceAs (Finite (r.generators j).I)⟩⟩⟩
  exact D.isFinitePresentation

/-- Stacks Project, Modules, Lemma 0H96
(blueprint: lem-weil-pbc-module-finite-presentation-cokernel).
The cokernel of a map from a finite-type module sheaf to a finitely presented module sheaf
on a ringed space is finitely presented.

Proof (the seven steps of the node):
1. Restriction to opens preserves epis and exactness by the local lifting criterion
   (lem-weil-pbc-ringed-space-module-exactness-local-lifting), hence cokernels by
   lem-weil-pbc-abelian-exact-epi-cokernel. Both finiteness conditions are local and invariant
   under isomorphism (def-weil-pbc-module-finite-type-presentation). Finite free modules are
   finite type, and finite presentation implies finite type by its finite generating family.
2. Near each point choose a presentation O^m -> O^n -> H -> 0. Restrict f and its cokernel
   there. Locality reduces the claim to this presentation on the whole space.
3. The relations M = ker(O^n -> H) are finite type: the induced map O^m -> M is epi by
   lem-weil-pbc-abelian-exact-iff-epi-kernel-lift, and finite type passes to epi images by
   lem-weil-pbc-module-finite-type-image-extension (1).
4. The map G -> im(f) is epi by the same kernel-lift lemma. Thus im(f) is finite type by
   lem-weil-pbc-module-finite-type-image-extension (1).
5. Let N be the preimage of im(f) in O^n. Sectionwise kernels and local lifting give an
   exact sequence 0 -> M -> N -> im(f) -> 0 (def-weil-pbc-exact-sequence). Therefore N is
   finite type by lem-weil-pbc-module-finite-type-image-extension (2).
6. Near each point choose an epi O^s -> N. Its composite into O^n has cokernel Coker(f),
   since restriction preserves exactness and epis and an exact epi is a cokernel
   (lem-weil-pbc-abelian-exact-epi-cokernel). This finite presentation proves the claim.
7. If G is also finitely presented, step 1 makes it finite type, giving the final clause
   in `isFinitePresentation_cokernel_of_both_isFinitePresentation`. -/
theorem isFinitePresentation_cokernel_of_isFiniteType
    (X : RingedSpace.{u}) {G H : SheafOfModules.{u} (moduleRings X)}
    (f : G ⟶ H) [G.IsFiniteType] [H.IsFinitePresentation] :
    (cokernel f).IsFinitePresentation := by
  classical
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData H
  have hfp (i : q.I) : ((cokernel f).over (q.X i)).IsFinitePresentation := by
    let P := q.presentation i
    let F := SheafOfModules.overFunctor (moduleRings X) (q.X i)
    let g := P.generators.π ≫ F.map (cokernel.π f)
    have : Epi g := inferInstanceAs (Epi (P.generators.π ≫ F.map (cokernel.π f)))
    let S := SheafOfModules.GeneratingSections.ofEpiFree g
    have : P.IsFinite := hq.isFinite_presentation i
    have : S.IsFiniteType := ⟨inferInstanceAs (Finite P.generators.I)⟩
    have : (kernel S.π).IsFiniteType := by
      simpa only [S, SheafOfModules.GeneratingSections.ofEpiFree_π] using
        kernel_composite_cokernel_isFiniteType X (q.X i) f P
    exact isFinitePresentation_of_generators_kernel ((cokernel f).over (q.X i)) S
  exact @SheafOfModules.IsFinitePresentation.of_coversTop _ _ _ _ _ _ _ _
    (cokernel f) q.I q.X q.coversTop hfp

/-- Stacks Project, Modules, Lemma 0H96, its finite-presentation special case
(blueprint: lem-weil-pbc-module-finite-presentation-cokernel).

Proof: step 7 of the node applies Mathlib's instance
`SheafOfModules.instIsFiniteTypeOfIsFinitePresentation` to G, as its
local finite presentation supplies finitely many generators
(def-weil-pbc-module-finite-type-presentation). Then steps 1-6, stated above in
`isFinitePresentation_cokernel_of_isFiniteType`, give finite presentation of the cokernel. -/
theorem isFinitePresentation_cokernel_of_both_isFinitePresentation
    (X : RingedSpace.{u}) {G H : SheafOfModules.{u} (moduleRings X)}
    (f : G ⟶ H) [G.IsFinitePresentation] [H.IsFinitePresentation] :
    (cokernel f).IsFinitePresentation := by
  exact isFinitePresentation_cokernel_of_isFiniteType X f

end AlgebraicGeometry.RingedSpace
