/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.AlgebraicGeometry.CokernelTuplePullbackLocalFreeCover
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import Mathlib.CategoryTheory.Abelian.CommSq

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

set_option backward.isDefEq.respectTransparency false in
private theorem overMap_preserves_kernel (X : RingedSpace.{u})
    (U V : Opens X) (hVU : V ≤ U)
    {A B : SheafOfModules.{u} ((moduleRings X).over U)} (g : A ⟶ B) :
    PreservesLimit (parallelPair g 0)
      (SheafOfModules.overMap.{u} (moduleRings X) (homOfLE hVU)) := by
  apply preservesLimit_of_preserves_limit_cone (kernelIsKernel g)
  apply isLimitOfReflects (SheafOfModules.forget ((moduleRings X).over V))
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro W
  let E := SheafOfModules.evaluation ((moduleRings X).over U)
    (Opposite.op ((Over.map (homOfLE hVU)).obj W.unop))
  let T := ModuleCat.restrictScalars
    (RingCat.Hom.hom (𝟙 ((moduleRings X).obj.obj (Opposite.op W.unop.left))))
  exact isLimitOfPreserves (E ⋙ T) (kernelIsKernel g)

-- Prove the kernel comparison in an abstract abelian category, so constructing
-- the pushout and composing epimorphisms does not unfold sheaf restriction.
private theorem exists_epi_kernel_pullback_snd
    {C : Type*} [Category C] [Abelian C] {L B B' H P K : C}
    (g : L ⟶ H) (q : B ⟶ H) (p : P ⟶ pullback g q) [Epi p]
    (eB : B ≅ B') (k : kernel g ≅ K) :
    ∃ e : kernel (p ≫ pullback.snd g q ≫ eB.hom) ⟶ K, Epi e := by
  let ψ := p ≫ pullback.snd g q
  let a := kernel.map ψ (pullback.snd g q) p (𝟙 _) (by simp only [ψ, Category.comp_id])
  let b := kernel.map (pullback.snd g q) g (pullback.fst g q) q
    pullback.condition.symm
  have sq : IsPushout ψ p (𝟙 _) (pullback.snd g q) :=
    IsPushout.of_vert_isIso_epi ⟨by simp only [ψ, Category.comp_id]⟩
  have : Epi a := Abelian.epi_kernel_map_of_isPushout sq
  have : IsIso b :=
    isIso_kernel_map_of_isPullback (IsPullback.of_hasPullback g q).flip
  let i : kernel ψ ≅ kernel (p ≫ pullback.snd g q ≫ eB.hom) :=
    kernel.mapIso _ _ (Iso.refl _) eB (by simp only [ψ, Iso.refl_hom,
      Category.id_comp, Category.assoc])
  exact ⟨i.inv ≫ a ≫ b ≫ k.hom, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
-- Unfold the slice restriction functor in the kernel and pullback comparisons.
/-- Finite-free replacement for cokernel relations on a neighbourhood of each point.
Source: Stacks Project, Modules, Lemma 01BY, cokernel paragraph.
(blueprint: lem-weil-pbc-coherent-cokernel-relations-local)

Proof: Fix x in U. The cokernel projection G → cokernel f is an epimorphism
of module sheaves, so each of the n sections defining g lifts near x. Intersect
these finitely many neighbourhoods. The image of f is an epimorphic image of
F and is therefore of finite type; shrink again to choose finitely many sections
generating that image. Write V for the resulting neighbourhood inside U.
Combine the image generators and the chosen lifts into a map ψ from a finite
free module of rank m to G.over V. Projection onto the summands corresponding
to the n lifts sends kernel ψ to the restricted relation kernel of g. This map
is epi: a relation of the lifted sections has image in the image of f, so locally
it is a linear combination of the chosen image generators, and subtracting that
combination gives a section of kernel ψ lifting the relation. Equivalently, apply
the snake lemma to the split finite-free sequence and the image-G-cokernel
sequence. Restriction preserves kernels, since kernels are computed sectionwise,
so the target is the overMap restriction of kernel g. No quasi-compactness or
nonemptiness assumption is needed; n = 0 and an empty U cause no difficulty.

Historical explanation: the old fixed-U conclusion was false. On P¹_k take
U = X, F = I_p ≅ O(-1), G = O, f the ideal inclusion of a rational point, and
n = 1 with g the quotient onto k(p). Every ψ : O^m → O is a row of constants,
whose kernel is O^m or O^(m-1). Every morphism from this kernel to O(-1) is zero
because H⁰(P¹_k, O(-1)) = 0, and hence cannot be epi onto the nonzero kernel g.
The neighbourhood quantifiers below restore the shrinking in the cited proof. -/
theorem coherent_cokernel_relations_local (X : RingedSpace.{u})
    (F G : SheafOfModules.{u} (moduleRings X)) (f : F ⟶ G)
    (hF : F.IsFiniteType) (hG : IsCoherent X G)
    (U : Opens X) (n : ℕ)
    (g : SheafOfModules.free (R := (moduleRings X).over U) (ULift.{u} (Fin n)) ⟶
      (cokernel f).over U) :
    ∀ x : X, x ∈ U →
      ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
        ∃ (m : ℕ)
          (ψ : SheafOfModules.free (R := (moduleRings X).over V)
            (ULift.{u} (Fin m)) ⟶ G.over V),
          ∃ e : kernel ψ ⟶
            (SheafOfModules.overMap (moduleRings X) (homOfLE hVU)).obj (kernel g),
            Epi e := by
  intro x hx
  have _ := hG
  obtain ⟨V, hVU, hxV, m, p, hp⟩ :=
    cokernel_tuple_pullback_local_free_cover X F G f hF U n g x hx
  let D := SheafOfModules.overMap.{u} (moduleRings X) (homOfLE hVU)
  let gV := D.map g
  let q := D.map ((cokernel.π f).over U)
  let cG := (SheafOfModules.overFunctorMap (moduleRings X) (homOfLE hVU)).app G
  let ψ := p ≫ pullback.snd gV q ≫ cG.hom
  have : Epi p := hp
  have := overMap_preserves_kernel X U V hVU g
  obtain ⟨e, he⟩ :=
    exists_epi_kernel_pullback_snd gV q p cG (PreservesKernel.iso D g).symm
  exact ⟨V, hVU, hxV, m, ψ, e, he⟩

end AlgebraicGeometry.RingedSpace
