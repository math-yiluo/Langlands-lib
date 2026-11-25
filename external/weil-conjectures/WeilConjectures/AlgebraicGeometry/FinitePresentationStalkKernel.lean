/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Exact.Basic
import WeilConjectures.AlgebraicGeometry.StalkInternalHomEvaluation
import WeilConjectures.AlgebraicGeometry.FinitePresentationSourceStalk
import WeilConjectures.AlgebraicGeometry.InternalHomGermZeroFiniteType
import WeilConjectures.AlgebraicGeometry.StalkLinearMapLocalLiftFinitePresentation
import Mathlib.LinearAlgebra.LeftExact
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-!
# A local finite presentation and its internal-Hom stalk kernel

Source: Stacks Project, Modules, Lemma 01CP (`lemma-stalk-internal-hom`), third paragraph
(blueprint: lem-weil-pbc-finite-presentation-stalk-kernel).
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

/-- A local finite presentation supplies a presentation of the source stalk and
an injective coordinate map on the internal-Hom stalk, with the indicated kernel image.
It does not construct or assert bijectivity of the canonical stalk-Hom map.

Source: Stacks Project, Modules, Lemma 01CP (`lemma-stalk-internal-hom`), third paragraph,
using Lemma 01CO (1) for the internal-Hom exact sequence.
(blueprint: lem-weil-pbc-finite-presentation-stalk-kernel)

Proof: Choose a finite free presentation on a neighborhood U of x from
IsFinitePresentation, with basis images s_i in F(U). Identify the stalks of the two
free modules with tuples over O_x by taking component germs. Finite tuples have
representatives on a common neighborhood, and equalities of their germs likewise
hold on a common neighborhood; this proves these identifications are bijective.
Exactness of module stalks gives maps a and b with b surjective and ker(b) = range(a).
Apply homObj_finitePresentation_kernel to the local presentation. Identify the stalk
of its finite product of copies of G with tuples in G_x by the same common-neighborhood
argument. The resulting map beta is injective, and its image is the kernel of
precomposition by a, transported through the finite free evaluation isomorphisms.
The displayed formula for beta follows by taking germs of the sectionwise evaluation
formula in homObj_finitePresentation_kernel. Restriction to U does not change any
stalk at x: its neighborhoods are cofinal among those in X, and restricting internal
Hom has the same local-morphism sections. Hence this formula holds for every W,
using the neighborhood U intersect W and the restricted basis sections. -/
theorem exists_finitePresentation_stalk_kernel
    (X : RingedSpace.{u})
    (F G : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf))
    [SheafOfModules.IsFinitePresentation.{u} F] (x : X) :
    ∃ (U : Opens X) (hxU : x ∈ U) (m n : ℕ) (s : Fin n → F.val.obj (op U))
      (a : (Fin m → X.presheaf.stalk x) →ₗ[X.presheaf.stalk x]
        (Fin n → X.presheaf.stalk x))
      (b : (Fin n → X.presheaf.stalk x) →ₗ[X.presheaf.stalk x]
        (moduleStalkFunctor X x).obj F)
      (β : (moduleStalkFunctor X x).obj (F.homObj G) →ₗ[X.presheaf.stalk x]
        (Fin n → (moduleStalkFunctor X x).obj G)),
      Function.Surjective b ∧ Function.Exact a b ∧
      (∀ i, b (Pi.single i 1) = TopCat.Presheaf.germ F.val.presheaf U x hxU (s i)) ∧
      Function.Injective β ∧
      LinearMap.range β = LinearMap.ker
        (((LinearEquiv.piRing (X.presheaf.stalk x)
          ((moduleStalkFunctor X x).obj G) (Fin m) (X.presheaf.stalk x)).toLinearMap).comp
          ((LinearMap.lcomp (X.presheaf.stalk x) ((moduleStalkFunctor X x).obj G) a).comp
            (LinearEquiv.piRing (X.presheaf.stalk x)
              ((moduleStalkFunctor X x).obj G) (Fin n) (X.presheaf.stalk x)).symm.toLinearMap)) ∧
      (∀ (W : Opens X) (hxW : x ∈ W) (φ : (F.homObj G).val.obj (op W)) (i : Fin n),
        β (TopCat.Presheaf.germ (F.homObj G).val.presheaf W x hxW φ) i =
          TopCat.Presheaf.germ G.val.presheaf (U ⊓ W) x ⟨hxU, hxW⟩
            (φ.app (op (Over.mk (homOfLE inf_le_right : U ⊓ W ⟶ W)))
              (F.val.presheaf.map (homOfLE inf_le_left : U ⊓ W ⟶ U).op (s i)))) := by
  classical
  obtain ⟨U, hxU, m, n, s, a, b, hb, hab, hs⟩ :=
    exists_finitePresentation_source_stalk X F x
  obtain ⟨c, hc⟩ := exists_stalk_internalHom_linearMap X F G x
  let R := X.presheaf.stalk x
  let N := (moduleStalkFunctor X x).obj G
  let θn := LinearEquiv.piRing R N (Fin n) R
  let θm := LinearEquiv.piRing R N (Fin m) R
  let ε := θn.toLinearMap.comp (LinearMap.lcomp R N b)
  let α := θm.toLinearMap.comp ((LinearMap.lcomp R N a).comp θn.symm.toLinearMap)
  let β := ε.comp c
  have hc_inj : Function.Injective c := by
    apply (injective_iff_map_eq_zero c).2
    intro h hh
    obtain ⟨W, hxW, φ, rfl⟩ :=
      TopCat.Presheaf.exists_germ_eq (F.homObj G).val.presheaf h
    apply internalHom_germ_eq_zero_of_finiteType X F G x W hxW φ
    intro V i hxV t
    rw [← hc W hxW φ V i hxV t, hh]
    rfl
  have hc_surj : Function.Surjective c := by
    intro χ
    obtain ⟨W, hxW, φ, hφ⟩ := exists_local_internalHom_of_stalkLinearMap X F G x χ
    refine ⟨TopCat.Presheaf.germ (F.homObj G).val.presheaf W x hxW φ, ?_⟩
    ext v
    obtain ⟨V, hxV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf v
    have hx : x ∈ W ⊓ V := ⟨hxW, hxV⟩
    rw [← TopCat.Presheaf.germ_res_apply F.val.presheaf
      (homOfLE inf_le_right : W ⊓ V ⟶ V) x hx t]
    exact (hc W hxW φ (W ⊓ V) (homOfLE inf_le_left) hx
      (F.val.presheaf.map (homOfLE inf_le_right : W ⊓ V ⟶ V).op t)).trans
        (hφ (W ⊓ V) (homOfLE inf_le_left) hx
          (F.val.presheaf.map (homOfLE inf_le_right : W ⊓ V ⟶ V).op t))
  have hε_inj : Function.Injective ε :=
    θn.injective.comp (LinearMap.lcomp_injective_of_surjective b hb)
  have hε_range : LinearMap.range ε = LinearMap.ker α := by
    ext y
    constructor
    · rintro ⟨χ, rfl⟩
      change θm ((LinearMap.lcomp R N a) (θn.symm (θn (χ.comp b)))) = 0
      rw [θn.symm_apply_apply]
      change θm ((χ.comp b).comp a) = 0
      rw [LinearMap.comp_assoc, hab.linearMap_comp_eq_zero, LinearMap.comp_zero, map_zero]
    · intro hy
      have hz : (LinearMap.lcomp R N a) (θn.symm y) = 0 := by
        apply θm.injective
        exact hy
      obtain ⟨χ, hχ⟩ :=
        (LinearMap.exact_lcomp_of_exact_of_surjective N hab hb) (θn.symm y) |>.mp hz
      refine ⟨χ, ?_⟩
      change θn ((LinearMap.lcomp R N b) χ) = y
      rw [hχ, θn.apply_symm_apply]
  refine ⟨U, hxU, m, n, s, a, b, β, hb, hab, hs, hε_inj.comp hc_inj, ?_, ?_⟩
  · exact (LinearMap.range_comp_of_range_eq_top ε
      (LinearMap.range_eq_top.mpr hc_surj)).trans hε_range
  · intro W hxW φ i
    change c (TopCat.Presheaf.germ (F.homObj G).val.presheaf W x hxW φ)
      (b (Pi.single i 1)) = _
    rw [hs]
    have hx : x ∈ U ⊓ W := ⟨hxU, hxW⟩
    rw [← TopCat.Presheaf.germ_res_apply F.val.presheaf
      (homOfLE inf_le_left : U ⊓ W ⟶ U) x hx (s i)]
    exact hc W hxW φ (U ⊓ W) (homOfLE inf_le_right) hx
      (F.val.presheaf.map (homOfLE inf_le_left : U ⊓ W ⟶ U).op (s i))

end AlgebraicGeometry.RingedSpace
