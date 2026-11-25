/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.LocallyConstantNonzeroGerms
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # A generic stalk detects kernels in a locally constant sheaf

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-weil-pbc-lisse-generic-kernel`
(blueprint: lem-weil-pbc-lisse-generic-kernel).
-/

@[expose] public section

universe u₂

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A morphism from a locally constant abelian étale sheaf is mono when its
geometric generic stalk map is mono. Local constancy is that of
`def-weil-pbc-etale-sheaves`, applied to the underlying sheaf of sets.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-weil-pbc-lisse-generic-kernel`,
node `lem-weil-pbc-lisse-generic-kernel` (blueprint: lem-weil-pbc-lisse-generic-kernel).
Proof:
1. Set `N = ker φ`. Exactness of geometric stalks
   (`prop-weil-pbc-geometric-stalks-exact`) gives injective maps from stalks of `N`
   to stalks of `F` and a zero generic stalk of `N`. If `N` were nonzero,
   `lemma-weil-pbc-geometric-stalk-conservative` would give a nonzero geometric germ.
   Choose an étale cover member `V` on which the underlying sheaf of sets of `F` is
   isomorphic to the constant sheaf of a set `M` (`def-weil-pbc-etale-sheaves`,
   `def-weil-pbc-constant-sheaf`).
   Lift the geometric point to `V`: the nonempty étale fibre over its algebraically
   closed field has a rational point. Pointed neighbourhoods over `V` are cofinal
   among those on `X`, by fibre products (`def-weil-pbc-geometric-stalks`), so both
   stalks are unchanged. Represent the nonzero germ by a section `s` of `N` on a
   pointed neighbourhood. The constant-sheaf stalk formula
   (`definition-torsion-sheaves--3`) identifies the germs of the image
   of `s` in `F` and of the zero section of `F` with elements `m ≠ z` of `M`.
   Equality in a filtered colimit holds after refinement: shrink to a nonempty pointed
   étale neighbourhood `W` where the image of `s` is constantly `m` and the zero
   section is constantly `z`.
2. The image of `W → X` is open by `lem-weil-pbc-flat-lfp-open`, since étale maps
   are flat and locally of finite presentation. It is nonempty and hence contains
   the generic point. The fibre over the chosen geometric generic point is
   nonempty and étale over an algebraically closed field, so has a rational point.
   At this pointed neighbourhood the section `s` of `N` has zero germ, since its
   generic stalk is zero. Its image in `F` nevertheless has nonzero germ: cofinality
   identifies this with the stalk of the constant sheaf on `V`, and
   `definition-torsion-sheaves--3` sends `m ≠ z` to distinct germs.
   This contradiction gives `N = 0`, and therefore `φ` is a monomorphism.
-/
theorem mono_of_mono_generic_stalk
    (X : Scheme.{u₂}) (hX : IsIrreducible (Set.univ : Set X))
    (hne : Nonempty X) (η : X)
    (hη : IsGenericPoint η (Set.univ : Set X))
    (Ω : Type u₂) [Field Ω] [IsAlgClosed Ω]
    (barη : Spec (.of Ω) ⟶ X) (hbarη : barη default = η)
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u₂ + 1})
    (hF : IsLocallyConstantEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u₂ + 1})).obj F))
    (φ : F ⟶ G)
    (hφ : Mono ((pointSmallEtale barη).sheafFiber.map φ)) : Mono φ := by
  classical
  have _ := hX
  have _ := hne
  let := hφ
  apply Abelian.mono_of_kernel_ι_eq_zero
  by_contra hk
  obtain ⟨U, hU, s, hs⟩ := exists_section_everywhere_nonzero_germ X (kernel φ) F hF
    (kernel.ι φ) hk
  have hopen : IsOpen (Set.range U.hom) := U.hom.isOpenMap.isOpen_range
  have hmem : η ∈ Set.range U.hom := (hη.mem_open_set_iff hopen).2
    ⟨U.hom (Classical.choice hU), Set.mem_univ _, Set.mem_range_self _⟩
  obtain ⟨w, hw⟩ := hmem
  obtain ⟨t, ht⟩ := pointSmallEtaleFiberObjToPreimage_surjective barη hbarη U
    ⟨w, by simpa using hw⟩
  have hz : (pointSmallEtale barη).sheafFiber.map (kernel.ι φ) = 0 := by
    apply (cancel_mono ((pointSmallEtale barη).sheafFiber.map φ)).1
    simp only [← Functor.map_comp, kernel.condition, Functor.map_zero, zero_comp]
  have hnat := (pointSmallEtale barη).toPresheafFiber_naturality
    (kernel.ι φ).hom U t
  have hzero : (pointSmallEtale barη).toPresheafFiber U t F.obj
      ((kernel.ι φ).hom.app (Opposite.op U) s) = 0 := by
    have heq : (kernel.ι φ).hom.app (Opposite.op U) ≫
        (pointSmallEtale barη).toPresheafFiber U t F.obj = 0 := by
      rw [← hnat]
      change (pointSmallEtale barη).toPresheafFiber U t (kernel φ).obj ≫
        (pointSmallEtale barη).sheafFiber.map (kernel.ι φ) = 0
      rw [hz, comp_zero]
    exact congrArg (fun f ↦ f s) heq
  exact hs Ω barη t hzero



end AlgebraicGeometry.Scheme
