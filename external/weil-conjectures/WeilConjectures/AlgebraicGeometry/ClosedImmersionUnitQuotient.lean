/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Abelian.Images
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitKernel
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Closed immersion unit and quotient

Source: Stacks Project, Morphisms of Spaces, Lemma 04CJ (part (1)), with the
stalkwise proof in Modules, Lemma 08KS (blueprint: lem-weil-pbc-closed-immersion-unit-quotient).
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- For a closed immersion `i : Z ⟶ Y` with ideal sheaf `J = i.ker`, and every
`𝒪_Y`-module `F`, the unit `η_F : F ⟶ i_* i^* F` of `i^* ⊣ i_*` is an epimorphism
with kernel `JF`, and it induces an isomorphism `η̄_F : F/JF ≅ i_* i^* F`, natural in `F`.

Here, as in `conductorIdealZeroIntersection`, `JF` is `image μ_F` for the multiplication map
`μ_F = J.toModulesι ▷ F ≫ λ_F : J ⊗ F ⟶ F`, `F/JF` is `cokernel (image.ι μ_F)`, and
`η̄_F` is the map with `cokernel.π ≫ η̄_F = η_F`. The last clause gives, for every
`a : F ⟶ G`, the induced map `q` on quotients and the naturality square of `η̄`.

Source: Stacks Project, Morphisms of Spaces, Lemma 04CJ (1), and Modules,
Lemma 08KS (blueprint: lem-weil-pbc-closed-immersion-unit-quotient).
Proof, following the node's six steps:
1. The adjunction of `def-pc-module-pullback` gives the unit. Compute its stalks,
using `lem-weil-pbc-module-iso-on-stalks` and
`lem-weil-pbc-locally-surjective-iff-stalks` to test isomorphisms and surjectivity.
2. Outside the closed image, `lem-weil-pbc-closed-pushforward-stalks` gives a zero
target stalk. On a neighbourhood disjoint from the image the ideal is the unit
ideal (`def-sbc-closed-immersion-ideal-sheaf`), so `JF` is the entire module.
3. At `x = i(z)`, the closed immersion makes the local ring map `R → S`
surjective, with kernel `K = J_x`, by the same ideal definition and pushforward
stalk calculation.
4. By `lem-weil-pbc-module-stalk-pullback` and the closed pushforward stalk lemma,
the unit is `M → M ⊗_R S`, sending `m` to `m ⊗ 1`.
5. Identify `S` with `R/K`. The inverse of the induced quotient map sends
`m ⊗ r̄` to `rm + KM`; the tensor relations show it is well-defined. Thus the
unit is surjective with kernel `KM`. The image of sheaf multiplication has
stalk `J_x F_x`, using `def-pur-sheaf-tensor-product`.
6. The stalk criteria give global sheaf surjectivity and kernel `JF`. The sheaf
first-isomorphism theorem gives the induced isomorphism `F/JF ≅ i_* i^* F`;
equivalently its stalks are the isomorphisms just computed. Naturality of the unit
and the universal property of cokernels give the final quotient squares. -/
theorem closedImmersion_unit_quotient {Y Z : Scheme.{w}} (i : Z ⟶ Y)
    [IsClosedImmersion i] :
    let adj : tensorPullback i ⊣ pushforward i :=
      Classical.choice (nonempty_tensorPullbackAdjunction i)
    let J : Y.IdealSheafData := i.ker
    let μ : ∀ F : Y.Modules, J.toModules ⊗ F ⟶ F := fun F =>
      J.toModulesι ▷ F ≫ (λ_ F).hom
    ∃ η' : ∀ F : Y.Modules,
        cokernel (image.ι (μ F)) ⟶ (pushforward i).obj ((tensorPullback i).obj F),
      (∀ F : Y.Modules,
        Epi (adj.unit.app F) ∧
          (∃ w : image.ι (μ F) ≫ adj.unit.app F = 0,
            Nonempty (IsLimit (KernelFork.ofι (image.ι (μ F)) w))) ∧
          cokernel.π (image.ι (μ F)) ≫ η' F = adj.unit.app F ∧ IsIso (η' F)) ∧
      ∀ (F G : Y.Modules) (a : F ⟶ G),
        ∃ q : cokernel (image.ι (μ F)) ⟶ cokernel (image.ι (μ G)),
          cokernel.π (image.ι (μ F)) ≫ q = a ≫ cokernel.π (image.ι (μ G)) ∧
            q ≫ η' G = η' F ≫ (pushforward i).map ((tensorPullback i).map a) := by
  dsimp
  let adj : tensorPullback i ⊣ pushforward i :=
    Classical.choice (nonempty_tensorPullbackAdjunction i)
  let μ : ∀ F : Y.Modules, i.ker.toModules ⊗ F ⟶ F := fun F =>
    i.ker.toModulesι ▷ F ≫ (λ_ F).hom
  have h := closedImmersion_unit_kernel i
  dsimp at h
  have hex : ∀ F : Y.Modules,
      ∃ e : cokernel (image.ι (μ F)) ≅ (pushforward i).obj ((tensorPullback i).obj F),
        cokernel.π (image.ι (μ F)) ≫ e.hom = adj.unit.app F := by
    intro F
    obtain ⟨he, w, ⟨hk⟩⟩ := h F
    have : Epi (adj.unit.app F) := he
    let hc := Abelian.epiIsCokernelOfKernel (KernelFork.ofι _ w) hk
    let e := (cokernelIsCokernel (image.ι (μ F))).coconePointUniqueUpToIso hc
    refine ⟨e, ?_⟩
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel (image.ι (μ F))) hc WalkingParallelPair.one
  choose e he using hex
  refine ⟨fun F => (e F).hom, ?_, ?_⟩
  · intro F
    exact ⟨(h F).1, (h F).2, he F, inferInstance⟩
  · intro F G a
    refine ⟨(e F).hom ≫ (pushforward i).map ((tensorPullback i).map a) ≫
      (e G).inv, ?_, ?_⟩
    · rw [← Category.assoc, he F]
      change adj.unit.app F ≫ (tensorPullback i ⋙ pushforward i).map a ≫
        (e G).inv = a ≫ cokernel.π (image.ι (μ G))
      rw [← adj.unit.naturality_assoc, ← he G]
      simp
    · simp

end
end AlgebraicGeometry.Scheme.Modules
