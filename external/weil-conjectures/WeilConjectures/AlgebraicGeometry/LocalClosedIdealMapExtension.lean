/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.AlgebraicGeometry.ClosedStructureAmbientIdealExtension
import WeilConjectures.AlgebraicGeometry.ClosedStructureIdealProductIso
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-! # Clearing denominators for a local map from a closed structure module

Source: Stacks Project, Tags 01YB and 01YE, the ideal-power extension step.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- A local map from a closed structure module extends after restricting its source
by a nonzero ideal on the integral closed subscheme. No injectivity is assumed or
asserted. Agreement holds on the entire given open, not just on the generic stalk.
Source: Stacks Project, Tag 01YB (extension from ideal powers), as used in the last
paragraph of Tag 01YE, with the affine closed-pushforward calculation of Tag 01QY.
(blueprint: lem-pc-local-closed-ideal-map-extension)

Proof: let I be the vanishing ideal of the closed complement of U. Mathlib's
support formula identifies its support with that complement. The ambient extension
lemma applies Tag 01YB to H = i_*O_W and G and gives n and chi:I^n H -> G with the
specified equality on U. Define J = (I^n).comap i using actual ideal-sheaf data.
Its support is the inverse image of the support of I^n, which is contained in the
support of I. If J were zero, its support would be all of W, so i(eta) would lie
outside U, contradicting hx. Thus J is nonzero, including when n = 0. The normalized
closed structure ideal-product comparison gives an isomorphism e:i_*J -> I^n H
commuting with the inclusions into H. Set alpha = e.hom followed by chi. Restriction
preserves composition; associativity and the two inclusion equations prove agreement
on the entire U. This also covers a zero local map and U = X; there is no assertion
that alpha is injective. The two bridge lemmas carry the ambient extension and affine
comparison steps separately. No unproved existence theorem supplies the data of J. -/
theorem local_closed_ideal_map_extension
    {X W : Scheme.{u}} [IsNoetherian X]
    (i : W ⟶ X) [IsClosedImmersion i] [IsIntegral W]
    (G : X.Modules) (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (U : X.Opens) (hx : i.base (genericPoint W) ∈ U)
    (φ : (restrictFunctor U.ι).obj
        ((pushforward i).obj (SheafOfModules.unit W.ringCatSheaf)) ⟶
      (restrictFunctor U.ι).obj G) :
    ∃ (J : W.IdealSheafData), J ≠ ⊥ ∧
      ∃ (α : (pushforward i).obj J.toModules ⟶ G),
        (restrictFunctor U.ι).map α =
          (restrictFunctor U.ι).map ((pushforward i).map J.toModulesι) ≫ φ := by
  let I : X.IdealSheafData := IdealSheafData.vanishingIdeal ⟨(U : Set X)ᶜ, U.2.isClosed_compl⟩
  have hI : (I.support : Set X) = (U : Set X)ᶜ := by
    simp [I]
  obtain ⟨n, χ, hχ⟩ := closed_structure_ambient_ideal_extension i I G hG U hI φ
  let J : W.IdealSheafData := (I ^ n).comap i
  have hJ : J ≠ ⊥ := by
    intro hzero
    have hmem : genericPoint W ∈ (J.support : Set W) := by
      rw [hzero, IdealSheafData.support_bot]
      trivial
    have hmem' : i.base (genericPoint W) ∈ ((I ^ n).support : Set X) := by
      change genericPoint W ∈ (((I ^ n).comap i).support : Set W) at hmem
      rw [IdealSheafData.support_comap] at hmem
      exact hmem
    have hmemI : i.base (genericPoint W) ∈ (I.support : Set X) :=
      IdealSheafData.support_pow_le n hmem'
    rw [hI] at hmemI
    exact hmemI hx
  obtain ⟨e, he⟩ := closed_structure_ideal_product_iso i (I ^ n)
  refine ⟨J, hJ, e.hom ≫ χ, ?_⟩
  rw [Functor.map_comp, hχ, ← Category.assoc, ← Functor.map_comp, he]


end AlgebraicGeometry.Scheme.Modules
