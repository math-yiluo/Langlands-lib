/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.CechComparisonSystem
import WeilConjectures.AlgebraicGeometry.Cohomology.CechCoverRelativeEffacementCore
import WeilConjectures.AlgebraicGeometry.Cohomology.InverseImageLocallySplitSections

/-! # Cover-relative effacement of positive Čech cohomology

Source: the relative-effacement argument of
`lem-pc-cech-comparison-inverse-image-unit`, Step 1, expanding the uniqueness
argument for Stacks Project, Tags 01EQ and 01FD.
(blueprint: lem-pc-cech-cover-relative-effacement)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- An effacement sequence split on cover members is suitable for both covers.

Source: `lem-pc-cech-comparison-inverse-image-unit`, proof Step 1; relative
Čech effacement used to identify normalized comparisons in Tags 01EQ and 01FD.
(blueprint: lem-pc-cech-cover-relative-effacement)

Proof: Set E to the product, over i, of the direct image of F restricted to U i,
and embed F by its restriction maps. This map is monic because the U i cover X.
Let Q be its cokernel. On U i, projection to the i-th factor retracts F → E,
so the cokernel sequence splits on U i and on every tuple intersection contained
in U i. Hence E → Q is surjective on all nonempty tuple sections. Exact inverse
image preserves the sequence and its splitting on preimages of U i. Every
V-tuple intersection lies in the preimage of its first U-member, so the pulled
back quotient map is also surjective on all V-tuple sections. In the Čech
complex of each direct-image factor, insert i at the front of a tuple; the
alternating face identity gives dh + hd = id in positive degrees. The Čech
complex of E is the product of these complexes; products of abelian groups are
exact, so E has zero positive Čech cohomology. The long exact sequence of the
sectionwise short exact Čech complexes therefore makes every positive connecting
map surjective. For an empty index, hcover forces X empty; Y is empty too and
the zero short exact sequence has every required property. -/
theorem exists_cechCoverRelativeEffacement
    {X Y : Scheme.{u}} {ι : Type u} (g : Y ⟶ X)
    (U : ι → X.Opens) (V : ι → Y.Opens) (hcover : iSup U = ⊤)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    ∃ (T : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})),
      T.X₁ = F ∧ ∃ (hT : T.ShortExact)
        (hg : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
          Function.Surjective (T.g.hom.app (op (⨅ l, U (y l))))),
        (∀ (k : ℕ) (y : Fin (k + 1) → ι),
          Function.Surjective (((invImage g).map T.g).hom.app (op (⨅ l, V (y l))))) ∧
        ∀ q, Function.Surjective (TopCat.Sheaf.cechδ U hT hg q) := by
  obtain ⟨T, hTF, hT, hg, hsplit, hδ⟩ :=
    exists_cechCoverRelativeEffacement_core U hcover F
  refine ⟨T, hTF, hT, hg, ?_, hδ⟩
  intro k y
  let W : X.Opens := U (y 0)
  have hB : (⨅ l, V (y l)) ≤ g ⁻¹ᵁ W := by
    calc
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)) := hinter k y
      _ ≤ g ⁻¹ᵁ W := by
        apply g.preimage_mono
        exact iInf_le _ 0
  exact inverseImage_surjective_sections_of_localSplit g T hT W
    (hsplit (y 0)) (⨅ l, V (y l)) hB

end AlgebraicGeometry.Scheme.Modules
