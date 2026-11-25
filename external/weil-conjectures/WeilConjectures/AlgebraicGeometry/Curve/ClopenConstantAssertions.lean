/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
import WeilConjectures.AlgebraicGeometry.Curve.ClopenConstantAssertionsFirst
import WeilConjectures.AlgebraicGeometry.Curve.ClopenConstantAssertionsLast
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.AlgebraicGeometry.EtaleSheafClopenProduct
import WeilConjectures.AlgebraicGeometry.FiniteCoproductCohomologyAssembly
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
import WeilConjectures.ConstructibleSheaf.Pullback

/-! # Assembling constant-coefficient assertions over a finite clopen partition -/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.IsCurve

/-- Constant-coefficient curve assertions assemble over a finite clopen partition.
Source: the blueprint smooth Kummer calculation, first paragraph (finite disjoint
unions commute with every comparison map), and the Artin--Schreier calculation,
first paragraph.
(blueprint: lem-pbc-k2-clopen-constant-assertions)

Proof: The clopen cover realizes X as the coproduct of its pieces. The etale sheaf
product theorem and finiteCoproductCohomologyAssembly identify cohomology with the
product of the component cohomology groups.
Restriction and finite direct image along their inclusions are exact, and the
adjunction units identify the constant sheaf with the finite biproduct of the direct
images of the constant sheaves on the pieces. Thus its cohomology is the finite
product of their cohomology. All comparison maps are the corresponding finite
products, by naturality of the adjunction and finite base change. Vanishing and
finiteness pass to finite products. Affineness restricts to the pieces, since they
are closed subschemes; properness does too, since their inclusions are finite.
Primary and invertible-order torsion restrict by the geometric-stalk formula, and
constructibility restricts to opens. These observations prove C1 through C7 from
the given assertions. For C8 pull an open immersion back to each piece and use
componentwise surjectivity; the inverse images remain a finite clopen partition
of the open. With no pieces the cover condition forces X to be empty, and every
cohomology group is zero. No connectedness, prime-annihilation, or finiteness of
the coefficient module is required. -/
theorem assertions_constant_of_isClopen (Λ : Type (u + 1)) [CommRing Λ]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] (M : ModuleCat.{u + 1} Λ)
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsClosed (U i : Set X))
    (hdisj : Pairwise (fun i j ↦ Disjoint (U i : Set X) (U j)))
    (hcov : ∀ x : X, ∃ i, x ∈ U i)
    (H : ∀ i, Assertions Λ ((U i).ι ≫ f)
      ((constantSheaf (U i).toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :
    Assertions Λ f ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) := by
  rcases clopen_first_four Λ f M U hU hdisj hcov H with ⟨h1, h2, h3, h4⟩
  rcases clopen_last_four Λ f M U hU hdisj hcov H with ⟨h5, h6, h7, h8⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

end AlgebraicGeometry.IsCurve
