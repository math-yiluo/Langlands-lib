/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.StrictHenselization


public import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianOpenSectionsStalk
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.FinitePushforwardSetStalkAux
import WeilConjectures.AlgebraicGeometry.FinitePushforwardSetStalkFiberFinite

/-!
# Stalks of finite direct images of étale sheaves of sets

Source: Stacks Project, Proposition 59.55.2, Tag 03QP (1), first display
(blueprint: lem-weil-pbc-sets-finite-pushforward-stalk).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For a finite morphism, the geometric lifts are finite and restriction of germs
identifies the stalk of the direct image of a set sheaf with the product of its stalks.
The component `colimit.pre` takes a germ at `(V, v)` to the germ of the same section at
`(V ×_Y X, (v, x))`, using `Etale.baseChangeNbhd`.

Source: Stacks Project, Proposition 59.55.2, Tag 03QP (1), first display
(blueprint: lem-weil-pbc-sets-finite-pushforward-stalk).

Proof (the node's ten steps):
1. Form the strict henselization C at y, its closed geometric point, and X^sh over C
   (`def-weil-pbc-strict-henselization-limit`,
   `lem-weil-pbc-strict-henselization-functoriality`). Pull H back to G on X^sh
   (`lem-weil-pbc-sets-etale-inverse-image-composition-units`).
2. The stalk of f_*H is G(X^sh), compatibly with germs, by
   `lem-weil-pbc-sets-pushforward-stalk-strict-henselization` (finite implies qcqs).
3. Finite base change is finite and affine, so X^sh = Spec B for B finite over C
   (`lem-weil-pbc-finite-morphism-permanence`, `def-weil-finite-integral-morphism`).
4. Decompose B into finitely many henselian local factors; their residue fields are
   finite extensions of the separably closed residue field of C, hence separably closed
   (`lem-weil-pbc-finite-over-henselian-local-product`,
   `lem-weil-pbc-sepclosed-finite-extension-unique-embedding`).
5. The factors yield disjoint clopen opens U_i = Spec B_i covering X^sh
   (`lem-weil-pbc-spec-clopen-idempotent`, `def-weil-affine-spectrum`).
6. Pullback identifies lifts of y with lifts of its closed point to X^sh. Each B_i
   has exactly one C-map to Ω, by the unique-embedding lemma of step 4. Thus the lifts
   are indexed by these finitely many factors (`def-pc-fibre-product`).
7. The sheaf condition for the disjoint étale cover U_i gives
   G(X^sh) = product G(U_i). Empty intersections have singleton sections, including
   the empty-family case (`lem-weil-pbc-open-immersion-etale`,
   `lem-weil-pbc-open-fibre-product`, `situation-conventions`).
8. The germ map on each strictly henselian local U_i is bijective
   (`lem-weil-pbc-sets-strictly-henselian-open-sections-stalk`).
9. Inverse-image stalks identify G at each lifted point with H at the corresponding
   point of X (`lem-weil-pbc-sets-etale-inverse-image-stalk-germ`).
10. On a representative section over V ×_Y X, this composite takes exactly the germ
    at (v, x), since restriction does not change germs
    (`def-weil-pbc-geometric-stalks`, `def-weil-pbc-category-colimit`). Reindex by
    the bijection of step 6 to obtain the asserted restriction map. -/
theorem finite_pushforward_set_stalk_bijective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (H : Sheaf X.smallEtaleTopology (Type (u + 1)))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    Finite {x : Spec (.of Ω) ⟶ X // x ≫ f = y} ∧
      Function.Bijective
        (fun a : (Scheme.pointSmallEtale y).sheafFiber.obj
            ((f.Etale.sheafPushforwardContinuous (Type (u + 1))
              Y.smallEtaleTopology X.smallEtaleTopology).obj H) ↦
          fun t : {x : Spec (.of Ω) ⟶ X // x ≫ f = y} ↦
            (colimit.pre
              ((Functor.Elements.π (Scheme.pointSmallEtale t.1).fiber).op ⋙ H.obj)
              (Etale.baseChangeNbhd f y t).op) a) := by
  let hfin := finite_pushforward_set_stalk_fiber_finite f y
  exact ⟨hfin, finite_pushforward_set_stalk_map_bijective_of_finite f H y hfin⟩

end AlgebraicGeometry
