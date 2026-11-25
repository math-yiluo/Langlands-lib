/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.Modules.Dual

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.Algebra.Homology.HomologyEvaluation
import WeilConjectures.AlgebraicGeometry.SelfExtTorResolutionModel

/-! # Evaluation between self Ext and self Tor

Source: Stacks Project, Tags 0BQY, 08DH and 068G.
(blueprint: lem-sc-self-ext-tor-dual-chart). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

-- Transport through the fixed derived tensor involves several composed object types.
/-- There is a global morphism `κ` from the pulled-back self-Ext sheaf to the dual of the
pulled-back self-Tor sheaf which is an isomorphism on every regular affine chart.

This statement is existential: `κ` is built from chosen resolutions (a common complex `T`
and a K-injective resolution `J` of `O_Z`, with chosen identifications of self Ext and self
Tor with the homology of `Hom(T, J)` and of `T`), and it is not asserted to be the canonical
Ext–Tor evaluation map. Only the existence of a global morphism that is chartwise invertible
is used downstream, to glue the chartwise inverses.

Source: Stacks Project, duality.tex, lemma-regular-ideal-ext (0BQY), its
zero-differential Hom calculation; cohomology.tex, derived evaluation (08DH);
more-algebra.tex, equation-simple-tor-product (068G).
(blueprint: lem-sc-self-ext-tor-dual-chart).

Proof: Choose a common complex T and an injective representative J of O_Z
using exists_selfExt_tor_resolution_model. Its isomorphisms identify pulled-back
self Ext with H^n(Hom(T,J)) and pulled-back self Tor with H^(-n)(T). Apply the
uniquely characterized homologyEvaluation: evaluate Hom cocycles on cycles of T,
pass to both homology quotients, and curry the resulting pairing. The internal
Hom bifunctor transports its target from Hom(H^(-n)(T),H^0(J)) to dual Q using
the Tor comparison and H^0(J) = O_Z. Compose with the Ext comparison to obtain κ.
For every regular affine U the model theorem gives a finite free
zero-differential model for T on the indicated over site and K-injectivity of
restricted J. homologyEvaluation_isIso applies on that site. The two comparison
isomorphisms remain isomorphisms after restriction and passage to the over site;
their composite with evaluation is therefore invertible. Rank zero, empty
charts, zero quotient rings and n above the Koszul length are included in the
two model/evaluation lemmas. -/
theorem selfExt_tor_dual_chart
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (n : ℕ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    let Q := (Scheme.Modules.tensorPullback i).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (-(n : ℤ))).obj
          (S.obj B ⊗ S.obj B))
    ∃ κ : (Scheme.Modules.tensorPullback i).obj G ⟶ Scheme.Modules.dual Q,
      ∀ (V : Z.Opens) (U : Y.affineOpens)
        (_hU : ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
          Ideal.span (Set.range f) = i.ker.ideal U ∧
            RingTheory.Sequence.IsKoszulRegular f),
        IsIso (((Scheme.Modules.restrictFunctor V.ι).map κ).over
          (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1))) := by
  obtain ⟨T, J, hJ, e0, eG, eQ, hcharts⟩ :=
    exists_selfExt_tor_resolution_model.{u, w} i n
  let eD := (Functor.uncurry.obj (SheafOfModules.homFunctor Z.sheaf)).mapIso
    (eQ.op.prod e0)
  let ε := homologyEvaluation Z T J (n : ℤ) hJ
  refine ⟨eG.hom ≫ ε ≫ eD.hom, ?_⟩
  intro V U hU
  obtain ⟨hI, hT⟩ := hcharts V U hU
  have hε : IsIso (((Scheme.Modules.restrictFunctor V.ι).map ε).over
      (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1))) :=
    homologyEvaluation_isIso Z T J (n : ℤ) hJ V _ hI hT
  change IsIso ((SheafOfModules.overFunctor V.toScheme.ringCatSheaf
    (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1))).map
      ((Scheme.Modules.restrictFunctor V.ι).map (eG.hom ≫ ε ≫ eD.hom)))
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp]
  infer_instance

end AlgebraicGeometry
