/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.LocallyRankedExteriorComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Idempotents.Basic
import WeilConjectures.AlgebraicGeometry.ClopenRankStratumModuleProjector

/-! # The derived summand cut out by a clopen rank stratum

Source: the rank-idempotent construction in steps 1--2 of
`lem-sc-clopen-rank-strata-homology-lift`; Stacks Tag 00EE (clopen idempotents).
(blueprint: lem-sc-clopen-rank-stratum-derived-projector)
-/

@[expose] public section

universe u v w wA

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem split_derived_natural_idempotent
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (η : 𝟭 C ⟶ 𝟭 C) (hη : η ≫ η = η) (K : DerivedCategory C) :
    ∃ (L : DerivedCategory C) (ι : L ⟶ K) (π : K ⟶ L),
      ι ≫ π = 𝟙 L ∧ ∀ m : ℤ,
        (DerivedCategory.homologyFunctor C m).map π ≫
          (DerivedCategory.homologyFunctor C m).map ι =
            η.app ((DerivedCategory.homologyFunctor C m).obj K) := by
  let P := DerivedCategory.Q.objPreimage K
  let e := DerivedCategory.Q.objObjPreimageIso K
  let p : P ⟶ P :=
    { f := fun m ↦ η.app (P.X m)
      comm' := fun m n _ ↦ (η.naturality (P.d m n)).symm }
  have hp : p ≫ p = p := by
    ext m
    exact congrArg (fun τ : 𝟭 C ⟶ 𝟭 C ↦ τ.app (P.X m)) hη
  obtain ⟨R, j, t, hR, ht⟩ := IsIdempotentComplete.idempotents_split P p hp
  refine ⟨DerivedCategory.Q.obj R, DerivedCategory.Q.map j ≫ e.hom,
    e.inv ≫ DerivedCategory.Q.map t, ?_, ?_⟩
  · simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, hR,
      CategoryTheory.Functor.map_id]
  · intro m
    let H := DerivedCategory.homologyFunctor C m
    let h := (DerivedCategory.homologyFunctorFactors C m).app P
    have hpm : HomologicalComplex.homologyMap p m = η.app (P.homology m) := by
      have hcycles : HomologicalComplex.cyclesMap p m = η.app (P.cycles m) := by
        apply (cancel_mono (P.iCycles m)).mp
        rw [HomologicalComplex.cyclesMap_i]
        exact η.naturality (P.iCycles m)
      apply (cancel_epi (P.homologyπ m)).mp
      rw [HomologicalComplex.homologyπ_naturality, hcycles]
      exact (η.naturality (P.homologyπ m)).symm
    have hQp : H.map (DerivedCategory.Q.map p) = η.app (H.obj (DerivedCategory.Q.obj P)) := by
      apply (cancel_mono h.hom).mp
      have hn := (DerivedCategory.homologyFunctorFactors C m).hom.naturality p
      change H.map (DerivedCategory.Q.map p) ≫ h.hom =
        h.hom ≫ HomologicalComplex.homologyMap p m at hn
      rw [hn, hpm]
      exact η.naturality h.hom
    change H.map (e.inv ≫ DerivedCategory.Q.map t) ≫
      H.map (DerivedCategory.Q.map j ≫ e.hom) = η.app (H.obj K)
    rw [← H.map_comp]
    have hcomp : (e.inv ≫ DerivedCategory.Q.map t) ≫
        (DerivedCategory.Q.map j ≫ e.hom) = e.inv ≫ DerivedCategory.Q.map p ≫ e.hom := by
      rw [Category.assoc, ← Category.assoc (DerivedCategory.Q.map t),
        ← DerivedCategory.Q.map_comp, ht]
    rw [hcomp, H.map_comp, H.map_comp, hQp]
    rw [← Category.assoc]
    rw [show H.map e.inv ≫ η.app (H.obj (DerivedCategory.Q.obj P)) =
      η.app (H.obj K) ≫ H.map e.inv from η.naturality (H.map e.inv)]
    rw [Category.assoc, ← H.map_comp, e.inv_hom_id, H.map_id]
    exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
/-- A rank stratum cuts out a retract of every derived direct-image-algebra module.
Its homology vanishes whenever the original homology is supported on a different
stratum. Maps from modules on the chosen stratum are fixed by the homology projector.
This statement constructs the summand, without a concentration hypothesis or a map
from a single complex.

Source: steps 1--2 of `lem-sc-clopen-rank-strata-homology-lift`, expanding the
rank-idempotent argument of `lem-sc-clopen-rank-strata-formality`; Stacks Tag 00EE.
(blueprint: lem-sc-clopen-rank-stratum-derived-projector)

Proof: The fiber U_q of r is clopen. Take the unique global section of O_Z which
restricts to 1 on U_q and 0 on its complement. Its direct image is a central
idempotent of i_*O_Z. On a cochain representative C of K, multiplication by this
section is a chain idempotent. Construct its image submodule sheaf in each degree;
restriction maps and differentials preserve these images. Call the image complex
C_q. Multiplication by the idempotent factors as a projection C to C_q followed by
the inclusion C_q to C, and their composite on C_q is the identity. Apply Q and
transport along Q(C) isomorphic to K to obtain L, inclusion and projection.
The image functor is exact: the decomposition M = eM plus (1-e)M is natural in M,
and kernels and cokernels split into the same two summands. Consequently H^m(C_q)
is the e-image of H^m(C). On a module pushed forward from U_k with k different
from q, e acts by zero: the fibers are disjoint, and the module has zero sections
on their complementary clopen component. The same remains true after direct image
along i. The e-image of this homology is therefore zero. On a module from U_q,
e acts by the identity. Every module-linear map from such a module commutes with
e, so composing it with the homology projector leaves it unchanged. These arguments
also cover empty fibers and arbitrary, possibly infinite, images of r; only one
idempotent is used. No choice of an arbitrary module from an existence theorem is
needed: C_q is the termwise image of the explicit multiplication chain map. -/
theorem clopenRankStratum_derived_projector
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{wA} (SheafOfModules.{u}
      (moduleRings (directImageAlgebraSpace i)))]
    (r : LocallyConstant Z ℕ) (q : ℕ)
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i)))) :
    ∃ (L : DerivedCategory
        (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))))
      (ι : L ⟶ K) (π : K ⟶ L),
      ι ≫ π = 𝟙 L ∧
      (∀ (m : ℤ) (k : ℕ)
        (F : (Scheme.Modules.exteriorRankOpen r k).toScheme.Modules),
        k ≠ q → Nonempty ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) m).obj K ≅
          (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)).obj
            ((Scheme.Modules.pushforward (Scheme.Modules.exteriorRankOpen r k).ι).obj F)) →
        IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) m).obj L)) ∧
      (∀ (m : ℤ) (F : (Scheme.Modules.exteriorRankOpen r q).toScheme.Modules)
        (a : (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)).obj
            ((Scheme.Modules.pushforward (Scheme.Modules.exteriorRankOpen r q).ι).obj F) ⟶
          (DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) m).obj K),
        a ≫ (DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) m).map π ≫
          (DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) m).map ι = a) := by
  let C := SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))
  obtain ⟨η, hη, hsupported⟩ := clopenRankStratum_module_projector i r q
  obtain ⟨L, ι, π, hsplit, hproject⟩ := split_derived_natural_idempotent η hη K
  refine ⟨L, ι, π, hsplit, ?_, ?_⟩
  · intro m k F hk ⟨e⟩
    let H := DerivedCategory.homologyFunctor C m
    have hzero : η.app (H.obj K) = 0 := by
      apply (cancel_mono e.hom).mp
      have hs := hsupported k F
      rw [ite_eq_right hk] at hs
      calc
        η.app (H.obj K) ≫ e.hom = e.hom ≫ η.app _ := (η.naturality e.hom).symm
        _ = e.hom ≫ 0 := congrArg (fun f ↦ e.hom ≫ f) hs
        _ = 0 ≫ e.hom := by rw [comp_zero, zero_comp]
    have hsplitH : H.map ι ≫ H.map π = 𝟙 (H.obj L) := by
      rw [← H.map_comp, hsplit, H.map_id]
    apply (IsZero.iff_id_eq_zero _).mpr
    calc
      𝟙 (H.obj L) = (H.map ι ≫ H.map π) ≫ (H.map ι ≫ H.map π) := by
        rw [hsplitH, Category.id_comp]
      _ = H.map ι ≫ (H.map π ≫ H.map ι) ≫ H.map π := by
        simp only [Category.assoc]
      _ = 0 := by rw [hproject m, hzero, zero_comp, comp_zero]
  · intro m F a
    rw [hproject m]
    have hs := hsupported q F
    rw [ite_eq_left rfl] at hs
    calc
      a ≫ η.app _ = η.app _ ≫ a := η.naturality a
      _ = 𝟙 _ ≫ a := congrArg (fun f ↦ f ≫ a) hs
      _ = a := Category.id_comp a

end AlgebraicGeometry
