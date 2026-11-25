/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Field.ULift
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

import WeilConjectures.ConstructibleSheaf.TorsorModuleDescentEquivalence
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Associated module sheaves on a connected finite torsor

Source: Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS.
(blueprint: lem-weil-pbc-connected-torsor-module-descent)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale

/-- Descent on a connected finite torsor produces an associated-sheaf functor and
recovers every sheaf trivialized by that torsor.
Source: Stacks Project, Tag 0DV5 (3), Tag 0DV6, and Tag 0A3R, proof identifying
pullback with the restricted monodromy representation; Tags 04TR and 04TS
(gluing sheaves and its mapping property).
(blueprint: lem-weil-pbc-connected-torsor-module-descent)

Proof:
1. For each P-representation N, transport scalars along the inverse ULift ring
equivalence and form the constant module sheaf on c.P. On c.P times_V c.P,
the torsor isomorphism identifies a pair of points with a group element. Give
the constant sheaf its descent isomorphism using that element's action on N,
with inverse action if the chosen ordering of the projections requires it.
The group-action law is exactly the cocycle condition on the triple overlap.
More explicitly, on W etale over V take the submodule of sections of the
constant module sheaf on W times_V c.P satisfying s(g*y) = g*s(y) for all g.
Restriction is restriction of sections. Compatible sections on an etale cover
glue uniquely upstairs; equivariance persists by uniqueness, so this is a sheaf.
On the cover c.P -> V a section of the pulled-back torsor identifies an
equivariant section with its value at that section. Hence its pullback is the
constant sheaf and its descent datum is the one above, as in 04TR and 04TS.
2. Equivariant linear maps commute with the descent isomorphisms and descend
uniquely. Identity and composition follow by uniqueness. Addition of maps
commutes with descent since the transition maps are linear; T is additive.
Equivalently, maps and their sums act pointwise on the equivariant sections.
This works for arbitrary N, including infinite-dimensional representations:
the finite discrete group P acts continuously on every discrete P-module.
3. Choose a geometric lift to c.P of the canonical algebraic-closure point at
each x of V. Pullback to this lift identifies the stalk of T(N) with N,
after the prescribed scalar restriction. Evaluation at the chosen lift
commutes with every equivariant linear map, giving a natural functor isomorphism.
4. Transport the canonical descent datum of c*F through the given constant
trivialization. On each component of c.P times_V c.P indexed by P, it is a
map between constant module sheaves on the connected nonempty scheme c.P.
To see constancy, each a in A gives a global section of the target constant
sheaf, hence a locally constant function on the connected nonempty total space,
which is constant. Evaluation at a point gives a linear map; linearity and
invertibility are checked on these constant sections. These sections generate
the constant sheaf locally, so evaluation determines the whole map.
Their cocycle condition gives a P action
on A (with the same projection convention as in step 1). Transport scalars to
ZMod l to obtain M. A's finite dimension is preserved by the ring equivalence.
Its descent datum is the original datum of F, so effective descent gives T(M)
isomorphic to F. In particular, M is determined from F and the trivialization;
it is not an arbitrary representation with the right stalk dimension.
5. The trivial rank-one representation has identity transition maps. Its
constant sheaf on c.P descends to the constant coefficient sheaf on V. All
steps include A = 0 and P = 1. Connectedness of c.P is essential in step 4. -/
theorem Scheme.GaloisCover.exists_module_descent_stalk_functor
    {V : Scheme.{u}} [ConnectedSpace V] (ℓ : ℕ) [Fact ℓ.Prime]
    (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) [ConnectedSpace c.P]
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
    [FiniteDimensional (ULift.{u + 1} (ZMod ℓ)) A]
    (hF : Nonempty ((c.π)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj F ≅
      (constantSheaf c.P.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj A)) :
    ∃ (M : Rep.{u + 1} (ZMod ℓ) P) (_ : FiniteDimensional (ZMod ℓ) M.V)
      (T : Rep.{u + 1} (ZMod ℓ) P ⥤
        Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
      (_ : T.Additive),
      (∀ x : V, Nonempty
        (T ⋙ (V.uliftPointSmallEtale x).sheafFiber
              (A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) ⋙
            ModuleCat.restrictScalars.{u + 1}
              (ULift.ringEquiv.symm.toRingHom : ZMod ℓ →+* ULift.{u + 1} (ZMod ℓ)) ≅
          forget₂ (Rep.{u + 1} (ZMod ℓ) P) (ModuleCat.{u + 1} (ZMod ℓ)))) ∧
      Nonempty (T.obj M ≅ F) ∧
      Nonempty (T.obj (Rep.trivial (ZMod ℓ) P (ULift.{u + 1} (ZMod ℓ))) ≅
        (constantSheaf V.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
          (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ)))) := by
  classical
  let := c.etale
  let C := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))
  let D : ObjectProperty (Sheaf V.smallEtaleTopology C) := fun G ↦
    ∃ B : C, Nonempty ((c.π)^*[C].obj G ≅
      (constantSheaf c.P.smallEtaleTopology C).obj B)
  obtain ⟨E, hT, ⟨eπ⟩, hunit⟩ := c.exists_module_descent_equivalence ℓ P
  let T := E.functor ⋙ D.ι
  -- The inverse equivalence recovers the representation from the sheaf itself.
  let G : D.FullSubcategory := ⟨F, A, hF⟩
  let M := E.inverse.obj G
  let eF : T.obj M ≅ F := D.ι.mapIso (E.counitIso.app G)
  obtain ⟨y⟩ := (inferInstance : Nonempty c.P)
  let Φ := c.P.uliftPointSmallEtale y
  let U := forget₂ (Rep.{u + 1} (ZMod ℓ) P) (ModuleCat.{u + 1} (ZMod ℓ))
  let S := ModuleCat.restrictScalars.{u + 1}
    (ULift.ringEquiv.toRingHom : ULift.{u + 1} (ZMod ℓ) →+* ZMod ℓ)
  obtain ⟨iF⟩ := hF
  -- Compare the two constant pullbacks at one geometric point upstairs.
  let iA : S.obj (U.obj M) ≅ A :=
    (Φ.sheafFiberConstantSheafIso (S.obj (U.obj M))).symm ≪≫
      Φ.sheafFiber.mapIso ((eπ.app M).symm ≪≫
        ((c.π)^*[C]).mapIso eF ≪≫ iF) ≪≫ Φ.sheafFiberConstantSheafIso A
  let f : A →ₛₗ[ULift.ringEquiv.toRingHom] M.V :=
    { toFun := iA.inv
      map_add' := iA.inv.hom.map_add
      map_smul' := fun r a ↦ iA.inv.hom.map_smul r a }
  have hM : FiniteDimensional (ZMod ℓ) M.V :=
    Module.Finite.of_surjective f iA.toLinearEquiv.symm.surjective
  refine ⟨M, hM, T, hT, ?_, ⟨eF⟩, hunit⟩
  intro x
  -- Lift the geometric point, then use the natural pullback and constant-stalk isomorphisms.
  obtain ⟨z, hz⟩ := c.surjective.surj x
  obtain ⟨s, hs, _⟩ := Scheme.exists_fac_of_etale_of_isSepClosed c.π
    (V.algClosurePoint x) z (by simpa using hz)
  let Ψ := (Scheme.pointSmallEtale s).ulift.{u + 1}
  let ebase : (c.π)^*[C] ⋙ Ψ.sheafFiber ≅
      (V.uliftPointSmallEtale x).sheafFiber :=
    (upperStarCompUliftSheafFiberIso C c.π s) ≪≫
      (eqToIso (by rw [hs]; rfl))
  let econst := Ψ.constantSheafCompSheafFiberIso c.P.smallEtaleTopology C
  let R := ModuleCat.restrictScalars.{u + 1}
    (ULift.ringEquiv.symm.toRingHom : ZMod ℓ →+* ULift.{u + 1} (ZMod ℓ))
  let ering : S ⋙ R ≅ 𝟭 (ModuleCat.{u + 1} (ZMod ℓ)) :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (ULift.ringEquiv : ULift.{u + 1} (ZMod ℓ) ≃+* ZMod ℓ)).unitIso.symm
  let e : T ⋙ (V.uliftPointSmallEtale x).sheafFiber ≅ U ⋙ S :=
    Functor.isoWhiskerLeft T ebase.symm ≪≫
      (Functor.associator T ((c.π)^*[C]) Ψ.sheafFiber).symm ≪≫
      Functor.isoWhiskerRight eπ Ψ.sheafFiber ≪≫
      Functor.associator U (S ⋙ constantSheaf c.P.smallEtaleTopology C) Ψ.sheafFiber ≪≫
      Functor.isoWhiskerLeft U
        (Functor.associator S (constantSheaf c.P.smallEtaleTopology C) Ψ.sheafFiber) ≪≫
      Functor.isoWhiskerLeft U (Functor.isoWhiskerLeft S econst) ≪≫
      Functor.isoWhiskerLeft U (Functor.rightUnitor S)
  exact ⟨(Functor.associator T (V.uliftPointSmallEtale x).sheafFiber R).symm ≪≫
    Functor.isoWhiskerRight e R ≪≫ Functor.associator U S R ≪≫
    Functor.isoWhiskerLeft U ering ≪≫ Functor.rightUnitor U⟩

end AlgebraicGeometry
