/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormalFibreCohomology
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.FormalFunctionsLocalStalkComparison
import WeilConjectures.AlgebraicGeometry.FormalFunctionsFiniteQuotientComparison
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.ModulePullbackFiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # The geometric dictionary for stalkwise formal functions

Source: Stacks Project, Tag 02OD, proof before applying Theorem 02OC
(blueprint: lem-weil-pbc-formal-functions-local-dictionary).

This identifies uncompleted cohomology and the finite quotient systems. It does not
assert a comparison of completed cohomology with an inverse limit.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

namespace AlgebraicGeometry

/-- The geometric identifications used before applying the theorem on formal functions.
Source: Stacks Project, Tag 02OD, proof, together with Tags 02KH, 01E4, 089W and 01FB
(blueprint: lem-weil-pbc-formal-functions-local-dictionary).

Proof: Put A = O_(Y,y), and base change f along the flat canonical map Spec A → Y.
A is Noetherian, the base-changed map is proper, and the pulled-back module is coherent:
pullback preserves quasi-coherence and finite type, which characterize coherence on
locally Noetherian schemes. Flat base change (02KH) identifies the higher direct image
stalk with the cohomology H on this base change. The section-class formula for flat
base change and the associated-presheaf description (01E4) identify this equivalence
on germs with pullback. Every open containing the closed point of Spec A is all of
Spec A, so the final stalk is global cohomology.
For each positive level n+1, paste the two pullback squares to identify the infinitesimal
fibre with the quotient base change of this local scheme. Its closed immersion has ideal
m^(n+1) O. The closed immersion unit has kernel m^(n+1) F', so it identifies the pushed
forward fibre module with formalModuleQuotient J (n+1) F'. The affine cohomology edge
isomorphism (089W) then gives the component of b. These components commute with
transitions: the two sheaf maps agree after precomposition with the epimorphic quotient
projection, hence agree; functoriality of the cohomology h-maps gives naturality.
Restrict the completed scalar action to A; on each component it is the same quotient
scalar action. The pullback maps on neighbourhood cohomology descend to A-linear maps
kappa on the stalk, by their compatibility with restrictions and the stalk colimit.
Functoriality identifies their values with b applied to the quotient restriction of a.
The section-class formula identifies these maps with IsFormalFunctionsTheta, for every
choice of injective resolutions and open comparison data. These arguments apply equally
to p=0, the zero module and an empty fibre; no nonzero or surjectivity hypothesis on a
finite-level cohomology map is used. -/
theorem formalFunctions_local_dictionary {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    [IsLocallyNoetherian Y] (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) (y : Y) (p : ℕ) :
    let X' := pullback (Y.fromSpecStalk y) f
    let f' := pullback.fst (Y.fromSpecStalk y) f
    let F' := (Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F
    let J := (Scheme.IdealSheafData.ofIdealTop
      ((maximalIdeal (Y.presheaf.stalk y)).map
        (Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv.hom)).comap f'
    let C := RingedSpace.moduleCohomology X'.toRingedSpace p ⋙
      ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫ f'.appTop).hom
    RingedSpace.IsCoherent X'.toRingedSpace F' ∧
      ∃ a : formalFunctionsStalk f y F p ≃ₗ[Y.presheaf.stalk y] C.obj F',
      ∃ b : formalCompletionSystem J F' ⋙ C ≅
        formalFibreCohomologySystem f y F p ⋙ ModuleCat.restrictScalars
          (algebraMap (Y.presheaf.stalk y)
            (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))),
      ∃ κ : ∀ n : ℕ, formalFunctionsStalk f y F p →ₗ[Y.presheaf.stalk y]
        formalFibreCohomologyLocal f y F p n,
        (∀ n : ℕ, IsFormalFunctionsTheta f y F p n (κ n)) ∧
        ∀ (n : ℕ) (z : formalFunctionsStalk f y F p),
          κ n z = (b.hom.app (op n))
            ((C.map (formalModuleQuotientπ J (n + 1) F')) (a z)) := by
  dsimp
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨hq, ht⟩ :=
    (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF
  have : F.IsQuasicoherent := hq
  have : F.IsFiniteType := ht
  let g := pullback.snd (Y.fromSpecStalk y) f
  let F' := (Scheme.Modules.tensorPullback g).obj F
  have : IsLocallyNoetherian (pullback (Y.fromSpecStalk y) f) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (Y.fromSpecStalk y) f)
  let e : Scheme.Modules.tensorPullback g ≅ Scheme.Modules.pullback g :=
    (Scheme.Modules.nonempty_tensorPullbackAdjunction g).some.leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction g)
  have hq' : F'.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent
      (pullback (Y.fromSpecStalk y) f).ringCatSheaf).prop_of_iso (e.app F).symm (by infer_instance)
  have ht' : F'.IsFiniteType :=
    (Scheme.Modules.tensorPullback_isFiniteType _ _ g F).1
  have hcoh := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
    (pullback (Y.fromSpecStalk y) f) F').mpr ⟨hq', ht'⟩
  refine ⟨hcoh, ?_⟩
  obtain ⟨a, ha⟩ := formalFunctions_local_stalk_comparison f F hF y p
  refine ⟨a, ?_⟩
  obtain ⟨b, r, heq, hr⟩ := formalFunctions_finite_quotient_comparison f F hF y p
  refine ⟨b, fun n ↦ (r n).comp a.toLinearMap, hr a.toLinearMap ha, ?_⟩
  intro n z
  exact heq n (a z)

end AlgebraicGeometry
