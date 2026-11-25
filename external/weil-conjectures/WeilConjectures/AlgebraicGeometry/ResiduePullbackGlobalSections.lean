/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk

/-! # Global sections of residue-point tensor pullback

Source: Stacks Project, Sheaves, Tag 0098.
(blueprint: lem-sc-residue-pullback-global-sections).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every neighborhood of the closed point of a local-ring spectrum is the whole spectrum.
Consequently every germ has a unique global representative. -/
private theorem globalGermBijective (R : CommRingCat.{u}) [IsLocalRing R]
    (M : (Spec R).Modules) :
    Function.Bijective
      (TopCat.Presheaf.germ M.val.presheaf ⊤ (IsLocalRing.closedPoint R) trivial) := by
  constructor
  · intro s t h
    obtain ⟨U, hx, i, j, he⟩ := TopCat.Presheaf.germ_eq M.val.presheaf (IsLocalRing.closedPoint R)
      (U := ⊤) (V := ⊤) trivial trivial s t h
    have hU : U = ⊤ := IsLocalRing.closed_point_mem_iff.mp hx
    subst U
    have hi : i = 𝟙 _ := Subsingleton.elim _ _
    have hj : j = 𝟙 _ := Subsingleton.elim _ _
    simpa [hi, hj] using he
  · intro m
    obtain ⟨U, hx, s, hs⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
    have hU : U = ⊤ := IsLocalRing.closed_point_mem_iff.mp hx
    subst U
    exact ⟨s, hs⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The global germ map, with both module structures transported to the local ring. -/
private noncomputable def globalStalkIso (R : CommRingCat.{u}) [IsLocalRing R] :
    SheafOfModules.evaluation (moduleRings (Spec R).toRingedSpace) (op ⊤) ⋙
        ModuleCat.restrictScalars (ΓSpecIso R).inv.hom ≅
      RingedSpace.moduleStalkFunctor (Spec R).toRingedSpace (IsLocalRing.closedPoint R) ⋙
        ModuleCat.restrictScalars (stalkClosedPointIso R).inv.hom := by
  let η :
      SheafOfModules.evaluation (moduleRings (Spec R).toRingedSpace) (op ⊤) ⋙
          ModuleCat.restrictScalars (ΓSpecIso R).inv.hom ⟶
        RingedSpace.moduleStalkFunctor (Spec R).toRingedSpace (IsLocalRing.closedPoint R) ⋙
          ModuleCat.restrictScalars (stalkClosedPointIso R).inv.hom :=
    { app := fun M ↦ ModuleCat.ofHom
        (X := (ModuleCat.restrictScalars (ΓSpecIso R).inv.hom).obj
          ((SheafOfModules.evaluation (moduleRings (Spec R).toRingedSpace) (op ⊤)).obj M))
        (Y := (ModuleCat.restrictScalars (stalkClosedPointIso R).inv.hom).obj
          ((RingedSpace.moduleStalkFunctor (Spec R).toRingedSpace
            (IsLocalRing.closedPoint R)).obj M))
        { toFun := TopCat.Presheaf.germ M.val.presheaf ⊤ (IsLocalRing.closedPoint R) trivial
          map_add' := map_add _
          map_smul' := by
            intro r m
            change TopCat.Presheaf.germ M.val.presheaf ⊤ (IsLocalRing.closedPoint R) trivial
              ((ΓSpecIso R).inv r • m) =
                (stalkClosedPointIso R).inv r •
                  TopCat.Presheaf.germ M.val.presheaf ⊤ (IsLocalRing.closedPoint R) trivial m
            rw [PresheafOfModules.germ_smul (R := (Spec R).presheaf)]
            rw [← ΓSpecIso_hom_stalkClosedPointIso_inv]
            simp }
      naturality := by
        intro M N a
        ext m
        exact (TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ _ trivial
          ((PresheafOfModules.toPresheaf _).map a.val) m).symm }
  have (M : (Spec R).Modules) : IsIso (η.app M) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (globalGermBijective R M)
  exact NatIso.ofComponents (fun M ↦ asIso (η.app M)) (fun a ↦ η.naturality a)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Scalar extension along a ring isomorphism agrees with restriction along its inverse.
Use uniqueness of left adjoints, followed by composition of extension of scalars. -/
private noncomputable def extendScalarsRingIso {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (e : B ≃+* C) :
    ModuleCat.extendScalars f ⋙ ModuleCat.restrictScalars e.symm.toRingHom ≅
      ModuleCat.extendScalars (e.toRingHom.comp f) := by
  let q := ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  let d : ModuleCat.extendScalars e.toRingHom ≅
      ModuleCat.restrictScalars e.symm.toRingHom :=
    (ModuleCat.extendRestrictScalarsAdj e.toRingHom).leftAdjointUniq q.symm.toAdjunction
  exact Functor.isoWhiskerLeft _ d.symm ≪≫ (ModuleCat.extendScalarsComp f e.toRingHom).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Residue-point pullback, evaluated globally with its residue-field scalars,
is naturally extension of scalars of the original stalk.
Source: Stacks Project, Sheaves, Tag 0098.
(blueprint: lem-sc-residue-pullback-global-sections).

Proof: Take the closed point y of Spec kappa(x). Every neighborhood of y is
the whole space. The germ map is surjective by representing each stalk element
by a section on a neighborhood; it is injective because equality of germs holds
after restriction to a neighborhood, which must again be the whole space.
Its linearity over kappa(x) follows from germ_smul and the compatibility of
GammaSpecIso with stalkClosedPointIso. The stalk-map germ formula gives naturality,
so these bijective linear maps form a natural isomorphism from global sections
to stalks, with scalars restricted along stalkClosedPointIso inverse.

Apply the natural tensor-pullback stalk isomorphism of Tag 0098 at y and
restrict its scalars to kappa(x). For a ring isomorphism B -> C, extension of
scalars and restriction along the inverse are left adjoints of the same functor.
Uniqueness of left adjoints identifies them. Combining this with composition of
extension of scalars changes the resulting functor to extension along the composite
O_X,f(y) -> O_Spec(kappa(x)),y -> kappa(x).

Finally, SpecToEquivOfLocalRing classifies a morphism from a local-ring spectrum by
its closed-point image and local stalk map. Its inverse sends (x, residue) to
Spec(residue) followed by fromSpecStalk x, exactly fromSpecResidueField x.
The inverse identity therefore identifies both the point and the composite ring
map at once. Applying the stalk-then-extension functor to this equality finishes
the composition of natural isomorphisms. All steps apply to arbitrary module
sheaves, including the zero sheaf, without quasi-coherence or flatness. -/
theorem nonempty_residuePullback_globalSections_iso (X : Scheme.{u}) (x : X) :
    Nonempty
      (Modules.tensorPullback (X.fromSpecResidueField x) ⋙
          (SheafOfModules.evaluation
            (moduleRings (Spec (X.residueField x)).toRingedSpace) (op ⊤) ⋙
              ModuleCat.restrictScalars (ΓSpecIso (X.residueField x)).inv.hom) ≅
        RingedSpace.moduleStalkFunctor X.toRingedSpace x ⋙
          ModuleCat.extendScalars (IsLocalRing.residue (X.presheaf.stalk x))) := by
  let R := X.residueField x
  let y : Spec R := IsLocalRing.closedPoint R
  let f := X.fromSpecResidueField x
  obtain ⟨e, _⟩ := Modules.exists_tensorPullback_stalk_iso f y
  let d := Functor.isoWhiskerLeft (Modules.tensorPullback f) (globalStalkIso R) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight e (ModuleCat.restrictScalars (stalkClosedPointIso R).inv.hom) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (RingedSpace.moduleStalkFunctor X.toRingedSpace (f y))
      (extendScalarsRingIso (f.stalkMap y).hom
        (stalkClosedPointIso R).commRingCatIsoToRingEquiv)
  have h := (SpecToEquivOfLocalRing X R).apply_symm_apply
    ⟨x, X.residue x,
      inferInstanceAs (IsLocalHom (IsLocalRing.residue (X.presheaf.stalk x)))⟩
  have hF := congrArg
    (fun p : Σ z, {a : X.presheaf.stalk z ⟶ R // IsLocalHom a.hom} ↦
      RingedSpace.moduleStalkFunctor X.toRingedSpace p.1 ⋙
        ModuleCat.extendScalars p.2.1.hom) h
  exact ⟨d ≪≫ eqToIso hF⟩

end AlgebraicGeometry.Scheme
