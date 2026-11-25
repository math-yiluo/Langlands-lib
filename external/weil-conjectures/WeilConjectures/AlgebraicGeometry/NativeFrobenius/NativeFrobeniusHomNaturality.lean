/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeFrobenius.NativeFrobeniusHomComparison

/-! # Naturality of the native small-model Hom comparison

## References

* Stacks 03D6 and 03EO
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.ProEtale.NativeFrobenius
variable (Y : Scheme.{u}) (l : ℕ) [Fact l.Prime]

attribute [local irreducible] comparisonRing nativeHom adicSectionModuleEquivalence
  inverseNativeHomComparison SheafOfModules.homObjMap

/-- The pointwise Hom comparisons commute with both variable maps.
Compose the small-site naturality square and the inverse-native naturality square,
after normalizing the curried ordinary Hom map with its composition equation. -/
theorem homComparison_naturality (H : AdicModuleHomComparisonCore l Y)
    {M M' N N' : TwistedActionRingedSite.Modules (ring Y l)}
    (f : M' ⟶ M) (g : N ⟶ N') :
    (equivalence Y l).functor.map (SheafOfModules.homObjMap (R := ring Y l) f g) ≫
        (homComparison Y l H M' N').hom =
      (homComparison Y l H M N).hom ≫
        (nativeHom Y l).map (((equivalence Y l).functor.map f).op,
          (equivalence Y l).functor.map g) := by
  let Q := SheafOfModules.SmallSite.restriction (Scheme.ProEt.topology Y) (comparisonRing l Y)
  let F := (adicSectionModuleEquivalence l Y).inverse
  let j : (op (Q.obj M), Q.obj N) ⟶ (op (Q.obj M'), Q.obj N') :=
    ((Q.map f).op, Q.map g)
  have hi := (inverseNativeHomComparison Y l H).hom.naturality j
  change F.map
      (SheafOfModules.homObjMap (R := comparisonRing l Y) (Q.map f) (𝟙 _) ≫
        SheafOfModules.homObjMap (R := comparisonRing l Y) (𝟙 _) (Q.map g)) ≫ _ = _ at hi
  simp only [SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp] at hi
  exact HomComparison.mapIso_comp_naturality F
    (SheafOfModules.SmallSite.homIso (Scheme.ProEt.topology Y) (comparisonRing l Y) M N)
    (SheafOfModules.SmallSite.homIso (Scheme.ProEt.topology Y) (comparisonRing l Y) M' N')
    ((inverseNativeHomComparison Y l H).app (op (Q.obj M), Q.obj N))
    ((inverseNativeHomComparison Y l H).app (op (Q.obj M'), Q.obj N'))
    (Q.map (SheafOfModules.homObjMap (R := ring Y l) f g))
    (SheafOfModules.homObjMap (R := comparisonRing l Y) (Q.map f) (Q.map g))
    ((nativeHom Y l).map ((F.map (Q.map f)).op, F.map (Q.map g)))
    (SheafOfModules.SmallSite.homIso_naturality
      (Scheme.ProEt.topology Y) (comparisonRing l Y) f g) hi

end AlgebraicGeometry.ProEtale.NativeFrobenius
