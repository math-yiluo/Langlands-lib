/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.AlgebraicGeometry.HomComplexSingleNatural
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-! # Deriving internal Hom from a module in degree zero

Source: Stacks Project, Cohomology on Sites, Section 08J7, Lemma 0A95;
Duality for Schemes, Tag 0BV1.
-/

@[expose] public section

universe u w

open CategoryTheory Opposite TopologicalSpace

namespace CategoryTheory

-- The localization comparisons unfold the sheaf and curry carrier encodings.
set_option backward.isDefEq.respectTransparency false in
/-- A right derived functor of termwise internal Hom from a fixed module agrees with
internal RHom from that module placed in degree zero. This comparison concerns only
O-modules, and requires neither an algebra structure nor an adjunction.

Source: Stacks Project, Cohomology on Sites, Section 08J7, Lemma 0A95;
Duality for Schemes, Tag 0BV1, lemma-sheafhom-affine-ext
(blueprint: lem-sc-derived-internal-hom-single-comparison).

Proof:
1. Let I be the functorial K-injective resolution of the Grothendieck abelian category
   of R-modules. The right derivability structure of K-injectives computes the given
   right derived functor S on I, with its comparison invertible on K-injective objects.
   Indeed, quasi-isomorphisms between K-injectives are homotopy equivalences;
   additive termwise Hom preserves homotopies, and Q inverts homotopy equivalences.
2. For M concentrated in degree zero, the degree n term of Hom-complex(M[0], I) is
   Hom(M, I.X n): only the degree-zero source factor survives in the product defining
   Hom-complex. Its differential is postcomposition with d_I, since d_M is zero.
   The existing homComplex_single_iso gives this identification objectwise. Its
   projection construction and the Hom-complex map formula show naturality. Thus
   projection onto that factor and insertion with zero in all other factors give a
   natural chain isomorphism with the termwise internal Hom complex.
3. Apply derivedInternalHom_comparison to this same I and fix the first variable at
   M[0]. Compose its comparison with the natural chain isomorphism from step 2.
4. The resulting comparisons identify both functors on K-injective representatives,
   naturally in all morphisms. The K-injective localization equivalence descends this
   natural isomorphism to the derived category. Equivalently, uniqueness of the right
   derived functor transports the comparison to the given S. This includes zero M,
   arbitrary unbounded complexes, and every choice of the derived-category universe. -/
theorem derivedInternalHom_single_comparison
    (X : AlgebraicGeometry.Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (AlgebraicGeometry.moduleRings X.toRingedSpace))]
    (M : SheafOfModules.{u} (AlgebraicGeometry.moduleRings X.toRingedSpace))
    [((SheafOfModules.homFunctor X.sheaf).obj (op M)).Additive]
    (S : DerivedCategory (SheafOfModules.{u}
      (AlgebraicGeometry.moduleRings X.toRingedSpace)) ⥤
      DerivedCategory (SheafOfModules.{u}
        (AlgebraicGeometry.moduleRings X.toRingedSpace)))
    (δ : ((SheafOfModules.homFunctor X.sheaf).obj (op M)).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ S)
    (hδ : S.IsRightDerivedFunctor δ (HomologicalComplex.quasiIso _ (.up ℤ))) :
    Nonempty (S ≅ (Functor.curry.obj
      (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf)).obj
        (op ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  let A := SheafOfModules.{u} (AlgebraicGeometry.moduleRings X.toRingedSpace)
  have : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let T := (SheafOfModules.homFunctor X.sheaf).obj (op M)
  let F := T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η := CochainComplex.toKInjectiveResolution.{u} A
  let L := (CochainComplex.singleFunctor A 0).obj M
  have hder : (CochainComplex.KInjectives.localizerMorphism A).Derives F := by
    intro K K' a ha
    have : K.obj.IsKInjective := K.property
    have : K'.obj.IsKInjective := K'.property
    have : QuasiIso a.hom := ha
    obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff a.hom).mp inferInstance
    have : QuasiIso ((T.mapHomologicalComplex (.up ℤ)).map a.hom) := by
      rw [← he]
      exact (T.mapHomotopyEquiv e).quasiIso_hom
    change IsIso (DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map a.hom))
    infer_instance
  have hδI (K : CochainComplex A ℤ) : IsIso (δ.app (I.obj K)) := by
    exact hder.isIso_of_isRightDerivedFunctor δ
      ⟨I.obj K, CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A K⟩
  have : IsIso (Functor.whiskerLeft I δ) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact hδI
  have hη (K : CochainComplex A ℤ) : IsIso (DerivedCategory.Q.map (η.app K)) := by
    have : QuasiIso (η.app K) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A K).2
    infer_instance
  let r : DerivedCategory.Q ≅ I ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun K ↦ asIso (DerivedCategory.Q.map (η.app K))) (by
      intro K K' f
      simpa only [Functor.comp_map, Functor.id_map, asIso_hom, Functor.map_comp] using
        congrArg DerivedCategory.Q.map (η.naturality f))
  let s : DerivedCategory.Q ⋙ S ≅ I ⋙ F :=
    Functor.isoWhiskerRight r S ≪≫ Functor.associator I DerivedCategory.Q S ≪≫
      (asIso (Functor.whiskerLeft I δ)).symm
  obtain ⟨e⟩ := AlgebraicGeometry.homComplex_single_natural_iso X M
  obtain ⟨c⟩ := derivedInternalHom_comparison.{u, w}
    (Opens.grothendieckTopology X) X.sheaf I η
    (fun K ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A K).2,
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A K⟩)
  let c' := (Functor.curry.mapIso c).app (op L)
  let a := (Functor.curryObjProdComp DerivedCategory.Q.op DerivedCategory.Q
    (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf)).app (op L)
  let b : (Functor.curry.obj
      ((𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := X.sheaf)) ⋙
        DerivedCategory.Q)).obj (op L) ≅
      I ⋙ (homComplexFunctor (R := X.sheaf)).obj (op L) ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun K ↦ Iso.refl _) (by intro K K' f; simp)
  let t := a.symm ≪≫ c' ≪≫ b ≪≫
    Functor.isoWhiskerLeft I (Functor.isoWhiskerRight e DerivedCategory.Q)
  exact ⟨(Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) _).preimageIso (s ≪≫ t.symm)⟩

end CategoryTheory
