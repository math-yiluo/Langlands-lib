/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.StrictlyPerfectDerivedInternalHom
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree

/-! # The finite free complex computing a local derived dual

Source: Stacks Project, Cohomology, Tags 08DQ and 08DM.
(blueprint: lem-pc-finite-free-derived-dual-model).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

noncomputable local instance (X : RingedSpace.{u}) (U : TopologicalSpace.Opens X)
    [hU : HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X).over U))] :
    Category.{w} (@DerivedCategory (SheafOfModules.{u}
      ((sheafCompose ((Opens.grothendieckTopology X).over U)
        (forget₂ CommRingCat RingCat)).obj (X.sheaf.over U))) _ _ hU) :=
  inferInstanceAs (Category.{w} (DerivedCategory
    (SheafOfModules.{u} ((moduleRings X).over U))))

private theorem isIso_dependent_projection {A : Type*} [Category A]
    {B : A} {T : ℤ → A} {k : ℤ} (π : ∀ q, k = q → (B ⟶ T q))
    {q : ℤ} (hq : k = q) (h : IsIso (π k rfl)) : IsIso (π q hq) := by
  subst q
  exact h

set_option backward.isDefEq.respectTransparency true in
private theorem homComplex_dual_term_iso
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    (F : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) (n : ℤ) :
    Nonempty ((homComplex (R := R) F
      ((CochainComplex.singleFunctor _ 0).obj (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))).X n ≅
          SheafOfModules.homObj (R := R) (F.X (-n))
            (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) := by
  classical
  let O := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let L := (CochainComplex.singleFunctor _ 0).obj O
  let D := ((homComplexFunctor (R := R)).obj (op F)).obj L
  have hadd (M : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
      ((SheafOfModules.homFunctor R).obj (op M)).Additive := by
    constructor
    intro A B f g
    apply SheafOfModules.hom_ext
    ext X φ
    rfl
  let π := Classical.choose
    (homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R))
  let T := fun p : ℤ => SheafOfModules.homObj (R := R) (F.X p) (L.X (p + n))
  have hc : IsLimit (Fan.mk (D.X n) (fun p : ℤ => π F L n p (p + n) rfl)) :=
    Classical.choice ((Classical.choose_spec
      (homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R))).1 F L n)
  have hz (p : ℤ) (h : p ≠ -n) : IsZero (T p) := by
    exact (((SheafOfModules.homFunctor R).obj (op (F.X p))).map_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 O
        (p + n) (by omega)))
  let v : T (-n) ⟶ D.X n := Fan.IsLimit.lift hc
    (fun p => if h : p = -n then eqToHom (congrArg T h.symm) else 0)
  have hv : v ≫ π F L n (-n) (-n + n) rfl = 𝟙 (T (-n)) := by
    change Fan.IsLimit.lift hc _ ≫
      (Fan.mk (D.X n) (fun p : ℤ => π F L n p (p + n) rfl)).proj (-n) = _
    rw [Fan.IsLimit.fac]
    simp
  have hπ : π F L n (-n) (-n + n) rfl ≫ v = 𝟙 (D.X n) := by
    apply Fan.IsLimit.hom_ext hc
    intro p
    change (π F L n (-n) (-n + n) rfl ≫ v) ≫ π F L n p (p + n) rfl =
      𝟙 (D.X n) ≫ π F L n p (p + n) rfl
    by_cases h : p = -n
    · subst p
      rw [Category.assoc, hv, Category.comp_id, Category.id_comp]
    · exact (hz p h).eq_of_tgt _ _
  have hi : IsIso (π F L n (-n) (-n + n) rfl) :=
    (Iso.mk (π F L n (-n) (-n + n) rfl) v hπ hv).isIso_hom
  have hi' : IsIso (π F L n (-n) 0 (by omega)) := by
    exact isIso_dependent_projection (fun q h => π F L n (-n) q h) (by omega) hi
  let e : L.X 0 ≅ O := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 O
  exact ⟨@asIso _ _ _ _ (π F L n (-n) 0 (by omega)) hi' ≪≫
    ((SheafOfModules.homFunctor R).obj (op (F.X (-n)))).mapIso e⟩

set_option backward.isDefEq.respectTransparency false in
private theorem restricted_derived_unit_iso (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj (𝟙_ (schemeDerivedCategory X)) ≅
        DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
          (SheafOfModules.unit ((moduleRings X.toRingedSpace).over U)))) := by
  let A := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let O := SheafOfModules.unit (moduleRings X.toRingedSpace)
  let E := (CochainComplex.singleFunctor A 0).obj O
  let T := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let e : DerivedCategory.Q.obj E ≅ 𝟙_ (schemeDerivedCategory X) :=
    (DerivedCategory.quotientCompQhIso A).symm.app E
  exact ⟨T.mapDerivedCategory.mapIso e.symm ≪≫ T.mapDerivedCategoryFactors.app E ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℤ) 0).app O)⟩

set_option backward.isDefEq.respectTransparency true in
private theorem homComplex_dual_bounded_finiteFree
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    (F : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (F.X n))
    (hf : ∀ n : ℤ, ∃ r : ℕ, Nonempty (F.X n ≅ SheafOfModules.free
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
        (ULift.{u} (Fin r)))) :
    let L := (CochainComplex.singleFunctor _ 0).obj
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R));
    let D := homComplex (R := R) F L;
    (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (D.X n)) ∧
      ∀ n : ℤ, ∃ r : ℕ, Nonempty (D.X n ≅ SheafOfModules.free
        (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
          (ULift.{u} (Fin r))) := by
  let O := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let L := (CochainComplex.singleFunctor _ 0).obj O
  let D := ((homComplexFunctor (R := R)).obj (op F)).obj L
  have he (n : ℤ) : Nonempty (D.X n ≅ SheafOfModules.homObj (R := R) (F.X (-n)) O) :=
    homComplex_dual_term_iso J R F n
  constructor
  · obtain ⟨a, b, hab⟩ := hb
    refine ⟨-b, -a, ?_⟩
    intro n hn
    have hz : IsZero (F.X (-n)) := hab (-n) (by omega)
    have hz' := ((SheafOfModules.homFunctor R).flip.obj O).map_isZero hz.op
    exact hz'.of_iso (he n).some
  · intro n
    obtain ⟨r, ⟨e⟩⟩ := hf (-n)
    refine ⟨r, ⟨(he n).some ≪≫
      ((SheafOfModules.homFunctor R).flip.obj O).mapIso e.symm.op ≪≫ ?_⟩⟩
    exact SheafOfModules.homObjFreeUnitIso (R := R) (ULift.{u} (Fin r))

set_option backward.isDefEq.respectTransparency false in
/-- The derived dual of a bounded finite free complex on an affine open is represented
by a bounded finite free complex. The second argument is the restriction of the actual
unit of the shared derived tensor structure.

Source: Stacks Project, Cohomology, Tag 08DQ, proof of lemma-dual-perfect-complex,
and Tag 08DM, lemma-RHom-strictly-perfect.
Proof: let O[0] be the single complex on the unit module of the localized ringed site.
Construct D as the ordinary Hom complex Hom(F,O[0]). In degree n its product has just
one potentially nonzero factor, Hom(F^(-n),O), because O[0] is zero in every other
degree. For a finite free F^(-n) of rank r this factor is finite free of rank r by the
dual-basis isomorphism. Hence D is finite free in every degree, and bounds [a,b] for F
give bounds [-b,-a] for D. A finite free term is its own finite free retract, so F is
strictly perfect. Apply `lem-pc-rhom-strict-perfect-hom` to F and O[0] to identify Q(D)
with RHom(Q(F),Q(O[0])). Exact open restriction carries the degree-zero unit module to
that of the localized site. The shared K-flat derived tensor unit is represented by
this degree-zero unit, so Q(O[0]) is canonically isomorphic to the displayed restriction
of the global unit. Apply RHom in its second variable to this isomorphism and compose.
The construction also applies to the zero complex and rank-zero terms; the signs in
its differential are those of the ordinary Hom complex, not a termwise dual with an
unspecified differential.
(blueprint: lem-pc-finite-free-derived-dual-model). -/
theorem exists_bounded_finiteFree_derived_dual_model
    (X : Scheme.{u}) (U : X.Opens) [IsAffine U.toScheme]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [hU : HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (F : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (F.X n))
    (hfree : ∀ n : ℤ, ∃ r : ℕ, Nonempty (F.X n ≅ SheafOfModules.free
      (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin r)))) :
    ∃ D : CochainComplex
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (D.X n)) ∧
      (∀ n : ℤ, ∃ r : ℕ, Nonempty (D.X n ≅ SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin r)))) ∧
      Nonempty (DerivedCategory.Q.obj D ≅
        (@derivedInternalHom.{u, w} (Over U) _
          ((Opens.grothendieckTopology X.toRingedSpace).over U)
          (X.toRingedSpace.sheaf.over U) hU).obj
          (op ((DerivedCategory.Q (C := SheafOfModules.{u}
              ((moduleRings X.toRingedSpace).over U))).obj F),
            (SheafOfModules.overFunctor.{u}
              (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj
                (𝟙_ (schemeDerivedCategory X)))) := by
  let R := X.toRingedSpace.sheaf.over U
  let O := SheafOfModules.unit ((moduleRings X.toRingedSpace).over U)
  let L := (CochainComplex.singleFunctor _ 0).obj O
  let D := homComplex (R := R) F L
  obtain ⟨hb, hf⟩ := homComplex_dual_bounded_finiteFree _ R F hbounded hfree
  refine ⟨D, hb, hf, ?_⟩
  have hstrict : IsStrictlyPerfect X U F := by
    refine ⟨hbounded, ?_⟩
    intro n
    obtain ⟨r, ⟨e⟩⟩ := hfree n
    exact ⟨r, e.hom, e.inv, e.hom_inv_id⟩
  obtain ⟨eD⟩ := (@isIso_homComplex_resolution_of_isStrictlyPerfect.{u, w}
    X U inferInstance hU F L hstrict).1
  obtain ⟨eU⟩ := restricted_derived_unit_iso X U
  let H := @derivedInternalHom.{u, w} (Over U) _
    ((Opens.grothendieckTopology X.toRingedSpace).over U) R hU
  exact ⟨eD ≪≫ H.mapIso ((Iso.refl _).prod eU.symm)⟩

end AlgebraicGeometry.Scheme
