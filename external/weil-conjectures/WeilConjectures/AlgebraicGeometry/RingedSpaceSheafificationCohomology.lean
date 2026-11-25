/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Topology.Sheaves.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Sheafification of cohomology over open subsets

Source: Stacks Project, Cohomology, Lemma 20.32.3, Tag 0BKJ
(blueprint: lem-pc-ringed-space-sheafification-cohomology).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

noncomputable section

-- Resolved section cohomology inverts quasi-isomorphisms via the homotopy category.
private theorem resolvedCohomology_inverts (X : RingedSpace.{u}) (q : ℤ) :
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (moduleRings X))
      (ComplexShape.up ℤ)).IsInvertedBy
      (CochainComplex.kInjectiveResolutionFunctor.{u}
          (SheafOfModules.{u} (moduleRings X)) ⋙
        (SheafOfModules.toSheaf (moduleRings X) ⋙
          sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) q) := by
  intro K L s hs
  let C := SheafOfModules.{u} (moduleRings X)
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} C
  let η := CochainComplex.toKInjectiveResolution.{u} C
  let F := SheafOfModules.toSheaf (moduleRings X) ⋙
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  have hη (M : CochainComplex C ℤ) : QuasiIso (η.app M) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} C M).2
  have : QuasiIso s := hs
  have : QuasiIso (η.app K ≫ I.map s) := by
    rw [← η.naturality s]
    let _ := hη L
    change QuasiIso (s ≫ η.app L)
    infer_instance
  let _ := hη K
  have : QuasiIso (I.map s) :=
    (quasiIso_iff_comp_left (η.app K) (I.map s)).mp inferInstance
  have : IsIso ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (I.map s)) :=
    HomotopyCategory.quotient_inverts_homotopyEquivalences _ _ _
      ((CochainComplex.IsKInjective.quasiIso_iff (I.map s)).mp inferInstance)
  have : IsIso ((HomotopyCategory.homologyFunctor _ (ComplexShape.up ℤ) q).map
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (I.map s)))) := by
    infer_instance
  exact (NatIso.isIso_map_iff
    (HomotopyCategory.homologyFunctorFactors _ (ComplexShape.up ℤ) q)
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (I.map s))).mp this

-- Exact abelian sheafification commutes with homology; its counit recovers a sheaf.
private def complexSheafificationHomologyIso (X : RingedSpace.{u}) (q : ℤ) :
    (SheafOfModules.toSheaf (moduleRings X) ⋙
        sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙
      HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) q ⋙
        presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ≅
    HomologicalComplex.homologyFunctor (SheafOfModules.{u} (moduleRings X))
        (ComplexShape.up ℤ) q ⋙ SheafOfModules.toSheaf (moduleRings X) := by
  let T := SheafOfModules.toSheaf (moduleRings X)
  let U := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let S := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let e : (T ⋙ U) ⋙ S ≅ T :=
    Functor.associator T U S ≪≫
      Functor.isoWhiskerLeft T (asIso (sheafificationAdjunction _ _).counit) ≪≫
        T.rightUnitor
  exact Functor.isoWhiskerLeft ((T ⋙ U).mapHomologicalComplex (ComplexShape.up ℤ))
      (S.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) q).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) q) ≪≫
    T.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) q

/-- Cohomology of sections of the functorial K-injective replacement descends to the
unbounded derived category. Its sheafification is naturally the cohomology sheaf.
The comparison with that sheaf is the sheafification unit followed by this isomorphism;
it represents every stalk element locally, detects zero locally, and commutes with
morphisms on germs.

Source: Stacks Project, Tag 0BKJ
(blueprint: lem-pc-ringed-space-sheafification-cohomology).

Proof:
1. Resolve by `CochainComplex.kInjectiveResolutionFunctor`, as in
   `def-pc-ringed-spaces-derived-direct-image`. A quasi-isomorphism between the resulting
   K-injective complexes is a homotopy equivalence. Taking sections and then cohomology
   therefore inverts quasi-isomorphisms and descends to the derived category.
2. Compute cycles, boundaries and their quotient sectionwise. Exact sheafification
   (`lem-weil-pbc-ringed-site-module-sheafification-exact`) identifies their sheafifications
   with the cycles, boundaries and cohomology sheaf of the resolution. The resolution
   quasi-isomorphism identifies the latter with the derived cohomology sheaf. This is
   natural in chain maps and hence, by localization, in all derived morphisms.
3. The sheafification unit is an isomorphism on stalks
   (`lem-weil-pbc-stalk-sheafification-space`). The stalk is the filtered colimit over
   neighborhoods (`def-weil-pbc-module-stalk`), so every element is represented locally
   and a zero germ vanishes on a smaller neighborhood. Naturality of the comparison
   gives the asserted compatibility for the germ of the image of a section. -/
theorem sheafification_cohomology (X : RingedSpace.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))] (q : ℤ) :
    ∃ P : DerivedCategory (SheafOfModules.{u} (moduleRings X)) ⥤
        ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}),
      Nonempty (DerivedCategory.Q ⋙ P ≅
        CochainComplex.kInjectiveResolutionFunctor.{u}
            (SheafOfModules.{u} (moduleRings X)) ⋙
          (Functor.mapHomologicalComplex
            (SheafOfModules.toSheaf (moduleRings X) ⋙
            sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
            (ComplexShape.up ℤ)) ⋙
          HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) q) ∧
      ∃ e : P ⋙ presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ≅
          DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings X)) q ⋙
            SheafOfModules.toSheaf (moduleRings X),
        ∃ θ : P ⟶
            DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings X)) q ⋙
              SheafOfModules.toSheaf (moduleRings X) ⋙
                sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u},
          θ = Functor.whiskerLeft P
              (sheafificationAdjunction (Opens.grothendieckTopology X)
                AddCommGrpCat.{u}).unit ≫
            Functor.whiskerRight e.hom
              (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ∧
          (∀ (K : DerivedCategory (SheafOfModules.{u} (moduleRings X))) (x : X)
            (t : ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
              ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (moduleRings X)) q ⋙
                  SheafOfModules.toSheaf (moduleRings X) ⋙
                    sheafToPresheaf (Opens.grothendieckTopology X)
                      AddCommGrpCat.{u}).obj K))),
            ∃ (U : Opens X) (hx : x ∈ U) (s : (P.obj K).obj (op U)),
              (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) _ U x hx)
                ((θ.app K).app (op U) s) = t) ∧
          (∀ (K : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
            (U : Opens X) (x : X) (hx : x ∈ U) (s : (P.obj K).obj (op U)),
            (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) _ U x hx) ((θ.app K).app (op U) s) = 0 →
              ∃ (V : Opens X) (_hxV : x ∈ V) (i : V ⟶ U),
                (P.obj K).map i.op s = 0) ∧
          (∀ (K L : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
            (f : K ⟶ L) (U : Opens X) (x : X) (hx : x ∈ U)
            (s : (P.obj K).obj (op U)),
            (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) _ U x hx)
                ((θ.app L).app (op U) ((P.map f).app (op U) s)) =
              ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
                ((DerivedCategory.homologyFunctor
                  (SheafOfModules.{u} (moduleRings X)) q ⋙
                    SheafOfModules.toSheaf (moduleRings X) ⋙
                      sheafToPresheaf (Opens.grothendieckTopology X)
                        AddCommGrpCat.{u}).map f))
                  ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) _ U x hx)
                    ((θ.app K).app (op U) s))) := by
  let C := SheafOfModules.{u} (moduleRings X)
  let J := Opens.grothendieckTopology X
  let T := SheafOfModules.toSheaf (moduleRings X)
  let U := sheafToPresheaf J AddCommGrpCat.{u}
  let S := presheafToSheaf J AddCommGrpCat.{u}
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} C
  let H := HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q
  let DH := DerivedCategory.homologyFunctor C q
  let R := I ⋙ (T ⋙ U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) q
  let W := HomologicalComplex.quasiIso C (ComplexShape.up ℤ)
  have hR : W.IsInvertedBy R := resolvedCohomology_inverts X q
  let P := Localization.lift R hR DerivedCategory.Q
  let η := CochainComplex.toKInjectiveResolution.{u} C
  let ηH : H ⟶ I ⋙ H := Functor.whiskerRight η H
  have hηH : IsIso ηH := by
    have (K : CochainComplex C ℤ) : IsIso (ηH.app K) := by
      have : QuasiIso (η.app K) :=
        (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} C K).2
      change IsIso (HomologicalComplex.homologyMap (η.app K) q)
      infer_instance
    exact NatIso.isIso_of_isIso_app ηH
  let c : R ⋙ S ≅ DerivedCategory.Q ⋙ DH ⋙ T :=
    Functor.isoWhiskerLeft I (complexSheafificationHomologyIso X q) ≪≫
      Functor.isoWhiskerRight (asIso ηH).symm T ≪≫
        Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors C q).symm T
  let e : P ⋙ S ≅ DH ⋙ T :=
    Localization.liftNatIso DerivedCategory.Q W (R ⋙ S) (DerivedCategory.Q ⋙ DH ⋙ T)
      (P ⋙ S) (DH ⋙ T) c
  let θ : P ⟶ DH ⋙ T ⋙ U :=
    Functor.whiskerLeft P (sheafificationAdjunction J AddCommGrpCat.{u}).unit ≫
      Functor.whiskerRight e.hom U
  have hθ (K : DerivedCategory C) (x : X) :
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (θ.app K)) := by
    have hu := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
      x AddCommGrpCat.{u} (P.obj K)
    change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((sheafificationAdjunction J AddCommGrpCat.{u}).unit.app (P.obj K) ≫
        U.map (e.hom.app K)))
    rw [Functor.map_comp]
    infer_instance
  refine ⟨P, ⟨Localization.fac R hR DerivedCategory.Q⟩, e, θ, rfl, ?_, ?_, ?_⟩
  · intro K x t
    let _ := hθ K x
    obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (θ.app K))).2 t
    obtain ⟨V, hx, s, hs⟩ := TopCat.Presheaf.exists_germ_eq (P.obj K) a
    refine ⟨V, hx, s, ?_⟩
    rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply, hs]
    exact ha
  · intro K V x hx s hs
    let _ := hθ K x
    have hz : TopCat.Presheaf.germ (P.obj K) V x hx s = 0 := by
      apply (ConcreteCategory.bijective_of_isIso
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (θ.app K))).1
      rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
      rw [map_zero]
      exact hs
    obtain ⟨Z, hxZ, i, j, heq⟩ :=
      TopCat.Presheaf.germ_eq (P.obj K) x hx hx s 0 (by simpa using hz)
    exact ⟨Z, hxZ, i, by simpa using heq⟩
  · intro K L f V x hx s
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    congr 1
    exact ConcreteCategory.congr_hom (NatTrans.congr_app (θ.naturality f) (op V)) s

end

end AlgebraicGeometry.RingedSpace
