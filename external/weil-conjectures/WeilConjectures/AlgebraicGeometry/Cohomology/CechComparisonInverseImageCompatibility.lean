/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.CechComparisonSystem
import WeilConjectures.AlgebraicGeometry.Cohomology.CechComparisonInverseImageUnit
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
import WeilConjectures.CategoryTheory.InjectiveCechAugmentationQuasiIso

/-! # Compatibility of normalized comparisons with inverse image

Source: Stacks Project, Tags 01EQ and 01FD. -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

private noncomputable def cechOverAbIso
    {R : Type u} [CommRing R] {X : Scheme.{u}} {ι : Type u}
    (f : X ⟶ Spec (.of R)) (U : ι → X.Opens) (M : X.Modules) :
    ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj
        (cechOver f U M) ≅
      (TopCat.Sheaf.cechComplexFunctor U).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) :=
  TopCat.Presheaf.cechComplexFunctorIso U (presheafOver f M) ≪≫
    (TopCat.Presheaf.cechComplex U).mapIso (presheafOverForgetIso f M)

private noncomputable def cechOverAbCycles
    {R : Type u} [CommRing R] {X : Scheme.{u}} {ι : Type u}
    (f : X ⟶ Spec (.of R)) (U : ι → X.Opens) (M : X.Modules) (q : ℕ)
    (z : (cechOver f U M).cycles q) :
    ((TopCat.Sheaf.cechComplexFunctor U).obj
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)).cycles q :=
  HomologicalComplex.cyclesMap (cechOverAbIso f U M).hom q
    ((((cechOver f U M).sc q).mapCyclesIso
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).inv z)

private lemma cechOverAbCycles_i
    {R : Type u} [CommRing R] {X : Scheme.{u}} {ι : Type u}
    (f : X ⟶ Spec (.of R)) (U : ι → X.Opens) (M : X.Modules) (q : ℕ)
    (z : (cechOver f U M).cycles q) (y : Fin (q + 1) → ι) :
    ((TopCat.Sheaf.cechComplexFunctor U).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)).iCycles q
        (cechOverAbCycles f U M q z) y =
      cechCoordinate f U M q y ((cechOver f U M).iCycles q z) := by
  set_option backward.isDefEq.respectTransparency false in
    let K := cechOver f U M
    let T := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
    have hi : (((T.mapHomologicalComplex (.up ℕ)).obj K).iCycles q)
        ((((K.sc q).mapCyclesIso T).inv) z) = K.iCycles q z := by
      have h := (K.sc q).mapCyclesIso_hom_iCycles T
      have h' : ((K.sc q).mapCyclesIso T).inv ≫ ((K.sc q).map T).iCycles =
          T.map (K.iCycles q) := by
        rw [← h, Iso.inv_hom_id_assoc]
        rfl
      exact ConcreteCategory.congr_hom h' z
    have h := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (cechOverAbIso f U M).hom q)
      ((((K.sc q).mapCyclesIso T).inv) z)
    change _ = (cechOverAbIso f U M).hom.f q
      ((((T.mapHomologicalComplex (.up ℕ)).obj K).iCycles q
        ((((K.sc q).mapCyclesIso T).inv) z))) at h
    rw [hi] at h
    exact congr_fun h y

private lemma cechOverAbCycles_π
    {R : Type u} [CommRing R] {X : Scheme.{u}} {ι : Type u}
    (f : X ⟶ Spec (.of R)) (U : ι → X.Opens) (M : X.Modules) (q : ℕ)
    (z : (cechOver f U M).cycles q) :
    cechOverHomologyAddEquiv f U M q ((cechOver f U M).homologyπ q z) =
      ((TopCat.Sheaf.cechComplexFunctor U).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)).homologyπ q
        (cechOverAbCycles f U M q z) := by
  set_option backward.isDefEq.respectTransparency false in
    let K := cechOver f U M
    let T := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
    let S := K.sc q
    have hp : (S.map T).homologyπ ≫ (S.mapHomologyIso T).hom =
        (S.mapCyclesIso T).hom ≫ T.map S.homologyπ := by
      let h := S.homologyData.left
      rw [h.mapHomologyIso_eq T, h.mapCyclesIso_eq T]
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
      rw [(h.map T).homologyπ_comp_homologyIso_hom_assoc]
      change (h.map T).cyclesIso.hom ≫ T.map h.π ≫ T.map h.homologyIso.inv = _
      rw [← T.map_comp, h.π_comp_homologyIso_inv, T.map_comp]
    have hp' : T.map (K.homologyπ q) ≫ (S.mapHomologyIso T).inv =
        (S.mapCyclesIso T).inv ≫ (S.map T).homologyπ := by
      apply (cancel_mono (S.mapHomologyIso T).hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, hp,
        Iso.inv_hom_id_assoc]
      rfl
    have h := ConcreteCategory.congr_hom hp' z
    change (S.mapHomologyIso T).inv (K.homologyπ q z) =
      (((T.mapHomologicalComplex (.up ℕ)).obj K).homologyπ q)
        ((S.mapCyclesIso T).inv z) at h
    have hn := ConcreteCategory.congr_hom
      (HomologicalComplex.homologyπ_naturality (cechOverAbIso f U M).hom q)
      ((S.mapCyclesIso T).inv z)
    change HomologicalComplex.homologyMap (cechOverAbIso f U M).hom q
        ((((T.mapHomologicalComplex (.up ℕ)).obj K).homologyπ q)
          ((S.mapCyclesIso T).inv z)) = _ at hn
    rw [← h] at hn
    change HomologicalComplex.homologyMap
        ((TopCat.Presheaf.cechComplex U).mapIso (presheafOverForgetIso f M)).hom q
        (HomologicalComplex.homologyMap
          (TopCat.Presheaf.cechComplexFunctorIso U (presheafOver f M)).hom q
          ((S.mapHomologyIso T).inv (K.homologyπ q z))) = _
    dsimp only [TopCat.Sheaf.cechComplexFunctor, Functor.comp_obj, sheafToPresheaf,
      ObjectProperty.ι, inducedFunctor] at hn ⊢
    simp only [K, S, T, cechOverAbIso, Iso.trans_hom,
      HomologicalComplex.homologyMap_comp, ConcreteCategory.comp_apply] at hn
    convert hn using 1
    rfl

/-- Inverse image respects any normalized additive Cech comparison systems.
This is a compatibility statement for existing systems, not an existence assertion.

Source: Stacks Project, Tag 01FD, Lemma 20.15.1, and the normalized comparison
construction of Tag 01EQ, Lemma 20.11.2.
(blueprint: lem-pc-cech-comparison-inverse-image-compatibility)

Proof: Pass from scalar-restricted Čech cycles to the explicit abelian complex
using cechComplexFunctorIso, presheafOverForgetIso, and mapCyclesIso for the exact
forgetful functor. The cycle inclusion is coordinatewise cechCoordinate, and the
homology projection agrees with cechOverHomologyAddEquiv by the canonical
mapCyclesIso/mapHomologyIso square and naturality of homologyπ.

Write F and G for the underlying abelian sheaves of M and N. Construct the Čech
chain map A associated to the underlying coefficient map a : F → g_*G. The
coordinate hypothesis says that A sends the transported cycle z to z'. Since the
cycle inclusion is monic, the transported cycles agree, and naturality of
homologyπ identifies their classes.

Factor a as the inverse-image adjunction unit followed by g_*coeff. Naturality
of coeff with respect to restrictions gives a factorization of A as the unit
Čech map B followed by the Čech coefficient map. Apply
cechComparison_inverseImage_unit to B, then the naturality of c'.comparison to
coeff. Functoriality of homology and the class equality give the displayed law.
The inverse-image-unit theorem contains the normalized uniqueness and resolution
pentagon arguments; coefficient naturality and scalar/cycle transport are proved
here. No affine-intersection, acyclicity or quasi-coherence hypothesis is used;
the chain-map and transport calculations also apply to an empty index set. -/
theorem cechComparison_inverseImage_compatibility
    {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}} {ι : Type u}
    (g : Y ⟶ X) (f : X ⟶ Spec (.of R)) (f' : Y ⟶ Spec (.of S))
    (U : ι → X.Opens) (V : ι → Y.Opens) (hcover : iSup U = ⊤)
    (hcover' : iSup V = ⊤) (M : X.Modules) (N : Y.Modules)
    (φ : M ⟶ (pushforward g).obj N)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (c : CechComparisonSystem U hcover) (c' : CechComparisonSystem V hcover') :
    ∀ (q : ℕ) (z : (cechOver f U M).cycles q) (z' : (cechOver f' V N).cycles q),
      (∀ y : Fin (q + 1) → ι,
        cechCoordinate f' V N q y ((cechOver f' V N).iCycles q z') =
          N.presheaf.map (homOfLE (hinter q y)).op
            (φ.val.app (op (⨅ l, U (y l)))
              (cechCoordinate f U M q y ((cechOver f U M).iCycles q z)))) →
      c'.overMap f' N q ((cechOver f' V N).homologyπ q z') =
        Sheaf.H.map (coeff g φ) q
          (Sheaf.H.mapFunctor (invImage g) (constIso g).symm
            ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) q
              (c.overMap f M q ((cechOver f U M).homologyπ q z))) := by
  set_option backward.isDefEq.respectTransparency false in
    intro q z z' hz
    let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj M
    let G := (SheafOfModules.toSheaf Y.ringCatSheaf).obj N
    let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base
    let a := (SheafOfModules.toSheaf X.ringCatSheaf).map φ
    let η := adj.unit.app F
    let ψ := coeff g φ
    let A := cechInverseImageCochainMap g U V hinter F G a.hom
    let B := cechInverseImageCochainMap g U V hinter F ((invImage g).obj F) η.hom
    have hη : η ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g.base).map ψ = a := by
      have h := (adj.homEquiv F G).apply_symm_apply a
      rw [adj.homEquiv_unit] at h
      exact h
    have hA : A = B ≫ (TopCat.Sheaf.cechComplexFunctor V).map ψ := by
      ext k : 1
      apply AddCommGrpCat.ext
      intro x
      funext y
      have hh := ConcreteCategory.congr_hom
        (congrArg (fun t ↦ t.hom.app (op (⨅ l, U (y l)))) hη) (x y)
      have hn := NatTrans.naturality_apply ψ.hom (homOfLE (hinter k y)).op
        (η.hom.app (op (⨅ l, U (y l))) (x y))
      change _ = G.obj.map (homOfLE (hinter k y)).op
        (ψ.hom.app _ (η.hom.app _ (x y))) at hn
      change G.obj.map (homOfLE (hinter k y)).op (a.hom.app _ (x y)) =
        ψ.hom.app _ (((invImage g).obj F).obj.map (homOfLE (hinter k y)).op
          (η.hom.app _ (x y)))
      exact (congrArg (G.obj.map (homOfLE (hinter k y)).op) hh.symm).trans hn.symm
    let w := cechOverAbCycles f U M q z
    let w' := cechOverAbCycles f' V N q z'
    have hw : HomologicalComplex.cyclesMap A q w = w' := by
      apply (AddCommGrpCat.mono_iff_injective
        (((TopCat.Sheaf.cechComplexFunctor V).obj G).iCycles q)).mp inferInstance
      have hi := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i A q) w
      change ((TopCat.Sheaf.cechComplexFunctor V).obj G).iCycles q
          (HomologicalComplex.cyclesMap A q w) =
        A.f q (((TopCat.Sheaf.cechComplexFunctor U).obj F).iCycles q w) at hi
      rw [hi]
      funext y
      change G.obj.map (homOfLE (hinter q y)).op
          (a.hom.app _ ((((TopCat.Sheaf.cechComplexFunctor U).obj F).iCycles q w) y)) = _
      rw [cechOverAbCycles_i, cechOverAbCycles_i]
      exact (hz y).symm
    let x := cechOverHomologyAddEquiv f U M q ((cechOver f U M).homologyπ q z)
    let x' := cechOverHomologyAddEquiv f' V N q ((cechOver f' V N).homologyπ q z')
    have hx : HomologicalComplex.homologyMap A q x = x' := by
      dsimp only [x, x']
      rw [cechOverAbCycles_π, cechOverAbCycles_π]
      have hh := ConcreteCategory.congr_hom
        (HomologicalComplex.homologyπ_naturality A q) w
      change _ = ((TopCat.Sheaf.cechComplexFunctor V).obj G).homologyπ q
        (HomologicalComplex.cyclesMap A q w) at hh
      rw [hw] at hh
      exact hh
    have hu := cechComparison_inverseImage_unit g U V hcover hcover' hinter c c' F q x
    have hn := ConcreteCategory.congr_hom ((c'.comparison q).naturality ψ)
      (HomologicalComplex.homologyMap B q x)
    change (c'.comparison q).app G
        (HomologicalComplex.homologyMap ((TopCat.Sheaf.cechComplexFunctor V).map ψ) q
          (HomologicalComplex.homologyMap B q x)) =
      Sheaf.H.map ψ q ((c'.comparison q).app ((invImage g).obj F)
        (HomologicalComplex.homologyMap B q x)) at hn
    change (c'.comparison q).app G x' =
      Sheaf.H.map ψ q (Sheaf.H.mapFunctor (invImage g) (constIso g).symm F q
        ((c.comparison q).app F x))
    rw [← hx, hA, HomologicalComplex.homologyMap_comp, ConcreteCategory.comp_apply,
      hn, hu]
end AlgebraicGeometry.Scheme.Modules
