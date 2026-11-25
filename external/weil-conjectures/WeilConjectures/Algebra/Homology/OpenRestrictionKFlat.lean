/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Topology.Sheaves.Abelian
import WeilConjectures.Algebra.Homology.ModuleExtensionByZeroUnitIsIso
import WeilConjectures.Algebra.Homology.OpenRestrictionTensorNatural
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # K-flatness under restriction to an open localized site

Source: Stacks Project, Tags 06YB and 03DH.
(blueprint: lem-pc-open-localized-restriction-kflat).
-/

@[expose] public section

universe u
open CategoryTheory

namespace CochainComplex

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Restriction preserves total tensors by naturality in both differentials and
  preservation of coproducts. Source: Stacks, Tags 01CD and 03DH. -/
private theorem localized_totalTensor_iso
    {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (U : TopologicalSpace.Opens X)
    (hzero : (SheafOfModules.overFunctor.{u} ((sheafCompose
      (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).PreservesZeroMorphisms)
    (P N : CochainComplex (SheafOfModules.{u} ((sheafCompose
      (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) :
    letI := hzero
    let A := (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R
    let V := SheafOfModules.overFunctor.{u} A U
    letI : MonoidalCategory (SheafOfModules.{u} A) :=
      SheafOfModules.monoidalCategory R
    letI : MonoidalCategory (SheafOfModules.{u} (A.over U)) :=
      SheafOfModules.monoidalCategory (R.over U)
    letI : MonoidalPreadditive (SheafOfModules.{u} A) :=
      Classical.choice (SheafOfModules.tensorClosed R).1
    letI : MonoidalPreadditive (SheafOfModules.{u} (A.over U)) :=
      Classical.choice (SheafOfModules.tensorClosed (R.over U)).1
    Nonempty ((V.mapHomologicalComplex (.up ℤ)).obj
      (mapBifunctor P N (MonoidalCategory.curriedTensor (SheafOfModules.{u} A))) ≅
        mapBifunctor ((V.mapHomologicalComplex (.up ℤ)).obj P)
          ((V.mapHomologicalComplex (.up ℤ)).obj N)
          (MonoidalCategory.curriedTensor (SheafOfModules.{u} (A.over U)))) := by
  classical
  let := hzero
  let A := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let V := SheafOfModules.overFunctor.{u} A U
  have : V.Additive := by
    constructor
    intro M N f g
    ext W x
    rfl
  have : CategoryTheory.Limits.PreservesColimitsOfSize.{0, 0} V := by
    dsimp [V, SheafOfModules.overFunctor]
    infer_instance
  let : MonoidalCategory (SheafOfModules.{u} A) :=
    SheafOfModules.monoidalCategory R
  let : MonoidalCategory (SheafOfModules.{u} (A.over U)) :=
    SheafOfModules.monoidalCategory (R.over U)
  let : MonoidalPreadditive (SheafOfModules.{u} A) :=
    Classical.choice (SheafOfModules.tensorClosed R).1
  let : MonoidalPreadditive (SheafOfModules.{u} (A.over U)) :=
    Classical.choice (SheafOfModules.tensorClosed (R.over U)).1
  let K := (((MonoidalCategory.curriedTensor (SheafOfModules.{u} A)).mapBifunctorHomologicalComplex
    (.up ℤ) (.up ℤ)).obj P).obj N
  have : V.PreservesTotalComplex K (.up ℤ) := fun _ ↦ inferInstance
  let e₁ := (HomologicalComplex₂.mapTotalIso V K (.up ℤ)).symm
  obtain ⟨e, he⟩ := SheafOfModules.exists_open_localized_tensor_natural R U
  let e₂ :
      (((V.mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℤ)).obj K) ≅
        (((MonoidalCategory.curriedTensor
          (SheafOfModules.{u} (A.over U))).mapBifunctorHomologicalComplex
          (.up ℤ) (.up ℤ)).obj
          ((V.mapHomologicalComplex (.up ℤ)).obj P)).obj
            ((V.mapHomologicalComplex (.up ℤ)).obj N) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents (fun q ↦ e (P.X p) (N.X q))
        (by
          intro q q' hq
          change (e (P.X p) (N.X q)).hom ≫
            MonoidalCategory.whiskerLeft (V.obj (P.X p)) (V.map (N.d q q')) =
            V.map (MonoidalCategory.whiskerLeft (P.X p) (N.d q q')) ≫ (e (P.X p) (N.X q')).hom
          simpa [V] using
            (he (P.X p) (P.X p) (N.X q) (N.X q') (𝟙 _) (N.d q q')).symm))
      (by
        intro p p' hp
        apply HomologicalComplex.Hom.ext
        funext q
        change (e (P.X p) (N.X q)).hom ≫
          MonoidalCategory.whiskerRight (V.map (P.d p p')) (V.obj (N.X q)) =
          V.map (MonoidalCategory.whiskerRight (P.d p p') (N.X q)) ≫ (e (P.X p') (N.X q)).hom
        simpa [V] using
          (he (P.X p) (P.X p') (N.X q) (N.X q) (P.d p p') (𝟙 _)).symm)
  exact ⟨e₁ ≪≫ HomologicalComplex₂.total.mapIso e₂ (.up ℤ)⟩

/-- Restriction of a K-flat complex to the localized open site is K-flat.
Source: Stacks Project, Tag 06YB (`lemma-check-K-flat-stalks`), and Tag 03DH.

Proof: for an acyclic localized test complex F, apply the exact extension-by-zero
functor termwise to obtain an acyclic global complex G. The invertible adjunction unit
identifies F with the restriction of G. K-flatness of P gives acyclicity of Tot(G ⊗ P),
and exact restriction preserves it. The natural sheaf tensor comparison induces an
isomorphism of bicomplexes; restriction preserves coproducts, hence this comparison
commutes with totalization. Thus its restriction is Tot(V(G) ⊗ V(P)). Transport once
more along the unit complex isomorphism to obtain acyclicity of Tot(F ⊗ V(P)).
No bounds or termwise-flatness assumptions are used, and the construction also applies
to the empty open and zero complexes. The zero-map witness only defines the termwise
restriction and adds no mathematical hypothesis.
(blueprint: lem-pc-open-localized-restriction-kflat). -/
theorem open_localized_restriction_isKFlat
    {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (U : TopologicalSpace.Opens X)
    (hzero : (SheafOfModules.overFunctor.{u} ((sheafCompose
      (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).PreservesZeroMorphisms)
    (P : CochainComplex (SheafOfModules.{u} ((sheafCompose
      (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (hP : IsKFlatTensor (R := R) P) :
    letI := hzero
    IsKFlatTensor (R := R.over U)
      (((SheafOfModules.overFunctor.{u} ((sheafCompose
        (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) := by
  classical
  let := hzero
  let RX : AlgebraicGeometry.RingedSpace.{u} :=
    { carrier := X, presheaf := R.obj, IsSheaf := R.property }
  let A := AlgebraicGeometry.moduleRings RX
  let V := SheafOfModules.overFunctor.{u} A U
  let L := SheafOfModules.extensionByZeroPresheaf.{u} A U ⋙
    PresheafOfModules.sheafification.{u} (𝟙 A.obj)
  have hex := AlgebraicGeometry.open_restriction_adjunction_exact RX U
  let : CategoryTheory.Limits.PreservesFiniteLimits V := hex.1
  let : CategoryTheory.Limits.PreservesFiniteColimits V := hex.2.1
  let : CategoryTheory.Limits.PreservesFiniteLimits L := hex.2.2.1
  let : CategoryTheory.Limits.PreservesFiniteColimits L := hex.2.2.2.1
  let : V.Additive := Functor.additive_of_preserves_binary_products V
  let : L.Additive := Functor.additive_of_preserves_binary_products L
  let VC := V.mapHomologicalComplex (.up ℤ)
  let LC := L.mapHomologicalComplex (.up ℤ)
  let adj := Classical.choice hex.2.2.2.2
  let : MonoidalCategory (SheafOfModules.{u} A) :=
    SheafOfModules.monoidalCategory R
  let : MonoidalCategory (SheafOfModules.{u} (A.over U)) :=
    SheafOfModules.monoidalCategory (R.over U)
  let : MonoidalPreadditive (SheafOfModules.{u} A) :=
    Classical.choice (SheafOfModules.tensorClosed R).1
  let : MonoidalPreadditive (SheafOfModules.{u} (A.over U)) :=
    Classical.choice (SheafOfModules.tensorClosed (R.over U)).1
  intro F hF
  let G := LC.obj F
  have hG : G.Acyclic := by
    intro i
    change ((F.sc i).map L).Exact
    exact (hF i).map L
  have hu (M : SheafOfModules.{u} (A.over U)) : IsIso (adj.unit.app M) :=
    AlgebraicGeometry.moduleExtensionByZero_unit_isIso RX U M
  let e : F ≅ VC.obj G := HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ asIso (adj.unit.app (F.X i))) (by
      intro i j hij
      exact (adj.unit.naturality (F.d i j)).symm)
  have hT : (VC.obj (mapBifunctor G P (MonoidalCategory.curriedTensor _))).Acyclic := by
    intro i
    change (((mapBifunctor G P (MonoidalCategory.curriedTensor _)).sc i).map V).Exact
    exact (hP G hG i).map V
  obtain ⟨t⟩ := localized_totalTensor_iso R U hzero G P
  let eT :=
    (((MonoidalCategory.curriedTensor (SheafOfModules.{u} (A.over U))).map₂CochainComplex).mapIso
      e).app (VC.obj P)
  intro i
  exact ((hT i).of_iso t).of_iso eT.symm

end CochainComplex
