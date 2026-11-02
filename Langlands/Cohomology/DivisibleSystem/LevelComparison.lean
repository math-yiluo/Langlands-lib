import Langlands.Cohomology.DivisibleSystem.AdicHyperext
import Langlands.Cohomology.DivisibleSystem.CompatibleExt

/-!
# Finite-level compatibility of the comparison map for `ℓ`-divisible systems of complexes

For `ℓ`-divisible systems `T` and `W` of cochain complexes in an `R`-linear abelian category
`C`, the Library's `homComplexLimitToDerived R T W n` maps the degree `n` cohomology of the
inverse limit `homComplexLimit R T W` of the Hom complexes `Hom^•(T m, W m)` to the morphisms
`towerComplex T ⟶ (towerComplex W)⟦n⟧` in the derived category of inverse systems in `C`.
This module shows that this map is compatible with the analogous maps at the finite levels.

* `linearHomComplexHomologyToDerived R K L n` is, for cochain complexes `K` and `L` in `C`,
  the map from the degree `n` cohomology of the module-valued Hom complex `Hom^•(K, L)` to the
  morphisms `K ⟶ L⟦n⟧` in the derived category of `C`, built like `homComplexLimitToDerived`
  (homotopy class, then the localization functor `Qh`).
  `linearHomComplexHomologyToDerived_homologyπ` computes it on the class of a cycle.
* `DivisibleSystem.derivedEval_homComplexLimitToDerived`: evaluating at level `m` (by the
  published `derivedEval`) the derived morphism attached to a class `x` gives the derived
  morphism `T m ⟶ (W m)⟦n⟧` attached to the image of `x` in the cohomology of
  `Hom^•(T m, W m)` (the projection of the inverse limit to level `m`).
* `DivisibleSystem.homComplexLimitToCompatible` is the resulting map into the compatible
  families of levelwise derived morphisms (`compatibleDerived`), with components given by
  `homComplexLimitToCompatible_apply_coe`.

The auxiliary results are: `homologyπ_comp_mapHomologyIso_hom` (homology comparison for a
functor preserving left homology, in terms of cycles), `linearHomComplexCocycle` (the cocycle
of a cycle of the module-valued Hom complex),
`linearHomComplexHomologyHomotopyAddEquiv_homologyπ`, `cocycleMap` (a cocycle mapped by an
additive functor), `map_equivHomShift_symm` and `DivisibleSystem.derivedEval_Q_map`.

This is the finite-level side of the comparison behind Harris's integral statement (4.10.4)
(Harris 1999, end of the proof of Proposition 4.10, printed p.312), which is obtained from the
complexes (4.10.2) at the finite levels `m`. No bijectivity of any of these maps is claimed.
-/

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite DerivedCategory CochainComplex.HomComplex
open HyperextSpectralSequence

universe w w' t t' v u

section MapHomology

variable {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms] (S : ShortComplex C) [S.HasHomology]
  [(S.map F).HasHomology] [F.PreservesLeftHomologyOf S]

set_option backward.isDefEq.respectTransparency false in
/-- The homology comparison `S.mapHomologyIso F` is induced by the cycles comparison
`S.mapCyclesIso F`, for a functor `F` preserving the left homology of `S`. -/
@[reassoc]
lemma homologyπ_comp_mapHomologyIso_hom :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  rw [ShortComplex.LeftHomologyData.mapHomologyIso_eq S.leftHomologyData F,
    ShortComplex.LeftHomologyData.mapCyclesIso_eq S.leftHomologyData F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc, Category.assoc,
    ShortComplex.LeftHomologyData.map_π, ← F.map_comp,
    ShortComplex.LeftHomologyData.π_comp_homologyIso_inv]

end MapHomology

section LinearHomComplex

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- The cocycle underlying a degree `n` cycle of the module-valued Hom complex. -/
noncomputable def linearHomComplexCocycle (K L : CochainComplex C ℤ) (n : ℤ)
    (c : (LinearHomComplex.complex R K L).cycles n) : Cocycle K L n :=
  Cocycle.mk (((LinearHomComplex.complex R K L).iCycles n).hom c) (n + 1) rfl
    (congrArg (fun f => f.hom c) ((LinearHomComplex.complex R K L).iCycles_d n (n + 1)))

@[simp]
lemma linearHomComplexCocycle_coe (K L : CochainComplex C ℤ) (n : ℤ)
    (c : (LinearHomComplex.complex R K L).cycles n) :
    (linearHomComplexCocycle R K L n c : Cochain K L n) =
      ((LinearHomComplex.complex R K L).iCycles n).hom c :=
  rfl

/-- The class of a cycle `c` of the module-valued Hom complex is sent by
`linearHomComplexHomologyHomotopyAddEquiv` to the homotopy class of the morphism
`K ⟶ L⟦n⟧` of the cocycle of `c`. -/
lemma linearHomComplexHomologyHomotopyAddEquiv_homologyπ (K L : CochainComplex C ℤ) (n : ℤ)
    (c : (LinearHomComplex.complex R K L).cycles n) :
    linearHomComplexHomologyHomotopyAddEquiv R K L n
        (((LinearHomComplex.complex R K L).homologyπ n).hom c) =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        (Cocycle.equivHomShift.symm (linearHomComplexCocycle R K L n c)) := by
  let S := (LinearHomComplex.complex R K L).sc n
  let F := forget₂ (ModuleCat.{v} R) AddCommGrpCat
  let φ := (linearHomComplexScIso R K L n).hom
  let h := CochainComplex.HomComplex.leftHomologyData K L n
  have key : F.map S.homologyπ ≫ (S.mapHomologyIso F).inv ≫ ShortComplex.homologyMap φ ≫
      h.homologyIso.hom =
      (S.mapCyclesIso F).inv ≫ ShortComplex.cyclesMap φ ≫ h.cyclesIso.hom ≫ h.π := by
    rw [← cancel_epi (S.mapCyclesIso F).hom, Iso.hom_inv_id_assoc,
      ← homologyπ_comp_mapHomologyIso_hom_assoc, Iso.hom_inv_id_assoc,
      ShortComplex.homologyπ_naturality_assoc,
      ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
  have keyi : (S.mapCyclesIso F).inv ≫ ShortComplex.cyclesMap φ ≫ h.cyclesIso.hom ≫ h.i =
      F.map S.iCycles ≫ φ.τ₂ := by
    rw [ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i, ShortComplex.cyclesMap_i,
      ← Category.assoc]
    congr 1
    rw [Iso.inv_comp_eq, ShortComplex.mapCyclesIso_hom_iCycles]
  have hc := congrArg (fun f => f.hom c) key
  have hi := congrArg (fun f => f.hom c) keyi
  have hcoc : (h.cyclesIso.hom.hom (ShortComplex.cyclesMap φ |>.hom
      ((S.mapCyclesIso F).inv.hom c))) = linearHomComplexCocycle R K L n c :=
    Subtype.ext hi
  change CohomologyClass.homAddEquiv (CochainComplex.HomComplex.homologyAddEquiv K L n
    (linearHomComplexHomologyAddEquiv R K L n _)) = _
  have : CochainComplex.HomComplex.homologyAddEquiv K L n
      (linearHomComplexHomologyAddEquiv R K L n
        (((LinearHomComplex.complex R K L).homologyπ n).hom c)) =
      CohomologyClass.mk (linearHomComplexCocycle R K L n c) :=
    hc.trans (congrArg CohomologyClass.mk hcoc)
  rw [this]
  rfl

end LinearHomComplex

section FunctorCocycle

variable {C : Type*} [Category C] [Preadditive C] {D : Type*} [Category D] [Preadditive D]
  (Φ : C ⥤ D) [Φ.Additive]

/-- The image of a cocycle under an additive functor, applied termwise. -/
def cocycleMap {K L : CochainComplex C ℤ} {n : ℤ} (z : Cocycle K L n) :
    Cocycle ((Φ.mapHomologicalComplex _).obj K) ((Φ.mapHomologicalComplex _).obj L) n :=
  Cocycle.mk ((z : Cochain K L n).map Φ) (n + 1) rfl (by
    rw [δ_map, Cocycle.δ_eq_zero, Cochain.map_zero])

@[simp]
lemma cocycleMap_coe {K L : CochainComplex C ℤ} {n : ℤ} (z : Cocycle K L n) :
    (cocycleMap Φ z : Cochain _ _ n) = (z : Cochain K L n).map Φ :=
  rfl

/-- Applying an additive functor to the morphism `K ⟶ L⟦n⟧` of a cocycle gives, up to the
identification of the shifts, the morphism of the image cocycle. -/
lemma map_equivHomShift_symm {K L : CochainComplex C ℤ} {n : ℤ} (z : Cocycle K L n) :
    (Φ.mapHomologicalComplex _).map (Cocycle.equivHomShift.symm z) ≫
        ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app L =
      Cocycle.equivHomShift.symm (cocycleMap Φ z) := by
  ext p
  simp [Cocycle.equivHomShift_symm_apply,
    Cochain.rightShift_v _ _ _ _ p p (add_zero p) (p + n) rfl]

end FunctorCocycle

section LinearHomComplexDerived

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [HasDerivedCategory.{t} C]

/-- The map from the degree `n` cohomology of the module-valued Hom complex `Hom^•(K, L)` to
the morphisms `K ⟶ L⟦n⟧` in the derived category: the identification with morphisms in the
homotopy category followed by the localization functor `Qh`. -/
noncomputable def linearHomComplexHomologyToDerived (K L : CochainComplex C ℤ) (n : ℤ) :
    (LinearHomComplex.complex R K L).homology n →+ (Q.obj K ⟶ (Q.obj L)⟦n⟧) :=
  ((precompAddEquiv ((quotientCompQhIso C).app K).symm _).trans
      (postcompAddEquiv _ ((quotientCompQhIso C).app (L⟦n⟧) ≪≫
        (Q.commShiftIso n).app L))).toAddMonoidHom.comp
    (Qh.mapAddHom.comp (linearHomComplexHomologyHomotopyAddEquiv R K L n).toAddMonoidHom)

/-- The value of `linearHomComplexHomologyToDerived` on the class of a cycle `c`: the image
under `Q` of the morphism `K ⟶ L⟦n⟧` of the cocycle of `c`, followed by the shift isomorphism
of `Q`. -/
lemma linearHomComplexHomologyToDerived_homologyπ (K L : CochainComplex C ℤ) (n : ℤ)
    (c : (LinearHomComplex.complex R K L).cycles n) :
    linearHomComplexHomologyToDerived R K L n
        (((LinearHomComplex.complex R K L).homologyπ n).hom c) =
      Q.map (Cocycle.equivHomShift.symm (linearHomComplexCocycle R K L n c)) ≫
        (Q.commShiftIso n).hom.app L := by
  change (((quotientCompQhIso C).app K).symm.hom ≫
      Qh.map (linearHomComplexHomologyHomotopyAddEquiv R K L n
        (((LinearHomComplex.complex R K L).homologyπ n).hom c))) ≫
        ((quotientCompQhIso C).app (L⟦n⟧) ≪≫ (Q.commShiftIso n).app L).hom = _
  rw [linearHomComplexHomologyHomotopyAddEquiv_homologyπ, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Iso.app_hom, ← Category.assoc,
    Category.assoc _ _ ((quotientCompQhIso C).hom.app (L⟦n⟧))]
  erw [NatIso.naturality_1 (quotientCompQhIso C)]

end LinearHomComplexDerived

namespace DivisibleSystem

section DerivedEval

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{t} C]
  [HasDerivedCategory.{t'} (ℕᵒᵖ ⥤ C)]

/-- The image under `derivedEval` of a derived morphism coming from a chain map
`f : K ⟶ L⟦n⟧` is the image under `Q` of the chain map evaluated at level `m`. -/
lemma derivedEval_Q_map (K L : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) (n : ℤ) (m : ℕ) (f : K ⟶ L⟦n⟧) :
    derivedEval K L n m (Q.map f ≫ (Q.commShiftIso n).hom.app L) =
      Q.map ((((evaluation ℕᵒᵖ C).obj (op m)).mapHomologicalComplex _).map f ≫
        ((((evaluation ℕᵒᵖ C).obj (op m)).mapHomologicalComplex
          (ComplexShape.up ℤ)).commShiftIso n).hom.app L) ≫
        (Q.commShiftIso n).hom.app (evalComplex L m) := by
  set F := (evaluation ℕᵒᵖ C).obj (op m)
  have hnat := F.mapDerivedCategoryFactors.hom.naturality f
  have hshift := NatTrans.shift_app_comm F.mapDerivedCategoryFactors.hom n L
  simp only [Functor.comp_map, Functor.commShiftIso_comp_hom_app, Category.assoc] at hnat hshift
  simp only [derivedEval, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Functor.map_comp, Category.assoc]
  rw [hshift, reassoc_of% hnat, Iso.inv_hom_id_app_assoc]

end DerivedEval

section Comparison

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  {ℓ : ℕ} [HasDerivedCategory.{t} C] [HasDerivedCategory.{w'} (ℕᵒᵖ ⥤ C)]

omit [HasDerivedCategory.{t} C] in
/-- `homComplexLimitToDerived` is `linearHomComplexHomologyToDerived` for the complexes of
inverse systems, transported along the identification of their Hom complex with the inverse
limit of the Hom complexes `Hom^•(T m, W m)`. -/
lemma homComplexLimitToDerived_apply (T W : DivisibleSystem (CochainComplex C ℤ) ℓ) (n : ℤ)
    (x : (homComplexLimit R T W).homology n) :
    homComplexLimitToDerived R T W n x =
      linearHomComplexHomologyToDerived R (towerComplex T) (towerComplex W) n
        ((HomologicalComplex.homologyMap (towerHomComplexIsoLimit R T W).inv n).hom x) :=
  rfl

/-- The finite-level compatibility of the comparison map: evaluating at level `m` the derived
morphism attached to a class of the inverse limit of the Hom complexes gives the derived
morphism attached to its image in the cohomology of `Hom^•(T m, W m)`. -/
theorem derivedEval_homComplexLimitToDerived (T W : DivisibleSystem (CochainComplex C ℤ) ℓ)
    (n : ℤ) (m : ℕ) (x : (homComplexLimit R T W).homology n) :
    derivedEval (towerComplex T) (towerComplex W) n m (homComplexLimitToDerived R T W n x) =
      linearHomComplexHomologyToDerived R (T.obj m) (W.obj m) n
        ((HomologicalComplex.homologyMap (limit.π (homComplexSystem R T W) (op m)) n).hom x) := by
  have hx : x = (HomologicalComplex.homologyMap (towerHomComplexIsoLimit R T W).hom n).hom
      ((HomologicalComplex.homologyMap (towerHomComplexIsoLimit R T W).inv n).hom x) := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp,
      Iso.inv_hom_id, HomologicalComplex.homologyMap_id]
    rfl
  rw [homComplexLimitToDerived_apply]
  conv_rhs => rw [hx]
  generalize (HomologicalComplex.homologyMap (towerHomComplexIsoLimit R T W).inv n).hom x = y
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp,
    towerHomComplexIsoLimit_hom_π]
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective _).1
    (inferInstance : Epi ((LinearHomComplex.complex R (towerComplex T)
      (towerComplex W)).homologyπ n)) y
  change _ = linearHomComplexHomologyToDerived R (T.obj m) (W.obj m) n
    ((HomologicalComplex.homologyMap (towerHomComplexEval R T W m) n).hom
      (((LinearHomComplex.complex R (towerComplex T) (towerComplex W)).homologyπ n).hom c))
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.homologyπ_naturality,
    ModuleCat.hom_comp, LinearMap.comp_apply, linearHomComplexHomologyToDerived_homologyπ,
    linearHomComplexHomologyToDerived_homologyπ, derivedEval_Q_map, map_equivHomShift_symm]
  have hcoc : cocycleMap ((evaluation ℕᵒᵖ C).obj (op m))
      (linearHomComplexCocycle R (towerComplex T) (towerComplex W) n c) =
      linearHomComplexCocycle R (T.obj m) (W.obj m) n
        ((HomologicalComplex.cyclesMap (towerHomComplexEval R T W m) n).hom c) := by
    apply Cocycle.ext
    rw [cocycleMap_coe, linearHomComplexCocycle_coe, linearHomComplexCocycle_coe,
      ← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.cyclesMap_i,
      ModuleCat.hom_comp, LinearMap.comp_apply, towerHomComplexEval_f_apply]
    ext p q hpq
    simp only [Cochain.map_v, evaluation_obj_map]
    exact (towerCochainEval_v T W _ m p q hpq).symm
  rw [hcoc]
  rfl

/-- The comparison map from the cohomology of the inverse limit of the Hom complexes to the
compatible families of levelwise derived morphisms: `homComplexLimitToDerived` followed by
`derivedToCompatible`. -/
noncomputable def homComplexLimitToCompatible (T W : DivisibleSystem (CochainComplex C ℤ) ℓ)
    (n : ℤ) :
    (homComplexLimit R T W).homology n →+ compatibleDerived (towerComplex T) (towerComplex W) n :=
  (derivedToCompatible (towerComplex T) (towerComplex W) n).comp
    (homComplexLimitToDerived R T W n)

/-- The level `m` component of `homComplexLimitToCompatible` is the derived morphism attached
to the image of the class in the cohomology of `Hom^•(T m, W m)`. -/
lemma homComplexLimitToCompatible_apply_coe (T W : DivisibleSystem (CochainComplex C ℤ) ℓ)
    (n : ℤ) (x : (homComplexLimit R T W).homology n) (m : ℕ) :
    (homComplexLimitToCompatible R T W n x).1 m =
      linearHomComplexHomologyToDerived R (T.obj m) (W.obj m) n
        ((HomologicalComplex.homologyMap (limit.π (homComplexSystem R T W) (op m)) n).hom x) :=
  derivedEval_homComplexLimitToDerived R T W n m x

end Comparison

end DivisibleSystem

end Langlands.Cohomology
