import Langlands.Cohomology.DivisibleSystem.TowerComplex
import Langlands.Cohomology.HyperextSecondPage

/-!
# The `ℓ`-adic hyperext spectral sequence of an `ℓ`-divisible system of complexes

Let `T` be an `ℓ`-divisible system of cochain complexes in an abelian category `C` and let
`towerComplex T` be the corresponding cochain complex in the abelian category `ℕᵒᵖ ⥤ C` of
inverse systems (`Langlands.Cohomology.DivisibleSystem.TowerComplex`). Assuming that
`ℕᵒᵖ ⥤ C` has a derived category, this module applies the Library's hyperext spectral sequence
for the standard t-structure to the image of `towerComplex T` in that derived category and to an
inverse system `W` placed in degree `0`.

* `adicHyperextSpectralSequence T W` is this spectral sequence. Its object in position `(p, q)`
  on page 2 is `Ext^p(m ↦ H^{-q}(T m), W)` for `p ≥ 0`, the Ext group being computed in
  `ℕᵒᵖ ⥤ C` (`adicHyperextSecondPageIso`), and zero for `p < 0`
  (`isZero_adicHyperextSecondPage_of_neg`). Its intended abutment in total degree `n` is the
  group of morphisms from `towerComplex T` to `W⟦n⟧` in the derived category
  (`adicHyperextAbutmentIso`). Convergence is not proved.
* `towerComplexSingleZeroIso W` identifies `towerComplex` of the system `m ↦ W m` placed in
  degree `0` (`singleZero W`) with the inverse system `W.tower` placed in degree `0`.
* `adicHyperextComparison R T W n` is an additive map from the degree `n` cohomology of the
  inverse limit `homComplexLimit R T (singleZero W)` of the Hom complexes `Hom^•(T m, W m)` to the
  abutment `Hom(towerComplex T, W.tower⟦n⟧)`: the identification of that cohomology with morphisms
  in the homotopy category (`homComplexLimitHomologyAddEquiv`) followed by the localization
  functor to the derived category. It is not claimed to be bijective.
* `smoothAdicHyperextSpectralSequence` is the spectral sequence for systems of complexes of
  smooth representations.

This is our formulation of the shape of Harris's integral statement (4.10.4) (Harris 1999, end
of the proof of Proposition 4.10, printed p.312): the integral Ext groups there are read as Ext
groups in the category of inverse systems. Harris's complexes are not constructed here.
-/

noncomputable section

namespace Langlands.Cohomology

namespace DivisibleSystem

open CategoryTheory CategoryTheory.Limits Opposite DerivedCategory
open HyperextSpectralSequence

universe w' w v u

section Single

variable {C : Type u} [Category.{v} C] [Abelian C] {ℓ : ℕ}

/-- The `ℓ`-divisible system of complexes `m ↦ W m` concentrated in degree `0`. -/
abbrev singleZero (W : DivisibleSystem C ℓ) : DivisibleSystem (CochainComplex C ℤ) ℓ :=
  W.map (HomologicalComplex.single C (ComplexShape.up ℤ) 0)

/-- The terms of `towerComplex W.singleZero` in degrees `p ≠ 0` are zero. -/
lemma isZero_towerComplex_singleZero_X (W : DivisibleSystem C ℓ) (p : ℤ) (hp : p ≠ 0) :
    IsZero ((towerComplex W.singleZero).X p) :=
  Functor.isZero _ (fun _ => HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) _ _ _ hp)

/-- The degree `0` term of `towerComplex W.singleZero` is the inverse system `W.tower`. -/
def towerComplexSingleZeroXIso (W : DivisibleSystem C ℓ) :
    (towerComplex W.singleZero).X 0 ≅ W.tower :=
  Functor.isoWhiskerLeft W.tower
    (HomologicalComplex.singleCompEvalIsoSelf C (ComplexShape.up ℤ) 0) ≪≫ W.tower.rightUnitor

/-- The complex of inverse systems of `W.singleZero` is the inverse system `W.tower` placed in
degree `0`. -/
def towerComplexSingleZeroIso (W : DivisibleSystem C ℓ) :
    towerComplex W.singleZero ≅
      (HomologicalComplex.single (ℕᵒᵖ ⥤ C) (ComplexShape.up ℤ) 0).obj W.tower where
  hom := HomologicalComplex.mkHomToSingle (towerComplexSingleZeroXIso W).hom (fun i hi =>
    (isZero_towerComplex_singleZero_X W i (by rintro rfl; simp at hi)).eq_of_src _ _)
  inv := HomologicalComplex.mkHomFromSingle (towerComplexSingleZeroXIso W).inv (fun k hk =>
    (isZero_towerComplex_singleZero_X W k (by rintro rfl; simp at hk)).eq_of_tgt _ _)
  hom_inv_id := by
    ext p : 1
    by_cases hp : p = 0
    · subst hp
      simp [HomologicalComplex.mkHomToSingle_f, HomologicalComplex.mkHomFromSingle_f]
    · exact (isZero_towerComplex_singleZero_X W p hp).eq_of_src _ _
  inv_hom_id := by
    apply HomologicalComplex.from_single_hom_ext
    simp [HomologicalComplex.mkHomToSingle_f, HomologicalComplex.mkHomFromSingle_f]

end Single

section Derived

variable {C : Type u} [Category.{v} C] [Abelian C] {ℓ : ℕ} [HasDerivedCategory.{w'} (ℕᵒᵖ ⥤ C)]

/-- The cohomology in degree `q` of the image of `towerComplex T` in the derived category of
inverse systems is the inverse system `m ↦ H^q(T m)`. -/
def towerDerivedHomologyIso (T : DivisibleSystem (CochainComplex C ℤ) ℓ) (q : ℤ) :
    (homologyFunctor (ℕᵒᵖ ⥤ C) q).obj (Q.obj (towerComplex T)) ≅
      T.tower ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q :=
  (homologyFunctorFactors (ℕᵒᵖ ⥤ C) q).app (towerComplex T) ≪≫
    (towerComplexHomologyIso T q).symm

/-- The image of `towerComplex W.singleZero` in the derived category of inverse systems is
`W.tower` placed in degree `0`. -/
def towerDerivedSingleZeroIso (W : DivisibleSystem C ℓ) :
    Q.obj (towerComplex W.singleZero) ≅ (singleFunctor (ℕᵒᵖ ⥤ C) 0).obj W.tower :=
  Q.mapIso (towerComplexSingleZeroIso W)

/-- The `ℓ`-adic hyperext spectral sequence of an `ℓ`-divisible system `T` of cochain complexes
and an inverse system `W`: the Library's hyperext spectral sequence for the standard t-structure
on the derived category of inverse systems `ℕᵒᵖ ⥤ C`, applied to the image of
`towerComplex T` and to `W` placed in degree `0`. -/
def adicHyperextSpectralSequence (T : DivisibleSystem (CochainComplex C ℤ) ℓ) (W : ℕᵒᵖ ⥤ C) :
    E₂CohomologicalSpectralSequence AddCommGrpCat.{w'} :=
  hyperextSpectralSequence TStructure.t (Q.obj (towerComplex T))
    ((singleFunctor (ℕᵒᵖ ⥤ C) 0).obj W)

/-- The object in position `(p, q)`, `p : ℕ`, on page 2 of the `ℓ`-adic hyperext spectral
sequence is `Ext^p(m ↦ H^{-q}(T m), W)`, computed in the category of inverse systems. -/
def adicHyperextSecondPageIso [HasExt.{w'} (ℕᵒᵖ ⥤ C)]
    (T : DivisibleSystem (CochainComplex C ℤ) ℓ) (W : ℕᵒᵖ ⥤ C) (p : ℕ) (q : ℤ) :
    ((adicHyperextSpectralSequence T W).page 2).X ⟨p, q⟩ ≅
      AddCommGrpCat.of (Abelian.Ext.{w'}
        (T.tower ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (-q)) W p) :=
  secondPageExtIso (Q.obj (towerComplex T)) W p q ≪≫
    ((Abelian.extFunctor.{w'} p).mapIso (towerDerivedHomologyIso T (-q)).symm.op).app W

/-- The objects in positions `(p, q)` with `p < 0` on page 2 of the `ℓ`-adic hyperext spectral
sequence are zero. -/
lemma isZero_adicHyperextSecondPage_of_neg (T : DivisibleSystem (CochainComplex C ℤ) ℓ)
    (W : ℕᵒᵖ ⥤ C) (p q : ℤ) (hp : p < 0) :
    IsZero (((adicHyperextSpectralSequence T W).page 2).X ⟨p, q⟩) :=
  isZero_secondPage_of_neg (Q.obj (towerComplex T)) W p q hp

/-- The term in total degree `n` of the spectral object underlying the `ℓ`-adic hyperext
spectral sequence is `Hom(T, W⟦n⟧)` in the derived category of inverse systems: the intended
abutment. Convergence is not proved. -/
def adicHyperextAbutmentIso (T : DivisibleSystem (CochainComplex C ℤ) ℓ) (W : ℕᵒᵖ ⥤ C) (n : ℤ) :
    ((hyperextSpectralObject TStructure.t (Q.obj (towerComplex T))
        ((singleFunctor (ℕᵒᵖ ⥤ C) 0).obj W)).H n).obj
      (ComposableArrows.mk₁ (homOfLE (show (⊥ : EInt) ≤ ⊤ from bot_le))) ≅
      AddCommGrpCat.of (Q.obj (towerComplex T) ⟶ ((singleFunctor (ℕᵒᵖ ⥤ C) 0).obj W)⟦n⟧) :=
  abutmentIso TStructure.t _ _ n

end Derived

section Comparison

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  {ℓ : ℕ} [HasDerivedCategory.{w'} (ℕᵒᵖ ⥤ C)]

/-- The map from the degree `n` cohomology of the inverse limit `homComplexLimit R T W` of the Hom
complexes to the group of morphisms `towerComplex T ⟶ (towerComplex W)⟦n⟧` in the derived
category of inverse systems: the isomorphism with morphisms in the homotopy category
(`homComplexLimitHomologyAddEquiv`) followed by the localization functor `Qh`. -/
def homComplexLimitToDerived (T W : DivisibleSystem (CochainComplex C ℤ) ℓ) (n : ℤ) :
    (homComplexLimit R T W).homology n →+
      (Q.obj (towerComplex T) ⟶ (Q.obj (towerComplex W))⟦n⟧) :=
  ((precompAddEquiv ((quotientCompQhIso (ℕᵒᵖ ⥤ C)).app (towerComplex T)).symm _).trans
      (postcompAddEquiv _ ((quotientCompQhIso (ℕᵒᵖ ⥤ C)).app ((towerComplex W)⟦n⟧) ≪≫
        (Q.commShiftIso n).app (towerComplex W)))).toAddMonoidHom.comp
    (Qh.mapAddHom.comp (homComplexLimitHomologyAddEquiv R T W n).toAddMonoidHom)

/-- The comparison map from the degree `n` cohomology of the inverse limit of the Hom complexes
`Hom^•(T m, W m)`, `W` placed in degree `0`, to the abutment `Hom(T, W⟦n⟧)` of the `ℓ`-adic
hyperext spectral sequence (`adicHyperextAbutmentIso`). It is not claimed to be bijective. -/
def adicHyperextComparison (T : DivisibleSystem (CochainComplex C ℤ) ℓ) (W : DivisibleSystem C ℓ)
    (n : ℤ) :
    (homComplexLimit R T W.singleZero).homology n →+
      (Q.obj (towerComplex T) ⟶ ((singleFunctor (ℕᵒᵖ ⥤ C) 0).obj W.tower)⟦n⟧) :=
  (postcompAddEquiv _ ((shiftFunctor (DerivedCategory (ℕᵒᵖ ⥤ C)) n).mapIso
    (towerDerivedSingleZeroIso W))).toAddMonoidHom.comp
    (homComplexLimitToDerived R T W.singleZero n)

end Comparison

end DivisibleSystem

section Smooth

open CategoryTheory

variable {R : Type u} [CommRing R] {G : Type v} [Group G] [TopologicalSpace G] {ℓ : ℕ}
  [HasDerivedCategory.{w'} (ℕᵒᵖ ⥤ SmoothRep.{u, v, w} R G)]

/-- The `ℓ`-adic hyperext spectral sequence of an `ℓ`-divisible system `T` of cochain complexes
of smooth representations and an inverse system `W` of smooth representations, in the derived
category of inverse systems `ℕᵒᵖ ⥤ SmoothRep R G`. -/
abbrev smoothAdicHyperextSpectralSequence (T : SmoothRepComplexDivisibleSystem.{v, u, w} R G ℓ)
    (W : ℕᵒᵖ ⥤ SmoothRep.{u, v, w} R G) :
    E₂CohomologicalSpectralSequence AddCommGrpCat.{w'} :=
  DivisibleSystem.adicHyperextSpectralSequence T W

end Smooth

end Langlands.Cohomology
