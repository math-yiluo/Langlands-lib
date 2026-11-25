/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictCompletionRestrictionData
import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictSectionQuotientTensorModels
import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictSectionQuotientConeMaps
import all WeilConjectures.CategoryTheory.RoosConeCalculus.RoosConeCalculus
import all WeilConjectures.Algebra.Homology.KFlatRoos.KFlatRoosRepresentativeInvariance
import all Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.Algebra.Homology.RoosCoordinatesQuasiIso
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi

/-! # Principal quotient tensor models for strict section cones -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a b w
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures
open scoped CategoryTheory.Obj
open CategoryTheory.InternalAbelianSheafModule
open AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison

-- Upstream's `HasDerivedCategory` instances on these module categories are found first and then
-- fail the final defeq check, which blocks `HasDerivedCategory.ofIsGrothendieckAbelian`.
attribute [-instance] AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
  AlgebraicGeometry.Scheme.ProjectionRestriction.derived
  AlgebraicGeometry.Scheme.ProjectionRestriction.derivedOver
  AlgebraicGeometry.Scheme.ProjectionRestriction.derivedOverModules

namespace AlgebraicGeometry.ProEtale.StrictCompletionRestriction
section RoosCoordinates
variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
open CategoryTheory.RoosConeCalculus

@[irreducible] private def signedCoordinates (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (i : ℤ) :
    (roosF.obj N).X i ≅ (roosP N).X i ⊞ (roosP N).X (i - 1) where
  hom := biprod.lift (v N i) (-ucoord N i (i - 1) rfl)
  inv := fibrePair N i (i - 1) rfl biprod.fst (-biprod.snd)
  hom_inv_id := by
    apply roos_ext i <;> simp [Category.assoc, fibrePair_v, fibrePair_u]
  inv_hom_id := by
    apply biprod.hom_ext <;> simp [Category.assoc, fibrePair_v, fibrePair_u]

private theorem signedCoordinates_d (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (i : ℤ) :
    (roosF.obj N).d i (i + 1) ≫ (signedCoordinates N (i + 1)).hom =
      (signedCoordinates N i).hom ≫
        biprod.lift (biprod.fst ≫ (roosP N).d i (i + 1))
          (biprod.fst ≫ (roosU N).f i ≫
            eqToHom (congrArg (roosP N).X (Int.add_sub_cancel i 1).symm) -
            biprod.snd ≫ (roosP N).d (i - 1) ((i + 1) - 1)) := by
  apply biprod.hom_ext
  · simpa only [signedCoordinates, Category.assoc, biprod.lift_fst,
      biprod.lift_fst_assoc] using (differential_coordinates N i).1
  · have h := congrArg (fun f ↦ f ≫
        eqToHom (congrArg (roosP N).X (Int.add_sub_cancel i 1).symm))
        (congrArg Neg.neg (differential_coordinates N i).2)
    have hu (j k : ℤ) (hj : i + 1 - 1 = j) (hk : i + 1 - 1 = k)
        (hjk : j = k) :
        ucoord N (i + 1) j hj ≫ eqToHom (congrArg (roosP N).X hjk) =
          ucoord N (i + 1) k hk := by
      cases hjk
      exact Category.comp_id (ucoord N (i + 1) j hj)
    have hd : (roosP N).d (i - 1) i ≫
        eqToHom (congrArg (roosP N).X (Int.add_sub_cancel i 1).symm) =
          (roosP N).d (i - 1) (i + 1 - 1) := by
      exact (roosP N).d_comp_eqToHom
        (by change i - 1 + 1 = i + 1 - 1; omega)
        (by change i - 1 + 1 = i; omega)
    simp only [signedCoordinates, Category.assoc, biprod.lift_snd,
      biprod.lift_fst_assoc, biprod.lift_snd_assoc, Preadditive.comp_sub,
      Preadditive.comp_neg, Preadditive.neg_comp]
    simpa only [Preadditive.neg_comp, Preadditive.sub_comp, Preadditive.add_comp, neg_sub, neg_neg,
      sub_neg_eq_add, Category.assoc, hu, hu i (i + 1 - 1) (by omega) rfl
        (Int.add_sub_cancel i 1).symm, hd, add_comm] using h

@[irreducible] private def coordinatesMap (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (V' L' : CochainComplex A ℤ) (s' : V' ⟶ V')
    (e' : ∀ i : ℤ, L'.X i ≅ V'.X i ⊞ V'.X (i - 1))
    (hd' : ∀ i : ℤ, L'.d i (i + 1) ≫ (e' (i + 1)).hom =
      (e' i).hom ≫ biprod.lift (biprod.fst ≫ V'.d i (i + 1))
        (biprod.fst ≫ s'.f i ≫
          eqToHom (congrArg V'.X (Int.add_sub_cancel i 1).symm) -
          biprod.snd ≫ V'.d (i - 1) ((i + 1) - 1)))
    (p : roosP N ⟶ V') (hs : roosU N ≫ p = p ≫ s') : roosF.obj N ⟶ L' :=
  CochainComplex.ofHom (fun i ↦ (signedCoordinates N i).hom ≫
    biprod.map (p.f i) (p.f (i - 1)) ≫ (e' i).inv) (by
      intro i
      apply (cancel_mono (e' (i + 1)).hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [hd', Iso.inv_hom_id_assoc]
      rw [← Category.assoc ((roosF.obj N).d i (i + 1)), signedCoordinates_d]
      simp only [Category.assoc]
      apply biprod.hom_ext
      · simp only [Category.assoc, biprod.map_fst_assoc, biprod.lift_fst,
          biprod.lift_fst_assoc, biprod.map_fst, p.comm]
      · have hi (j : ℤ) := congrArg (fun f ↦ f.f j) hs
        simp only [HomologicalComplex.comp_f] at hi
        simp only [Category.assoc, Preadditive.comp_sub, Preadditive.sub_comp,
          biprod.map_fst_assoc, biprod.map_snd_assoc, biprod.lift_snd,
          biprod.lift_snd_assoc, biprod.map_snd, HomologicalComplex.Hom.comm,
          Category.assoc]
        rw [← eqToHom_naturality (fun j ↦ p.f j) (Int.add_sub_cancel i 1).symm]
        rw [← Category.assoc ((roosU N).f i), hi i]
        simp only [Category.assoc])

private theorem coordinatesMap_f (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (V' L' : CochainComplex A ℤ) (s' : V' ⟶ V')
    (e' : ∀ i : ℤ, L'.X i ≅ V'.X i ⊞ V'.X (i - 1))
    (hd' : ∀ i : ℤ, L'.d i (i + 1) ≫ (e' (i + 1)).hom =
      (e' i).hom ≫ biprod.lift (biprod.fst ≫ V'.d i (i + 1))
        (biprod.fst ≫ s'.f i ≫
          eqToHom (congrArg V'.X (Int.add_sub_cancel i 1).symm) -
          biprod.snd ≫ V'.d (i - 1) ((i + 1) - 1)))
    (p : roosP N ⟶ V') (hs : roosU N ≫ p = p ≫ s') (i : ℤ) :
    (coordinatesMap N V' L' s' e' hd' p hs).f i ≫ (e' i).hom =
      (signedCoordinates N i).hom ≫ biprod.map (p.f i) (p.f (i - 1)) := by
  simp only [coordinatesMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem signedAugmentation (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (P : CochainComplex A ℤ) (a : P ⟶ roosF.obj N)
    (ha : ∀ j : ℤ, a.f (j + 1) ≫ (roosχ N j).hom ≫ biprod.fst = 0)
    (V' : CochainComplex A ℤ) (p : roosP N ⟶ V') (i : ℤ) :
    a.f i ≫ (signedCoordinates N i).hom ≫ biprod.map (p.f i) (p.f (i - 1)) =
      biprod.lift ((a ≫ roosProj N ≫ p).f i) 0 := by
  apply biprod.hom_ext
  · simp only [signedCoordinates, Category.assoc, biprod.map_fst,
      biprod.lift_fst, biprod.lift_fst_assoc, v, HomologicalComplex.comp_f]
  · simp only [signedCoordinates, Category.assoc, biprod.map_snd,
      biprod.lift_snd, biprod.lift_snd_assoc, Preadditive.comp_neg,
      Preadditive.neg_comp]
    have ht : ∀ j (hj : j + 1 = i),
        a.f i ≫ ucoord N i j (by omega) = 0 := by
      intro j hj
      subst i
      simpa only [ucoord_χ, Category.assoc] using ha j
    rw [← Category.assoc, ht (i - 1) (by omega)]
    simp

end RoosCoordinates

private theorem completionComparison {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableProducts A] [HasDerivedCategory.{w} A] (T : Presentation.{a, b, w} A)
    (P Z : CochainComplex A ℤ) (q : roosF.obj (T.tower.obj P) ⟶ Z)
    (hq : QuasiIso q) (a : P ⟶ Z) (hu : T.augmentation.app P ≫ q = a)
    (K : DerivedCategory.{w} A) (e : DerivedCategory.Q.obj P ≅ K) :
    ∃ ψ : T.completion.obj K ≅ DerivedCategory.Q.obj Z,
      T.unit.app K ≫ ψ.hom = e.inv ≫ DerivedCategory.Q.map a := by
  have : QuasiIso q := hq
  let c := T.descent.app P ≪≫ asIso (DerivedCategory.Q.map q)
  refine ⟨(T.completion.mapIso e).symm ≪≫ c, ?_⟩
  change T.unit.app K ≫ (T.completion.map e.inv ≫
    ((T.descent.app P).hom ≫ DerivedCategory.Q.map q)) = _
  rw [← Category.assoc, ← T.unit.naturality e.inv]
  simp only [Functor.id_map, Category.assoc]
  have hd : T.unit.app (DerivedCategory.Q.obj P) ≫ (T.descent.app P).hom =
      DerivedCategory.Q.map (T.augmentation.app P) := T.unit_descent P
  rw [← Category.assoc (T.unit.app (DerivedCategory.Q.obj P)), hd]
  rw [← Functor.map_comp, hu]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The scalar-cone presentation computes the actual principal quotient tensors,
with their normalized tensor models and augmented Roos completion.

Source: blueprint latest, derived-nakayama-first-reduction proof, Cones paragraph;
Locality in integral-ctf-equals-bc; Stacks Tags 03EK, 06YS, 06YT and 08TC
(blueprint: lem-sfb-strict-section-principal-quotient-models).

Proof:
The canonical datum identifies d with multiplication by the chosen uniformizer.
The point resolution 0 to A, multiplication by pi^(n+1), A to A/pi^(n+1) to 0
is short exact. Exact point pullback and the exact section-action equivalence give
the same short exact resolution of the section quotient module. Its scalar is
precisely the given section multiplication, by evaluation at one. The actual
quotient ring sheaves and their sectionScalarMap transitions form B and its algebra
map from the constant ring tower; quotient-transition compatibility follows from
the quotient homomorphisms.

Tensor this two-term resolution with an arbitrary K-flat complex. Tensoring a
quasi-isomorphism with that K-flat complex is a quasi-isomorphism, even when the
quotient is nonflat and the complex is unbounded. The single-degree-zero total
comparison has only the (p,0) summand and sends x tensor y to the same local pure
tensor. The cone-to-tensor map therefore identifies each strict level with the
actual KFlatRoos.level. The two maps on the free coefficient resolution for a
successor transition are identity and multiplication by pi. Hence the cone maps
commute with all transitions, and the cone inclusion maps to x tensor 1.

Fix the supplied section derived tensor structure and its TensorComparison.
Resolve the quotient in the second variable by a K-flat Q. The comparison from
its total tensor to the singleton quotient total, followed by the preceding level
map, is a quasi-isomorphism. Its inverse after localization gives model. The
universal derived tensor comparison gives tensor; naturality of the same map gives
tensor_model exactly, with no twist. Localization of the cone inclusion and the
successor squares proves the unit and step fields.

The level quasi-isomorphisms form an augmented tower map. Exact countable products
on the small pro-etale site and the Roos cone lemma make its Roos map a
quasi-isomorphism. The two Roos coordinates and the level unit equations identify
its augmentation with the actual tensor-Roos augmentation. The presentation descent
then gives the displayed completion isomorphism for Q(P); transport it along e to
arbitrary K. Naturality of its unit gives e.inv followed by that augmentation.
The argument includes the zero quotient, empty site and every positive exponent. -/
theorem strictSectionPrincipalQuotientModels (X : Scheme.{u})
    (T : Presentation.{u + 2, u + 1, u + 1}
      (Modules (DerivedNakayama.integerRing l E) X))
    (data : PrincipalReduction.PrincipalReductionConeData l E X)
    (hdata : data.IsCanonical l E X)
    (hscalar : ∀ (M : Modules (DerivedNakayama.integerRing l E) X) (U : X.ProEtᵒᵖ)
      (x : M.val.obj U),
      (T.scalar.asHom.app M).val.app U x = sectionScalarValue l E X data.d U • x)
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (ι : (Functor.const ℕᵒᵖ).obj (ring (DerivedNakayama.integerRing l E) X) ⟶ B)
    (hB : ∀ n : ℕ, B.obj (op n) = sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
        (AdicCompletion.finiteRing l E X n))
    (hι : ∀ n : ℕ, HEq (ι.app (op n))
        (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
          (AdicCompletion.quotient l E X n)))
    (hstep : ∀ n : ℕ, HEq (B.map (homOfLE (Nat.le_succ n)).op)
        (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
          (AdicCompletion.transition l E X n)))
    (H : CoefficientClosedStructure (hom (DerivedNakayama.integerRing l E) X))
    (HM : CoefficientTensorModels.{u, u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (ring (DerivedNakayama.integerRing l E) X) H)
    (t : TensorComparison (DerivedNakayama.integerRing l E) X H HM) :
      Nonempty (SectionReductionModels l E X T H HM B ι) ∧
      ∀ (K : DerivedCategory (Modules (DerivedNakayama.integerRing l E) X))
        (P : CochainComplex (Modules (DerivedNakayama.integerRing l E) X) ℤ)
        (_hP : CochainComplex.IsKFlatIndependentCoefficients
          (R := ring (DerivedNakayama.integerRing l E) X) P)
        (e : DerivedCategory.Q.obj P ≅ K),
        ∃ ψ : T.completion.obj K ≅
            DerivedCategory.Q.obj (SheafOfModules.KFlatRoos.roos.{u + 1, u, u + 1} B ι P),
          T.unit.app K ≫ ψ.hom = e.inv ≫
            DerivedCategory.Q.map
              (SheafOfModules.KFlatRoos.augmentation.{u + 1, u, u + 1} B ι P) := by
  obtain ⟨models⟩ := strictSectionQuotientTensorModels l E X T data
    hdata hscalar B ι hB hι hstep H HM t
  refine ⟨⟨models⟩, ?_⟩
  intro K P hP e
  obtain ⟨c, hc, hcoord⟩ := strictSectionQuotientConeMaps l E X T data
    hdata hscalar B ι hB hι P hP
  have hstepc (n : ℕ) :
      (T.tower.obj P).asFunctor.map (homOfLE (Nat.le_succ n)).op ≫ c n =
        c (n + 1) ≫ SheafOfModules.KFlatRoos.transition.{u + 1, u, u + 1} B ι P n := by
    ext i : 1
    have ht := congrArg (fun f ↦ f ≫ (biprod.fst : P.X i ⊞ P.X (i + 1) ⟶ P.X i) ≫
      (SheafOfModules.KFlatRoos.tensorUnit.{u + 1, u, u + 1} (ι.app (op n))).app (P.X i))
      (T.transition P n i)
    simp only [Category.assoc] at ht
    erw [biprod.map_fst_assoc, Category.id_comp] at ht
    have h := congrArg (fun η ↦ η.app (P.X i))
      (SheafOfModules.KFlatRoos.tensorUnit_levelMap.{u + 1, u, u + 1} B ι n)
    simpa +instances only [HomologicalComplex.comp_f, hcoord,
      SheafOfModules.KFlatRoos.transition, NatTrans.mapHomologicalComplex_app_f,
      Category.assoc, NatTrans.comp_app, ← h] using ht
  have hunitc (n : ℕ) :
      T.augmentation.app P ≫ roosEval (T.tower.obj P) n ≫ c n =
        (NatTrans.mapHomologicalComplex
            (SheafOfModules.KFlatRoos.tensorUnit.{u + 1, u, u + 1}
              (ι.app (op n))) (.up ℤ)).app P := by
    ext i : 1
    obtain ⟨j, hj⟩ := (Equiv.addRight (1 : ℤ)).surjective i
    change j + 1 = i at hj
    subst i
    simp only [HomologicalComplex.comp_f, hcoord, roosEval_f, Category.assoc]
    rw [reassoc_of% (T.augmentation_level P n j)]
    simp
  let p : roosP (T.tower.obj P) ⟶ SheafOfModules.KFlatRoos.product.{u + 1, u, u + 1} B ι P :=
    Limits.Pi.map c
  have hp : QuasiIso p := by
    let : CountableAB4Star (AdicCompletion.Modules l E X) :=
      .of_epi_π_app_zero (Mod.epiπAppZeroOfEpi
        AlgebraicGeometry.Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat)
    let : HasExactLimitsOfShape (Discrete ℕ)
        (Modules (DerivedNakayama.integerRing l E) X) :=
      HasExactLimitsOfShape.of_codomain_equivalence (Discrete ℕ)
        (ModuleObjectRingedComparison.equivalence (DerivedNakayama.integerRing l E) X)
    let f := Discrete.natTrans
      (F := Discrete.functor (fun n : ℕ ↦ (T.tower.obj P).asFunctor.obj (op n)))
      (G := Discrete.functor (fun n : ℕ ↦
        (SheafOfModules.KFlatRoos.level.{u + 1, u, u + 1} B ι n).obj P)) (fun n ↦ c n.as)
    have (n : Discrete ℕ) : QuasiIso (f.app n) := hc n.as
    exact HomologicalComplex.quasiIso_limMap f
  have hs : roosU (T.tower.obj P) ≫ p =
      p ≫ SheafOfModules.KFlatRoos.oneSubShift.{u + 1, u, u + 1} B ι P := by
    have ht : SheafOfModules.KFlatRoos.oneSubShift.{u + 1, u, u + 1} B ι P =
        towerTransitionEndomorphism
          (fun n ↦ SheafOfModules.KFlatRoos.transition.{u + 1, u, u + 1} B ι P n) := by
      apply Pi.hom_ext
      intro n
      simp only [SheafOfModules.KFlatRoos.oneSubShift, towerTransitionEndomorphism,
        towerProductShift, Preadditive.sub_comp, Pi.lift_comp_π]
      erw [Category.id_comp]
    rw [ht]
    exact (towerTransitionEndomorphism_natural_backward _ _ c
      (fun n ↦ (hstepc n).symm)).symm
  let V := SheafOfModules.KFlatRoos.product.{u + 1, u, u + 1} B ι P
  let L := SheafOfModules.KFlatRoos.roos.{u + 1, u, u + 1} B ι P
  let S := SheafOfModules.KFlatRoos.oneSubShift.{u + 1, u, u + 1} B ι P
  let eL (i : ℤ) : L.X i ≅ V.X i ⊞ V.X (i - 1) := Iso.refl _
  have hdL (i : ℤ) : L.d i (i + 1) ≫ (eL (i + 1)).hom =
      (eL i).hom ≫ biprod.lift (biprod.fst ≫ V.d i (i + 1))
        (biprod.fst ≫ S.f i ≫ eqToHom (congrArg V.X (Int.add_sub_cancel i 1).symm) -
          biprod.snd ≫ V.d (i - 1) ((i + 1) - 1)) := by
    simp only [eL, Iso.refl_hom, Category.comp_id, Category.id_comp]
    simp only [L, SheafOfModules.KFlatRoos.roos, CochainComplex.of_d,
      SheafOfModules.KFlatRoos.roosD, V, S]
  let q : roosF.obj (T.tower.obj P) ⟶ L :=
    coordinatesMap (T.tower.obj P) V L S eL hdL p hs
  have hqf (i : ℤ) : q.f i = (signedCoordinates (T.tower.obj P) i).hom ≫
      biprod.map (p.f i) (p.f (i - 1)) := by
    have h := coordinatesMap_f (T.tower.obj P) V L S eL hdL p hs i
    change q.f i ≫ 𝟙 _ = _ at h
    exact (Category.comp_id _).symm.trans h
  have hq : QuasiIso q := by
    exact CochainComplex.quasiIso_of_roos_coordinates (roosP (T.tower.obj P)) V
      (roosF.obj (T.tower.obj P)) L (roosU (T.tower.obj P)) S
      (signedCoordinates (T.tower.obj P)) eL
      (signedCoordinates_d (T.tower.obj P)) hdL p q
      (coordinatesMap_f (T.tower.obj P) V L S eL hdL p hs) hp
  have hu : T.augmentation.app P ≫ q =
      SheafOfModules.KFlatRoos.augmentation.{u + 1, u, u + 1} B ι P := by
    have hup : T.augmentation.app P ≫ roosProj (T.tower.obj P) ≫ p =
        SheafOfModules.KFlatRoos.unitProduct.{u + 1, u, u + 1} B ι P := by
      apply Pi.hom_ext
      intro n
      simp only [p, SheafOfModules.KFlatRoos.unitProduct, Category.assoc,
        Pi.map_π, Pi.lift_comp_π]
      ext i : 1
      have hn := congrArg (fun f ↦ f.f i) (hunitc n)
      simpa only [HomologicalComplex.comp_f, roosEval, Category.assoc] using hn
    ext i : 1
    have h := signedAugmentation (T.tower.obj P) P (T.augmentation.app P)
      (T.augmentation_zero P) V p i
    have h' := congrArg (fun f ↦ biprod.lift (f.f i)
      (0 : P.X i ⟶ V.X (i - 1))) hup
    have hh := h.trans h'
    change (T.augmentation.app P).f i ≫ q.f i = _
    exact (congrArg (fun f ↦ (T.augmentation.app P).f i ≫ f) (hqf i)).trans hh
  exact completionComparison T P L q hq
    (SheafOfModules.KFlatRoos.augmentation.{u + 1, u, u + 1} B ι P) hu K e

end AlgebraicGeometry.ProEtale.StrictCompletionRestriction
