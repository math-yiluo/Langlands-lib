/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
import WeilConjectures.CategoryTheory.RingedSingletonCoefficientCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone

/-! # The singleton dual Koszul tensor as a scalar cone

Source: Stacks Project, algebraization.tex, Lemma derived-completion-koszul (0A0E).
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})

local instance instIsGrothendieckAbelianRingedSingletonKoszulCone :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  SheafOfModules.isGrothendieckAbelian _
local instance instMonoidalCategoryRingedSingletonKoszulCone : MonoidalCategory (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  SheafOfModules.monoidalCategory O
local instance instSymmetricCategoryRingedSingletonKoszulCone :
    SymmetricCategory (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  SheafOfModules.symmetricCategory O
local instance instMonoidalPreadditiveRingedSingletonKoszulCone :
    MonoidalPreadditive (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  Classical.choice (SheafOfModules.tensorClosed O).1
local instance instMonoidalClosedRingedSingletonKoszulCone : MonoidalClosed (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  Classical.choice (SheafOfModules.tensorClosed O).2.1

attribute [local irreducible] homComplexFunctor

/-- The positive scalar power acting on the tensor with O[0].
Source: Stacks 0A0E (auxiliary; not a blueprint node). -/
@[irreducible] def ringedSingletonKoszulPower
    (a : (O.obj ⋙ forget CommRingCat).sections) (P : ringedSiteComplex O) (n : ℕ) :
    End (((ringedKoszulTensor O).obj P).obj (ringedSiteRingComplex O)) :=
  End.of (((ringedKoszulTensor O).obj P).map
    ((HomologicalComplex.single _ (.up ℤ) 0).map (ringedKoszulScalar O a ^ (n + 1)).asHom))

private abbrev singletonScalar
    (a : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) :=
  (HomologicalComplex.single _ (.up ℤ) 0).map (ringedKoszulScalar O a ^ (n + 1)).asHom

private abbrev singletonTensorPower
    (a : (O.obj ⋙ forget CommRingCat).sections) (P : ringedSiteComplex O) (n : ℕ) :=
  HomologicalComplex.mapBifunctorMap (𝟙 P) (singletonScalar O a n)
    (curriedTensor _) (.up ℤ)

private def singletonTensorIso
    (a : (O.obj ⋙ forget CommRingCat).sections) (P : ringedSiteComplex O)
    (d : ∀ n : ℕ, (ringedKoszulDualTower O 1 (fun _ ↦ a)).obj (op n) ≅
      CochainComplex.mappingCone (singletonScalar O a n)) (n : ℕ) :
    HomologicalComplex.mapBifunctor P
        ((ringedKoszulDualTower O 1 (fun _ ↦ a)).obj (op n)) (curriedTensor _) (.up ℤ) ≅
      CochainComplex.mappingCone (singletonTensorPower O a P n) :=
  (((curriedTensor _).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)).obj P).mapIso
      (d n) ≪≫
    CochainComplex.mapBifunctorMappingCone₂Iso P (singletonScalar O a n) (curriedTensor _)

private theorem singletonTensorIso_hom
    (a : (O.obj ⋙ forget CommRingCat).sections) (P : ringedSiteComplex O)
    (d : ∀ n : ℕ, (ringedKoszulDualTower O 1 (fun _ ↦ a)).obj (op n) ≅
      CochainComplex.mappingCone (singletonScalar O a n)) (n : ℕ) :
    (singletonTensorIso O a P d n).hom =
      HomologicalComplex.mapBifunctorMap (𝟙 P) (d n).hom
          (curriedTensor _) (.up ℤ) ≫
        CochainComplex.mapBifunctorMappingCone₂Iso.hom P (singletonScalar O a n)
          (curriedTensor _) := rfl

attribute [local irreducible] singletonTensorIso

private theorem singletonTensorIso_unit
    (a : (O.obj ⋙ forget CommRingCat).sections) (P : ringedSiteComplex O)
    (d : ∀ n : ℕ, (ringedKoszulDualTower O 1 (fun _ ↦ a)).obj (op n) ≅
      CochainComplex.mappingCone (singletonScalar O a n))
    (hu : ∀ n, ringedKoszulDualUnit O 1 (fun _ ↦ a) n ≫ (d n).hom =
      CochainComplex.mappingCone.inr (singletonScalar O a n)) (n : ℕ) :
    HomologicalComplex.mapBifunctorMap (𝟙 P) (ringedKoszulDualUnit O 1 (fun _ ↦ a) n)
        (curriedTensor _) (.up ℤ) ≫ (singletonTensorIso O a P d n).hom =
      CochainComplex.mappingCone.inr (singletonTensorPower O a P n) := by
  rw [singletonTensorIso_hom, ← Category.assoc]
  have ht : HomologicalComplex.mapBifunctorMap (𝟙 P)
        (ringedKoszulDualUnit O 1 (fun _ ↦ a) n) (curriedTensor _) (.up ℤ) ≫
      HomologicalComplex.mapBifunctorMap (𝟙 P) (d n).hom
        (curriedTensor _) (.up ℤ) =
      HomologicalComplex.mapBifunctorMap (𝟙 P)
        (CochainComplex.mappingCone.inr (singletonScalar O a n)) (curriedTensor _)
          (.up ℤ) := by
    apply HomologicalComplex.hom_ext
    intro q
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p j hpj
    simp only [HomologicalComplex.comp_f, HomologicalComplex.ι_mapBifunctorMap_assoc,
      HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.id_f, Functor.map_id,
      NatTrans.id_app, Category.id_comp]
    rw [← Functor.map_comp_assoc, ← HomologicalComplex.comp_f,
      hu n]
  rw [ht]
  exact CochainComplex.mapBifunctorMap_inr_mapBifunctorMappingCone₂Iso_hom P
    (singletonScalar O a n) (curriedTensor _)

private theorem singletonTensorIso_snd
    (a : (O.obj ⋙ forget CommRingCat).sections) (P : ringedSiteComplex O)
    (d : ∀ n : ℕ, (ringedKoszulDualTower O 1 (fun _ ↦ a)).obj (op n) ≅
      CochainComplex.mappingCone (singletonScalar O a n))
    (n : ℕ) (p j q : ℤ) (hpj : p + j = q) :
    HomologicalComplex.ιMapBifunctor P
        ((ringedKoszulDualTower O 1 (fun _ ↦ a)).obj (op n))
        (curriedTensor _) (.up ℤ) p j q hpj ≫
      (singletonTensorIso O a P d n).hom.f q ≫
        (CochainComplex.mappingCone.snd (singletonTensorPower O a P n)).v
          q q (add_zero q) =
      (curriedTensor _ |>.obj (P.X p)).map
        ((d n).hom.f j ≫
          (CochainComplex.mappingCone.snd (singletonScalar O a n)).v j j (add_zero j)) ≫
        HomologicalComplex.ιMapBifunctor P (ringedSiteRingComplex O)
          (curriedTensor _) (.up ℤ) p j q hpj := by
  rw [singletonTensorIso_hom]
  simp only [HomologicalComplex.comp_f, Category.assoc,
    HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.id_f,
    Functor.map_id, NatTrans.id_app, Category.id_comp]
  simp only [CochainComplex.mapBifunctorMappingCone₂Iso.hom,
    CochainComplex.mappingCone.lift_f_snd_v,
    CochainComplex.mapBifunctorMappingCone₂Iso.ι_p₂_v,
    ← Functor.map_comp_assoc]

private theorem singletonTensorCone
    (a : (O.obj ⋙ forget CommRingCat).sections) (P : ringedSiteComplex O) :
    ∃ e : ∀ n : ℕ,
        HomologicalComplex.mapBifunctor P
          ((ringedKoszulDualTower O 1 (fun _ ↦ a)).obj (op n)) (curriedTensor _) (.up ℤ) ≅
          CochainComplex.mappingCone (singletonTensorPower O a P n),
      (∀ n, HomologicalComplex.mapBifunctorMap (𝟙 P)
          (ringedKoszulDualUnit O 1 (fun _ ↦ a) n) (curriedTensor _) (.up ℤ) ≫
        (e n).hom = CochainComplex.mappingCone.inr (singletonTensorPower O a P n)) ∧
      (∀ (n : ℕ) (p j : ℤ), j ≠ 0 →
        HomologicalComplex.ιMapBifunctor P
            ((ringedKoszulDualTower O 1 (fun _ ↦ a)).obj (op n))
            (curriedTensor _) (.up ℤ) p j (p + j) rfl ≫
          (e n).hom.f (p + j) ≫
            (CochainComplex.mappingCone.snd (singletonTensorPower O a P n)).v
                (p + j) (p + j) (add_zero _) = 0) ∧
      (∀ (n : ℕ) (q : ℤ),
        (HomologicalComplex.mapBifunctorMap (𝟙 P)
          ((ringedKoszulDualTower O 1 (fun _ ↦ a)).map
            (homOfLE (Nat.le_add_right n 1)).op) (curriedTensor _) (.up ℤ)).f q ≫
          (e n).hom.f q ≫
            (CochainComplex.mappingCone.snd (singletonTensorPower O a P n)).v
              q q (add_zero _) =
          (e (n + 1)).hom.f q ≫
            (CochainComplex.mappingCone.snd (singletonTensorPower O a P (n + 1))).v
              q q (add_zero _)) := by
  obtain ⟨d, hu, ht⟩ := ringedSingletonCoefficientCone O a
  refine ⟨singletonTensorIso O a P d, ?_, ?_, ?_⟩
  · intro n
    exact singletonTensorIso_unit O a P d hu n
  · intro n p j hj
    rw [singletonTensorIso_snd]
    have hz : (d n).hom.f j ≫
        (CochainComplex.mappingCone.snd
          ((HomologicalComplex.single _ (.up ℤ) 0).map
            (ringedKoszulScalar O a ^ (n + 1)).asHom)).v j j (add_zero j) = 0 :=
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ j hj).eq_of_tgt _ _
    rw [hz, Functor.map_zero, zero_comp]
  · intro n q
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p j hpj
    simp only [HomologicalComplex.ι_mapBifunctorMap_assoc,
      HomologicalComplex.id_f, Functor.map_id, NatTrans.id_app, Category.id_comp]
    rw [singletonTensorIso_snd, singletonTensorIso_snd]
    rw [← Functor.map_comp_assoc, ht n j]

/-- The cone coordinates of a singleton dual tensor, including its degree-zero
projection. This is a finite linear algebra statement on an arbitrary ringed site;
it mentions no quotient, residue map, coefficient field or flatness hypothesis.

Source: Stacks Project, algebraization.tex, Lemma derived-completion-koszul (0A0E),
the two-term finite free Koszul complex and its dual.
(auxiliary; not a blueprint node).

Proof: identify the negative singleton complex with the internal dual by
ringedNegativeKoszulSuccDuality at rank one. The tail factor is O[0], removed
by the right unitor. The remaining negative factor is O --a^(n+1)--> O in
degrees -1 and 0. Identify this double complex with the mapping cone of the
same scalar on O[0], using its two supported degrees. Tensor with P and apply
the second-variable tensor-cone comparison. The resulting
endomorphism is exactly the specified tensor of the positive scalar power. In degree q
its cone coordinates are (P tensor O[0])^(q+1) and (P tensor O[0])^q;
the shifted coordinate has the usual (-1)^p tensor-cone sign. The dual unit
is the inclusion of the second coordinate, giving the first equation.
The cone's second projection is zero on every nonzero Koszul-degree summand,
giving the second equation, including unsupported degrees. The successor map
has diagonal entries a and 1, so it preserves the second projection. This is
the last equation. All maps use finite free bases and unitors, so the formulas
also hold on an empty site, over the zero ring, and for a zero complex. -/
theorem ringedSingletonKoszulCone
    (a : (O.obj ⋙ forget CommRingCat).sections) (P : ringedSiteComplex O) :
    ∃ e : ∀ n : ℕ,
        ((ringedKoszulTensorTower O 1 (fun _ ↦ a)).obj P).obj (op n) ≅
          CochainComplex.mappingCone (ringedSingletonKoszulPower O a P n).asHom,
      (∀ n, ringedKoszulTensorUnitComponent O 1 (fun _ ↦ a) P (op n) ≫
        (e n).hom = (ringedKoszulRightUnitIso O P).inv ≫
          CochainComplex.mappingCone.inr (ringedSingletonKoszulPower O a P n).asHom) ∧
      (∀ (n : ℕ) (p j : ℤ), j ≠ 0 →
        HomologicalComplex.ιMapBifunctor P
            ((ringedKoszulDualTower O 1 (fun _ ↦ a)).obj (op n))
            (curriedTensor _) (.up ℤ) p j (p + j) rfl ≫
          (e n).hom.f (p + j) ≫
            (CochainComplex.mappingCone.snd
              (ringedSingletonKoszulPower O a P n).asHom).v
                (p + j) (p + j) (add_zero _) = 0) ∧
      (∀ (n : ℕ) (q : ℤ),
        (((ringedKoszulTensorTower O 1 (fun _ ↦ a)).obj P).map
          (homOfLE (Nat.le_add_right n 1)).op).f q ≫ (e n).hom.f q ≫
            (CochainComplex.mappingCone.snd
              (ringedSingletonKoszulPower O a P n).asHom).v q q (add_zero _) =
          (e (n + 1)).hom.f q ≫
            (CochainComplex.mappingCone.snd
              (ringedSingletonKoszulPower O a P (n + 1)).asHom).v q q (add_zero _)) := by
  unfold ringedSingletonKoszulPower
  dsimp only [ringedKoszulTensorUnitComponent,
    ringedKoszulTensorTower, ringedKoszulTensor, Functor.comp_obj, Functor.comp_map,
    Functor.whiskeringLeft, Functor.map₂HomologicalComplex]
  obtain ⟨e, he, hz, ht⟩ := singletonTensorCone O a P
  refine ⟨e, ?_, hz, ht⟩
  intro n
  rw [Category.assoc]
  exact congrArg ((ringedKoszulRightUnitIso O P).inv ≫ ·) (he n)

end CategoryTheory
