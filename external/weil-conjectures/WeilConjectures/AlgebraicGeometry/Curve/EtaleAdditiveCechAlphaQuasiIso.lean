/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization
import WeilConjectures.AlgebraicGeometry.EtaleOpenCechInjectiveAugmentation
import WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleCore

/-! # Global restriction augmentation quasi-isomorphism
Source: Stacks Project, Tag 01EQ, Lemma 20.11.2. -/


@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable def restriction₀
    (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
    (F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    F.obj (op (Scheme.Etale.mk (𝟙 X))) ⟶
      ((cechComplexFunctor U).obj ((additiveCechOpenInclusion X).op ⋙ F)).X 0 :=
  Limits.Pi.lift (fun y : Fin 1 → ι ↦ F.map
    (MorphismProperty.Over.homMk (∏ᶜ fun l ↦ U (y l)).ι (Category.comp_id _) :
      (additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l)) ⟶
        Scheme.Etale.mk (𝟙 X)).op)

private theorem restriction₀_naturality
    (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
    {F G : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (f : F ⟶ G) :
    restriction₀ X U F ≫
      ((cechComplexFunctor U).map
        (Functor.whiskerLeft (additiveCechOpenInclusion X).op f)).f 0 =
      f.app (op (Scheme.Etale.mk (𝟙 X))) ≫ restriction₀ X U G := by
  apply Limits.Pi.hom_ext
  intro t
  dsimp [restriction₀, cechComplexFunctor, Limits.FormalCoproduct.cochainComplexFunctor,
    Limits.FormalCoproduct.cosimplicialObjectFunctor,
    AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.map, Limits.FormalCoproduct.evalOp]
  simp only [Category.assoc, Limits.Pi.lift_comp_π, Limits.Pi.map_π, Limits.Pi.lift_comp_π_assoc]
  exact f.naturality _

private theorem restriction₀_d
    (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
    (F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    restriction₀ X U F ≫
      ((cechComplexFunctor U).obj ((additiveCechOpenInclusion X).op ⋙ F)).d 0 1 = 0 := by
  change restriction₀ X U F ≫
    (∑ j : Fin 2, (-1 : ℤ) ^ j.val •
      Limits.Pi.lift (fun t : Fin 2 → ι ↦
        Limits.Pi.π (fun s : Fin 1 → ι ↦
          F.obj (op ((additiveCechOpenInclusion X).obj (∏ᶜ fun k ↦ U (s k)))))
            (t ∘ j.succAbove) ≫
        F.map ((additiveCechOpenInclusion X).map (Limits.Pi.lift (fun k : Fin 1 ↦
          Limits.Pi.π (fun k : Fin 2 ↦ U (t k)) (j.succAbove k)))).op)) = 0
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    Preadditive.comp_add, Preadditive.comp_neg]
  apply Limits.Pi.hom_ext
  intro t
  simp only [Preadditive.add_comp, Preadditive.neg_comp, Category.assoc, Limits.Pi.lift_comp_π,
    restriction₀, Limits.zero_comp]
  erw [Limits.Pi.lift_comp_π_assoc, Limits.Pi.lift_comp_π_assoc]
  rw [← F.map_comp, ← F.map_comp]
  have hh :
      (MorphismProperty.Over.homMk (∏ᶜ fun l ↦ U ((t ∘ (0 : Fin 2).succAbove) l)).ι
        (Category.comp_id _) : _ ⟶ Scheme.Etale.mk (𝟙 X)).op ≫
          ((additiveCechOpenInclusion X).map (Limits.Pi.lift fun k ↦
            Limits.Pi.π (fun k ↦ U (t k)) ((0 : Fin 2).succAbove k))).op =
      (MorphismProperty.Over.homMk (∏ᶜ fun l ↦ U ((t ∘ (1 : Fin 2).succAbove) l)).ι
        (Category.comp_id _) : _ ⟶ Scheme.Etale.mk (𝟙 X)).op ≫
          ((additiveCechOpenInclusion X).map (Limits.Pi.lift fun k ↦
            Limits.Pi.π (fun k ↦ U (t k)) ((1 : Fin 2).succAbove k))).op := by
    apply Quiver.Hom.unop_inj
    exact (MorphismProperty.Over.mkIdTerminal @Etale X).hom_ext _ _
  rw [hh]
  exact add_neg_cancel _

/-- The global restriction augmentation is a quasi-isomorphism of complexes.
Source: Stacks Project, Tag 01EQ, Lemma 20.11.2, augmentation alpha.
(blueprint: lem-pbc-etale-additive-cech-alpha-quasiiso)

Proof: Global restrictions commute with the resolution differential and with the
alternating Cech cofaces. The latter cancel in horizontal degree zero, so the
components alpha form a chain map. The canonical open inclusion preserves
coverings and finite limits, and its value at top is terminal. Each injective
resolution term therefore has a quasi-isomorphic augmented open-cover Cech row,
by etaleOpenCechInjectiveAugmentation_quasiIso. Apply the first-quadrant column
augmentation criterion, with Cech degree first, to these rows. Its component
formula is precisely additiveCechAlpha, so the resulting map is a quasi-isomorphism.
Degree zero uses sheaf gluing; empty covers force the scheme and its sections to
be empty and zero respectively, and repeated or empty intersections cause no change. -/
theorem etaleAdditiveCech_alpha_quasiIso
    {X : Scheme.{u}} {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hcover : iSup U = ⊤) (I : InjectiveResolution X.etaleAdditiveSheaf) :
    ∃ a : additiveCechGlobal I ⟶ additiveCechTotal U I,
      (∀ n : ℕ, a.f n = additiveCechAlpha U I n) ∧ QuasiIso a := by
  let i := additiveCechOpenInclusion X
  obtain ⟨j, hj, hcj, hlj, ⟨htj⟩, hcont, _⟩ := zariski_to_etale_core X
  let e : i ≅ j := Functor.fullyFaithfulCancelRight (Scheme.Etale.forget X)
    (eqToIso (show i ⋙ Scheme.Etale.forget X = X.restrictFunctor from rfl) ≪≫
      (eqToIso hj).symm)
  have : Limits.PreservesFiniteLimits j := hlj
  have : Limits.PreservesFiniteLimits i := Limits.preservesFiniteLimits_of_natIso e.symm
  have : RepresentablyFlat i := flat_of_preservesFiniteLimits i
  have : j.IsContinuous (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology :=
    hcont
  have : i.IsContinuous (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology :=
    Functor.isContinuous_of_iso e.symm _ _
  have hc : CoverPreserving (Opens.grothendieckTopology X.carrier)
      X.smallEtaleTopology i := Functor.isContinuous_iff_coverPreserving.mp inferInstance
  have ht : Limits.IsTerminal (i.obj ⊤) := Limits.isTerminalTop.isTerminalObj i ⊤
  let D := etaleOpenCechResolutionDoubleComplex X i U I
  let A := additiveCechGlobal I
  let a : A ⟶ D.X 0 :=
    { f := fun q ↦ restriction₀ X U (I.cocomplex.X q).obj
      comm' := by
        intro q r h
        exact restriction₀_naturality X U (I.cocomplex.d q r).hom }
  have ha : a ≫ D.d 0 1 = 0 := by
    apply HomologicalComplex.hom_ext
    intro q
    exact restriction₀_d X U (I.cocomplex.X q).obj
  let b : A ⟶ D.total (.up ℕ) :=
    { f := fun q ↦ a.f q ≫ D.ιTotal (.up ℕ) 0 q q (by simp)
      comm' := by
        intro q r h
        have hr : q + 1 = r := h
        subst r
        simp only [HomologicalComplex₂.total_d, Category.assoc,
          Preadditive.comp_add, HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
        rw [D.d₁_eq (.up ℕ) (by simp : (ComplexShape.up ℕ).Rel 0 1)
          q (q + 1) (by simp [Nat.add_comm]),
          D.d₂_eq (.up ℕ) 0
            (by simp : (ComplexShape.up ℕ).Rel q (q + 1)) (q + 1) (by simp)]
        have hz := congrArg (fun f ↦ f.f q) ha
        simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at hz
        have hs₁ : ComplexShape.ε₁ (.up ℕ) (.up ℕ) (.up ℕ) (0, q) = 1 := rfl
        have hs₂ : ComplexShape.ε₂ (.up ℕ) (.up ℕ) (.up ℕ) (0, q) = 1 := by
          change (-1 : ℤˣ) ^ 0 = 1
          exact pow_zero _
        simp only [hs₁, hs₂, one_smul, ← Category.assoc, hz, Limits.zero_comp, zero_add]
        rw [a.comm q (q + 1)] }
  have hcol : ∀ q : ℕ, QuasiIso
      ((CochainComplex.fromSingle₀Equiv (D.flip.X q) (A.X q)).symm
        ⟨a.f q, by simpa using congrArg (fun f ↦ f.f q) ha⟩) := by
    intro q
    let c := (CochainComplex.fromSingle₀Equiv (D.flip.X q) (A.X q)).symm
      ⟨a.f q, by simpa using congrArg (fun f ↦ f.f q) ha⟩
    let t : i.obj ⊤ ≅ Scheme.Etale.mk (𝟙 X) :=
      ht.uniqueUpToIso (MorphismProperty.Over.mkIdTerminal @Etale X)
    let s := (CochainComplex.single₀ AddCommGrpCat.{u + 1}).mapIso
      ((I.cocomplex.X q).obj.mapIso t.symm.op)
    have hs : QuasiIso (s.hom ≫ c) := by
      apply etaleOpenCechInjectiveAugmentation_quasiIso X i hc ht U hcover
        (I.cocomplex.X q)
      intro y
      dsimp only [c]
      simp only [HomologicalComplex.comp_f, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
      change (I.cocomplex.X q).obj.map t.inv.op ≫
        restriction₀ X U (I.cocomplex.X q).obj ≫ Limits.Pi.π _ y = _
      dsimp only [restriction₀]
      erw [Limits.Pi.lift_comp_π]
      rw [← Functor.map_comp]
      congr 1
      apply Quiver.Hom.unop_inj
      exact ht.hom_ext _ _
    exact (quasiIso_iff_comp_left s.hom c).mp hs
  refine ⟨b, fun _ ↦ rfl, ?_⟩
  exact HomologicalComplex₂.quasiIso_of_column_augmentation
    D A a ha b (fun _ ↦ rfl) hcol


end AlgebraicGeometry.Scheme.Modules
