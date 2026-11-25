/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement

/-! # Restriction of the unbounded affine compact-support comparison

Source: blueprint vector integration, comparison of ordered compact supports.
(blueprint: lem-amb-affine-trace-compact-comparison-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] rightDerivedLowerShriekOfCompactificationIso
  unboundedEtaleLowerShriekCompIso unboundedEtaleLowerShriekId
  rightDerivedLowerShriekOfCompactificationPlusIso rightDerivedLowerShriekPlusCompIso
  upperStar

/-- Construct the unbounded tower comparison from the compact-support identity,
the standard affine-line compactifications and the compact-support compositor.
Source: blueprint sec-smooth-purity/sk-prop-an, vector integration overlap calculation.
(blueprint: lem-amb-affine-trace-compact-comparison-restriction). -/
def affineTraceUnboundedCompactComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] : (d : ℕ) →
    affineTraceLeft A S d ≅
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)
  | 0 => (unboundedEtaleLowerShriekId A S).symm
  | d + 1 =>
    letI := affineTraceNoetherian S d
    let e := rightDerivedLowerShriekIso A
      (affineTraceLineCompactification (affineTraceTower S d))
    Functor.isoWhiskerRight e (affineTraceLeft A S d) ≪≫
      Functor.isoWhiskerLeft _ (affineTraceUnboundedCompactComparison A S d) ≪≫
      unboundedEtaleLowerShriekCompIso A
        (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
        (affineTraceProjection S d)

-- Composition compatibility forces the identity comparison to preserve its unit.
private lemma restriction_identity
    {C D : Type*} [Category C] [Category D] (I : C ⥤ D)
    {Pp : C ⥤ C} {P : D ⥤ D} (ep : Pp ≅ 𝟭 C) (e : P ≅ 𝟭 D)
    (κ : Pp ⋙ I ≅ I ⋙ P)
    (h : ∀ K, I.map (Pp.map (ep.hom.app K)) ≫ κ.hom.app K =
      κ.hom.app (Pp.obj K) ≫ P.map (κ.hom.app K) ≫ P.map (e.hom.app (I.obj K)))
    (K : C) :
    e.inv.app (I.obj K) = I.map (ep.inv.app K) ≫ κ.hom.app K := by
  have : P.Faithful := Functor.Faithful.of_iso e.symm
  have hn := κ.hom.naturality (ep.hom.app K)
  simp only [Functor.comp_map, Functor.id_obj] at hn
  have hu : I.map (ep.hom.app K) = κ.hom.app K ≫ e.hom.app (I.obj K) := by
    apply P.map_injective
    apply (cancel_epi (κ.hom.app (Pp.obj K))).1
    rw [← hn, h K, P.map_comp]
  apply (cancel_mono (e.hom.app (I.obj K))).1
  rw [Iso.inv_hom_id_app, Category.assoc, ← hu, ← I.map_comp,
    Iso.inv_hom_id_app, I.map_id]
  rfl

-- A diagram calculation on morphisms keeps every supplied comparison at its native type.
private lemma map_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {W X Y Z : C} {a : W ⟶ X} {b : X ⟶ Z} {c : W ⟶ Y} {d : Y ⟶ Z}
    (h : a ≫ b = c ≫ d) : F.map a ≫ F.map b = F.map c ≫ F.map d := by
  simpa only [Functor.map_comp] using congrArg F.map h

private lemma restriction_paste
    {E : Type*} [Category E] {W A B C D V X Y Z T R : E}
    {a : W ⟶ A} {b : A ⟶ B} {c : B ⟶ C} {d : C ⟶ D} {e : D ⟶ V}
    {l : A ⟶ Y} {r : Y ⟶ C} {p : W ⟶ X} {q : X ⟶ Y}
    {β : Y ⟶ T} {v : T ⟶ D} {s : X ⟶ Z} {t : Z ⟶ T}
    {μ : Z ⟶ R} {κ : R ⟶ V}
    (hline : b ≫ c = l ≫ r) (hn : a ≫ l = p ≫ q)
    (hn' : r ≫ d = β ≫ v) (hprev : q ≫ β = s ≫ t)
    (hcomp : t ≫ v ≫ e = μ ≫ κ) :
    a ≫ b ≫ c ≫ d ≫ e = p ≫ s ≫ μ ≫ κ := by
  rw [← Category.assoc b, hline]
  simp only [Category.assoc]
  rw [reassoc_of% hn, reassoc_of% hn', reassoc_of% hprev, hcomp]

-- Combine component equations without retyping the recursive natural isomorphisms.
private lemma combine_components
    {E Ep : Type*} [Category E] [Category Ep] (k : Ep ⥤ E)
    {W Z Y₁ Y₂ : Ep} {U V U₁ U₂ U₃ : E}
    {a : k.obj W ⟶ U} {b : U ⟶ V} {c : W ⟶ Z} {κ : k.obj Z ⟶ V}
    {a₁ : k.obj W ⟶ U₁} {a₂ : U₁ ⟶ U}
    {b₁ : U ⟶ U₂} {b₂ : U₂ ⟶ U₃} {b₃ : U₃ ⟶ V}
    {c₁ : W ⟶ Y₁} {c₂ : Y₁ ⟶ Y₂} {c₃ : Y₂ ⟶ Z}
    (ha : a = a₁ ≫ a₂) (hb : b = b₁ ≫ b₂ ≫ b₃) (hc : c = c₁ ≫ c₂ ≫ c₃)
    (hp : a₁ ≫ a₂ ≫ b₁ ≫ b₂ ≫ b₃ =
      k.map c₁ ≫ k.map c₂ ≫ k.map c₃ ≫ κ) : a ≫ b = k.map c ≫ κ := by
  rw [ha, hb, hc]
  simpa only [Functor.map_comp, Category.assoc] using hp

private lemma identity_restriction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S]
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (unboundedEtaleLowerShriekId A S).inv.app (DerivedCategory.Plus.ι.obj K) =
      DerivedCategory.Plus.ι.map ((rightDerivedLowerShriekPlusId A S).inv.app K) ≫
        (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) (𝟙 S)).hom.app K := by
  apply restriction_identity DerivedCategory.Plus.ι (rightDerivedLowerShriekPlusId A S)
    (unboundedEtaleLowerShriekId A S)
    (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) (𝟙 S)) _ K
  intro M
  have hb := congr_app (rightDerivedLowerShriekPlusCompIso_id_left A (𝟙 S)) M
  have hu := congr_app (unboundedEtaleLowerShriekCompIso_units A (𝟙 S)).1
    (DerivedCategory.Plus.ι.obj M)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    rightDerivedLowerShriekPlusCongr, CompactSupportFormalism.lowerShriekCongr,
    unboundedEtaleLowerShriekCongr, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id] at hb hu
  change (rightDerivedLowerShriekPlusCompIso A (𝟙 S) (𝟙 S)).hom.app M =
    (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) (𝟙 S)).map
      ((rightDerivedLowerShriekPlusId A S).hom.app M) ≫ 𝟙 _ ≫ 𝟙 _ at hb
  change (unboundedEtaleLowerShriekCompIso A (𝟙 S) (𝟙 S)).hom.app
    (DerivedCategory.Plus.ι.obj M) =
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 S)).map
        ((unboundedEtaleLowerShriekId A S).hom.app (DerivedCategory.Plus.ι.obj M)) ≫
        𝟙 _ at hu
  simp only [Category.comp_id] at hb hu
  have h := unboundedEtaleCompactSupport_composition_plus A (𝟙 S) (𝟙 S) M
  rw [hb, hu] at h
  exact h

private lemma restriction_compactification
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] (c : Compactification f)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map
        ((rightDerivedLowerShriekOfCompactificationPlusIso A c
          (HasCompactification.compactification f)).hom.app K) ≫
      (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f).hom.app K =
    (rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) c).hom.app K ≫
      (rightDerivedLowerShriekIso A c).hom.app (DerivedCategory.Plus.ι.obj K) := by
  exact unboundedEtaleCompactSupport_comparison_plus A f c
    (HasCompactification.compactification f) K

private lemma restriction_zero
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S]
    (K : DerivedCategory.Plus
      (Sheaf (affineTraceTower S 0).smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (affineTracePlusCompatibility A S 0).hom.app K ≫
        (affineTraceUnboundedCompactComparison A S 0).hom.app
          (DerivedCategory.Plus.ι.obj K) =
      DerivedCategory.Plus.ι.map ((affineTraceCompactSupportComparison A S 0).hom.app K) ≫
        (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A)
          (affineTraceProjection S 0)).hom.app K := by
  change (𝟙 _ ≫ 𝟙 _) ≫
    (unboundedEtaleLowerShriekId A S).inv.app (DerivedCategory.Plus.ι.obj K) =
      DerivedCategory.Plus.ι.map ((rightDerivedLowerShriekPlusId A S).inv.app K) ≫
        (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) (𝟙 S)).hom.app K
  simpa only [Category.id_comp] using identity_restriction A S K

-- Component equations keep recursion separate from the diagram calculation.
private lemma unbounded_succ_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    [IsNoetherian (affineTraceTower S d)]
    (K : DerivedCategoryModule A (affineTraceTower S (d + 1))) :
    (affineTraceUnboundedCompactComparison A S (d + 1)).hom.app K =
      (affineTraceLeft A S d).map
        ((rightDerivedLowerShriekIso A
          (affineTraceLineCompactification (affineTraceTower S d))).hom.app K) ≫
      (affineTraceUnboundedCompactComparison A S d).hom.app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A)
          (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)).obj K) ≫
      (unboundedEtaleLowerShriekCompIso A
        (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
        (affineTraceProjection S d)).hom.app K := by
  rfl

private lemma plus_succ_iso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    [IsNoetherian (affineTraceTower S d)] :
    affineTraceCompactSupportComparison A S (d + 1) =
      Functor.isoWhiskerRight
        (rightDerivedLowerShriekOfCompactificationPlusIso A
          (affineTraceLineCompactification (affineTraceTower S d))
          (HasCompactification.compactification
            (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)))
        (affineTraceLeftPlus A S d) ≪≫
      Functor.isoWhiskerLeft
        (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A)
          (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d))
        (affineTraceCompactSupportComparison A S d) ≪≫
      rightDerivedLowerShriekPlusCompIso A
        (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
        (affineTraceProjection S d) := by
  exact affineTraceCompactSupportComparison.eq_2 A S d

private lemma comparison_step_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L Q : C ⥤ D} {F P : D ⥤ E} {H : C ⥤ E}
    (a : L ≅ Q) (b : F ≅ P) (c : Q ⋙ P ≅ H) (K : C) :
    (Functor.isoWhiskerRight a F ≪≫ Functor.isoWhiskerLeft Q b ≪≫ c).hom.app K =
      F.map (a.hom.app K) ≫ b.hom.app (Q.obj K) ≫ c.hom.app K := by
  rfl

private lemma plus_succ_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    [IsNoetherian (affineTraceTower S d)]
    (K : DerivedCategory.Plus
      (Sheaf (affineTraceTower S (d + 1)).smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (affineTraceCompactSupportComparison A S (d + 1)).hom.app K =
      (affineTraceLeftPlus A S d).map
        ((rightDerivedLowerShriekOfCompactificationPlusIso A
          (affineTraceLineCompactification (affineTraceTower S d))
          (HasCompactification.compactification
            (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d))).hom.app
          K) ≫
      (affineTraceCompactSupportComparison A S d).hom.app
        ((rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A)
          (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)).obj K) ≫
      (rightDerivedLowerShriekPlusCompIso A
        (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
        (affineTraceProjection S d)).hom.app K := by
  have h := congrArg (fun e ↦ e.hom.app K)
    (plus_succ_iso A S d)
  exact h.trans (comparison_step_app _ _ _ K)

private lemma compatibility_succ_app
    (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) (d : ℕ)
    (K : DerivedCategory.Plus
      (Sheaf (affineTraceTower S (d + 1)).smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (affineTracePlusCompatibility A S (d + 1)).hom.app K =
      (affineTracePlusCompatibility A S d).hom.app
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
          (affineTraceLineCompactification (affineTraceTower S d))).obj K) ≫
      (affineTraceLeft A S d).map
        ((rightDerivedLowerShriekOfCompactificationPlusCompatibility (ModuleCat.{u + 1} A)
          (affineTraceLineCompactification (affineTraceTower S d))).hom.app K) := by
  simp only [affineTracePlusCompatibility, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app]
  change 𝟙 _ ≫ (affineTracePlusCompatibility A S d).hom.app _ ≫ 𝟙 _ ≫
    (affineTraceLeft A S d).map
      ((rightDerivedLowerShriekOfCompactificationPlusCompatibility (ModuleCat.{u + 1} A)
        (affineTraceLineCompactification (affineTraceTower S d))).hom.app K) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

-- Record the native composition equation separately from the pasted square.
private theorem successor_composition
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (K : DerivedCategory.Plus
      (Sheaf (affineTraceTower S (d + 1)).smallEtaleTopology (ModuleCat.{u + 1} A))) :
    letI := affineTraceNoetherian S d
    letI : IsNoetherian (AffineSpace PUnit.{u + 1} (affineTraceTower S d)) :=
      affineTraceNoetherian S (d + 1)
    let q := AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d
    (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A)
      (affineTraceProjection S d)).hom.app
        ((rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) q).obj K) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)).map
        ((rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) q).hom.app K) ≫
      (unboundedEtaleLowerShriekCompIso A q (affineTraceProjection S d)).hom.app
        (DerivedCategory.Plus.ι.obj K) =
    DerivedCategory.Plus.ι.map
        ((rightDerivedLowerShriekPlusCompIso A q (affineTraceProjection S d)).hom.app K) ≫
      (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A)
        (q ≫ affineTraceProjection S d)).hom.app K :=
  letI := affineTraceNoetherian S d
  letI : IsNoetherian (AffineSpace PUnit.{u + 1} (affineTraceTower S d)) :=
    affineTraceNoetherian S (d + 1)
  (unboundedEtaleCompactSupport_composition_plus A
    (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
    (affineTraceProjection S d) K).symm

private theorem successor_paste
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (ih : ∀ (M : DerivedCategory.Plus
      (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} A))),
      (affineTracePlusCompatibility A S d).hom.app M ≫
        (affineTraceUnboundedCompactComparison A S d).hom.app
          (DerivedCategory.Plus.ι.obj M) =
      DerivedCategory.Plus.ι.map ((affineTraceCompactSupportComparison A S d).hom.app M) ≫
        (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A)
          (affineTraceProjection S d)).hom.app M)
    (K : DerivedCategory.Plus
      (Sheaf (affineTraceTower S (d + 1)).smallEtaleTopology (ModuleCat.{u + 1} A))) :
    letI := affineTraceNoetherian S d
    letI : IsNoetherian (AffineSpace PUnit.{u + 1} (affineTraceTower S d)) :=
      affineTraceNoetherian S (d + 1)
    let q := AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d
    let c := affineTraceLineCompactification (affineTraceTower S d)
    (affineTracePlusCompatibility A S d).hom.app
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).obj K) ≫
      (affineTraceLeft A S d).map
        ((rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} A) c).hom.app K) ≫
      (affineTraceLeft A S d).map
        ((rightDerivedLowerShriekIso A c).hom.app (DerivedCategory.Plus.ι.obj K)) ≫
      (affineTraceUnboundedCompactComparison A S d).hom.app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).obj
          (DerivedCategory.Plus.ι.obj K)) ≫
      (unboundedEtaleLowerShriekCompIso A q (affineTraceProjection S d)).hom.app
        (DerivedCategory.Plus.ι.obj K) =
    DerivedCategory.Plus.ι.map ((affineTraceLeftPlus A S d).map
        ((rightDerivedLowerShriekOfCompactificationPlusIso A c
          (HasCompactification.compactification q)).hom.app K)) ≫
      DerivedCategory.Plus.ι.map ((affineTraceCompactSupportComparison A S d).hom.app
        ((rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) q).obj K)) ≫
      DerivedCategory.Plus.ι.map
        ((rightDerivedLowerShriekPlusCompIso A q (affineTraceProjection S d)).hom.app K) ≫
      (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A)
        (q ≫ affineTraceProjection S d)).hom.app K :=
  letI := affineTraceNoetherian S d
  letI : IsNoetherian (AffineSpace PUnit.{u + 1} (affineTraceTower S d)) :=
    affineTraceNoetherian S (d + 1)
  let q := AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d
  let c := affineTraceLineCompactification (affineTraceTower S d)
  restriction_paste
    (map_square (affineTraceLeft A S d) (restriction_compactification A q c K).symm)
    ((affineTracePlusCompatibility A S d).hom.naturality
      ((rightDerivedLowerShriekOfCompactificationPlusIso A c
        (HasCompactification.compactification q)).hom.app K)).symm
    ((affineTraceUnboundedCompactComparison A S d).hom.naturality
      ((rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) q).hom.app K))
    (ih ((rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) q).obj K))
    (successor_composition A S d K)

private lemma restriction_successor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (ih : ∀ (M : DerivedCategory.Plus
      (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} A))),
      (affineTracePlusCompatibility A S d).hom.app M ≫
        (affineTraceUnboundedCompactComparison A S d).hom.app
          (DerivedCategory.Plus.ι.obj M) =
      DerivedCategory.Plus.ι.map ((affineTraceCompactSupportComparison A S d).hom.app M) ≫
        (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A)
          (affineTraceProjection S d)).hom.app M)
    (K : DerivedCategory.Plus
      (Sheaf (affineTraceTower S (d + 1)).smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (affineTracePlusCompatibility A S (d + 1)).hom.app K ≫
        (affineTraceUnboundedCompactComparison A S (d + 1)).hom.app
          (DerivedCategory.Plus.ι.obj K) =
      DerivedCategory.Plus.ι.map ((affineTraceCompactSupportComparison A S (d + 1)).hom.app K) ≫
        (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A)
          (affineTraceProjection S (d + 1))).hom.app K := by
  let := affineTraceNoetherian S d
  have hp := successor_paste A S d ih K
  exact combine_components DerivedCategory.Plus.ι
    (compatibility_succ_app A S d K)
    (unbounded_succ_app A S d (DerivedCategory.Plus.ι.obj K)) (plus_succ_app A S d K) hp

/-- The recursively constructed unbounded comparison restricts to the specified
bounded-below comparison.
Source: blueprint sec-smooth-purity/sk-prop-an/def-amb-vector-integration.proof.md,
overlap calculation, bounded-below/unbounded compact-support comparison.
(blueprint: lem-amb-affine-trace-compact-comparison-restriction).

Proof: induct on d. In dimension zero, use the compact-support composition restriction
for the identity pair and the left unit equations on D+ and D. Naturality of the
inclusion comparison and faithfulness of compact supports along the identity identify
its unit restriction; compose with the inverse identity comparisons to obtain the
asserted zero equation. For a successor, write q for the last affine-line projection
and c for its standard projective-line compactification. The comparison restriction
for c and the chosen compactification says that the inclusion of their D+ comparison,
followed by the chosen inclusion comparison, equals the c inclusion comparison followed
by the unbounded compactification comparison. Take components of the successor tower
comparison equations. Apply the line restriction equation under the preceding tower
functor. Naturality of the preceding inclusion comparison moves the bounded-below line
comparison across it. Naturality of the preceding unbounded tower comparison then
moves the line inclusion comparison across that comparison. The induction hypothesis
and the compact-support composition restriction finish the pasted square.
Reassociation proves the equation. These
arguments apply to all bounded-below objects, including zero objects and empty bases. -/
theorem affineTraceUnboundedCompactComparison_restriction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (K : DerivedCategory.Plus
      (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (affineTracePlusCompatibility A S d).hom.app K ≫
        (affineTraceUnboundedCompactComparison A S d).hom.app
          (DerivedCategory.Plus.ι.obj K) =
      DerivedCategory.Plus.ι.map ((affineTraceCompactSupportComparison A S d).hom.app K) ≫
        (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A)
          (affineTraceProjection S d)).hom.app K := by
  induction d with
  | zero => exact restriction_zero A S K
  | succ d ih => exact restriction_successor A S d ih K

end AlgebraicGeometry.Etale
