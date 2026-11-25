/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.CategoryTheory.RingedSiteModules

/-! # Rigidity of the cochain tensor model

Source: Stacks Project, Tags 013H, 06YS, 06YT and 06YU; blueprint
`prose-03-02`, first sentence
(auxiliary; not a blueprint node).

The helpers expose the given homotopy model and its comparisons, then write the four
arrows of the canonical cochain comparison. No resolutions are chosen functorially.

## Main statements

- `cochain_tensor_model_rigidity`: the specified representative comparison, normalized
  uniqueness of tensor models, and full faithfulness of restriction.
-/

@[expose] public section

universe u v w d e z

open CategoryTheory MonoidalCategory

namespace SheafOfModules

set_option autoImplicit false
set_option synthInstance.maxSize 4096

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{w})
  [HasDerivedCategory.{d} (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))]

/-- The cochain representative property: precisely K-flatness and flatness in every degree.
Source: Stacks 06YS, 06YU (auxiliary; not a blueprint node). -/
def cochainTensorFlatRepresentatives : ObjectProperty (CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ) :=
  fun K ↦ CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) K ∧
    ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (K.X n)

/-- The given homotopy representative subcategory from tensor descent. Its membership is
characterized by the exact same K-flat and degreewise flat predicates as the cochain property.
Source: Stacks 06YU (auxiliary; not a blueprint node). -/
noncomputable def cochainTensorHomotopyRepresentatives :
    ObjectProperty (HomotopyCategory (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) (.up ℤ)) :=
  (site_derived_tensor_descent_independentCoefficients.{u, v, w, d, 0, 0} J R).choose

/-- Restriction of the homotopy quotient to flat-term K-flat representatives. The membership
proof uses the characterization supplied by the existing descent theorem, not a new predicate.
Source: Stacks 013H, 06YU (auxiliary; not a blueprint node). -/
noncomputable def cochainTensorRepresentativeQuotient :
    (cochainTensorFlatRepresentatives J R).FullSubcategory ⥤
      (cochainTensorHomotopyRepresentatives J R).FullSubcategory :=
  (cochainTensorHomotopyRepresentatives J R).lift
    ((cochainTensorFlatRepresentatives J R).ι ⋙ HomotopyCategory.quotient _ (.up ℤ))
    (fun K ↦ ((site_derived_tensor_descent_independentCoefficients.{u, v, w, d, 0, 0}
      J R).choose_spec.1 _).2 K.property)

/-- The cochain localization restricted to these representatives.
Source: Stacks 013H, 06YU (auxiliary; not a blueprint node). -/
noncomputable def cochainTensorRepresentativeLocalization :
    (cochainTensorFlatRepresentatives J R).FullSubcategory ⥤ DerivedCategory (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) :=
  (cochainTensorFlatRepresentatives J R).ι ⋙ DerivedCategory.Q

/-- The signed direct-sum total tensor on cochain complexes, using the existing sheaf tensor.
Source: Stacks 06YN, 06YU (auxiliary; not a blueprint node). -/
noncomputable def cochainTensorTotal : (CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ) ×
    (CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ) ⥤
    (CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ) :=
  Functor.uncurry.obj ((curriedTensor (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))

/-- The homotopy total tensor selected together with its comparison by the descent theorem.
Source: Stacks 06YU (auxiliary; not a blueprint node). -/
noncomputable def cochainTensorHomotopyTotal : (HomotopyCategory (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) (.up ℤ)) ×
    (HomotopyCategory (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) (.up ℤ)) ⥤
    (HomotopyCategory (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) (.up ℤ)) :=
  (site_derived_tensor_descent_independentCoefficients.{u, v, w, d, 0, 0}
    J R).choose_spec.2.2.1.choose

/-- The given comparison between homotopy tensor and the quotient of cochain tensor.
Source: Stacks 013H, 06YU (auxiliary; not a blueprint node). -/
noncomputable def cochainTensorHomotopyTotalComparison :
    ((HomotopyCategory.quotient (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) (.up ℤ)).prod
      (HomotopyCategory.quotient (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) (.up ℤ))) ⋙
      cochainTensorHomotopyTotal J R ≅
        cochainTensorTotal J R ⋙ HomotopyCategory.quotient (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) (.up ℤ) :=
  (site_derived_tensor_descent_independentCoefficients.{u, v, w, d, 0, 0}
    J R).choose_spec.2.2.1.choose_spec.1.some

/-- The given representative comparison for the selected derived tensor model. The choices
are exactly the packet defining `siteDerivedTensorIndependentCoefficients`, with its comparison.
Source: Stacks 06YU (auxiliary; not a blueprint node). -/
noncomputable def cochainTensorHomotopyDerivedComparison :
    ((cochainTensorHomotopyRepresentatives J R).ι.prod
      (cochainTensorHomotopyRepresentatives J R).ι) ⋙
        cochainTensorHomotopyTotal J R ⋙ DerivedCategory.Qh ≅
    (((cochainTensorHomotopyRepresentatives J R).ι ⋙ DerivedCategory.Qh).prod
      ((cochainTensorHomotopyRepresentatives J R).ι ⋙ DerivedCategory.Qh)) ⋙
        siteDerivedTensorIndependentCoefficients J R :=
  (site_derived_tensor_descent_independentCoefficients.{u, v, w, d, 0, 0}
    J R).choose_spec.2.2.1.choose_spec.2.choose_spec.some

/-- The four-arrow composite: Q→Qhπ, the cochain/homotopy tensor comparison, the given
homotopy representative comparison, and T applied to Qhπ→Q in both variables.
Source: Stacks 013H, 06YU (auxiliary; not a blueprint node). -/
noncomputable def cochainTensorRepresentativeArrow
    (X : (cochainTensorFlatRepresentatives J R).FullSubcategory ×
      (cochainTensorFlatRepresentatives J R).FullSubcategory) :
    DerivedCategory.Q.obj ((cochainTensorTotal J R).obj (X.1.obj, X.2.obj)) ⟶
      (siteDerivedTensorIndependentCoefficients J R).obj
        (DerivedCategory.Q.obj X.1.obj, DerivedCategory.Q.obj X.2.obj) :=
  (DerivedCategory.quotientCompQhIso (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))).inv.app
      ((cochainTensorTotal J R).obj (X.1.obj, X.2.obj)) ≫
    DerivedCategory.Qh.map ((cochainTensorHomotopyTotalComparison J R).inv.app
      (X.1.obj, X.2.obj)) ≫
    (cochainTensorHomotopyDerivedComparison J R).hom.app
      ((cochainTensorRepresentativeQuotient J R).obj X.1,
        (cochainTensorRepresentativeQuotient J R).obj X.2) ≫
    (siteDerivedTensorIndependentCoefficients J R).map
      ((DerivedCategory.quotientCompQhIso (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))).hom.app X.1.obj,
        (DerivedCategory.quotientCompQhIso (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))).hom.app X.2.obj)

-- Descent through the restricted quotient is componentwise, since it has the
-- same objects and every homotopy class has a cochain-map representative.
private theorem representative_quotient_bijective
    (E : Type e) [Category.{z} E]
    (U V : (cochainTensorHomotopyRepresentatives J R).FullSubcategory ×
      (cochainTensorHomotopyRepresentatives J R).FullSubcategory ⥤ E) :
    Function.Bijective (fun τ : U ⟶ V ↦ Functor.whiskerLeft
      ((cochainTensorRepresentativeQuotient J R).prod
        (cochainTensorRepresentativeQuotient J R)) τ) := by
  let p := cochainTensorRepresentativeQuotient J R
  let lift (X : (cochainTensorHomotopyRepresentatives J R).FullSubcategory) :
      (cochainTensorFlatRepresentatives J R).FullSubcategory :=
    ⟨X.obj.as, ((site_derived_tensor_descent_independentCoefficients.{u, v, w, d, 0, 0}
      J R).choose_spec.1 X.obj).1 X.property⟩
  constructor
  · intro τ σ h
    ext X
    exact congrArg (fun t ↦ t.app (lift X.1, lift X.2)) h
  · intro τ
    let σ : U ⟶ V :=
      { app := fun X ↦ τ.app (lift X.1, lift X.2)
        naturality := by
          intro X Y f
          let g₁ : lift X.1 ⟶ lift Y.1 := ObjectProperty.homMk f.1.hom.out
          let g₂ : lift X.2 ⟶ lift Y.2 := ObjectProperty.homMk f.2.hom.out
          have h₁ : p.map g₁ = f.1 := by
            apply ObjectProperty.hom_ext
            exact HomotopyCategory.quotient_map_out _
          have h₂ : p.map g₂ = f.2 := by
            apply ObjectProperty.hom_ext
            exact HomotopyCategory.quotient_map_out _
          have hg : (p.prod p).map (X := (lift X.1, lift X.2))
              (Y := (lift Y.1, lift Y.2)) (g₁, g₂) = f :=
            CategoryTheory.Prod.hom_ext h₁ h₂
          have hn := τ.naturality (X := (lift X.1, lift X.2))
            (Y := (lift Y.1, lift Y.2)) (g₁, g₂)
          change U.map ((p.prod p).map (X := (lift X.1, lift X.2))
              (Y := (lift Y.1, lift Y.2)) (g₁, g₂)) ≫ τ.app (lift Y.1, lift Y.2) =
            τ.app (lift X.1, lift X.2) ≫ V.map ((p.prod p).map
              (X := (lift X.1, lift X.2)) (Y := (lift Y.1, lift Y.2)) (g₁, g₂)) at hn
          rw [hg] at hn
          exact hn }
    exact ⟨σ, rfl⟩

-- Combine homotopy descent with quotient descent, and transport along Q ≅ π ⋙ Qh.
private theorem representative_localization_bijective
    (E : Type e) [Category.{z} E]
    (U V : DerivedCategory (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ×
      DerivedCategory (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ⥤ E) :
    Function.Bijective (fun τ : U ⟶ V ↦ Functor.whiskerLeft
      ((cochainTensorRepresentativeLocalization J R).prod
        (cochainTensorRepresentativeLocalization J R)) τ) := by
  classical
  let A := SheafOfModules.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
  let P := cochainTensorFlatRepresentatives J R
  let p := cochainTensorRepresentativeQuotient J R
  let l := (cochainTensorHomotopyRepresentatives J R).ι ⋙ DerivedCategory.Qh
  let q := cochainTensorRepresentativeLocalization J R
  let α := DerivedCategory.quotientCompQhIso A
  let δ : (p ⋙ l).prod (p ⋙ l) ≅ q.prod q :=
    NatIso.prod (Functor.isoWhiskerLeft P.ι α) (Functor.isoWhiskerLeft P.ι α)
  have hl (U V : DerivedCategory A × DerivedCategory A ⥤ E) :
      Function.Bijective (fun τ : U ⟶ V ↦ Functor.whiskerLeft (l.prod l) τ) := by
    let h := site_derived_tensor_descent_independentCoefficients.{u, v, w, d, e, z} J R
    have hp : h.choose = cochainTensorHomotopyRepresentatives J R := by
      funext X
      apply propext
      exact (h.choose_spec.1 X).trans
        ((site_derived_tensor_descent_independentCoefficients.{u, v, w, d, 0, 0}
          J R).choose_spec.1 X).symm
    have hh := h.choose_spec.2.2.2 E inferInstance U V
    rw [hp] at hh
    exact hh
  let W := (Functor.whiskeringLeft _ _ E).obj ((p ⋙ l).prod (p ⋙ l))
  have hb (U V : DerivedCategory A × DerivedCategory A ⥤ E) :
      Function.Bijective (W.map (X := U) (Y := V)) := by
    exact (representative_quotient_bijective J R E (l.prod l ⋙ U)
      (l.prod l ⋙ V)).comp (hl U V)
  exact (((Functor.FullyFaithful.nonempty_iff_map_bijective W).2 hb).some.ofIso
    ((Functor.whiskeringLeft _ _ E).mapIso δ)).map_bijective U V

-- Lift a normalized comparison through any fully faithful functor. Keeping this
-- cancellation argument abstract avoids unfolding the tensor comparison data.
private theorem normalized_iso_unique
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B) (hF : F.FullyFaithful)
    {X Y : A} {Z : B} (r : Z ≅ F.obj X) (s : Z ≅ F.obj Y) :
    ∃! e : X ≅ Y, r.hom ≫ F.map e.hom = s.hom := by
  let e := hF.preimageIso (r.symm ≪≫ s)
  refine ⟨e, ?_, ?_⟩
  · change r.hom ≫ F.map e.hom = s.hom
    rw [show F.map e.hom = (r.symm ≪≫ s).hom from hF.map_preimage _]
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
  · intro e' he'
    apply Iso.ext
    apply hF.map_injective
    rw [show F.map e.hom = (r.symm ≪≫ s).hom from hF.map_preimage _]
    calc
      F.map e'.hom = r.inv ≫ (r.hom ≫ F.map e'.hom) := by
        rw [Iso.inv_hom_id_assoc]
      _ = r.inv ≫ s.hom := congrArg (r.inv ≫ ·) he'
      _ = (r.symm ≪≫ s).hom := rfl

/-- The canonical cochain tensor comparison, its normalized uniqueness, and full faithfulness
of restriction along the product of the cochain representative localizations.
Source: Stacks 013H, 06YS, 06YT, 06YU; blueprint `prose-03-02`, first sentence
(auxiliary; not a blueprint node).

Proof:
1. The restricted quotient to the homotopy representative category is identity on objects
   and full on morphisms. A transformation on its product restriction descends componentwise:
   represent each homotopy class by a cochain map to check naturality. Restriction and this
   extension are inverse on every set of transformations, for any target category.
2. Apply the arbitrary-transformation descent clause of
   `lem-weil-pbc-site-derived-tensor-descent` to the homotopy representative localization.
   Combine its bijection with Step 1, and conjugate by `DerivedCategory.quotientCompQhIso`
   restricted to the cochain representatives. This gives the last clause below.
3. Compose Q→Qhπ, the inverse cochain/homotopy tensor comparison, the given homotopy
   representative comparison, and T applied to Qhπ→Q in both variables. Every arrow is a
   natural isomorphism, and its component is `cochainTensorRepresentativeArrow`.
   Both representative predicates and both tensors are literally those of the dependencies.
4. For r', full faithfulness lifts r⁻¹;r' and its inverse to transformations on D(R)×D(R).
   Faithfulness shows their composites are identities, so the lift is an isomorphism e.
   Its restriction gives r;e=r'. Any other compatible e has the same restriction after
   cancellation of r, so faithfulness proves equality. No functorial resolutions are used.
-/
theorem cochain_tensor_model_rigidity :
    ∃ r : (((cochainTensorFlatRepresentatives J R).ι.prod
        (cochainTensorFlatRepresentatives J R).ι) ⋙ cochainTensorTotal J R ⋙
          DerivedCategory.Q) ≅
      ((cochainTensorRepresentativeLocalization J R).prod
        (cochainTensorRepresentativeLocalization J R)) ⋙
          siteDerivedTensorIndependentCoefficients J R,
      (∀ X, r.hom.app X = cochainTensorRepresentativeArrow J R X) ∧
      (∀ (T' : (DerivedCategory (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))) ×
        (DerivedCategory (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))) ⥤
        (DerivedCategory (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))))
        (r' : (((cochainTensorFlatRepresentatives J R).ι.prod
          (cochainTensorFlatRepresentatives J R).ι) ⋙ cochainTensorTotal J R ⋙
            DerivedCategory.Q) ≅
          ((cochainTensorRepresentativeLocalization J R).prod
            (cochainTensorRepresentativeLocalization J R)) ⋙ T'),
        ∃! e : siteDerivedTensorIndependentCoefficients J R ≅ T',
          r.hom ≫ Functor.whiskerLeft
            ((cochainTensorRepresentativeLocalization J R).prod
              (cochainTensorRepresentativeLocalization J R)) e.hom = r'.hom) ∧
      (∀ (E : Type e) (_ : Category.{z} E)
        (U V : (DerivedCategory (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))) ×
        (DerivedCategory (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))) ⥤ E),
        Function.Bijective (fun τ : U ⟶ V ↦ Functor.whiskerLeft
          ((cochainTensorRepresentativeLocalization J R).prod
            (cochainTensorRepresentativeLocalization J R)) τ)) := by
  classical
  let A := SheafOfModules.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
  let P := cochainTensorFlatRepresentatives J R
  let p := cochainTensorRepresentativeQuotient J R
  let l := (cochainTensorHomotopyRepresentatives J R).ι ⋙ DerivedCategory.Qh
  let q := cochainTensorRepresentativeLocalization J R
  let T := siteDerivedTensorIndependentCoefficients J R
  let α := DerivedCategory.quotientCompQhIso A
  let δ : (p ⋙ l).prod (p ⋙ l) ≅ q.prod q :=
    NatIso.prod (Functor.isoWhiskerLeft P.ι α) (Functor.isoWhiskerLeft P.ι α)
  let a := Functor.isoWhiskerLeft ((P.ι.prod P.ι) ⋙ cochainTensorTotal J R) α.symm
  let b := Functor.isoWhiskerLeft (P.ι.prod P.ι)
    (Functor.isoWhiskerRight (cochainTensorHomotopyTotalComparison J R).symm
      DerivedCategory.Qh)
  let c := Functor.isoWhiskerLeft (p.prod p)
    (cochainTensorHomotopyDerivedComparison J R)
  let r := a ≪≫ b ≪≫ c ≪≫ Functor.isoWhiskerRight δ T
  refine ⟨r, ?_, ?_, ?_⟩
  · intro X
    rfl
  · intro T' r'
    let W := (Functor.whiskeringLeft _ _ (DerivedCategory A)).obj (q.prod q)
    have hW : W.FullyFaithful :=
      ((Functor.FullyFaithful.nonempty_iff_map_bijective W).2
        (representative_localization_bijective J R (DerivedCategory A))).some
    exact normalized_iso_unique W hW r r'
  · intro E hE U V
    exact representative_localization_bijective J R E U V

end SheafOfModules
