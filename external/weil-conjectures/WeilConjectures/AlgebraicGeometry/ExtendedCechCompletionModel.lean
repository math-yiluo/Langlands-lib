/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.LocalExtendedCechDescription
public import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.CategoryTheory.RingedCompletionUnit
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import WeilConjectures.AlgebraicGeometry.ExtendedCechReflectorCore
import WeilConjectures.AlgebraicGeometry.FunctorialRingComplexCechComparison
import WeilConjectures.AlgebraicGeometry.FunctorialRingComplexDescentData
import WeilConjectures.AlgebraicGeometry.RingComplexGodementFunctorial

/-!
# Global extended Cech model and its derived completion unit

Source: Stacks Project, algebraization.tex, Tags 099E and 099F
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option linter.privateModule false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

private theorem compose_three_squares {D : Type*} [Category D]
    {A₁ A₂ B₁ B₂ C₁ C₂ D₁ D₂ : D}
    {f : A₁ ⟶ A₂} {g : B₁ ⟶ B₂} {h : C₁ ⟶ C₂} {k : D₁ ⟶ D₂}
    {a : A₁ ⟶ B₁} {a' : A₂ ⟶ B₂} {b : B₁ ⟶ C₁} {b' : B₂ ⟶ C₂}
    {c : C₁ ⟶ D₁} {c' : C₂ ⟶ D₂}
    (ha : f ≫ a' = a ≫ g) (hb : g ≫ b' = b ≫ h) (hc : h ≫ c' = c ≫ k) :
    f ≫ (a' ≫ b' ≫ c') = (a ≫ b ≫ c) ≫ k := by
  calc
    _ = (f ≫ a') ≫ b' ≫ c' := by simp only [Category.assoc]
    _ = a ≫ (g ≫ b') ≫ c' := by rw [ha]; simp only [Category.assoc]
    _ = a ≫ b ≫ (h ≫ c') := by rw [hb]; simp only [Category.assoc]
    _ = _ := by rw [hc]; simp only [Category.assoc]

-- Descending evaluation compares several expanded product-localization functors.
set_option backward.isDefEq.respectTransparency false in
/-- The actual augmentation-induced completion unit is natural for every augmented
complex, without a boundedness or completeness hypothesis.

Source: Stacks Project, algebraization.tex, Tag 099F; sites-cohomology.tex, Section 08J7.
(auxiliary; not a blueprint node).

Proof: on complexes, compose the functorial K-injective replacement map with inverse
evaluation at one and the localization factorization of derived internal Hom. Evaluation
at one commutes with postcomposition, so this is a natural transformation on complexes.
Fully faithful whiskering with localization descends it to the derived category. Its
component on each chosen localization representative equals ringedDerivedHomUnit by
naturality at that representative isomorphism. Precomposition with the augmentation
commutes with every postcomposition map in the internal-Hom bifunctor. Composing the
two squares proves the displayed equation for the actual completion unit. -/
theorem completion_unit_natural
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    (K : ringedSiteComplex O) (ε : K ⟶ ringedSiteRingComplex O)
    (E E' : ringedSiteDerived O) (g : E ⟶ E') :
    ringedCechCompletionUnit O K ε E ≫ (ringedCechCompletionFunctor O K).map g =
      g ≫ ringedCechCompletionUnit O K ε E' := by
  let A := ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let Q := DerivedCategory.Q (C := A)
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η := CochainComplex.toKInjectiveResolution.{u} A
  let H := derivedInternalHom J O
  let F := ringedCechCompletionFunctor O (ringedSiteRingComplex O)
  let c := Localization.fac
    ((𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := O)) ⋙ Q)
    (derivedInternalHom_inverts J O I η (fun M ↦
      ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ M).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} _ M⟩))
    (Q.op.prod Q)
  let a : (homComplexFunctor (R := O)).obj
      (Opposite.op (ringedSiteRingComplex O)) ≅ 𝟭 _ :=
    NatIso.ofComponents (ringedHomUnitEvaluationIso O) (by
      intro M N f
      apply HomologicalComplex.hom_ext
      intro n
      exact homComplex_unit_evaluation_naturality J O f n)
  let t : Q ⋙ 𝟭 _ ⟶ Q ⋙ F :=
    { app := fun M ↦ Q.map (η.app M) ≫
        Q.map (a.inv.app (I.obj M)) ≫ (c.inv.app (Opposite.op (ringedSiteRingComplex O), M))
      naturality := by
        intro M N f
        dsimp only [Functor.comp_map, Functor.id_map, F, ringedCechCompletionFunctor]
        have hc := c.inv.naturality
          (X := (Opposite.op (ringedSiteRingComplex O), M))
          (Y := (Opposite.op (ringedSiteRingComplex O), N)) (𝟙 _, f)
        have ha := a.inv.naturality (I.map f)
        have hη := η.naturality f
        dsimp at hc ha hη
        simp only [Functor.map_id, NatTrans.id_app, Category.id_comp, op_id] at hc
        change Q.map f ≫ (Q.map (η.app N) ≫ Q.map (a.inv.app (I.obj N)) ≫
            c.inv.app (Opposite.op (ringedSiteRingComplex O), N)) =
          (Q.map (η.app M) ≫ Q.map (a.inv.app (I.obj M)) ≫
            c.inv.app (Opposite.op (ringedSiteRingComplex O), M)) ≫
              H.map
                (X := (Opposite.op (Q.obj (ringedSiteRingComplex O)), Q.obj M))
                (Y := (Opposite.op (Q.obj (ringedSiteRingComplex O)), Q.obj N))
                (𝟙 _, Q.map f)
        have hη' : Q.map f ≫ Q.map (η.app N) = Q.map (η.app M) ≫ Q.map (I.map f) := by
          simpa only [← Q.map_comp] using congrArg Q.map hη
        have ha' : Q.map (I.map f) ≫ Q.map (a.inv.app (I.obj N)) =
            Q.map (a.inv.app (I.obj M)) ≫
              Q.map ((homComplexFunctor (R := O)).obj
                (Opposite.op (ringedSiteRingComplex O)) |>.map (I.map f)) := by
          simpa only [← Q.map_comp] using congrArg Q.map ha
        exact compose_three_squares hη' ha' hc }
  let W := HomologicalComplex.quasiIso A (ComplexShape.up ℤ)
  let full := Localization.fullyFaithfulWhiskeringLeft Q W (DerivedCategory A)
  let d : 𝟭 (DerivedCategory A) ⟶ F := full.preimage t
  have hd (M : CochainComplex A ℤ) : d.app (Q.obj M) = t.app M :=
    congrArg (fun z ↦ z.app M) (full.map_preimage t)
  have hu (X : ringedSiteDerived O) : ringedDerivedHomUnit O X = d.app X := by
    let e := Q.objObjPreimageIso X
    have hn := d.naturality e.hom
    dsimp at hn
    rw [← cancel_epi e.hom]
    rw [hn, hd]
    simp only [ringedDerivedHomUnit, t, a, e, Q, I, η, c,
      Category.assoc, Iso.hom_inv_id_assoc]
    rfl
  have hn := d.naturality g
  change (ringedDerivedHomUnit O E ≫ H.map
      (X := (Opposite.op (Q.obj (ringedSiteRingComplex O)), E))
      (Y := (Opposite.op (Q.obj K), E)) ((Q.map ε).op, 𝟙 E)) ≫
      H.map (X := (Opposite.op (Q.obj K), E))
        (Y := (Opposite.op (Q.obj K), E')) (𝟙 _, g) =
    g ≫ ringedDerivedHomUnit O E' ≫ H.map
      (X := (Opposite.op (Q.obj (ringedSiteRingComplex O)), E'))
      (Y := (Opposite.op (Q.obj K), E')) ((Q.map ε).op, 𝟙 E')
  have hs : H.map
      (X := (Opposite.op (Q.obj (ringedSiteRingComplex O)), E))
      (Y := (Opposite.op (Q.obj K), E)) ((Q.map ε).op, 𝟙 E) ≫
      H.map (X := (Opposite.op (Q.obj K), E))
        (Y := (Opposite.op (Q.obj K), E')) (𝟙 _, g) =
      H.map (X := (Opposite.op (Q.obj (ringedSiteRingComplex O)), E))
        (Y := (Opposite.op (Q.obj (ringedSiteRingComplex O)), E')) (𝟙 _, g) ≫
      H.map (X := (Opposite.op (Q.obj (ringedSiteRingComplex O)), E'))
        (Y := (Opposite.op (Q.obj K), E')) ((Q.map ε).op, 𝟙 E') := by
    rw [← H.map_comp, ← H.map_comp]
    congr 1
    ext <;> simp
  rw [Category.assoc, hs, ← Category.assoc, hu E, hu E']
  change (d.app E ≫ F.map g) ≫ _ = _
  rw [← hn, Category.assoc]
  rfl

private theorem unit_isIso_of_complete_universal
    {D : Type*} [Category D] (P : D → Prop) (F : D ⥤ D)
    (η : ∀ E, E ⟶ F.obj E)
    (hc : ∀ E, P (F.obj E))
    (hu : ∀ E L, P L → Function.Bijective (fun h : F.obj E ⟶ L ↦ η E ≫ h))
    (E : D) (hE : P E) : IsIso (η E) := by
  obtain ⟨r, hr⟩ := (hu E E hE).2 (𝟙 E)
  have hs : r ≫ η E = 𝟙 (F.obj E) := by
    apply (hu E (F.obj E) (hc E)).1
    simp only [← Category.assoc, hr, Category.id_comp, Category.comp_id]
  exact ⟨⟨r, hr, hs⟩⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The global augmented model exists.
Source: Stacks Project, algebraization.tex, Tag 099E.
(auxiliary; not a blueprint node).

Proof: take the cover indexed by all specified finite generating lists. Sheafify the
concrete Godement ring family on each slice. The independence-of-ideals descent theorem
and effective gluing of augmented complexes give a global augmented complex. For any
generating list, compose its derived Čech comparison with the inverse local gluing
isomorphism and the comparison for derived restriction. Naturality of the latter and
the two augmentation squares give the required augmented local description.
-/
theorem exists_ringedExtendedCech_global_model
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [Mono ι] [I.IsFiniteType] :
    ∃ (K : ringedSiteComplex O) (ε : K ⟶ ringedSiteRingComplex O),
      HasLocalExtendedCechDescription O I ι K ε := by
  let KR : AlgebraicGeometry.RingComplexFamily.{u} :=
    fun A I ↦ AlgebraicGeometry.ringComplexGodement A I.val
  let εR : AlgebraicGeometry.RingComplexAugmentations KR :=
    fun A I ↦ AlgebraicGeometry.ringComplexGodementAugmentation A I.val
  obtain ⟨m, hm⟩ := AlgebraicGeometry.ringComplex_godement_functorial.{u}
  obtain ⟨D⟩ := exists_ringFamily_descentData O I ι KR εR m hm
  obtain ⟨K, ε, e, he⟩ := SheafOfModules.exists_augmentedComplex_of_glueData
    (coversTop_ringedIdealGeneratingIndex O I ι) D
  refine ⟨K, ε, ?_⟩
  intro U r f hf
  let p : RingedIdealGeneratingIndex O I ι := ⟨U, r, f, hf⟩
  obtain ⟨β, hβ⟩ := ringFamilySheafModel_cech (O.over U) m hm r
    (fun i ↦ ringedSliceSection O U (f i))
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
  let : HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over U)) :=
    inferInstanceAs (HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U))))
  let F := SheafOfModules.overFunctor.{u} R U
  let fac := F.mapDerivedCategoryFactors
  let a := ringedRestrictionRingComplexIso O U
  have hε : (e p).inv ≫ (F.mapHomologicalComplex (.up ℤ)).map ε ≫ a.hom =
      (ringFamilySliceModel O KR εR m hm I ι p).2 := by
    rw [← he p]
    simp only [a, p, Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
  refine ⟨β ≪≫ DerivedCategory.Q.mapIso (e p).symm ≪≫ (fac.app K).symm, ?_⟩
  change (β.hom ≫ DerivedCategory.Q.map (e p).inv ≫ (fac.app K).inv) ≫
      F.mapDerivedCategory.map (DerivedCategory.Q.map ε) ≫
      (fac.app (ringedSiteRingComplex O)).hom ≫ DerivedCategory.Q.map a.hom = _
  calc
    _ = β.hom ≫ DerivedCategory.Q.map
        ((e p).inv ≫ (F.mapHomologicalComplex (.up ℤ)).map ε ≫ a.hom) := by
      simp only [Functor.map_comp, Category.assoc]
      have hn := F.mapDerivedCategoryFactors_hom_naturality ε
      change F.mapDerivedCategory.map (DerivedCategory.Q.map ε) ≫
        (fac.app (ringedSiteRingComplex O)).hom =
        (fac.app K).hom ≫
          DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map ε) at hn
      simpa only [Category.assoc, Iso.inv_hom_id_assoc] using congrArg
        (fun z ↦ β.hom ≫ DerivedCategory.Q.map (e p).inv ≫
          (fac.app K).inv ≫ z ≫ DerivedCategory.Q.map a.hom) hn
    _ = _ := by rw [hε]; exact hβ

/-- The internal-Hom reflector properties of every local extended Cech model.
Source: Stacks Project, algebraization.tex, Tags 099B and 099F.
(auxiliary; not a blueprint node).

Proof: on each finite-generator slice, contract the localized extended Cech complex, filter the
augmentation cone by its positive localization terms, and use the internal-Hom tensor identity
to prove orthogonality. Globalize by restriction and use zeroth derived global sections for the
mapping bijection; the unit isomorphism follows from the resulting universal property.
-/
theorem ringedExtendedCech_reflector_properties
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [Mono ι] [I.IsFiniteType]
    (K : ringedSiteComplex O) (ε : K ⟶ ringedSiteRingComplex O)
    (hK : HasLocalExtendedCechDescription O I ι K ε) :
    (∀ E : ringedSiteDerived O,
      IsLocallyDerivedRingedIdealComplete O I ι ((ringedCechCompletionFunctor O K).obj E)) ∧
    (∀ (E E' : ringedSiteDerived O) (g : E ⟶ E'),
      ringedCechCompletionUnit O K ε E ≫ (ringedCechCompletionFunctor O K).map g =
        g ≫ ringedCechCompletionUnit O K ε E') ∧
    (∀ (E L : ringedSiteDerived O), IsLocallyDerivedRingedIdealComplete O I ι L →
      Function.Bijective
        (fun h : (ringedCechCompletionFunctor O K).obj E ⟶ L ↦
          ringedCechCompletionUnit O K ε E ≫ h)) ∧
    (∀ E : ringedSiteDerived O, IsLocallyDerivedRingedIdealComplete O I ι E →
      IsIso (ringedCechCompletionUnit O K ε E)) := by
  obtain ⟨hcomplete, hbijective⟩ :=
    ringedExtendedCech_reflector_core J O I ι K ε hK
  refine ⟨hcomplete, ?_, hbijective, ?_⟩
  · exact completion_unit_natural O K ε
  · intro E hE
    exact unit_isIso_of_complete_universal
      (IsLocallyDerivedRingedIdealComplete O I ι)
      (ringedCechCompletionFunctor O K)
      (ringedCechCompletionUnit O K ε)
      hcomplete hbijective E hE

end CategoryTheory
