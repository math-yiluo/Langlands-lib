/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleOpenCohomologyComparison
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerCoefficients

/-! # Integral open–closed sequence with its sections normalization

Source: Stacks Project, Tags 095L and 03F3, and the Cartier proof (G1).
(auxiliary; not a blueprint node). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

private def restrictConstant (X : Scheme.{u}) (W : X.Opens)
    (M : AddCommGrpCat.{u + 1}) :
    (constantSheaf W.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M ⟶
      (openImmersionRestriction AddCommGrpCat.{u + 1} W.ι).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) := by
  let L := MorphismProperty.Over.map ⊤ (inferInstance : Etale W.ι)
  exact ⟨sheafifyLift _ (Functor.whiskerLeft L.op
    (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)))
      ((openImmersionRestriction AddCommGrpCat.{u + 1} W.ι).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)).property⟩

private theorem restrictConstant_unit (X : Scheme.{u}) (W : X.Opens)
    (M : AddCommGrpCat.{u + 1}) :
    toSheafify W.toScheme.smallEtaleTopology ((Functor.const W.toScheme.Etaleᵒᵖ).obj M) ≫
      (restrictConstant X W M).hom =
      Functor.whiskerLeft (MorphismProperty.Over.map ⊤ (inferInstance : Etale W.ι)).op
        (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)) := by
  apply toSheafify_sheafifyLift

private theorem restrictConstant_isIso (X : Scheme.{u}) (W : X.Opens)
    (M : AddCommGrpCat.{u + 1}) : IsIso (restrictConstant X W M) := by
  have : W.toScheme.smallEtaleTopology.HasSheafCompose
      (forget AddCommGrpCat.{u + 1}) := by
    have : PreservesLimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{u + 1}) :=
      preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
    infer_instance
  rw [← Sheaf.isLocallyBijective_iff_isIso (restrictConstant X W M)]
  have : X.smallEtaleTopology.HasSheafCompose
      (forget AddCommGrpCat.{u + 1}) := by
    have : PreservesLimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{u + 1}) :=
      preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
    infer_instance
  have : W.toScheme.smallEtaleTopology.WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} := inferInstance
  have : X.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1} := inferInstance
  let L := MorphismProperty.Over.map ⊤ (inferInstance : Etale W.ι)
  have : L.IsCocontinuous W.toScheme.smallEtaleTopology X.smallEtaleTopology :=
    Scheme.isCocontinuous_overMap (inferInstance : Etale W.ι) le_rfl
  have h₁ : Presheaf.IsLocallyInjective W.toScheme.smallEtaleTopology
      (Functor.whiskerLeft L.op
        (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M))) :=
    Presheaf.isLocallyInjective_whisker W.toScheme.smallEtaleTopology
      X.smallEtaleTopology L _
  have h₂ : Presheaf.IsLocallySurjective W.toScheme.smallEtaleTopology
      (Functor.whiskerLeft L.op
        (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M))) :=
    Presheaf.isLocallySurjective_whisker W.toScheme.smallEtaleTopology
      X.smallEtaleTopology L _
  rw [← restrictConstant_unit] at h₁ h₂
  have h₃ : Presheaf.IsLocallyInjective W.toScheme.smallEtaleTopology
      (toSheafify W.toScheme.smallEtaleTopology
        ((Functor.const W.toScheme.Etaleᵒᵖ).obj M)) :=
    (W.toScheme.smallEtaleTopology.W_toSheafify _).isLocallyInjective
  have h₄ : Presheaf.IsLocallySurjective W.toScheme.smallEtaleTopology
      (toSheafify W.toScheme.smallEtaleTopology
        ((Functor.const W.toScheme.Etaleᵒᵖ).obj M)) :=
    (W.toScheme.smallEtaleTopology.W_toSheafify _).isLocallySurjective
  exact ⟨(Presheaf.comp_isLocallyInjective_iff _ _ _).mp h₁,
    (Presheaf.comp_isLocallySurjective_iff _ _ _).mp h₂⟩

private theorem restrictedSectionsEquiv_apply {X : Scheme.{u}} (W : X.Opens)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (f : EtaleOpenComparison.integerSheaf W.toScheme ⟶
      (openImmersionRestriction AddCommGrpCat.{u + 1} W.ι).obj G) :
    EtaleOpenComparison.restrictedSectionsEquiv W.ι G f =
      G.obj.map ((MorphismProperty.Over.isoMk (Iso.refl W.toScheme)
        (Category.id_comp W.ι)).inv.op)
        (f.hom.app (op (Scheme.Etale.mk (𝟙 W.toScheme)))
          ((toSheafify W.toScheme.smallEtaleTopology
            ((Functor.const W.toScheme.Etaleᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
                (op (Scheme.Etale.mk (𝟙 W.toScheme))) ⟨1⟩)) := by
  dsimp only [EtaleOpenComparison.restrictedSectionsEquiv, AddEquiv.trans_apply,
    Adjunction.homAddEquiv_apply]
  rw [constantSheafAdj_homEquiv_apply, AddCommGrpCat.uliftZMultiplesAddEquiv_eq]
  exact Iso.addCommGroupIsoToAddEquiv_apply _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The integral open–closed sequence has an open source representing sections,
with its inclusion corresponding to the constant section one.
Source: Stacks Project, Tags 095L and 03F3.
(auxiliary; not a blueprint node)
Proof: apply the open–closed short exact sequence to the integer constant sheaf.
Identify its closed restriction with the integer constant on D. Replace open
pullback by literal restriction. Its constant comparison is an isomorphism:
whiskering the sheafification unit is locally bijective, and the unit on the open
is locally bijective as well. The lower-shriek adjunction and the constant-sheaf
sections adjunction give the additive sections equivalence. Adjunction naturality
proves naturality in the target. The counit transposes to identity; evaluating the
constant comparison on one and using sheafification-unit naturality gives the
specified normalization. These arguments cover empty opens and empty schemes. -/
theorem exists_integral_openClosed_sections {D X : Scheme.{u}} (i : D ⟶ X)
    [IsClosedImmersion i] (W : X.Opens) (hW : (W : Set X) = (Set.range i.base)ᶜ) :
    let P := EtaleOpenComparison.integerSheaf X
    let Q := (lowerStar AddCommGrpCat.{u + 1} i).obj (EtaleOpenComparison.integerSheaf D)
    let q : P ⟶ Q := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).homEquiv _ _
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} i).app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom
    ∃ (L : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (t : L ⟶ P)
      (htq : t ≫ q = 0), (ShortComplex.mk t q htq).ShortExact ∧
      ∃ η : ∀ A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
        (L ⟶ A) ≃+ A.obj.obj (op (Scheme.Etale.mk W.ι)),
        (∀ {A B} (f : A ⟶ B) (g : L ⟶ A),
          η B (g ≫ f) = f.hom.app (op (Scheme.Etale.mk W.ι)) (η A g)) ∧
        η P t = (toSheafify X.smallEtaleTopology
          ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
            (op (Scheme.Etale.mk W.ι)) ⟨1⟩ := by
  intro P Q q
  let R := openImmersionRestriction AddCommGrpCat.{u + 1} W.ι
  let F := openImmersionLowerShriek AddCommGrpCat.{u + 1} W.ι
  let adj := openImmersionLowerShriekAdjunction AddCommGrpCat.{u + 1} W.ι
  let c := upperStarIsoOpenImmersionRestriction AddCommGrpCat.{u + 1} W.ι
  have hic : Set.range i.base = (Set.range W.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι, hW, compl_compl]
  let S := openClosedShortComplex AddCommGrpCat.{u + 1} W.ι i
    (disjoint_range_of_range_eq_compl W.ι i hic) P
  have hS : S.ShortExact := shortExact_openClosedShortComplex
    AddCommGrpCat.{u + 1} W.ι i P hic
  let k := restrictConstant X W (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  have hk : IsIso k := restrictConstant_isIso X W _
  let e₁ := F.mapIso (c.app P ≪≫ (asIso k).symm)
  let e₃ := (lowerStar AddCommGrpCat.{u + 1} i).mapIso
    ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} i).app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
  let t := F.map k ≫ adj.counit.app P
  have ht : e₁.hom ≫ t = S.f := by
    change F.map ((c.app P).hom ≫ inv k) ≫ (F.map k ≫ adj.counit.app P) = _
    rw [F.map_comp, Category.assoc, ← Category.assoc (F.map (inv k)),
      ← F.map_comp, IsIso.inv_hom_id, F.map_id, Category.id_comp]
    rfl
  have hq : S.g ≫ e₃.hom = q := by
    change _ = (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).homEquiv _ _ _
    rw [Adjunction.homEquiv_unit]
    rfl
  have htq : t ≫ q = 0 := by
    apply (cancel_epi e₁.hom).1
    rw [← Category.assoc, ht, ← hq, ← Category.assoc, S.zero, zero_comp, comp_zero]
  have hT : (ShortComplex.mk t q htq).ShortExact :=
    ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk (S₁ := S) (S₂ := ShortComplex.mk t q htq)
        e₁ (Iso.refl _) e₃ (by simpa using ht) (by simpa using hq.symm)) hS
  let η (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
      (F.obj (EtaleOpenComparison.integerSheaf W.toScheme) ⟶ A) ≃+
        A.obj.obj (op (Scheme.Etale.mk W.ι)) :=
    (adj.homAddEquiv (EtaleOpenComparison.integerSheaf W.toScheme) A).trans
      (EtaleOpenComparison.restrictedSectionsEquiv W.ι A)
  refine ⟨F.obj (EtaleOpenComparison.integerSheaf W.toScheme), t, htq, hT, η, ?_, ?_⟩
  · intro A B f g
    change EtaleOpenComparison.restrictedSectionsEquiv W.ι B
      (adj.homEquiv (EtaleOpenComparison.integerSheaf W.toScheme) B (g ≫ f)) = _
    exact (congrArg (EtaleOpenComparison.restrictedSectionsEquiv W.ι B)
      (adj.homEquiv_naturality_right g f)).trans
      (EtaleOpenComparison.restrictedSectionsEquiv_naturality W.ι f
        (adj.homEquiv (EtaleOpenComparison.integerSheaf W.toScheme) A g))
  · have ht' : t = (adj.homEquiv (EtaleOpenComparison.integerSheaf W.toScheme) P).symm k := by
      rw [Adjunction.homEquiv_counit]
    change EtaleOpenComparison.restrictedSectionsEquiv W.ι P
      (adj.homEquiv (EtaleOpenComparison.integerSheaf W.toScheme) P t) = _
    rw [ht', Equiv.apply_symm_apply]
    rw [restrictedSectionsEquiv_apply]
    have hu := congr_app (restrictConstant_unit X W
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
      (op (Scheme.Etale.mk (𝟙 W.toScheme)))
    have hue := ConcreteCategory.congr_hom hu (ULift.up 1)
    let e : Scheme.Etale.mk (𝟙 W.toScheme ≫ W.ι) ≅ Scheme.Etale.mk W.ι :=
      MorphismProperty.Over.isoMk (Iso.refl W.toScheme) (Category.id_comp W.ι)
    have hn := ConcreteCategory.congr_hom
      ((toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).naturality
        e.inv.op) (ULift.up 1)
    exact (congrArg (fun x => P.obj.map e.inv.op x) hue).trans hn.symm

end AlgebraicGeometry.Etale
