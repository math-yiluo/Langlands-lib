/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Pi.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.LocalProperties
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Complement
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful

/-!
# Abelian etale sheaves on a finite coproduct

Source: Stacks Project, Etale Cohomology, proof of Lemma 0A5B, first paragraph,
finite disjoint-union reduction (blueprint: lem-weil-pbc-etale-sheaf-clopen-product).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private theorem single_product_projection {D : Type*} [Category D] [HasZeroMorphisms D]
    {I : Type*} (G : I → D) [HasProduct G] (i : I)
    (h : ∀ j, j ≠ i → IsZero (G j)) : IsIso (Pi.π G i) := by
  classical
  let q : G i ⟶ ∏ᶜ G := Pi.lift (fun j ↦ if e : i = j then eqToHom (congrArg G e) else 0)
  refine ⟨⟨q, ?_, ?_⟩⟩
  · apply Pi.hom_ext
    intro j
    by_cases e : j = i
    · subst j
      simp [q]
    · exact (h j e).eq_of_tgt _ _
  · simp [q]

private theorem component_open {I : Type v} [Finite I] {X : Scheme.{u}}
    (C : I → Scheme.{u}) (ι : ∀ i, C i ⟶ X) (hc : IsColimit (Cofan.mk X ι)) (i : I) :
    IsOpenImmersion (ι i) := by
  let e := (coproductIsCoproduct C).coconePointUniqueUpToIso hc
  have he : Sigma.ι C i ≫ e.hom = ι i := by
    exact IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _
  rw [← he]
  infer_instance

private theorem component_disjoint {I : Type v} [Finite I] {X : Scheme.{u}}
    (C : I → Scheme.{u}) (ι : ∀ i, C i ⟶ X) (hc : IsColimit (Cofan.mk X ι))
    (i j : I) (hij : i ≠ j) : Disjoint (Set.range (ι i).base) (Set.range (ι j).base) := by
  let e := (coproductIsCoproduct C).coconePointUniqueUpToIso hc
  have he (i : I) : Sigma.ι C i ≫ e.hom = ι i := by
    exact IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _
  rw [← he i, ← he j]
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx⟩ ⟨y, hy⟩
  have hxy : Sigma.ι C i x = Sigma.ι C j y := by
    apply e.hom.homeomorph.injective
    exact hx.trans hy.symm
  have h := (sigmaι_eq_iff C i j x y).mp hxy
  exact hij (Sigma.mk.inj_iff.mp h).1

private theorem components_cover {I : Type v} [Finite I] {X : Scheme.{u}}
    (C : I → Scheme.{u}) (ι : ∀ i, C i ⟶ X) (hc : IsColimit (Cofan.mk X ι))
    [∀ i, IsOpenImmersion (ι i)] :
    X.smallEtaleTopology.CoversTop (fun i ↦ Scheme.Etale.mk (ι i)) := by
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal X.smallEtaleTopology
    (Scheme.Etale.mk (𝟙 X)) (MorphismProperty.Over.mkIdTerminal (@Etale) X)]
  let f (i : I) : Scheme.Etale.mk (ι i) ⟶ Scheme.Etale.mk (𝟙 X) :=
    MorphismProperty.Over.homMk (ι i) (by simp)
  apply X.smallEtaleTopology.superset_covering _
    ((Scheme.ofArrows_mem_smallEtaleTopology_iff f).mpr ?_)
  · rintro Y g ⟨i, b, e⟩
    rcases e with ⟨g', ⟨j⟩, hgj⟩
    exact ⟨j, ⟨b⟩⟩
  · apply Set.eq_univ_of_forall
    intro x
    let e := (coproductIsCoproduct C).coconePointUniqueUpToIso hc
    obtain ⟨y, hy⟩ := (sigmaOpenCover C).covers (e.inv x)
    refine Set.mem_iUnion.mpr ⟨(sigmaOpenCover C).idx (e.inv x), y, ?_⟩
    have he (i : I) : Sigma.ι C i ≫ e.hom = ι i :=
      IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _
    change (Sigma.ι C _) y = e.inv x at hy
    change (ι _) y = x
    rw [← he, Scheme.Hom.comp_apply, hy]
    simp [← Scheme.Hom.comp_apply]

private theorem iso_of_component_iso {I : Type v} [Finite I] {X : Scheme.{u}}
    (C : I → Scheme.{u}) (ι : ∀ i, C i ⟶ X) (hc : IsColimit (Cofan.mk X ι))
    [∀ i, IsOpenImmersion (ι i)] {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : F ⟶ G) (h : ∀ i, IsIso ((Etale.upperStar AddCommGrpCat.{u + 1} (ι i)).map φ)) :
    IsIso φ := by
  apply Sheaf.isIso_of_coversTop (components_cover C ι hc)
  intro i
  have hQ : IsIso ((Etale.openImmersionRestriction AddCommGrpCat.{u + 1} (ι i)).map φ) := by
    let e := Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} (ι i)
      (inferInstance : Etale (ι i))
    have : IsIso ((Etale.upperStar AddCommGrpCat.{u + 1} (ι i)).map φ) := h i
    rw [← isIso_comp_left_iff (e.hom.app F)]
    erw [← e.hom.naturality φ]
    infer_instance
  have happ : ∀ T, IsIso (((X.smallEtaleTopology.overPullback AddCommGrpCat.{u + 1}
      (Scheme.Etale.mk (ι i))).map φ).hom.app T) := by
    rintro ⟨T⟩
    let V : (C i).Etale := Scheme.Etale.mk T.hom.left
    let W : X.Etale :=
      (MorphismProperty.Over.map ⊤ (inferInstance : Etale (ι i))).obj V
    let e : W ≅ T.left := MorphismProperty.Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ T.left.hom = T.hom.left ≫ ι i
      simpa using (MorphismProperty.Over.w T.hom).symm)
    have : IsIso (φ.hom.app (op W)) :=
      inferInstanceAs (IsIso (((Etale.openImmersionRestriction
        AddCommGrpCat.{u + 1} (ι i)).map φ).hom.app (op V)))
    change IsIso (φ.hom.app (op T.left))
    rw [← isIso_comp_left_iff (F.obj.map e.inv.op), φ.hom.naturality]
    infer_instance
  have : IsIso (((X.smallEtaleTopology.overPullback AddCommGrpCat.{u + 1}
    (Scheme.Etale.mk (ι i))).map φ).hom) := NatIso.isIso_of_isIso_app _
  have : IsIso ((sheafToPresheaf (X.smallEtaleTopology.over (Scheme.Etale.mk (ι i)))
      AddCommGrpCat.{u + 1}).map
      ((X.smallEtaleTopology.overPullback AddCommGrpCat.{u + 1}
        (Scheme.Etale.mk (ι i))).map φ)) := this
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

private theorem clopen_reconstruction_unit {I : Type v} [Finite I] {X : Scheme.{u}}
    (C : I → Scheme.{u}) (ι : ∀ i, C i ⟶ X) (hc : IsColimit (Cofan.mk X ι)) :
    let R := Functor.pi' (fun i ↦ Etale.upperStar AddCommGrpCat.{u + 1} (ι i))
    let S := Functor.pi (fun i ↦ Etale.lowerStar AddCommGrpCat.{u + 1} (ι i)) ⋙
      Pi.functor I
    Nonempty (𝟭 _ ≅ R ⋙ S)  := by
  classical
  let (i : I) : IsOpenImmersion (ι i) := component_open C ι hc i
  let R := Functor.pi' (fun i ↦ Etale.upperStar AddCommGrpCat.{u + 1} (ι i))
  let S := Functor.pi (fun i ↦ Etale.lowerStar AddCommGrpCat.{u + 1} (ι i)) ⋙ Pi.functor I
  let η : 𝟭 _ ⟶ R ⋙ S :=
    { app := fun F ↦ Pi.lift (fun i ↦
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (ι i)).unit.app F)
      naturality := by
        intro F G f
        apply Pi.hom_ext
        intro i
        dsimp [R, S]
        simp only [Category.assoc, Pi.lift_comp_π, Pi.map_π, Pi.lift_comp_π_assoc]
        exact (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
          (ι i)).unit.naturality f }
  have hη (F) : IsIso (η.app F) := by
    apply iso_of_component_iso C ι hc
    intro i
    let U := Etale.upperStar AddCommGrpCat.{u + 1} (ι i)
    let Gi := fun j ↦ (Etale.lowerStar AddCommGrpCat.{u + 1} (ι j)).obj ((R.obj F) j)
    have hz (j : I) (hji : j ≠ i) : IsZero (U.obj (Gi j)) := by
      exact IsZero.of_iso
        (Etale.isZero_openImmersionRestriction_lowerStar AddCommGrpCat.{u + 1}
          (ι j) (ι i) (component_disjoint C ι hc j i hji) ((R.obj F) j))
        ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
          (ι i) inferInstance).app (Gi j))
    have : IsIso (Pi.π (fun j ↦ U.obj (Gi j)) i) := single_product_projection _ i hz
    have : PreservesLimitsOfShape (Discrete I) U := by infer_instance
    have : IsIso (U.map (Pi.π Gi i)) := by
      rw [← piComparison_comp_π]
      infer_instance
    rw [← isIso_comp_right_iff _ (U.map (Pi.π Gi i)), ← U.map_comp]
    have he : η.app F ≫ Pi.π Gi i =
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (ι i)).unit.app F := by
      exact Pi.lift_comp_π _ _
    rw [he]
    infer_instance
  have : ∀ F, IsIso (η.app F) := hη
  have : IsIso η := NatIso.isIso_of_isIso_app η
  exact ⟨asIso η⟩


private theorem clopen_reconstruction_counit {I : Type v} [Finite I] {X : Scheme.{u}}
    (C : I → Scheme.{u}) (ι : ∀ i, C i ⟶ X) (hc : IsColimit (Cofan.mk X ι)) :
    let R := Functor.pi' (fun i ↦ Etale.upperStar AddCommGrpCat.{u + 1} (ι i))
    let S := Functor.pi (fun i ↦ Etale.lowerStar AddCommGrpCat.{u + 1} (ι i)) ⋙
      Pi.functor I
    Nonempty (S ⋙ R ≅ 𝟭 _) := by
  classical
  let S := Functor.pi (fun i ↦ Etale.lowerStar AddCommGrpCat.{u + 1} (ι i)) ⋙ Pi.functor I
  let R := Functor.pi' (fun i ↦ Etale.upperStar AddCommGrpCat.{u + 1} (ι i))
  let (i : I) : IsOpenImmersion (ι i) := component_open C ι hc i
  let ε : S ⋙ R ⟶ 𝟭 _ :=
    { app := fun G i ↦
        (Etale.upperStar AddCommGrpCat.{u + 1} (ι i)).map (Pi.π _ i) ≫
          (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (ι i)).counit.app (G i)
      naturality := by
        intro G H f
        funext i
        dsimp [S, R]
        simp only [← Functor.map_comp_assoc]
        erw [Pi.map_π]
        simp only [Functor.map_comp, Category.assoc]
        exact congrArg (fun k ↦ _ ≫ k)
          ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
            (ι i)).counit.naturality (f i)) }
  have hε (G) (i : I) : IsIso (ε.app G i) := by
    let U := Etale.upperStar AddCommGrpCat.{u + 1} (ι i)
    let Gi := fun j ↦ (Etale.lowerStar AddCommGrpCat.{u + 1} (ι j)).obj (G j)
    have hz (j : I) (hji : j ≠ i) : IsZero (U.obj (Gi j)) := by
      exact IsZero.of_iso
        (Etale.isZero_openImmersionRestriction_lowerStar AddCommGrpCat.{u + 1}
          (ι j) (ι i) (component_disjoint C ι hc j i hji) (G j))
        ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
          (ι i) inferInstance).app (Gi j))
    have : IsIso (Pi.π (fun j ↦ U.obj (Gi j)) i) := single_product_projection _ i hz
    have : PreservesLimitsOfShape (Discrete I) U := by infer_instance
    have : IsIso (U.map (Pi.π Gi i)) := by
      rw [← piComparison_comp_π]
      infer_instance
    change IsIso (U.map (Pi.π Gi i) ≫
      (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (ι i)).counit.app (G i))
    infer_instance
  have hεG (G) : IsIso (ε.app G) := by
    let (i : I) : IsIso (ε.app G i) := hε G i
    exact ⟨⟨(fun i ↦ inv (ε.app G i)), funext (fun i ↦ by simp),
      funext (fun i ↦ by simp)⟩⟩
  have : ∀ G, IsIso (ε.app G) := hεG
  have : IsIso ε := NatIso.isIso_of_isIso_app ε
  exact ⟨asIso ε⟩


/-- Restriction to the clopen components of a finite coproduct is an equivalence of
abelian etale sheaf categories, and global sections are naturally the product of
component global sections. The coproduct is any coproduct cocone
`hc : IsColimit (Cofan.mk X ι)` (as in lem-weil-pbc-direct-image-split-cover-product), its
coprojections open and closed by `lem-weil-pbc-scheme-coproduct-family`; global sections
are sections at `Scheme.Etale.mk (𝟙 X)`. Source: Stacks Project, proof of Lemma 0A5B,
first paragraph
(blueprint: lem-weil-pbc-etale-sheaf-clopen-product).

Proof:
1. For an etale object U over the coproduct, pull back the coprojections to obtain
pairwise disjoint clopen U_i covering U (`lem-weil-pbc-scheme-coproduct-family`). The
sheaf equalizer condition (`situation-conventions`) gives F(U) = product F(U_i);
the empty covering gives F(empty) = 0.
2. Localization of the etale site at a component is its small etale site
(`lem-weil-pbc-etale-site-localization-open`). Inverse image is restriction, naturally
in the sheaf (`lem-weil-pbc-etale-inverse-image-restriction`), identifying F(U_i) with
sections of the component inverse image.
3. Conversely, reconstruct a sheaf from G_i by assigning to U the product of
G_i(U x_C C_i). Products preserve the sheaf equalizer condition. Disjointness and
G_i(empty) = 0 give the quasi-inverse identifications, using
`lem-weil-pbc-scheme-coproduct-family` and `situation-conventions`.
4. Naturality of the decomposition recovers morphisms componentwise. Evaluate at
U = C, using `lem-weil-pbc-etale-inverse-image-restriction`, to obtain the natural
isomorphism of global-sections functors. -/
theorem Etale.sheaf_clopen_product {I : Type v} [Finite I] {X : Scheme.{u}}
    (C : I → Scheme.{u}) (ι : ∀ i, C i ⟶ X) (hc : IsColimit (Cofan.mk X ι)) :
    let R := Functor.pi' (fun i ↦ Etale.upperStar AddCommGrpCat.{u + 1} (ι i))
    R.IsEquivalence ∧
      Nonempty
        ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
            (op (Scheme.Etale.mk (𝟙 X))) ≅
          R ⋙ Functor.pi (fun i ↦
            (sheafSections (C i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
              (op (Scheme.Etale.mk (𝟙 (C i))))) ⋙ Pi.functor I) := by
  let R := Functor.pi' (fun i ↦ Etale.upperStar AddCommGrpCat.{u + 1} (ι i))
  let S := Functor.pi (fun i ↦ Etale.lowerStar AddCommGrpCat.{u + 1} (ι i)) ⋙
    Pi.functor I
  obtain ⟨η⟩ := clopen_reconstruction_unit C ι hc
  obtain ⟨ε⟩ := clopen_reconstruction_counit C ι hc
  have hR : R.IsEquivalence := (CategoryTheory.Equivalence.mk R S η ε).isEquivalence_functor
  refine ⟨hR, ?_⟩
  let Γ := (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (op (Scheme.Etale.mk (𝟙 X)))
  let Γi := fun i ↦
    (sheafSections (C i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op (Scheme.Etale.mk (𝟙 (C i))))
  have eΓ (Y : Scheme.{u}) :
      (sheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op (⊤_ Y.Etale)) ≅
      (sheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op (Scheme.Etale.mk (𝟙 Y))) :=
    (sheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso
      (terminalIsoIsTerminal (MorphismProperty.Over.mkIdTerminal (@Etale) Y)).op.symm
  have ei (i : I) : Etale.lowerStar AddCommGrpCat.{u + 1} (ι i) ⋙ Γ ≅ Γi i :=
    (Functor.isoWhiskerLeft _ (eΓ X)).symm ≪≫
      Etale.lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} (ι i) ≪≫ eΓ (C i)
  have hΓ : PreservesLimitsOfShape (Discrete I) Γ := by
    change PreservesLimitsOfShape (Discrete I)
      (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 X))))
    infer_instance
  have e : S ⋙ Γ ≅ Functor.pi Γi ⋙ Pi.functor I := by
    refine NatIso.ofComponents (fun G ↦ ?_) ?_
    · exact PreservesProduct.iso Γ (fun i ↦
        (Etale.lowerStar AddCommGrpCat.{u + 1} (ι i)).obj (G i)) ≪≫
        Pi.mapIso (fun i ↦ (ei i).app (G i))
    · intro G H f
      apply Pi.hom_ext
      intro i
      dsimp only [Iso.trans_hom, S, Functor.comp_map, Functor.comp_obj,
        Pi.functor_map, Pi.functor_obj, Functor.pi_obj, Functor.pi_map]
      simp only [Category.assoc, Pi.mapIso_hom_π, PreservesProduct.iso_hom,
        Pi.map_π, Pi.mapIso_hom_π_assoc, piComparison_comp_π_assoc,
        ← Γ.map_comp_assoc]
      dsimp only [Functor.pi_map]
      erw [Pi.map_π]
      rw [Γ.map_comp, Category.assoc]
      exact congrArg (fun k ↦ Γ.map (Pi.π _ i) ≫ k) ((ei i).hom.naturality (f i))
  exact ⟨(Functor.leftUnitor Γ).symm ≪≫ Functor.isoWhiskerRight η Γ ≪≫
    Functor.associator R S Γ ≪≫ Functor.isoWhiskerLeft R e ≪≫
    (Functor.associator R (Functor.pi Γi) (Pi.functor I)).symm⟩

end AlgebraicGeometry
