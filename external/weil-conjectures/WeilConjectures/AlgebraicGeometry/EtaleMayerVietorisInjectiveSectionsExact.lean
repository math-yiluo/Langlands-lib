/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleMayerVietorisSectionComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Sites.MayerVietorisSquare
import Mathlib.CategoryTheory.Abelian.Injective.Basic
import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
# Degreewise exactness of injective section complexes

Source: Stacks Project, Tag 0A50, proof.
(blueprint: lem-weil-pbc-etale-mayer-vietoris-injective-sections-exact).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- The square of the two open inclusions and their intersection. -/
private noncomputable def openSquare {X : Scheme.{u}} (U V : X.Opens) : Square X.Etale where
  X₁ := Scheme.Etale.mk (U ⊓ V).ι
  X₂ := Scheme.Etale.mk U.ι
  X₃ := Scheme.Etale.mk V.ι
  X₄ := Scheme.Etale.mk (𝟙 X)
  f₁₂ := MorphismProperty.Over.homMk (X.homOfLE inf_le_left) (X.homOfLE_ι _)
  f₁₃ := MorphismProperty.Over.homMk (X.homOfLE inf_le_right) (X.homOfLE_ι _)
  f₂₄ := MorphismProperty.Over.homMk U.ι (Category.comp_id _)
  f₃₄ := MorphismProperty.Over.homMk V.ι (Category.comp_id _)
  fac := by
    apply MorphismProperty.Over.Hom.ext
    exact (X.homOfLE_ι inf_le_left).trans (X.homOfLE_ι inf_le_right).symm

private theorem openSquare_pullback {X : Scheme.{u}} (U V : X.Opens) :
    (openSquare U V).IsPullback := by
  apply IsPullback.of_map (Scheme.Etale.forget X ⋙ Over.forget X)
  · exact (openSquare U V).fac
  · exact isPullback_opens_inf U V

private theorem openSquare_cover {X : Scheme.{u}} (U V : X.Opens) (hc : U ⊔ V = ⊤) :
    Sieve.ofTwoArrows (openSquare U V).f₂₄ (openSquare U V).f₃₄ ∈
      X.smallEtaleTopology (openSquare U V).X₄ := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  ext x
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  have hx : x ∈ U ∨ x ∈ V := by
    change x ∈ U ⊔ V
    rw [hc]
    trivial
  rcases hx with hx | hx
  · exact ⟨WalkingPair.left, ⟨x, hx⟩, rfl⟩
  · exact ⟨WalkingPair.right, ⟨x, hx⟩, rfl⟩

/-- Sections as maps out of the free abelian sheaf of lifted Yoneda. -/
private noncomputable def sectionEquiv {X : Scheme.{u}} (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ((presheafToSheaf X.smallEtaleTopology _).obj
      (uliftYoneda.{u + 1}.obj W ⋙ AddCommGrpCat.free) ⟶ F) ≃ F.obj.obj (op W) :=
  ((sheafificationAdjunction X.smallEtaleTopology _).homEquiv _ F).trans
    (((AddCommGrpCat.adj.whiskerRight X.Etaleᵒᵖ).homEquiv _ F.obj).trans uliftYonedaEquiv)

set_option backward.isDefEq.respectTransparency false in
private theorem sectionEquiv_naturality {X : Scheme.{u}} {A B : X.Etale}
    (f : A ⟶ B) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (t : (presheafToSheaf X.smallEtaleTopology _).obj
      (uliftYoneda.{u + 1}.obj B ⋙ AddCommGrpCat.free) ⟶ F) :
    sectionEquiv A F ((presheafToSheaf X.smallEtaleTopology _).map
      (Functor.whiskerRight (uliftYoneda.{u + 1}.map f) AddCommGrpCat.free) ≫ t) =
      F.obj.map f.op (sectionEquiv B F t) := by
  dsimp only [sectionEquiv, Equiv.trans_apply]
  rw [(sheafificationAdjunction X.smallEtaleTopology _).homEquiv_naturality_left]
  erw [(AddCommGrpCat.adj.whiskerRight X.Etaleᵒᵖ).homEquiv_naturality_left
    (uliftYoneda.{u + 1}.map f)
    (((sheafificationAdjunction X.smallEtaleTopology _).homEquiv _ F) t)]
  exact (uliftYonedaEquiv_naturality _ f.op).symm

/-- Injectivity extends any section along a monomorphism of etale objects. -/
private theorem restriction_surjective {X : Scheme.{u}} {A B : X.Etale}
    (f : A ⟶ B) [Mono f] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    [Injective F] : Function.Surjective (F.obj.map f.op) := by
  let m := (presheafToSheaf X.smallEtaleTopology _).map
    (Functor.whiskerRight (uliftYoneda.{u + 1}.map f) AddCommGrpCat.free)
  have : Mono m := by dsimp [m]; infer_instance
  intro x
  let t := (sectionEquiv A F).symm x
  refine ⟨sectionEquiv B F (Injective.factorThru t m), ?_⟩
  rw [← sectionEquiv_naturality, Injective.comp_factorThru]
  exact (sectionEquiv A F).apply_symm_apply x

private noncomputable def sectionGroupShortComplex {X : Scheme.{u}} (U V : X.Opens)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ShortComplex AddCommGrpCat.{u + 1} :=
  let sq := (openSquare U V).op.map F.obj
  ShortComplex.mk (biprod.lift sq.f₁₂ sq.f₁₃)
    (biprod.desc sq.f₂₄ (-sq.f₃₄)) sq.kernelFork.condition

private theorem sectionGroupShortComplex_shortExact {X : Scheme.{u}} (U V : X.Opens)
    (hc : U ⊔ V = ⊤) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    [Injective F] : (sectionGroupShortComplex U V F).ShortExact := by
  let sq := (openSquare U V).op.map F.obj
  have hsq : sq.IsPullback := by
    let P := F.obj ⋙ forget AddCommGrpCat.{u + 1}
    have hP : Presheaf.IsSheaf X.smallEtaleTopology P :=
      Presheaf.isSheaf_comp_of_isSheaf _ _ _ F.property
    have : Mono (openSquare U V).f₂₄ :=
      (Scheme.Etale.forget X ⋙ Over.forget X).mono_of_mono_map
        (by change Mono U.ι; infer_instance)
    have : Mono (openSquare U V).f₃₄ :=
      (Scheme.Etale.forget X ⋙ Over.forget X).mono_of_mono_map
        (by change Mono V.ι; infer_instance)
    have hp : ((openSquare U V).op.map P).IsPullback := by
      apply Square.IsPullback.mk
      let hs := openSquare_pullback U V
      let hc' := openSquare_cover U V hc
      refine PullbackCone.IsLimit.mk _
        (fun t ↦ hP.amalgamateOfArrows _ hc'
          (fun j ↦ WalkingPair.casesOn j t.fst t.snd)
          (fun W ↦ by
            rintro (_ | _) (_ | _) a b fac
            · obtain rfl : a = b := by
                apply (cancel_mono (openSquare U V).f₂₄).mp
                exact fac
              rfl
            · obtain ⟨φ, rfl, rfl⟩ := PullbackCone.IsLimit.lift' hs.isLimit _ _ fac
              simpa using t.condition =≫ P.map φ.op
            · obtain ⟨φ, rfl, rfl⟩ := PullbackCone.IsLimit.lift' hs.isLimit _ _ fac.symm
              simpa using t.condition.symm =≫ P.map φ.op
            · obtain rfl : a = b := by
                apply (cancel_mono (openSquare U V).f₃₄).mp
                exact fac
              rfl)) (fun _ ↦ ?_) (fun _ ↦ ?_) (fun t m hm₁ hm₂ ↦ ?_)
      · exact hP.amalgamateOfArrows_map _ _ _ _ WalkingPair.left
      · exact hP.amalgamateOfArrows_map _ _ _ _ WalkingPair.right
      · apply hP.hom_ext_ofArrows _ hc'
        rintro (_ | _)
        · rw [hP.amalgamateOfArrows_map _ _ _ _ WalkingPair.left]
          exact hm₁
        · rw [hP.amalgamateOfArrows_map _ _ _ _ WalkingPair.right]
          exact hm₂
    apply Square.IsPullback.of_map (forget AddCommGrpCat.{u + 1})
    exact hp
  have hk : IsLimit (KernelFork.ofι (sectionGroupShortComplex U V F).f
      (sectionGroupShortComplex U V F).zero) := hsq.isLimitKernelFork
  obtain ⟨he, hm⟩ :=
    (sectionGroupShortComplex U V F).exact_and_mono_f_iff_f_is_kernel.mpr ⟨hk⟩
  have : Mono (openSquare U V).f₁₂ :=
    (Scheme.Etale.forget X ⋙ Over.forget X).mono_of_mono_map (by
      change Mono (X.homOfLE (inf_le_left : U ⊓ V ≤ U))
      infer_instance)
  have hg : Function.Surjective (sectionGroupShortComplex U V F).g := by
    intro x
    obtain ⟨y, hy⟩ := restriction_surjective (openSquare U V).f₁₂ F x
    refine ⟨(biprod.inl : sq.X₂ ⟶ sq.X₂ ⊞ sq.X₃) y, ?_⟩
    change (biprod.inl ≫ biprod.desc sq.f₂₄ (-sq.f₃₄)) y = x
    rw [biprod.inl_desc]
    exact hy
  exact { exact := he, mono_f := hm, epi_g := (AddCommGrpCat.epi_iff_surjective _).mpr hg }
/-- Evaluation carries the complex-level pair and difference to their section maps. -/
private noncomputable def degreeIso {X : Scheme.{u}} (U V : X.Opens)
    (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) (q : ℕ) :
    (etaleSectionShortComplex U V I).map
      (HomologicalComplex.eval AddCommGrpCat.{u + 1} (.up ℕ) q) ≅
      sectionGroupShortComplex U V (I.X q) := by
  let E := HomologicalComplex.eval AddCommGrpCat.{u + 1} (.up ℕ) q
  let A := ((etaleSectionFunctor (Scheme.Etale.mk U.ι)).mapHomologicalComplex (.up ℕ)).obj I
  let B := ((etaleSectionFunctor (Scheme.Etale.mk V.ι)).mapHomologicalComplex (.up ℕ)).obj I
  refine ShortComplex.isoMk (Iso.refl _) (E.mapBiprod A B) (Iso.refl _) ?_ ?_
  · change biprod.lift _ _ = E.map (biprod.lift _ _) ≫ (E.mapBiprod A B).hom
    rw [biprod.map_lift_mapBiprod]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id]
    let c := etaleSectionMap
      (MorphismProperty.Over.homMk (X.homOfLE (inf_le_left : U ⊓ V ≤ U))
        (X.homOfLE_ι _) : Scheme.Etale.mk (U ⊓ V).ι ⟶ Scheme.Etale.mk U.ι) I
    let d := etaleSectionMap
      (MorphismProperty.Over.homMk (X.homOfLE (inf_le_right : U ⊓ V ≤ V))
        (X.homOfLE_ι _) : Scheme.Etale.mk (U ⊓ V).ι ⟶ Scheme.Etale.mk V.ι) I
    change (E.mapBiprod A B).hom ≫ biprod.desc (E.map c) (-(E.map d)) =
      E.map (biprod.desc c (-d))
    rw [← E.map_neg]
    rw [biprod.mapBiprod_hom_desc]

/-- The section short complex of an open cover is short exact in an injective degree.
Source: Stacks Project, Tag 0A50, proof.
(blueprint: lem-weil-pbc-etale-mayer-vietoris-injective-sections-exact)

Proof: Evaluate the short complex in degree q. Its objects are I^q(X), the biproduct
of I^q(U) and I^q(V), and I^q(U intersection V). Construct the square of the etale
objects given by the two opens and their intersection. The intersection is their
pullback, and the two inclusion maps form a covering by the cover hypothesis.
For any abelian sheaf, forgetting to sets preserves its sheaf condition. Amalgamation
of the two sections on this covering makes the square of sections a pullback.
Its associated kernel fork therefore proves injectivity of the restriction pair
and exactness at the middle term.

For any monomorphism A to B of etale objects, lift Yoneda to the coefficient universe
and take the free abelian sheaf. This functor preserves the monomorphism. Maps from
these free sheaves to I^q correspond to sections on A and B by the sheafification,
free-forgetful and lifted Yoneda adjunctions. Injectivity extends a map out of the free
sheaf of A to the free sheaf of B. Naturality of those equivalences shows that this
extension is a section restricting to the prescribed section on A. Apply this to
the inclusion of the intersection into U. Surjectivity of this restriction makes
the difference from the biproduct surjective by taking the second component zero.

Finally evaluation of a complex preserves its biproduct. The canonical mapBiprod
isomorphism identifies evaluation of the section short complex with the just proved
short exact group sequence, including both arrows. Transport short exactness across
this isomorphism. Empty opens give zero section groups and both opens equal to X
give the split diagonal/difference sequence. -/
theorem etaleSectionShortComplex_degreewise_shortExact
    {X : Scheme.{u}} (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (q : ℕ) [Injective (I.X q)] :
    ((etaleSectionShortComplex U V I).map
      (HomologicalComplex.eval AddCommGrpCat.{u + 1} (.up ℕ) q)).ShortExact := by
  exact (ShortComplex.shortExact_iff_of_iso (degreeIso U V I q)).mpr
    (sectionGroupShortComplex_shortExact U V hcover (I.X q))

end AlgebraicGeometry.Etale
