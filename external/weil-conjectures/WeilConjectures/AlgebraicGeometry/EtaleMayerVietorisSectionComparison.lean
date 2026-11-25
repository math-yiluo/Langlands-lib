/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleMayerVietorisSectionComplex
public import Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionHomology
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Resolution comparison for the étale section complexes

Source: Stacks Project, Tag 0A50, proof.
(blueprint: lem-weil-pbc-etale-mayer-vietoris-section-comparison).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

set_option backward.isDefEq.respectTransparency false in
private theorem exists_lift_to_injective_complex
    {C : Type*} [Category* C] [Abelian C] {G : C} (I : InjectiveResolution G)
    (L : CochainComplex C ℕ) [∀ n, Injective (L.X n)]
    (f : G ⟶ L.X 0) (hf : f ≫ L.d 0 1 = 0) :
    ∃ α : I.cocomplex ⟶ L, I.ι.f 0 ≫ α.f 0 = f := by
  let a₀ : I.cocomplex.X 0 ⟶ L.X 0 := Injective.factorThru f (I.ι.f 0)
  have ha₀ : I.ι.f 0 ≫ a₀ = f := by simp [a₀]
  let a₁ : I.cocomplex.X 1 ⟶ L.X 1 :=
    I.exact₀.descToInjective (a₀ ≫ L.d 0 1) (by rw [← Category.assoc, ha₀, hf])
  have ha₁ : a₀ ≫ L.d 0 1 = I.cocomplex.d 0 1 ≫ a₁ := by
    exact (I.exact₀.comp_descToInjective _ _).symm
  let next (n : ℕ) (a : I.cocomplex.X n ⟶ L.X n)
      (b : I.cocomplex.X (n + 1) ⟶ L.X (n + 1))
      (h : a ≫ L.d n (n + 1) = I.cocomplex.d n (n + 1) ≫ b) :
      Σ' c : I.cocomplex.X (n + 2) ⟶ L.X (n + 2),
        b ≫ L.d (n + 1) (n + 2) = I.cocomplex.d (n + 1) (n + 2) ≫ c :=
    ⟨(I.exact_succ n).descToInjective (b ≫ L.d (n + 1) (n + 2))
      (by rw [← Category.assoc, ← h, Category.assoc, L.d_comp_d, comp_zero]),
      ((I.exact_succ n).comp_descToInjective _ _).symm⟩
  refine ⟨CochainComplex.mkHom I.cocomplex L a₀ a₁ ha₁
    (fun n ⟨a, b, h⟩ ↦ next n a b h), ?_⟩
  simpa only [CochainComplex.mkHom_f_0] using ha₀

set_option backward.isDefEq.respectTransparency false in
private noncomputable def homologyBiprodEquiv
    (K L : CochainComplex AddCommGrpCat.{u + 1} ℕ) (q : ℕ) :
    (K ⊞ L).homology q ≃+ (K.homology q × L.homology q) :=
  (((HomologicalComplex.homologyFunctor _ _ q).mapBiprod K L) ≪≫
    AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv

set_option backward.isDefEq.respectTransparency false in
private theorem homologyBiprodEquiv_apply
    (K L : CochainComplex AddCommGrpCat.{u + 1} ℕ) (q : ℕ)
    (x : (K ⊞ L).homology q) :
    homologyBiprodEquiv K L q x =
      (HomologicalComplex.homologyMap (biprod.fst : K ⊞ L ⟶ K) q x,
       HomologicalComplex.homologyMap (biprod.snd : K ⊞ L ⟶ L) q x) := by
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (.up ℕ) q
  have hf : (AddCommGrpCat.biprodIsoProd (K.homology q) (L.homology q)).hom ≫
      AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) = biprod.fst := by
    rw [← cancel_epi (AddCommGrpCat.biprodIsoProd _ _).inv]
    simp
  have hs : (AddCommGrpCat.biprodIsoProd (K.homology q) (L.homology q)).hom ≫
      AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) = biprod.snd := by
    rw [← cancel_epi (AddCommGrpCat.biprodIsoProd _ _).inv]
    simp
  apply Prod.ext
  · change (((H.mapBiprod K L).hom ≫ (AddCommGrpCat.biprodIsoProd _ _).hom ≫
      AddCommGrpCat.ofHom (AddMonoidHom.fst _ _)) x) = (H.map biprod.fst) x
    erw [hf]
    exact congrArg (fun f ↦ f x) (Functor.biprodComparison_fst H K L)
  · change (((H.mapBiprod K L).hom ≫ (AddCommGrpCat.biprodIsoProd _ _).hom ≫
      AddCommGrpCat.ofHom (AddMonoidHom.snd _ _)) x) = (H.map biprod.snd) x
    erw [hs]
    exact congrArg (fun f ↦ f x) (Functor.biprodComparison_snd H K L)

set_option backward.isDefEq.respectTransparency false in
private theorem homologyBiprodEquiv_lift
    {A B C : CochainComplex AddCommGrpCat.{u + 1} ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (q : ℕ) (x : A.homology q) :
    homologyBiprodEquiv B C q (HomologicalComplex.homologyMap (biprod.lift f g) q x) =
      (HomologicalComplex.homologyMap f q x, HomologicalComplex.homologyMap g q x) := by
  rw [homologyBiprodEquiv_apply]
  apply Prod.ext
  · have h : HomologicalComplex.homologyMap (biprod.lift f g) q ≫
        HomologicalComplex.homologyMap (biprod.fst : B ⊞ C ⟶ B) q =
          HomologicalComplex.homologyMap f q := by
      rw [← HomologicalComplex.homologyMap_comp, biprod.lift_fst]
    exact congrArg (fun f ↦ f x) h
  · have h : HomologicalComplex.homologyMap (biprod.lift f g) q ≫
        HomologicalComplex.homologyMap (biprod.snd : B ⊞ C ⟶ C) q =
          HomologicalComplex.homologyMap g q := by
      rw [← HomologicalComplex.homologyMap_comp, biprod.lift_snd]
    exact congrArg (fun f ↦ f x) h

set_option backward.isDefEq.respectTransparency false in
private theorem homologyBiprodEquiv_desc_neg
    {A B C : CochainComplex AddCommGrpCat.{u + 1} ℕ} (f : A ⟶ C) (g : B ⟶ C)
    (q : ℕ) (x : (A ⊞ B).homology q) :
    HomologicalComplex.homologyMap (biprod.desc f (-g)) q x =
      HomologicalComplex.homologyMap f q (homologyBiprodEquiv A B q x).1 -
        HomologicalComplex.homologyMap g q (homologyBiprodEquiv A B q x).2 := by
  rw [homologyBiprodEquiv_apply]
  simp only [biprod.desc_eq, HomologicalComplex.homologyMap_add,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_neg,
    AddCommGrpCat.hom_add_apply, AddCommGrpCat.comp_apply, sub_eq_add_neg]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A comparison of the prescribed resolution section complexes, with homology
identifications respecting the prescribed restriction and pullback maps.
Source: Stacks Project, Tag 0A50, proof, and the explicit resolution comparison
of the parent node, steps 1, 2 and 4.
(blueprint: lem-weil-pbc-etale-mayer-vietoris-section-comparison)

Proof: Use the given nonnegative injective resolutions I of G and J of g⁻¹G. Exact inverse
image preserves the quasi-isomorphism from G to I. The bounded below injective
resolution J is K-injective, so a comparison beta from g⁻¹I to J exists over the
augmentations. The possible homotopy of augmentations has values in degree -1 of J,
which is zero, so it is an equality. On X take the complexes of sections of I on
X, the product of its sections on U and V, and its sections on U ∩ V, with the
restriction pair and difference of restrictions. On Y do the same with J and the
inverse-image opens. The unit on sections followed by beta commutes with restriction
by naturality, and
with its difference by additivity, and gives the morphism phi of short
complexes. No cover or short exactness
is needed for this step.

Identify homology of these complexes with the displayed Ext cohomology groups using
Hom from the constant integer sheaf, evaluated at 1. For opens, restriction preserves
injectives by its exact extension-by-zero left adjoint, so the same resolutions compute
the restricted cohomology. The identification for the middle complex uses homology's
preservation of the finite product. The coefficient composition comparison gives the
four asserted horizontal identities. To check the two vertical identities, represent
an Ext class by a cocycle in Hom from the constant integer sheaf to I. Exact inverse
image applies to that cocycle, and precomposition with the constant-sheaf comparison
is the adjunction unit on its section. Composing with beta therefore gives precisely
cohomologyMap g. On U ∩ V the restricted resolution and the pullback-unit identity
identify this with openCohomologyPullback, including its coefficient comparisons.
Thus the same identifications satisfy all six identities simultaneously; mere abstract
existence of unrelated isomorphisms is not being used. Empty opens give zero section
complexes. For identity pullback, compare the given resolutions by a homotopy
equivalence; if they agree, choose the identity comparison. No
connecting maps or long-exact-sequence assertions are part of this statement. -/
theorem etaleSectionShortComplex_pullback_comparison
    {X Y : Scheme.{u}} (g : Y ⟶ X) (U V : X.Opens)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G)
    (J : InjectiveResolution ((upperStar AddCommGrpCat.{u + 1} g).obj G)) :
    let SX := etaleSectionShortComplex U V I.cocomplex
    let SY := etaleSectionShortComplex (g ⁻¹ᵁ U) (g ⁻¹ᵁ V) J.cocomplex
    ∃ φ : SX ⟶ SY,
    ∃ eAX : ∀ q : ℕ, SX.X₁.homology q ≃+ Sheaf.H G q,
    ∃ eBX : ∀ q : ℕ, SX.X₂.homology q ≃+
      (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} U.ι).obj G) q ×
        Sheaf.H ((upperStar AddCommGrpCat.{u + 1} V.ι).obj G) q),
    ∃ eCX : ∀ q : ℕ, SX.X₃.homology q ≃+
      Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (U ⊓ V).ι).obj G) q,
    ∃ eAY : ∀ q : ℕ, SY.X₁.homology q ≃+
      Sheaf.H ((upperStar AddCommGrpCat.{u + 1} g).obj G) q,
    ∃ eBY : ∀ q : ℕ, SY.X₂.homology q ≃+
      (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (g ⁻¹ᵁ U).ι).obj
        ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q ×
       Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (g ⁻¹ᵁ V).ι).obj
        ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q),
    ∃ eCY : ∀ q : ℕ, SY.X₃.homology q ≃+
      Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (g ⁻¹ᵁ (U ⊓ V)).ι).obj
        ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q,
    (∀ q x, eBX q (HomologicalComplex.homologyMap SX.f q x) =
      (cohomologyMap U.ι G q (eAX q x), cohomologyMap V.ι G q (eAX q x))) ∧
    (∀ q x, eCX q (HomologicalComplex.homologyMap SX.g q x) =
      openCohomologyRestriction (inf_le_left : U ⊓ V ≤ U) G q (eBX q x).1 -
        openCohomologyRestriction (inf_le_right : U ⊓ V ≤ V) G q (eBX q x).2) ∧
    (∀ q x, eBY q (HomologicalComplex.homologyMap SY.f q x) =
      (cohomologyMap (g ⁻¹ᵁ U).ι ((upperStar AddCommGrpCat.{u + 1} g).obj G) q (eAY q x),
       cohomologyMap (g ⁻¹ᵁ V).ι ((upperStar AddCommGrpCat.{u + 1} g).obj G) q (eAY q x))) ∧
    (∀ q x, eCY q (HomologicalComplex.homologyMap SY.g q x) =
      openCohomologyRestriction (g.preimage_mono (inf_le_left : U ⊓ V ≤ U))
        ((upperStar AddCommGrpCat.{u + 1} g).obj G) q (eBY q x).1 -
      openCohomologyRestriction (g.preimage_mono (inf_le_right : U ⊓ V ≤ V))
        ((upperStar AddCommGrpCat.{u + 1} g).obj G) q (eBY q x).2) ∧
    (∀ q x, eAY q (HomologicalComplex.homologyMap φ.τ₁ q x) =
      cohomologyMap g G q (eAX q x)) ∧
    (∀ q x, eCY q (HomologicalComplex.homologyMap φ.τ₃ q x) =
      openCohomologyPullback g (U ⊓ V) G q (eCX q x)) := by
  let R := lowerStar AddCommGrpCat.{u + 1} g
  let L := (R.mapHomologicalComplex (.up ℕ)).obj J.cocomplex
  let adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g
  have hinj (n : ℕ) : Injective (L.X n) :=
    adj.map_injective (J.cocomplex.X n) inferInstance
  let f : G ⟶ L.X 0 := adj.unit.app G ≫ R.map (J.ι.f 0)
  have hf : f ≫ L.d 0 1 = 0 := by
    change (adj.unit.app G ≫ R.map (J.ι.f 0)) ≫ R.map (J.cocomplex.d 0 1) = 0
    rw [Category.assoc, ← R.map_comp, J.ι_f_zero_comp_complex_d, R.map_zero, comp_zero]
  obtain ⟨α, hα⟩ := exists_lift_to_injective_complex I L f hf
  obtain ⟨eX, eOX, eY, eOY, hrX, hiX, hrY, hiY, hp, hpO⟩ :=
    exists_resolutionSection_homology_comparison g G I J α hα
  let φ := resolutionSectionShortComplexTransfer g U V I.cocomplex J.cocomplex α
  let KX (W : X.Opens) :=
    ((etaleSectionFunctor (Scheme.Etale.mk W.ι)).mapHomologicalComplex (.up ℕ)).obj
      I.cocomplex
  let KY (W : Y.Opens) :=
    ((etaleSectionFunctor (Scheme.Etale.mk W.ι)).mapHomologicalComplex (.up ℕ)).obj
      J.cocomplex
  let eBX : ∀ q : ℕ, (KX U ⊞ KX V).homology q ≃+
      (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} U.ι).obj G) q ×
        Sheaf.H ((upperStar AddCommGrpCat.{u + 1} V.ι).obj G) q) :=
    fun q ↦ (homologyBiprodEquiv (KX U) (KX V) q).trans
    ((eOX U q).prodCongr (eOX V q))
  let eBY : ∀ q : ℕ, (KY (g ⁻¹ᵁ U) ⊞ KY (g ⁻¹ᵁ V)).homology q ≃+
      (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (g ⁻¹ᵁ U).ι).obj
        ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q ×
        Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (g ⁻¹ᵁ V).ι).obj
          ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q) :=
    fun q ↦ (homologyBiprodEquiv (KY (g ⁻¹ᵁ U)) (KY (g ⁻¹ᵁ V)) q).trans
    ((eOY (g ⁻¹ᵁ U) q).prodCongr (eOY (g ⁻¹ᵁ V) q))
  let rX (W : X.Opens) := etaleSectionMap
    (MorphismProperty.Over.homMk W.ι (Category.comp_id _) :
      Scheme.Etale.mk W.ι ⟶ Scheme.Etale.mk (𝟙 X)) I.cocomplex
  let rY (W : Y.Opens) := etaleSectionMap
    (MorphismProperty.Over.homMk W.ι (Category.comp_id _) :
      Scheme.Etale.mk W.ι ⟶ Scheme.Etale.mk (𝟙 Y)) J.cocomplex
  let dX (A B : X.Opens) (h : A ≤ B) := etaleSectionMap
    (MorphismProperty.Over.homMk (X.homOfLE h) (X.homOfLE_ι _) :
      Scheme.Etale.mk A.ι ⟶ Scheme.Etale.mk B.ι) I.cocomplex
  let dY (A B : Y.Opens) (h : A ≤ B) := etaleSectionMap
    (MorphismProperty.Over.homMk (Y.homOfLE h) (Y.homOfLE_ι _) :
      Scheme.Etale.mk A.ι ⟶ Scheme.Etale.mk B.ι) J.cocomplex
  refine ⟨φ, eX, eBX, eOX (U ⊓ V), eY, eBY, eOY (g ⁻¹ᵁ (U ⊓ V)), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, hp, hpO (U ⊓ V)⟩
  · intro q x
    change eBX q (HomologicalComplex.homologyMap (biprod.lift (rX U) (rX V)) q x) = _
    dsimp only [eBX, AddEquiv.trans_apply]
    rw [homologyBiprodEquiv_lift]
    exact Prod.ext (hrX U q x) (hrX V q x)
  · intro q x
    change eOX (U ⊓ V) q (HomologicalComplex.homologyMap
      (biprod.desc (dX (U ⊓ V) U inf_le_left) (-dX (U ⊓ V) V inf_le_right)) q x) = _
    rw [homologyBiprodEquiv_desc_neg, map_sub]
    exact congrArg₂ (fun a b ↦ a - b)
      (hiX (U ⊓ V) U inf_le_left q _) (hiX (U ⊓ V) V inf_le_right q _)
  · intro q x
    change eBY q (HomologicalComplex.homologyMap
      (biprod.lift (rY (g ⁻¹ᵁ U)) (rY (g ⁻¹ᵁ V))) q x) = _
    dsimp only [eBY, AddEquiv.trans_apply]
    rw [homologyBiprodEquiv_lift]
    exact Prod.ext (hrY (g ⁻¹ᵁ U) q x) (hrY (g ⁻¹ᵁ V) q x)
  · intro q x
    change eOY (g ⁻¹ᵁ (U ⊓ V)) q (HomologicalComplex.homologyMap
      (biprod.desc
        (dY (g ⁻¹ᵁ (U ⊓ V)) (g ⁻¹ᵁ U) (g.preimage_mono inf_le_left))
        (-dY (g ⁻¹ᵁ (U ⊓ V)) (g ⁻¹ᵁ V) (g.preimage_mono inf_le_right))) q x) = _
    rw [homologyBiprodEquiv_desc_neg, map_sub]
    exact congrArg₂ (fun a b ↦ a - b)
      (hiY _ _ (g.preimage_mono (inf_le_left : U ⊓ V ≤ U)) q _)
      (hiY _ _ (g.preimage_mono (inf_le_right : U ⊓ V ≤ V)) q _)

end AlgebraicGeometry.Etale
