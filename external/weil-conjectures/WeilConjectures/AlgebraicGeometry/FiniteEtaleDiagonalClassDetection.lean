/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCanonicalEtale
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals
import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalCartier
import WeilConjectures.AlgebraicGeometry.FiniteP1DiagonalAlpha
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.ConstructibleSheaf.RankOne
public import WeilConjectures.ConstructibleSheaf.LisseRankOne
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologyZero
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.Tactic.TransportExact

/-! # Finite etale diagonal classes detect ordinary roots-line maps

Source: diagonal coefficient changes (3), positive residue and finite P1 integrals.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096
universe u v w
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.rightDerivedFunctor HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.ofIsGrothendieckAbelian

namespace CategoryTheory.Abelian.Ext
private theorem comp_natural_endomorphism
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [EnoughInjectives C]
    (θ : 𝟭 C ⟶ 𝟭 C) {X Y : C} {n : ℕ} (x : Ext X Y n) :
    x.comp (mk₀ (θ.app Y)) (add_zero n) =
      (mk₀ (θ.app X)).comp x (zero_add n) := by
  induction n generalizing Y with
  | zero =>
    obtain ⟨f, rfl⟩ := (mk₀_bijective X Y).2 x
    rw [mk₀_comp_mk₀, mk₀_comp_mk₀]
    exact congrArg mk₀ (θ.naturality f)
  | succ n ih =>
    let ι := Injective.ι Y
    let S := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel ι }
    obtain ⟨y, rfl⟩ := covariant_sequence_exact₁ X hS x (eq_zero_of_injective _) rfl
    let φ : S ⟶ S :=
      { τ₁ := θ.app S.X₁
        τ₂ := θ.app S.X₂
        τ₃ := θ.app S.X₃
        comm₁₂ := (θ.naturality S.f).symm
        comm₂₃ := (θ.naturality S.g).symm }
    have hnat : hS.extClass.comp (mk₀ (θ.app Y)) (add_zero 1) =
        (mk₀ (θ.app S.X₃)).comp hS.extClass (zero_add 1) :=
      hS.extClass_naturality hS φ
    rw [comp_assoc_of_third_deg_zero, hnat,
      ← comp_assoc_of_second_deg_zero, ih]
    exact comp_assoc (mk₀ (θ.app X)) y hS.extClass (zero_add n) rfl (by omega)
end CategoryTheory.Abelian.Ext

namespace CategoryTheory
open MonoidalCategory
private theorem class_detects_from_integral_and_unit_action
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [EnoughInjectives C]
    [HasDerivedCategory.{w} C] [MonoidalCategory C] [MonoidalClosed C]
    {D : Type*} [Category D] (R : DerivedCategory C ⥤ D)
    {S L : C} [IsIso (MonoidalClosed.id L)] (δ : Ext S L 2)
    {Q : D} (s : Q ≅ R.obj ((DerivedCategory.singleFunctor C 0).obj S))
    (t : R.obj (((DerivedCategory.singleFunctor C 0).obj L)⟦(2 : ℤ)⟧) ⟶ Q)
    (hint : s.hom ≫ R.map δ.hom ≫ t = 𝟙 Q)
    (hunit : Function.Injective (fun a : End (𝟙_ C) ↦
      R.map ((DerivedCategory.singleFunctor C 0).map (unitEndAction S a).asHom))) :
    Function.Injective (fun f : L ⟶ L ↦ δ.comp (Abelian.Ext.mk₀ f) (add_zero 2)) := by
  intro f g hfg
  obtain ⟨a, ha⟩ := (bijective_unitEndAction L).2 (End.of f)
  obtain ⟨b, hb⟩ := (bijective_unitEndAction L).2 (End.of g)
  have ha : (unitEndAction L a).asHom = f := congrArg End.asHom ha
  have hb : (unitEndAction L b).asHom = g := congrArg End.asHom hb
  have hcenter (a : End (𝟙_ C)) :
      δ.comp (Abelian.Ext.mk₀ (unitEndAction L a).asHom) (add_zero 2) =
        (Abelian.Ext.mk₀ (unitEndAction S a).asHom).comp δ (zero_add 2) := by
    let θ : 𝟭 C ⟶ 𝟭 C :=
      { app := fun X ↦ (unitEndAction X a).asHom
        naturality := fun _ _ f ↦ (unitEndAction_naturality f a).symm }
    exact Abelian.Ext.comp_natural_endomorphism θ δ
  have h : (Abelian.Ext.mk₀ (unitEndAction S a).asHom).comp δ (zero_add 2) =
      (Abelian.Ext.mk₀ (unitEndAction S b).asHom).comp δ (zero_add 2) := by
    rw [← hcenter, ← hcenter, ha, hb]
    exact hfg
  have hh := congrArg (fun z : Ext S L 2 ↦ (z.hom :
    (DerivedCategory.singleFunctor C 0).obj S ⟶
      ((DerivedCategory.singleFunctor C 0).obj L)⟦(2 : ℤ)⟧)) h
  simp only [Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, ShiftedHom.mk₀_comp] at hh
  have hR := congrArg (fun z ↦ R.map z ≫ t ≫ s.hom) hh
  have hs : R.map δ.hom ≫ t ≫ s.hom = 𝟙 _ := by
    apply (cancel_epi s.hom).1
    simpa only [Category.assoc, Category.id_comp, Category.comp_id] using
      congrArg (fun z ↦ z ≫ s.hom) hint
  have hab : a = b := by
    apply hunit
    simpa only [R.map_comp, Category.assoc, hs, Category.comp_id] using hR
  exact ha.symm.trans ((congrArg (fun c ↦ (unitEndAction L c).asHom) hab).trans hb)
end CategoryTheory

namespace CategoryTheory
private theorem map_eq_of_derived_single_map_eq
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
    [HasKInjectiveResolutions D]
    (G : D ⥤ C) [G.Additive] [PreservesFiniteLimits G]
    {X Y : D} (f g : X ⟶ Y)
    (h : G.rightDerivedFunctor.map ((DerivedCategory.singleFunctor D 0).map f) =
      G.rightDerivedFunctor.map ((DerivedCategory.singleFunctor D 0).map g)) :
    G.map f = G.map g := by
  let α := G.singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso
  apply (cancel_epi (α.hom.app X)).1
  rw [← α.hom.naturality f, ← α.hom.naturality g]
  exact congrArg (fun z ↦ (DerivedCategory.homologyFunctor C 0).map z ≫ α.hom.app Y) h

private theorem source_unit_action_detected
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory D]
    (F : C ⥤ D) (G : D ⥤ C) (H : D ⥤ E) (K : E ⥤ D)
    (adj : F ⊣ G) (adjH : H ⊣ K)
    [F.Full] [F.Faithful] [(F ⋙ H).Full] [(F ⋙ H).Faithful]
    {Z : C} (e : 𝟙_ D ≅ F.obj Z) {V : E} (r : H.obj (𝟙_ D) ≅ V) :
    Function.Injective (fun a : End (𝟙_ D) ↦ G.map (unitEndAction (K.obj V) a).asHom) := by
  have hF : IsIso (G.map (adjH.unit.app (F.obj Z))) := by
    have h : IsIso ((adj.comp adjH).unit.app Z) := inferInstance
    rw [Adjunction.comp_unit_app] at h
    exact IsIso.of_isIso_comp_left (adj.unit.app Z) _
  have hU : IsIso (G.map (adjH.unit.app (𝟙_ D))) := by
    have hn := adjH.unit.naturality e.hom
    simp only [Functor.id_map] at hn
    have h : IsIso (G.map (adjH.unit.app (𝟙_ D)) ≫ G.map ((H ⋙ K).map e.hom)) := by
      rw [← G.map_comp, ← hn, G.map_comp]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (G.map ((H ⋙ K).map e.hom))
  let q := adjH.unit.app (𝟙_ D) ≫ K.map r.hom
  have hq : IsIso (G.map q) := by dsimp [q]; rw [G.map_comp]; infer_instance
  have hε : IsIso (adj.counit.app (𝟙_ D)) := adj.isIso_counit_app_of_iso e
  intro a b hab
  dsimp only at hab
  have hnat (a : End (𝟙_ D)) : a.asHom ≫ q = q ≫ (unitEndAction (K.obj V) a).asHom := by
    simpa only [Functor.id_obj, unitEndAction_unit] using unitEndAction_naturality q a
  have habG : G.map a.asHom = G.map b.asHom := by
    apply (cancel_mono (G.map q)).1
    calc
      G.map a.asHom ≫ G.map q = G.map (a.asHom ≫ q) := (G.map_comp _ _).symm
      _ = G.map (q ≫ (unitEndAction (K.obj V) a).asHom) := congrArg G.map (hnat a)
      _ = G.map q ≫ G.map (unitEndAction (K.obj V) a).asHom := G.map_comp _ _
      _ = G.map q ≫ G.map (unitEndAction (K.obj V) b).asHom :=
        congrArg (fun z ↦ G.map q ≫ z) hab
      _ = G.map (q ≫ (unitEndAction (K.obj V) b).asHom) := (G.map_comp _ _).symm
      _ = G.map (b.asHom ≫ q) := congrArg G.map (hnat b).symm
      _ = G.map b.asHom ≫ G.map q := G.map_comp _ _
  apply End.ext
  apply (cancel_epi (adj.counit.app (𝟙_ D))).1
  have hn (a : End (𝟙_ D)) := adj.counit.naturality a.asHom
  simp only [Functor.id_map, Functor.comp_map] at hn
  exact (hn a).symm.trans ((congrArg
    (fun z ↦ F.map z ≫ adj.counit.app (𝟙_ D)) habG).trans (hn b))
end CategoryTheory

namespace AlgebraicGeometry.Scheme
private theorem isIso_id_of_lisseRankOne
    {X : Scheme.{u}} {A : Type (u + 1)} [CommRing A]
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hL : IsLisseRankOneSheaf L) : IsIso (MonoidalClosed.id L) := by
  obtain ⟨U, hU⟩ := hL
  let : IsLocallyConstantSheaf L :=
    ⟨⟨⟨U, fun i ↦
      (isConstant_over_iff_upperStar _ (U.etalePrecoverageToEtale i) L).2
        (Sheaf.isConstant_of_iso _ (hU i).some)⟩⟩⟩
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} A)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have hRank : HasRankOneStalks L := by
    intro Ω _ _ s
    obtain ⟨i, t, rfl⟩ := U.exists_comp_eq_of_isSepClosed s
    refine ⟨((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) (U.f i) t).app L).symm ≪≫
      (pointSmallEtale t).sheafFiber.mapIso (hU i).some ≪≫
      (pointSmallEtale t).sheafFiberConstantSheafIso (ModuleCat.of A A)⟩
  exact isIso_id_of_hasRankOneStalks L hRank
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale
private theorem canonical_diagonal_integral
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (Y : Scheme.{u}) (hY : IsUnit (N : Γ(Y, ⊤))) :
    ∃ (t : OrdinaryFiniteTwistTransport A N hA)
      (d : ∀ (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))),
        ArbitraryBaseFiniteP1Splitting A N hA t S hS),
      ∀ a : Bool,
        ordinaryFiniteP1DiagonalSupportedMap A N hA Y a
          (geoCartierEtaleClass A N hN hA
            (pullback.diagonal (ProjectiveLine Y ↘ Y))
            (projectiveLine_diagonal_ker_isInvertible Y)
            (finiteP1_unitOnPullback N
              ((pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) ≫
                (ProjectiveLine Y ↘ Y)) hY)) ≫
          arbitraryBaseFiniteP1DiagonalTrace A N hA t d Y hY a =
            𝟙 (ordinaryFiniteUnit A (ProjectiveLine Y)) := by
  obtain ⟨t, d, _, h⟩ := exists_arbitraryBaseFiniteP1Integrals N hN A hA
  obtain ⟨hI, κ, hκ, htrace⟩ := h Y hY
  have he := (geoCartierEtaleClass_spec A N hN hA
    (pullback.diagonal (ProjectiveLine Y ↘ Y)) hI
    (finiteP1_unitOnPullback N
      ((pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) ≫
        (ProjectiveLine Y ↘ Y)) hY)).2 κ hκ
  refine ⟨t, d, ?_⟩
  intro a
  simpa only [he] using (htrace a).2
end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale
private theorem unit_pullback (Λ : Type (u + 1)) [CommRing Λ]
    {X S : Scheme.{u}} (p : X ⟶ S)
    [Flat p] [QuasiCompact p] [GeometricallyConnected p]
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app G) := by
  let adj := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p
  have hi (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
      IsIso (adj.unit.app G) := by
    have : IsIso ((sheafToPresheaf _ _).map (adj.unit.app G)) := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro V
      let q := pullback.fst V.unop.hom p
      let φ := 𝟙 ((MorphismProperty.Over.pullback @Etale ⊤ p).obj V.unop)
      have hq : φ.left ≫ q = q := Category.id_comp _
      let : Flat (φ.left ≫ q) := by rw [hq]; dsimp [q]; infer_instance
      let : QuasiCompact (φ.left ≫ q) := by rw [hq]; dsimp [q]; infer_instance
      let : GeometricallyConnected (φ.left ≫ q) := by rw [hq]; dsimp [q]; infer_instance
      have h := Etale.isIso_upperStarSectionsMap Λ p G φ
      change IsIso ((adj.unit.app G).hom.app V)
      change IsIso ((adj.unit.app G).hom.app V ≫
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) p).obj G).obj.map (𝟙 _)) at h
      rw [CategoryTheory.Functor.map_id] at h
      exact (isIso_comp_right_iff ((adj.unit.app G).hom.app V) (𝟙 _)).mp h
    exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)
  exact hi G

private theorem projectiveLine_connected (S : Scheme.{u}) :
    GeometricallyConnected (ProjectiveLine S ↘ S) := by
  refine ⟨fun K _ y Z fst snd h ↦ ?_⟩
  have e : Z ≅ ProjectiveLine (Spec (.of K)) :=
    h.isoIsPullback _ _ (ProjectiveSpace.isPullback_map _ y)
  exact (Scheme.homeoOfIso e.symm).connectedSpace_iff.1 inferInstance



section

-- Elaborate with the proposition instances stored in the ordinary derived category, so that
-- both sides of the transport below carry the same instance proofs.
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

/-- The final step of `finiteEtaleDiagonalClass_postcomp_injective`, stated without local
definitions: the normalized diagonal integral is the integral hypothesis of
`class_detects_from_integral_and_unit_action`. The two sides differ in spelling
(`DerivedCategoryModule` against `DerivedCategory`, named objects against their values), and
`transport_exact` compares them along their common structure. -/
private theorem diagonal_class_detects
    (Y : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (hI : (pullback.diagonal (ProjectiveLine Y ↘ Y)).ker.IsInvertible)
    (hW : IsUnit (N : Γ(pullback (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y), ⊤)))
    (hY : IsUnit (N : Γ(Y, ⊤)))
    [IsIso (MonoidalClosed.id (Scheme.finiteEtaleTateLine
      (pullback (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) N A hA))]
    (t : OrdinaryFiniteTwistTransport A N hA)
    (d : ∀ (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))),
      ArbitraryBaseFiniteP1Splitting A N hA t S hS)
    (ht : ordinaryFiniteP1DiagonalSupportedMap A N hA Y false
        (geoCartierEtaleClass A N hN hA (pullback.diagonal (ProjectiveLine Y ↘ Y)) hI hW) ≫
      arbitraryBaseFiniteP1DiagonalTrace A N hA t d Y hY false =
        𝟙 (ordinaryFiniteUnit A (ProjectiveLine Y)))
    (hunit : Function.Injective (fun a : End (𝟙_ (Sheaf
        (pullback (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)).smallEtaleTopology
          (ModuleCat.{u + 1} A))) ↦
      (ordinaryFinitePushforward A (projectiveLineDiagonalProjection Y false)).map
        ((DerivedCategory.singleFunctor _ 0).map (unitEndAction
          ((lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine Y ↘ Y))).obj
            (ordinaryFiniteConstant A (ProjectiveLine Y))) a).asHom))) :
    Function.Injective (fun f : Scheme.finiteEtaleTateLine
        (pullback (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) N A hA ⟶
        Scheme.finiteEtaleTateLine
          (pullback (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) N A hA ↦
      (geoCartierEtaleClass A N hN hA (pullback.diagonal (ProjectiveLine Y ↘ Y))
        hI hW).comp (Ext.mk₀ f) (add_zero 2)) := by
  have := isIso_projectiveLineDiagonalAlpha A Y false
  apply CategoryTheory.class_detects_from_integral_and_unit_action
    (ordinaryFinitePushforward A (projectiveLineDiagonalProjection Y false)) _
    (asIso (projectiveLineDiagonalAlpha A Y false) ≪≫
      (ordinaryFinitePushforward A (projectiveLineDiagonalProjection Y false)).mapIso
        ((lowerStar (ModuleCat.{u + 1} A)
          (pullback.diagonal (ProjectiveLine Y ↘ Y))).singleFunctorCompRightDerivedFunctorIso.app
            (ordinaryFiniteConstant A (ProjectiveLine Y))))
    (arbitraryBaseFiniteP1DiagonalTrace A N hA t d Y hY false) _ hunit
  simp only [ordinaryFiniteP1DiagonalSupportedMap, ordinaryFiniteSupportedRealization,
    supportedExactDerivedMap, Functor.map_comp, Category.assoc] at ht
  simp only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Category.assoc]
  transport_exact ht

end

-- The scalar and derived normalization calculations need extra elaboration.
/-- The supported Kummer class of the relative projective-line diagonal detects
endomorphisms of its finite etale Tate line. This statement concerns only finite
etale coefficients; it has no reduction tower, completion or pro-etale object.
Source: diagonal coefficient changes (3), residue one, using the arbitrary-base
finite P1 integral normalization.
(blueprint: lem-diagonal-finite-etale-class-detection).

Proof: choose an arbitrary-base finite P1 splitting and use uniqueness of the
positive supported Kummer boundary to identify its diagonal class with the
canonical class. The first-projection integral of that class is the identity.
Local triviality of the finite Tate line identifies its endomorphisms with
endomorphisms of the monoidal unit. Every such action is a natural
endomorphism of the identity functor, hence commutes with all Ext classes;
this is proved by dimension shifting through injective objects. Move the
two scalar actions to the supported source and apply the normalized integral.
The resulting derived equality gives equality after ordinary direct image
by the degree-zero homology comparison. To reflect scalar equality on the
supported source, use the two inverse-image/direct-image adjunctions of the
first projection and the diagonal. The first inverse image is fully faithful
by connected-fibre smooth base change; its composite with diagonal inverse
image is the identity. The composite adjunction unit therefore makes the
diagonal unit invertible after first direct image. Naturality of unit actions,
followed by the invertible first-adjunction counit on its unit object, reflects
the scalar equality. Bijectivity of unit action on a rank-one object finishes.
This argument also includes empty schemes and the zero coefficient ring. -/
theorem finiteEtaleDiagonalClass_postcomp_injective
    (Y : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (hI : (pullback.diagonal (ProjectiveLine Y ↘ Y)).ker.IsInvertible)
    (hW : IsUnit (N : Γ(pullback (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y), ⊤))) :
    let W := pullback (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)
    let L := Scheme.finiteEtaleTateLine W N A hA
    Function.Injective (fun f : L ⟶ L ↦
      (geoCartierEtaleClass A N hN hA (pullback.diagonal (ProjectiveLine Y ↘ Y))
        hI hW).comp (Ext.mk₀ f) (add_zero 2)) := by
  dsimp only
  let P := ProjectiveLine Y
  let q := P ↘ Y
  let W := pullback q q
  let p : W ⟶ P := pullback.fst q q
  let i : P ⟶ W := pullback.diagonal q
  let F := upperStar (ModuleCat.{u + 1} A) p
  let G := lowerStar (ModuleCat.{u + 1} A) p
  let H := upperStar (ModuleCat.{u + 1} A) i
  let K := lowerStar (ModuleCat.{u + 1} A) i
  let adj := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p
  let adjH := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i
  let L := Scheme.finiteEtaleTateLine W N A hA
  let S := K.obj (ordinaryFiniteConstant A P)
  let R := ordinaryFinitePushforward A (projectiveLineDiagonalProjection Y false)
  have hY : IsUnit (N : Γ(Y, ⊤)) := by
    simpa only [map_natCast] using hW.map
      ((ProjectiveLine.infinity Y ≫ i).appTop.hom)
  have hInv (x : W) : IsUnit (N : W.presheaf.stalk x) := by
    simpa only [map_natCast] using (hW.map ((W.presheaf.germ ⊤ x (by trivial)).hom))
  have hL : IsIso (MonoidalClosed.id L) := by
    apply Scheme.isIso_id_of_lisseRankOne
    exact Scheme.finiteEtaleTateLine_localTrivial W N hN hInv A hA
  let : GeometricallyConnected q := projectiveLine_connected Y
  let : Smooth q := SmoothOfRelativeDimension.smooth 1 q
  let : Flat q := inferInstance
  let : ∀ M : Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A),
      IsIso (adj.unit.app M) := unit_pullback A p
  let : IsIso adj.unit := NatIso.isIso_of_isIso_app _
  let FF : F.FullyFaithful := adj.fullyFaithfulLOfIsIsoUnit
  let : F.Full := FF.full
  let : F.Faithful := FF.faithful
  have hip : i ≫ p = 𝟙 P := by simp [i, p]
  let ep : F ⋙ H ≅ 𝟭 _ :=
    (upperStarComp (ModuleCat.{u + 1} A) i p (𝟙 P) hip.symm).symm ≪≫
      upperStarId (ModuleCat.{u + 1} A) P
  let : (F ⋙ H).IsEquivalence := Functor.isEquivalence_of_iso ep.symm
  have hunit₀ := CategoryTheory.source_unit_action_detected F G H K adj adjH
    (Functor.Monoidal.εIso F) (Functor.Monoidal.εIso H).symm
  have hunit : Function.Injective (fun a : End
      (𝟙_ (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A))) ↦
      R.map ((DerivedCategory.singleFunctor _ 0).map (unitEndAction S a).asHom)) := by
    intro a b hab
    apply hunit₀
    have hR : R = G.rightDerivedFunctor := rfl
    rw [hR] at hab
    exact CategoryTheory.map_eq_of_derived_single_map_eq G _ _ hab
  obtain ⟨t, d, ht⟩ := canonical_diagonal_integral N hN A hA Y hY
  exact diagonal_class_detects Y N hN A hA hI hW hY t d (ht false) hunit

end AlgebraicGeometry.Etale
