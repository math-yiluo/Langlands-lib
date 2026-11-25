/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
public import WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Pullback stability of constructible sheaves

For a morphism of schemes `g : Y ⟶ X`, the pullback `g^*` sends locally constant sheaves to
locally constant sheaves (`AlgebraicGeometry.Scheme.IsLocallyConstantSheaf.upperStar`), finite
sheaves to finite sheaves (`IsFiniteSheaf.upperStar`), finite locally constant sheaves to
finite locally constant sheaves (`IsFiniteLocallyConstantSheaf.upperStar`) and constructible
sheaves to constructible sheaves (`IsConstructibleSheaf.upperStar`); all four notions are
invariant under isomorphism of sheaves.

The restriction `F.over U` of `F` to the small étale site localized at an étale `X`-scheme `U`
is identified with the pullback `(U.hom)^* F` on the small étale site of `U.left`
(`AlgebraicGeometry.Scheme.isConstant_over_iff_upperStar`), through the equivalence of sites
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`; with this the trivialising
cover of `g^* F` is the pullback of a trivialising cover of `F`, and constancy is preserved by
pullback (`AlgebraicGeometry.Scheme.upperStarConstantSheafIso`). Finiteness is checked on
stalks, which pullback preserves (`AlgebraicGeometry.Etale.upperStarCompSheafFiberIso`), and
a stratification pulls back to a stratification
(`AlgebraicGeometry.Scheme.Stratification.pullback`).
(blueprint: `prop-constructible-pullback`)

-/

@[expose] public section

universe u u'

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

section Constant

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

omit [HasSmallSiteSheafify A] in
/-- The pullback of a constant sheaf is constant. -/
lemma _root_.CategoryTheory.Sheaf.IsConstant.upperStar (g : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology A) [F.IsConstant X.smallEtaleTopology] :
    ((Etale.upperStar A g).obj F).IsConstant Y.smallEtaleTopology := by
  obtain ⟨a, ⟨i⟩⟩ := F.mem_essImage_of_isConstant
  exact Sheaf.isConstant_of_iso _
    ((Etale.upperStar A g).mapIso i.symm ≪≫ (upperStarConstantSheafIso A g).app a)

/-- The restriction of `F` to the small étale site localized at `U`, transported to the small
étale site of `U.left`, is the pullback of `F` along `U.hom`. -/
def overSheafEquivFunctorObjOverIso (U : X.Etale) (F : Sheaf X.smallEtaleTopology A) :
    (Etale.overSheafEquiv U A).functor.obj (F.over U) ≅ (Etale.upperStar A U.hom).obj F :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (X := (Etale.overSheafEquiv U A).functor.obj (F.over U))
    (Y := (GrothendieckTopology.localizationRestriction A @Etale @Etale le_rfl U.hom U.prop).obj F)
    (Functor.isoWhiskerRight (NatIso.op (Etale.etaleToOverCompForgetIso U).symm) F.obj) ≪≫
    ((GrothendieckTopology.upperStarIsoLocalizationRestriction A @Etale @Etale le_rfl U.hom
      U.prop).app F).symm

/-- The restriction of `F` to the small étale site localized at an étale `X`-scheme `U` is
constant if and only if the pullback of `F` to `U.left` is constant. -/
lemma isConstant_over_iff_upperStar (U : X.Etale) (F : Sheaf X.smallEtaleTopology A) :
    (F.over U).IsConstant (X.smallEtaleTopology.over U) ↔
      ((Etale.upperStar A U.hom).obj F).IsConstant U.left.smallEtaleTopology := by
  rw [← Sheaf.isConstant_sheafCongr_functor_iff (J := X.smallEtaleTopology.over U)
    (K := U.left.smallEtaleTopology) (Etale.overEquiv U) Over.mkIdTerminal (F.over U)]
  constructor
  · intro h
    have : ((Etale.overSheafEquiv U A).functor.obj (F.over U)).IsConstant
      U.left.smallEtaleTopology := h
    exact Sheaf.isConstant_congr _ (overSheafEquivFunctorObjOverIso A U F)
  · intro h
    exact Sheaf.isConstant_congr _ (overSheafEquivFunctorObjOverIso A U F).symm

end Constant

section LocallyConstant

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

instance : etalePrecoverage.{u}.IsStableUnderBaseChange :=
  inferInstanceAs (precoverage @Etale).IsStableUnderBaseChange

omit [HasSmallSiteSheafify A] in
/-- Locally constant sheaves are invariant under isomorphism.
(blueprint: `lemma-constructible-iso-invariance`) -/
lemma IsLocallyConstantSheaf.of_iso {F F' : Sheaf X.smallEtaleTopology A} (i : F ≅ F')
    [IsLocallyConstantSheaf F] : IsLocallyConstantSheaf F' := by
  obtain ⟨⟨𝒰, h𝒰⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
  exact ⟨⟨⟨𝒰, fun j ↦
    have := h𝒰 j
    Sheaf.isConstant_congr _ ((X.smallEtaleTopology.overPullback A _).mapIso i)⟩⟩⟩

/-- **Pullback of a locally constant sheaf is locally constant**: the pullback of a
trivialising cover is a trivialising cover.
(blueprint: `lemma-constructible-pullback-locally-constant`) -/
theorem IsLocallyConstantSheaf.upperStar (g : Y ⟶ X) (F : Sheaf X.smallEtaleTopology A)
    [IsLocallyConstantSheaf F] : IsLocallyConstantSheaf ((Etale.upperStar A g).obj F) := by
  obtain ⟨⟨𝒰, h𝒰⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
  refine ⟨⟨⟨𝒰.pullback₂ g, fun j ↦ ?_⟩⟩⟩
  rw [isConstant_over_iff_upperStar]
  have h₁ : ((Etale.upperStar A (𝒰.f j)).obj F).IsConstant (𝒰.X j).smallEtaleTopology :=
    (isConstant_over_iff_upperStar A (𝒰.etalePrecoverageToEtale j) F).mp (h𝒰 j)
  have h₂ : ((Etale.upperStar A (pullback.fst (𝒰.f j) g)).obj
      ((Etale.upperStar A (𝒰.f j)).obj F)).IsConstant
        (Cover.etalePrecoverageToEtale (𝒰.pullback₂ g) j).left.smallEtaleTopology :=
    Sheaf.IsConstant.upperStar A _ _
  let e : (Etale.upperStar A (pullback.fst (𝒰.f j) g)).obj ((Etale.upperStar A (𝒰.f j)).obj F) ≅
      (Etale.upperStar A (pullback.snd (𝒰.f j) g)).obj ((Etale.upperStar A g).obj F) :=
    ((Etale.upperStarComp A (pullback.fst (𝒰.f j) g) (𝒰.f j)).app F).symm ≪≫
      eqToIso (congrArg (fun m ↦ (Etale.upperStar A m).obj F) pullback.condition) ≪≫
      (Etale.upperStarComp A (pullback.snd (𝒰.f j) g) g).app F
  exact Sheaf.isConstant_congr _ e

end LocallyConstant

section Finite

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

omit [HasSmallSiteSheafify A] in
/-- Finite sheaves are invariant under isomorphism.
(blueprint: `lemma-constructible-iso-invariance`) -/
lemma IsFiniteSheaf.of_iso {F F' : Sheaf X.smallEtaleTopology A} (i : F ≅ F')
    [IsFiniteSheaf F] : IsFiniteSheaf F' where
  isFinitelyGenerated_sheafFiber Ω _ _ s :=
    (IsFiniteSheaf.isFinitelyGenerated_sheafFiber (FA := FA) (CA := CA) (F := F) Ω s).of_iso
      ((pointSmallEtale s).sheafFiber.mapIso i)

omit [HasSmallSiteSheafify A] in
/-- **Pullback of a finite sheaf is finite**: the stalks of `g^* F` are stalks of `F`.
(blueprint: `lemma-constructible-pullback-finite`) -/
theorem IsFiniteSheaf.upperStar (g : Y ⟶ X) (F : Sheaf X.smallEtaleTopology A)
    [IsFiniteSheaf F] : IsFiniteSheaf ((Etale.upperStar A g).obj F) where
  isFinitelyGenerated_sheafFiber Ω _ _ s :=
    (IsFiniteSheaf.isFinitelyGenerated_sheafFiber (FA := FA) (CA := CA) (F := F) Ω
      (s ≫ g)).of_iso ((Etale.upperStarCompSheafFiberIso A g s).app F).symm

omit [HasSmallSiteSheafify A] in
/-- Finite locally constant sheaves are invariant under isomorphism.
(blueprint: `lemma-constructible-iso-invariance`) -/
lemma IsFiniteLocallyConstantSheaf.of_iso {F F' : Sheaf X.smallEtaleTopology A} (i : F ≅ F')
    [IsFiniteLocallyConstantSheaf F] : IsFiniteLocallyConstantSheaf F' where
  toIsLocallyConstantSheaf := IsLocallyConstantSheaf.of_iso i
  toIsFiniteSheaf := IsFiniteSheaf.of_iso i

/-- **Pullback of a finite locally constant sheaf is finite locally constant.** -/
theorem IsFiniteLocallyConstantSheaf.upperStar (g : Y ⟶ X) (F : Sheaf X.smallEtaleTopology A)
    [IsFiniteLocallyConstantSheaf F] :
    IsFiniteLocallyConstantSheaf ((Etale.upperStar A g).obj F) where
  toIsLocallyConstantSheaf := IsLocallyConstantSheaf.upperStar g F
  toIsFiniteSheaf := IsFiniteSheaf.upperStar g F

end Finite

section Stratification

/-- The pullback of a stratification of `X` along `g : Y ⟶ X`: the strata are the preimages
of the strata, with the base changes of the immersions.
(blueprint: `lemma-constructible-pullback-stratification`) -/
@[simps n stratum domain immersion]
def Stratification.pullback (S : Stratification X) (g : Y ⟶ X) : Stratification Y where
  n := S.n
  stratum i := g.base ⁻¹' S.stratum i
  isLocallyClosed_stratum i := (S.isLocallyClosed_stratum i).preimage g.continuous
  iUnion_stratum_eq_univ := by
    rw [← Set.preimage_iUnion, S.iUnion_stratum_eq_univ, Set.preimage_univ]
  pairwise_disjoint_stratum i j hij := (S.pairwise_disjoint_stratum hij).preimage _
  isConstructible_stratum i := g.isConstructible_preimage (S.isConstructible_stratum i)
  domain i := Limits.pullback (S.immersion i) g
  immersion i := Limits.pullback.snd (S.immersion i) g
  range_immersion i := by rw [Pullback.range_snd, S.range_immersion]

end Stratification

section Constructible

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

omit [HasSmallSiteSheafify A] in
/-- Constructible sheaves are invariant under isomorphism.
(blueprint: `lemma-constructible-iso-invariance`) -/
lemma IsConstructibleSheaf.of_iso {F F' : Sheaf X.smallEtaleTopology A} (i : F ≅ F')
    [IsConstructibleSheaf F] : IsConstructibleSheaf F' := by
  obtain ⟨S, hS⟩ := IsConstructibleSheaf.exists_stratification (FA := FA) (CA := CA) (F := F)
  exact ⟨S, fun j ↦
    have := hS j
    IsFiniteLocallyConstantSheaf.of_iso ((Etale.upperStar A (S.immersion j)).mapIso i)⟩

/-- **Pullback of a constructible sheaf is constructible**: the stratification pulls back, and
the pullback of `F` to a pulled-back stratum is the pullback of the pullback of `F` to the
stratum. (blueprint: `prop-constructible-pullback`) -/
theorem IsConstructibleSheaf.upperStar (g : Y ⟶ X) (F : Sheaf X.smallEtaleTopology A)
    [IsConstructibleSheaf F] : IsConstructibleSheaf ((Etale.upperStar A g).obj F) := by
  obtain ⟨S, hS⟩ := IsConstructibleSheaf.exists_stratification (FA := FA) (CA := CA) (F := F)
  refine ⟨S.pullback g, fun j ↦ ?_⟩
  have := hS j
  have h : IsFiniteLocallyConstantSheaf ((Etale.upperStar A (pullback.fst (S.immersion j) g)).obj
      ((Etale.upperStar A (S.immersion j)).obj F)) :=
    IsFiniteLocallyConstantSheaf.upperStar _ _
  refine IsFiniteLocallyConstantSheaf.of_iso
    (F := (Etale.upperStar A (pullback.fst (S.immersion j) g)).obj
      ((Etale.upperStar A (S.immersion j)).obj F)) ?_
  exact ((Etale.upperStarComp A (pullback.fst (S.immersion j) g) (S.immersion j)).app F).symm ≪≫
    eqToIso (congrArg (fun m ↦ (Etale.upperStar A m).obj F) pullback.condition) ≪≫
    (Etale.upperStarComp A (pullback.snd (S.immersion j) g) g).app F

end Constructible

end AlgebraicGeometry.Scheme

end
