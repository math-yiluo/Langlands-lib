/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.IhomComparison
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Conservative
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.InternalHom

/-!
# The internal hom of finite locally constant sheaves

Let `Λ` be a commutative ring. For sheaves of `Λ`-modules on the small étale site of a scheme
`X`:

- the constant sheaf functor preserves internal homs out of finitely presented modules
  (`AlgebraicGeometry.Etale.isIso_ihomComparison_constantSheaf_app`): it is monoidal and exact;
- for `Λ` noetherian, the internal hom `[L, M]` of two finite locally constant sheaves is finite
  locally constant (`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.ihom`, blueprint
  `lemma-section-normal-bundle--1`, clause (1)): on a common trivialising cover, pullback
  commuting with internal homs, it is the constant sheaf at `Hom_Λ(P, Q)` for finitely generated,
  hence finitely presented, modules `P` and `Q`.

We also record two local criteria along an étale cover: a morphism of sheaves whose pullbacks to
the members of an étale cover are isomorphisms is an isomorphism
(`AlgebraicGeometry.Etale.isIso_of_isIso_upperStar_map_of_cover`), and finiteness of a sheaf is
étale local (`AlgebraicGeometry.Scheme.IsFiniteSheaf.of_cover`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal

namespace AlgebraicGeometry

open Scheme

variable {X : Scheme.{u}}

/-- A geometric point of `X` lifts to a member of an étale cover of `X`. -/
lemma Scheme.Cover.exists_comp_eq_of_isSepClosed (𝒰 : Cover.{u} etalePrecoverage X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    ∃ (i : 𝒰.I₀) (t : Spec (.of Ω) ⟶ 𝒰.X i), t ≫ 𝒰.f i = s := by
  obtain ⟨i, v, hv⟩ := 𝒰.exists_eq (s.base (IsLocalRing.closedPoint Ω))
  have : Etale (𝒰.f i) := 𝒰.map_prop i
  obtain ⟨t, -⟩ := pointSmallEtaleFiberObjToPreimage_surjective s rfl (Scheme.Etale.mk (𝒰.f i))
    ⟨v, hv.trans (congrArg s.base (Subsingleton.elim _ _))⟩
  exact ⟨i, t.left, Over.w t⟩

section General

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- **Isomorphy is étale local**: a morphism of étale sheaves whose pullbacks to the members of
an étale cover are isomorphisms is an isomorphism. -/
lemma Etale.isIso_of_isIso_upperStar_map_of_cover (𝒰 : Cover.{u} etalePrecoverage X)
    {F G : Sheaf X.smallEtaleTopology A} (φ : F ⟶ G)
    (h : ∀ i, IsIso ((Etale.upperStar A (𝒰.f i)).map φ)) : IsIso φ := by
  have : ∀ i, Etale (𝒰.f i) := 𝒰.map_prop
  refine Etale.isIso_of_isIso_localizationRestriction A _ 𝒰.f ?_ fun i ↦ ?_
  · refine Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
    exact Set.mem_iUnion.2 ⟨i, y, hy⟩
  · let r := Etale.upperStarIsoLocalizationRestriction A (𝒰.f i) inferInstance
    have h' := r.hom.naturality φ
    rw [← cancel_epi (r.inv.app _), Iso.inv_hom_id_app_assoc] at h'
    rw [← h']
    have := h i
    infer_instance

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

/-- **Finiteness is étale local**: if the pullbacks of `G` to the members of an étale cover are
finite, so is `G`. -/
theorem Scheme.IsFiniteSheaf.of_cover (𝒰 : Cover.{u} etalePrecoverage X)
    (G : Sheaf X.smallEtaleTopology A)
    [∀ i, IsFiniteSheaf (FA := FA) (CA := CA) ((Etale.upperStar A (𝒰.f i)).obj G)] :
    IsFiniteSheaf (FA := FA) (CA := CA) G where
  isFinitelyGenerated_sheafFiber Ω _ _ s := by
    obtain ⟨i, t, rfl⟩ := 𝒰.exists_comp_eq_of_isSepClosed s
    exact (IsFiniteSheaf.isFinitelyGenerated_sheafFiber (FA := FA) (CA := CA)
      (F := (Etale.upperStar A (𝒰.f i)).obj G) Ω t).of_iso
      ((Etale.upperStarCompSheafFiberIso A (𝒰.f i) t).app G)

end General

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The constant sheaf at a finitely generated module is finite: its stalks are the module. -/
lemma Scheme.isFiniteSheaf_constantSheaf (H : ModuleCat.{u + 1} Λ) [Module.Finite Λ H] :
    IsFiniteSheaf ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj H) where
  isFinitelyGenerated_sheafFiber Ω _ _ s := by
    have : PreservesFilteredColimitsOfSize.{u, u}
        (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
      preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    exact ((ModuleCat.isFinitelyGenerated_iff H).2 inferInstance).of_iso
      ((pointSmallEtale s).sheafFiberConstantSheafIso H).symm

/-- **The constant sheaf functor preserves internal homs out of finitely presented modules**:
for `P` finitely presented, the comparison map `[P, Q]_X ⟶ [P_X, Q_X]` is an isomorphism. The
constant sheaf functor is monoidal, additive, left exact and a left adjoint. -/
theorem Etale.isIso_ihomComparison_constantSheaf_app (P Q : ModuleCat.{u + 1} Λ)
    [Module.FinitePresentation Λ P] :
    IsIso ((ihomComparison (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      P).app Q) := by
  have := MonoidalClosed.monoidalPreadditive_of_braided
    (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  have : PreservesFiniteLimits (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    comp_preservesFiniteLimits (Functor.const _) (presheafToSheaf _ _)
  have :=
    (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ) terminalIsTerminal).isLeftAdjoint
  exact ModuleCat.isIso_ihomComparison_app_of_finitePresentation _ P Q

/-- Blueprint `lemma-section-normal-bundle--1`: Rigidity of morphisms of finite locally
constant sheaves

*The Hom sheaf*, clause (1): for `Λ` noetherian, the internal hom `[L, M]` of two finite
locally constant sheaves of `Λ`-modules on `X_ét` is finite locally constant. On a common
trivialising cover, nonempty members, `L` and `M` are the constant sheaves at finitely generated,
hence finitely presented, modules `P` and `Q`; the pullback commutes with internal homs
(`AlgebraicGeometry.Etale.isIso_ihomComparison_upperStar`) and so does the constant sheaf
functor (`AlgebraicGeometry.Etale.isIso_ihomComparison_constantSheaf_app`), so that `[L, M]` is
there the constant sheaf at the finitely generated module `Hom_Λ(P, Q)`. -/
theorem Scheme.IsFiniteLocallyConstantSheaf.ihom [IsNoetherianRing Λ]
    (L M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsFiniteLocallyConstantSheaf L] [IsFiniteLocallyConstantSheaf M] :
    IsFiniteLocallyConstantSheaf ((CategoryTheory.ihom L).obj M) := by
  obtain ⟨𝒰₀, h𝒰₀⟩ := IsLocallyConstantSheaf.exists_cover₂ L M
  let 𝒰 := 𝒰₀.nonemptyMembers
  have key (i : 𝒰.I₀) : ∃ H : ModuleCat.{u + 1} Λ, Module.Finite Λ H ∧
      Nonempty ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj
          ((CategoryTheory.ihom L).obj M) ≅
        (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj H) := by
    set Y := 𝒰.X i
    set g := 𝒰.f i
    have : Etale g := 𝒰.map_prop i
    have hL : ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj L).IsConstant Y.smallEtaleTopology :=
      (h𝒰₀ i.1).1
    have hM : ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj M).IsConstant Y.smallEtaleTopology :=
      (h𝒰₀ i.1).2
    obtain ⟨P, ⟨eL⟩⟩ := ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj L).mem_essImage_of_isConstant
    obtain ⟨Q, ⟨eM⟩⟩ := ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj M).mem_essImage_of_isConstant
    have : IsFiniteSheaf ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj P) :=
      have := IsFiniteSheaf.upperStar (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) g L
      IsFiniteSheaf.of_iso eL.symm
    have : IsFiniteSheaf ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj Q) :=
      have := IsFiniteSheaf.upperStar (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) g M
      IsFiniteSheaf.of_iso eM.symm
    have : Module.Finite Λ P := moduleFinite_of_isFiniteSheaf_constantSheaf (Y := Y) P
    have : Module.Finite Λ Q := moduleFinite_of_isFiniteSheaf_constantSheaf (Y := Y) Q
    have : Module.FinitePresentation Λ P := Module.finitePresentation_of_finite Λ P
    have := Etale.isIso_ihomComparison_constantSheaf_app (X := Y) P Q
    have := Etale.isIso_ihomComparison_upperStar (ModuleCat.{u + 1} Λ) g L
    refine ⟨(CategoryTheory.ihom P).obj Q, ?_, ⟨?_⟩⟩
    · have : Module.Finite Λ (P →ₗ[Λ] Q) := Module.Finite.linearMap_of_isNoetherianRing
      exact Module.Finite.equiv ModuleCat.homLinearEquiv.symm
    · exact asIso ((ihomComparison (Etale.upperStar (ModuleCat.{u + 1} Λ) g) L).app M) ≪≫
        (CategoryTheory.ihom _).mapIso eM.symm ≪≫
        asIso ((MonoidalClosed.pre eL.hom).app _) ≪≫
        (asIso ((ihomComparison (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
          P).app Q)).symm
  choose H hH e using key
  have hc (i : 𝒰.I₀) : ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj
      ((CategoryTheory.ihom L).obj M)).IsConstant (𝒰.X i).smallEtaleTopology :=
    Sheaf.isConstant_of_iso _ (e i).some
  have (i : 𝒰.I₀) : IsFiniteSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj
      ((CategoryTheory.ihom L).obj M)) :=
    have := hH i
    have := Scheme.isFiniteSheaf_constantSheaf (X := 𝒰.X i) (H i)
    IsFiniteSheaf.of_iso (e i).some.symm
  exact
    { toIsLocallyConstantSheaf := ⟨⟨⟨𝒰, fun i ↦ (isConstant_over_iff_upperStar _ _ _).2 (hc i)⟩⟩⟩
      toIsFiniteSheaf := IsFiniteSheaf.of_cover 𝒰 _ }

end AlgebraicGeometry
