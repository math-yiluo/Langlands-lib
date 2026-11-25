/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.ConstructibleSheaf.GenericConstancy
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Products

/-!
# Finite direct sums of finite locally constant sheaves

A finite direct sum of constant sheaves is constant, the constant sheaf functor being a left
adjoint (`CategoryTheory.Sheaf.IsConstant.biprod`). The pullbacks `g^*` are left adjoints as
well, so the direct sum of two locally constant sheaves is trivialised by the fibre product of
trivialising covers (`AlgebraicGeometry.Scheme.IsLocallyConstantSheaf.biprod`); the stalk
functors are left adjoints (to the skyscraper functors), so the stalk of a direct sum is the
direct sum of the stalks, and a direct sum of finitely generated objects is finitely generated
when the forgetful functor of the coefficient category preserves finite limits
(`CategoryTheory.ConcreteCategory.IsFinitelyGenerated.biprod`); hence a direct sum of finite
sheaves is finite (`IsFiniteSheaf.biprod`). Together,
finite direct sums of finite locally constant sheaves are finite locally constant
(`IsFiniteLocallyConstantSheaf.biprod`).
(blueprint: `lemma:constructible-flc-biproduct`)

-/

@[expose] public section

universe u u' v v'

open CategoryTheory Limits Opposite

noncomputable section

namespace CategoryTheory

section Adjunction

variable {C : Type*} [Category* C] {D : Type*} [Category* D] [Preadditive C] [Preadditive D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D] {F : C ⥤ D} {G : D ⥤ C}

/-- The comparison isomorphism `F (X ⊞ Y) ≅ F X ⊞ F Y` for a left adjoint `F` between
categories with binary biproducts: `F` preserves binary coproducts. -/
def Adjunction.leftAdjointBiprodIso (adj : F ⊣ G) (X Y : C) :
    F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y :=
  have := adj.leftAdjoint_preservesColimits
  F.mapIso (biprod.isoCoprod X Y) ≪≫ (PreservesColimitPair.iso F X Y).symm ≪≫
    (biprod.isoCoprod _ _).symm

end Adjunction

section Constant

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u') [Category.{v'} A] [HasWeakSheafify J A] [Preadditive A] [HasBinaryBiproducts A]
  [HasBinaryBiproducts (Sheaf J A)] {T : C} (hT : IsTerminal T)

include hT in
/-- **A finite direct sum of constant sheaves is constant**: the constant sheaf functor is a
left adjoint, so `M_X ⊞ N_X ≅ (M ⊞ N)_X`. -/
lemma Sheaf.IsConstant.biprod (F G : Sheaf J A) [F.IsConstant J] [G.IsConstant J] :
    (F ⊞ G).IsConstant J := by
  obtain ⟨a, ⟨i⟩⟩ := F.mem_essImage_of_isConstant
  obtain ⟨b, ⟨j⟩⟩ := G.mem_essImage_of_isConstant
  exact Sheaf.isConstant_of_iso _
    (biprod.mapIso i.symm j.symm ≪≫ ((constantSheafAdj J A hT).leftAdjointBiprodIso a b).symm)

end Constant

end CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

section LocallyConstant

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

/-- The direct sum of two locally constant sheaves is locally constant, trivialised by the
fibre product of trivialising covers. (blueprint: `lemma:constructible-flc-biproduct`) -/
theorem IsLocallyConstantSheaf.biprod (F G : Sheaf X.smallEtaleTopology A)
    [IsLocallyConstantSheaf F] [IsLocallyConstantSheaf G] : IsLocallyConstantSheaf (F ⊞ G) := by
  obtain ⟨⟨𝒰, h𝒰⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
  obtain ⟨⟨𝒱, h𝒱⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := G)
  refine ⟨⟨⟨𝒰.bind fun i ↦ 𝒱.pullback₂ (𝒰.f i), fun ⟨i, j⟩ ↦ ?_⟩⟩⟩
  rw [isConstant_over_iff_upperStar]
  set f := pullback.snd (𝒱.f j) (𝒰.f i) ≫ 𝒰.f i
  change ((Etale.upperStar A f).obj (F ⊞ G)).IsConstant
    (pullback (𝒱.f j) (𝒰.f i)).smallEtaleTopology
  have hF : ((Etale.upperStar A f).obj F).IsConstant
      (pullback (𝒱.f j) (𝒰.f i)).smallEtaleTopology := by
    have h₁ : ((Etale.upperStar A (𝒰.f i)).obj F).IsConstant (𝒰.X i).smallEtaleTopology :=
      (isConstant_over_iff_upperStar A (𝒰.etalePrecoverageToEtale i) F).mp (h𝒰 i)
    have h₂ : ((Etale.upperStar A (𝒰.f i) ⋙ Etale.upperStar A (pullback.snd (𝒱.f j) (𝒰.f i))).obj
        F).IsConstant (pullback (𝒱.f j) (𝒰.f i)).smallEtaleTopology :=
      Sheaf.IsConstant.upperStar A (pullback.snd (𝒱.f j) (𝒰.f i))
        ((Etale.upperStar A (𝒰.f i)).obj F)
    exact Sheaf.isConstant_congr _
      ((Etale.upperStarComp A (pullback.snd (𝒱.f j) (𝒰.f i)) (𝒰.f i)).app F).symm
  have hG : ((Etale.upperStar A f).obj G).IsConstant
      (pullback (𝒱.f j) (𝒰.f i)).smallEtaleTopology := by
    have h₁ : ((Etale.upperStar A (𝒱.f j)).obj G).IsConstant (𝒱.X j).smallEtaleTopology :=
      (isConstant_over_iff_upperStar A (𝒱.etalePrecoverageToEtale j) G).mp (h𝒱 j)
    have h₂ : ((Etale.upperStar A (𝒱.f j) ⋙ Etale.upperStar A (pullback.fst (𝒱.f j) (𝒰.f i))).obj
        G).IsConstant (pullback (𝒱.f j) (𝒰.f i)).smallEtaleTopology :=
      Sheaf.IsConstant.upperStar A (pullback.fst (𝒱.f j) (𝒰.f i))
        ((Etale.upperStar A (𝒱.f j)).obj G)
    refine Sheaf.isConstant_congr _
      (((Etale.upperStarComp A (pullback.fst (𝒱.f j) (𝒰.f i)) (𝒱.f j)).app G).symm ≪≫
        eqToIso (congrArg (fun m ↦ (Etale.upperStar A m).obj G) pullback.condition))
  have hFG : ((Etale.upperStar A f).obj F ⊞ (Etale.upperStar A f).obj G).IsConstant
      (pullback (𝒱.f j) (𝒰.f i)).smallEtaleTopology :=
    Sheaf.IsConstant.biprod _ _ terminalIsTerminal _ _
  exact Sheaf.isConstant_congr _
    ((Etale.upperStarLowerStarAdjunction A f).leftAdjointBiprodIso F G).symm

end LocallyConstant

section Finite

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [PreservesFiniteLimits (CategoryTheory.forget A)]

omit [HasSmallSiteSheafify A] in
/-- The direct sum of two finite sheaves is finite: the stalk of `F ⊞ G` is the direct sum of the
stalks, which is finitely generated. (blueprint: `lemma:constructible-flc-biproduct`) -/
theorem IsFiniteSheaf.biprod (F G : Sheaf X.smallEtaleTopology A)
    [IsFiniteSheaf F] [IsFiniteSheaf G] : IsFiniteSheaf (F ⊞ G) where
  isFinitelyGenerated_sheafFiber Ω _ _ s :=
    ((IsFiniteSheaf.isFinitelyGenerated_sheafFiber (FA := FA) (CA := CA) (F := F) Ω s).biprod
      (IsFiniteSheaf.isFinitelyGenerated_sheafFiber (FA := FA) (CA := CA) (F := G) Ω s)).of_iso
      (((pointSmallEtale s).skyscraperSheafAdjunction (A := A)).leftAdjointBiprodIso F G).symm

/-- **A finite direct sum of finite locally constant sheaves is finite locally constant.**
(blueprint: `lemma:constructible-flc-biproduct`) -/
theorem IsFiniteLocallyConstantSheaf.biprod (F G : Sheaf X.smallEtaleTopology A)
    [IsFiniteLocallyConstantSheaf F] [IsFiniteLocallyConstantSheaf G] :
    IsFiniteLocallyConstantSheaf (F ⊞ G) where
  toIsLocallyConstantSheaf := IsLocallyConstantSheaf.biprod F G
  toIsFiniteSheaf := IsFiniteSheaf.biprod F G

end Finite

end AlgebraicGeometry.Scheme

end
