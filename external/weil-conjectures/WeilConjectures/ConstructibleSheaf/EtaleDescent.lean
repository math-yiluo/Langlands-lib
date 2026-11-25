/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DensePoints
public import WeilConjectures.ConstructibleSheaf.GenericConstancy

/-!
# Descent of finite locally constant sheaves along surjective étale morphisms

Let `u : U ⟶ T` be surjective and étale. A geometric point of `T` lifts to `U`: its base change
along `u` is a nonempty étale scheme over a separably closed field, which has a rational point
(`AlgebraicGeometry.Scheme.exists_comp_eq_of_etale_of_surjective`). Since `u` is moreover a
one-member étale cover of `T`, a sheaf `G` on `T` is finite locally constant as soon as `u^* G`
is (`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.of_upperStar_of_etale`).
-/

@[expose] public section

universe u u'

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {U T : Scheme.{u}} (u : U ⟶ T) [Etale u] [Surjective u]

/-- **Geometric points lift along a surjective étale morphism**: for `Ω` separably closed, every
`s : Spec Ω ⟶ T` factors through `u`. The base change of `u` along `s` is a nonempty étale, hence
smooth, `Ω`-scheme, and so has an `Ω`-rational point. -/
lemma exists_comp_eq_of_etale_of_surjective {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ T) : ∃ s' : Spec (.of Ω) ⟶ U, s' ≫ u = s := by
  have : Nonempty (pullback u s : Scheme.{u}) :=
    ⟨((pullback.snd u s).surjective (IsLocalRing.closedPoint Ω)).choose⟩
  obtain ⟨⟨p, hp⟩⟩ := (pullback.snd u s).nonempty_fieldPoints
  refine ⟨p ≫ pullback.fst u s, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hp]
  simp

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The one-member étale cover of `T` given by a surjective étale `u : U ⟶ T`. -/
def Cover.ofEtaleOfSurjective : Cover.{u} etalePrecoverage T where
  I₀ := PUnit
  X _ := U
  f _ := u
  mem₀ := by
    refine (presieve₀_mem_precoverage_iff _).mpr ⟨fun t ↦ ?_, fun _ ↦ inferInstance⟩
    obtain ⟨x, rfl⟩ := u.surjective t
    exact ⟨⟨⟩, x, rfl⟩

/-- **Local constancy descends along a surjective étale morphism**, `u` being a one-member étale
cover. -/
theorem IsLocallyConstantSheaf.of_upperStar_of_etale [HasSmallSiteSheafify A]
    (G : Sheaf T.smallEtaleTopology A) [IsLocallyConstantSheaf ((Etale.upperStar A u).obj G)] :
    IsLocallyConstantSheaf G :=
  have : ∀ i, IsLocallyConstantSheaf
      ((Etale.upperStar A ((Cover.ofEtaleOfSurjective u).f i)).obj G) := fun _ ↦ ‹_›
  IsLocallyConstantSheaf.of_cover (Cover.ofEtaleOfSurjective u) G

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

/-- **Finiteness descends along a surjective étale morphism**: a geometric point of `T` lifts
to `U`, and the stalk of `u^* G` at the lift is the stalk of `G`. -/
theorem IsFiniteSheaf.of_upperStar_of_etale (G : Sheaf T.smallEtaleTopology A)
    [IsFiniteSheaf ((Etale.upperStar A u).obj G)] : IsFiniteSheaf G where
  isFinitelyGenerated_sheafFiber Ω _ _ s := by
    obtain ⟨s', rfl⟩ := exists_comp_eq_of_etale_of_surjective u s
    exact (IsFiniteSheaf.isFinitelyGenerated_sheafFiber (FA := FA) (CA := CA)
      (F := (Etale.upperStar A u).obj G) Ω s').of_iso
      ((Etale.upperStarCompSheafFiberIso A u s').app G)

/-- **Finite local constancy descends along a surjective étale morphism.** -/
theorem IsFiniteLocallyConstantSheaf.of_upperStar_of_etale [HasSmallSiteSheafify A]
    (G : Sheaf T.smallEtaleTopology A)
    [IsFiniteLocallyConstantSheaf ((Etale.upperStar A u).obj G)] :
    IsFiniteLocallyConstantSheaf G where
  toIsLocallyConstantSheaf := IsLocallyConstantSheaf.of_upperStar_of_etale u G
  toIsFiniteSheaf := IsFiniteSheaf.of_upperStar_of_etale u G

end AlgebraicGeometry.Scheme
