/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedPointLift
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Descent of locally constant sheaves along universal homeomorphisms

Let `u : X ⟶ Y` be a universal homeomorphism. Pullback along `u` is an equivalence of the
categories of étale sheaves (`AlgebraicGeometry.Etale.isEquivalence_upperStar`, Stacks 03SI),
so a sheaf `G` on `Y` is constant if and only if `u^* G` is
(`CategoryTheory.Sheaf.isConstant_upperStar_iff`). Since base change along `u` is moreover
essentially surjective on étale schemes (Stacks 04DZ), a trivialising cover of `u^* G` comes
from an étale cover of `Y`, and `G` is locally constant if `u^* G` is
(`AlgebraicGeometry.Scheme.IsLocallyConstantSheaf.of_upperStar`).

Finiteness of the stalks descends along a *surjective closed immersion* `p : W ⟶ Z`: every
geometric point of `Z` lifts to `W` (`AlgebraicGeometry.Scheme.exists_comp_eq_of_surjective`,
the residue field maps of a closed immersion being surjective), and the stalk of `p^* G` at a
lift is the stalk of `G` (`AlgebraicGeometry.Scheme.IsFiniteSheaf.of_upperStar`,
`IsFiniteLocallyConstantSheaf.of_upperStar`). This is the case needed for the independence of
constructibility from the scheme structures on the strata, see
`WeilConjectures.ConstructibleSheaf.Refinement`.
(blueprint: `lemma-constructible-universal-homeomorphism-invariance`)

-/

@[expose] public section

universe u u'

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme

section Points

variable {W Z : Scheme.{u}} (p : W ⟶ Z) [SurjectiveOnStalks p]

/-- Field-valued points lift along a surjective morphism which is surjective on stalks, for
instance along a surjective closed immersion. -/
lemma exists_comp_eq_of_surjective [Surjective p] {K : Type u} [Field K]
    (s : Spec (.of K) ⟶ Z) : ∃ s' : Spec (.of K) ⟶ W, s' ≫ p = s :=
  exists_comp_eq_of_mem_range p s (p.surjective _)

end Points

section Constant

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
variable {X Y : Scheme.{u}} (u : X ⟶ Y) [IsUniversalHomeomorphism u]

omit [HasSmallSiteSheafify A] in
/-- **Constancy descends along a universal homeomorphism**: `u^*` is fully faithful and carries
constant sheaves to constant sheaves. -/
lemma _root_.CategoryTheory.Sheaf.isConstant_upperStar_iff (G : Sheaf Y.smallEtaleTopology A) :
    ((Etale.upperStar A u).obj G).IsConstant X.smallEtaleTopology ↔
      G.IsConstant Y.smallEtaleTopology := by
  refine ⟨fun h ↦ ?_, fun _ ↦ Sheaf.IsConstant.upperStar A u G⟩
  have := Etale.isEquivalence_upperStar A u
  obtain ⟨a, ⟨i⟩⟩ := ((Etale.upperStar A u).obj G).mem_essImage_of_isConstant
  exact Sheaf.isConstant_of_iso _ ((Etale.upperStar A u).preimageIso
    (i.symm ≪≫ ((upperStarConstantSheafIso A u).app a).symm))

end Constant

section LocallyConstant

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
variable {X Y : Scheme.{u}} (u : X ⟶ Y) [IsUniversalHomeomorphism u]

attribute [local instance] Scheme.Hom.isEquivalence_etale

instance : JointlySurjective etalePrecoverage.{u} :=
  inferInstanceAs (JointlySurjective (precoverage @Etale))

/-- **Local constancy descends along a universal homeomorphism** `u : X ⟶ Y`: every member
`V' ⟶ X` of a trivialising cover of `u^* G` is the base change of an étale `V ⟶ Y`
(Stacks 04DZ), the `V` cover `Y` since `u` is surjective, and `V ×_Y X ⟶ V` is again a
universal homeomorphism, along which the constancy of the pullback of `G` to `V ×_Y X`
descends to `V`. (blueprint: `lemma-constructible-universal-homeomorphism-invariance`) -/
theorem IsLocallyConstantSheaf.of_upperStar (G : Sheaf Y.smallEtaleTopology A)
    [IsLocallyConstantSheaf ((Etale.upperStar A u).obj G)] : IsLocallyConstantSheaf G := by
  obtain ⟨⟨𝒰, h𝒰⟩⟩ :=
    IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := (Etale.upperStar A u).obj G)
  let V (i : 𝒰.I₀) : Y.Etale := u.Etale.objPreimage (𝒰.etalePrecoverageToEtale i)
  let e (i : 𝒰.I₀) : u.Etale.obj (V i) ≅ 𝒰.etalePrecoverageToEtale i :=
    u.Etale.objObjPreimageIso _
  have hinv (i : 𝒰.I₀) : (e i).inv.left ≫ pullback.snd (V i).hom u = 𝒰.f i :=
    MorphismProperty.Over.w (e i).inv
  let 𝒱 : Cover.{u} etalePrecoverage Y :=
    { I₀ := 𝒰.I₀
      X i := (V i).left
      f i := (V i).hom
      mem₀ := by
        refine (presieve₀_mem_precoverage_iff _).mpr ⟨fun y ↦ ?_, fun i ↦ (V i).prop⟩
        obtain ⟨x, rfl⟩ := u.surjective y
        obtain ⟨i, x', rfl⟩ := 𝒰.exists_eq x
        refine ⟨i, (pullback.fst (V i).hom u) ((e i).inv.left x'), ?_⟩
        change ((e i).inv.left ≫ pullback.fst (V i).hom u ≫ (V i).hom) x' = (𝒰.f i ≫ u) x'
        rw [pullback.condition, ← Category.assoc, hinv]
        rfl }
  refine ⟨⟨⟨𝒱, fun i ↦ ?_⟩⟩⟩
  rw [isConstant_over_iff_upperStar]
  change ((Etale.upperStar A (V i).hom).obj G).IsConstant (V i).left.smallEtaleTopology
  refine (Sheaf.isConstant_upperStar_iff A (pullback.fst (V i).hom u) _).mp ?_
  have h₁ : ((Etale.upperStar A (𝒰.f i)).obj ((Etale.upperStar A u).obj G)).IsConstant
      (𝒰.etalePrecoverageToEtale i).left.smallEtaleTopology :=
    (isConstant_over_iff_upperStar A (𝒰.etalePrecoverageToEtale i) _).mp (h𝒰 i)
  have h₂ : ((Etale.upperStar A (e i).hom.left).obj
      ((Etale.upperStar A (𝒰.f i)).obj ((Etale.upperStar A u).obj G))).IsConstant
        (pullback (V i).hom u).smallEtaleTopology :=
    Sheaf.IsConstant.upperStar A _ _
  have hsnd : pullback.snd (V i).hom u = (e i).hom.left ≫ 𝒰.f i :=
    (MorphismProperty.Over.w (e i).hom).symm
  let e' : (Etale.upperStar A (pullback.fst (V i).hom u)).obj
      ((Etale.upperStar A (V i).hom).obj G) ≅
      (Etale.upperStar A (e i).hom.left).obj
        ((Etale.upperStar A (𝒰.f i)).obj ((Etale.upperStar A u).obj G)) :=
    ((Etale.upperStarComp A (pullback.fst (V i).hom u) (V i).hom).app G).symm ≪≫
      eqToIso (congrArg (fun m ↦ (Etale.upperStar A m).obj G) pullback.condition) ≪≫
      (Etale.upperStarComp A (pullback.snd (V i).hom u) u).app G ≪≫
      eqToIso (congrArg (fun m ↦ (Etale.upperStar A m).obj ((Etale.upperStar A u).obj G)) hsnd) ≪≫
      (Etale.upperStarComp A (e i).hom.left (𝒰.f i)).app ((Etale.upperStar A u).obj G)
  exact Sheaf.isConstant_congr _ e'.symm

end LocallyConstant

section Finite

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
variable {W Z : Scheme.{u}} (p : W ⟶ Z) [IsClosedImmersion p] [Surjective p]

omit [HasSmallSiteSheafify A] in
/-- **Finiteness descends along a surjective closed immersion** `p : W ⟶ Z`: a geometric
point of `Z` lifts to `W`, and the stalk of `p^* G` at the lift is the stalk of `G`.
(blueprint: `lemma-constructible-universal-homeomorphism-invariance`) -/
theorem IsFiniteSheaf.of_upperStar (G : Sheaf Z.smallEtaleTopology A)
    [IsFiniteSheaf ((Etale.upperStar A p).obj G)] : IsFiniteSheaf G where
  isFinitelyGenerated_sheafFiber Ω _ _ s := by
    obtain ⟨s', rfl⟩ := exists_comp_eq_of_surjective p s
    exact (IsFiniteSheaf.isFinitelyGenerated_sheafFiber (FA := FA) (CA := CA)
      (F := (Etale.upperStar A p).obj G) Ω s').of_iso
      ((Etale.upperStarCompSheafFiberIso A p s').app G)

/-- **Finite local constancy descends along a surjective closed immersion.**
(blueprint: `lemma-constructible-universal-homeomorphism-invariance`) -/
theorem IsFiniteLocallyConstantSheaf.of_upperStar (G : Sheaf Z.smallEtaleTopology A)
    [IsFiniteLocallyConstantSheaf ((Etale.upperStar A p).obj G)] :
    IsFiniteLocallyConstantSheaf G where
  toIsLocallyConstantSheaf := IsLocallyConstantSheaf.of_upperStar p G
  toIsFiniteSheaf := IsFiniteSheaf.of_upperStar p G

/-- A sheaf is finite locally constant if and only if its pullback along a surjective closed
immersion is. -/
theorem isFiniteLocallyConstantSheaf_upperStar_iff (G : Sheaf Z.smallEtaleTopology A) :
    IsFiniteLocallyConstantSheaf ((Etale.upperStar A p).obj G) ↔
      IsFiniteLocallyConstantSheaf G :=
  ⟨fun _ ↦ IsFiniteLocallyConstantSheaf.of_upperStar p G,
    fun _ ↦ IsFiniteLocallyConstantSheaf.upperStar p G⟩

end Finite

end AlgebraicGeometry.Scheme

end
