/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientPullback
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
public import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange

/-! # A step of diagonal scalar pullback propagation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private theorem diagonal_isPullback {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (b : BaseSquares g) :
    IsPullback (baseP g) (diagonalImmersion Y') (diagonalImmersion Y) (baseW g) := by
  have hp := ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g
  refine IsPullback.mk' b.diagonal_square.symm ?_ ?_
  · intro T a a' _ h
    exact (cancel_mono (diagonalImmersion Y')).mp h
  · intro T a d h
    have h₁ : (d ≫ pullback.fst _ _) ≫ baseP g = a := by
      have hh := h =≫ pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)
      simpa [diagonalImmersion, baseW, Category.assoc] using hh.symm
    have h₂ : (d ≫ pullback.snd _ _) ≫ baseP g = a := by
      have hh := h =≫ pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)
      simpa [diagonalImmersion, baseW, Category.assoc] using hh.symm
    have hd : d ≫ pullback.fst _ _ = d ≫ pullback.snd _ _ := by
      apply hp.hom_ext
      · exact h₁.trans h₂.symm
      · simp only [Category.assoc, pullback.condition]
    refine ⟨d ≫ pullback.fst _ _, h₁, ?_⟩
    apply pullback.hom_ext
    · simp [diagonalImmersion, Category.assoc]
    · simpa [diagonalImmersion, Category.assoc] using hd

private theorem exchangeRight_isIso
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    {L : B ⥤ A} {Q : A ⥤ B} {L' : B' ⥤ A'} {Q' : A' ⥤ B'}
    {G : B ⥤ B'} {G' : A ⥤ A'} (a : L ⊣ Q) (a' : L' ⊣ Q')
    (e : G ⋙ L' ≅ L ⋙ G') (hc : IsIso a.counit)
    (hu : ∀ M : A, IsIso (a'.unit.app (G.obj (Q.obj M)))) :
    IsIso (Adjunction.exchangeRight a a' e) := by
  let _ := hc
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have h := hu M
  rw [Adjunction.exchangeRight_app]
  infer_instance

private theorem abelian_pullback_supported
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (hX : X' ⟶ X) (hS : S' ⟶ S) [IsClosedImmersion f] [IsClosedImmersion f']
    (sq : IsPullback hX f' f hS) (M : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :
    IsZero ((upperStar Ab.{u + 1} f'.openComplement.ι).obj
      ((upperStar Ab.{u + 1} hS).obj ((lowerStar Ab.{u + 1} f).obj M))) := by
  let j := f.openComplement.ι
  let j' := f'.openComplement.ι
  have hav : Set.range (j' ≫ hS).base ⊆ Set.range j.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change hS (j' x) ∉ Set.range f
    rintro ⟨z, hz⟩
    obtain ⟨t, _, ht⟩ := Scheme.exists_preimage_of_isPullback sq z (j' x) hz
    exact x.2 (Set.mem_range.mpr ⟨t, ht⟩)
  let l := IsOpenImmersion.lift j (j' ≫ hS) hav
  have he : l ≫ j = j' ≫ hS := IsOpenImmersion.lift_fac j (j' ≫ hS) hav
  have hzero := isZero_upperStar_lowerStar_of_disjoint Ab.{u + 1} f j
    (by simp only [j, Scheme.Opens.range_ι, Scheme.Hom.coe_openComplement]
        exact disjoint_compl_right) M
  refine ((upperStar Ab.{u + 1} l).map_isZero hzero).of_iso ?_
  exact ((upperStarComp Ab.{u + 1} j' hS).app _).symm ≪≫
    (upperStarCongr Ab.{u + 1} he.symm).app _ ≪≫
    (upperStarComp Ab.{u + 1} l j).app _

private theorem module_closed_unit
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    [IsClosedImmersion f] [IsClosedImmersion f'] [IsNoetherian S']
    (sq : IsPullback hX f' f hS) (M : Modules R X) :
    IsIso ((CondensedRing.upperStarLowerStarAdjunction R f').unit.app
      ((CondensedRing.upperStar R hS).obj ((CondensedRing.lowerStar R f).obj M))) := by
  let N := (CondensedRing.upperStar R hS).obj ((CondensedRing.lowerStar R f).obj M)
  have hz₀ := abelian_pullback_supported f f' hX hS sq ((Mod.forget _).obj M)
  have hz : IsZero ((upperStar Ab.{u + 1} f'.openComplement.ι).obj
      ((Mod.forget _).obj N)) := by
    refine hz₀.of_iso ((upperStar Ab.{u + 1} f'.openComplement.ι).mapIso ?_)
    exact ((upperStar Ab.{u + 1} hS).mapIso
      ((CondensedRing.lowerStarForgetIso R f).app M) ≪≫
      (CondensedRing.upperStarForgetIso R hS).app
        ((CondensedRing.lowerStar R f).obj M)).symm
  have hu := (abelian_closed_support_counit_and_unit f' f'.openComplement.ι
    (by simp only [Scheme.Opens.range_ι, Scheme.Hom.coe_openComplement])).2 _ hz
  have hm : IsIso ((Mod.forget _).map
      ((CondensedRing.upperStarLowerStarAdjunction R f').unit.app N)) := by
    rw [CondensedRing.forget_map_upperStarLowerStarAdjunction_unit_app' R f' N]
    infer_instance
  exact isIso_of_reflects_iso _ (Mod.forget _)

private theorem module_closed_exchange
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    [IsClosedImmersion f] [IsClosedImmersion f'] [IsNoetherian S']
    (sq : IsPullback hX f' f hS) :
    IsIso (ordinaryExchange R f f' hX hS sq.w.symm) := by
  have hc : IsIso (CondensedRing.upperStarLowerStarAdjunction R f).counit := by
    infer_instance
  have hx := exchangeRight_isIso
    (A := Modules R X) (B := Modules R S) (A' := Modules R X') (B' := Modules R S')
    (L := CondensedRing.upperStar R f) (Q := CondensedRing.lowerStar R f)
    (L' := CondensedRing.upperStar R f') (Q' := CondensedRing.lowerStar R f')
    (G := CondensedRing.upperStar R hS) (G' := CondensedRing.upperStar R hX)
    (CondensedRing.upperStarLowerStarAdjunction R f)
    (CondensedRing.upperStarLowerStarAdjunction R f')
    ((CondensedRing.upperStarComp R f' hS).symm ≪≫
      CondensedRing.upperStarCongr R sq.w.symm ≪≫ CondensedRing.upperStarComp R hX f)
    hc (module_closed_unit R f f' hX hS sq)
  exact hx

/-- Invertibility of the canonical ordinary supported-source map for the diagonal.

Source: latest blueprint, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (3), closed diagonal base change.
(blueprint: lem-diagonal-scalar-closed-source-exchange).

Proof: The diagonal square is Cartesian by projective-space base change and the
universal property of the self-product. The inverse image of a closed direct image
vanishes on the primed open complement, since inverse-image composition identifies
its restriction with inverse image of the unprimed complementary restriction.
Closed-support localization makes the primed closed adjunction unit invertible.
The closed counit is invertible by full faithfulness. Expanding the exchange mate
as this unit, the inverse-image comparison and this counit therefore proves it
invertible. The forgetful comparisons identify the supported underlying sheaf
and express the underlying module unit as the abelian unit followed by isomorphisms.
The forgetful functor reflects invertibility; the module closed counit is also
invertible. The same generic mate calculation therefore applies to module objects.
Compose with direct image of c.iso; its composite is sourcePullbackMap by definition.
This argument includes the empty scheme and does not use coefficients or a trace. -/
theorem diagonalScalar_source_map_isIso
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [IsNoetherian Y] [IsNoetherian Y']
    (b : BaseSquares g) (c : UnitPullEndpoint R (baseP g)) :
    IsIso (sourcePullbackMap R g b.diagonal_square c) := by
  have : IsNoetherian (ProjectiveLine Y') :=
    isNoetherian_of_locallyOfFiniteType (ProjectiveLine Y' ↘ Y')
  have : IsNoetherian (diagonalSurface Y') :=
    isNoetherian_of_locallyOfFiniteType
      (pullback.fst (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y'))
  have hs := module_closed_exchange R (diagonalImmersion Y) (diagonalImmersion Y')
    (baseP g) (baseW g) (diagonal_isPullback g b)
  unfold sourcePullbackMap
  infer_instance

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
