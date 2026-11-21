import Langlands.Global.AdelicLeadingCuspidalComponents
import Langlands.Global.EisensteinConstantTerm.Height
import Langlands.GroupScheme.Rational.NestedSplitComponentFactorization

/-! # Positive split components and parameters for nested adelic parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν

omit [NumberField F] in
private theorem parabolicRepresented (P : Idx) :
    (SubgroupFunctor.range (𝓕.p P)).IsRepresentedBy (𝓕.p P) := by
  let := (𝓕.isCompatible P).parabolic.isClosedSubgroup.mono
  exact ⟨Over.mono_of_mono_left _, rfl⟩

omit [NumberField F] in
private theorem leviRepresented (P : Idx) :
    (SubgroupFunctor.range (𝓕.l P ≫ 𝓕.p P)).IsRepresentedBy (𝓕.l P ≫ 𝓕.p P) := by
  let := ((𝓕.isCompatible P).levi.isClosedSubgroup.comp
    (𝓕.isCompatible P).parabolic.isClosedSubgroup).mono
  exact ⟨Over.mono_of_mono_left _, rfl⟩

/-- The all-test inclusion of the specified `Q` into `P`. -/
def nestedParabolicHom {Q P : Idx} (hQP : Q ≤ P) : 𝓕.P Q ⟶ 𝓕.P P :=
  (𝓕.parabolicRepresented P).factorHom (𝓕.p Q) ((𝓕.le_iff_range_le Q P).mp hQP)

omit [NumberField F] in
@[simp] theorem nestedParabolicHom_comp {Q P : Idx} (hQP : Q ≤ P) :
    𝓕.nestedParabolicHom hQP ≫ 𝓕.p P = 𝓕.p Q :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

omit [NumberField F] in
private theorem nestedLevi_range_le {Q P : Idx} (hQP : Q ≤ P) :
    SubgroupFunctor.range (𝓕.l Q ≫ 𝓕.p Q) ≤ SubgroupFunctor.range (𝓕.l P ≫ 𝓕.p P) := by
  rw [(𝓕.isCompatible Q).levi_eq, (𝓕.isCompatible P).levi_eq]
  exact (((standardParabolicOrder F G 𝓕.connectedReductive 𝓕.T 𝓕.i 𝓕.maximalSplit
    𝓕.ν 𝓕.generic).1 Q.1 P.1 Q.2 P.2).2 hQP).1

/-- The inclusion of the specified Levi of `Q` into the specified Levi of `P`. -/
def nestedLeviHom {Q P : Idx} (hQP : Q ≤ P) : 𝓕.M Q ⟶ 𝓕.M P :=
  (𝓕.leviRepresented P).factorHom (𝓕.l Q ≫ 𝓕.p Q) (𝓕.nestedLevi_range_le hQP)

omit [NumberField F] in
@[simp] theorem nestedLeviHom_comp {Q P : Idx} (hQP : Q ≤ P) :
    𝓕.nestedLeviHom hQP ≫ 𝓕.l P ≫ 𝓕.p P = 𝓕.l Q ≫ 𝓕.p Q :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

private def rootPresentation (P : Idx) : ParabolicRootPresentation (𝓕.p P) (𝓕.l P) (𝓕.a P) :=
  ⟨⟨𝓕.T, 𝓕.i, 𝓕.ν, P.1, 𝓕.f P⟩, 𝓕.isCompatible P⟩

/-- The specified split component of `P` maps into the specified split component of `Q`. -/
def nestedSplitComponentHom {Q P : Idx} (hQP : Q ≤ P) : 𝓕.A P ⟶ 𝓕.A Q :=
  (𝓕.rootPresentation Q).intermediateSplitComponentFactor (𝓕.l P ≫ 𝓕.p P)
    ((𝓕.isCompatible P).levi.isClosedSubgroup.comp (𝓕.isCompatible P).parabolic.isClosedSubgroup)
    (𝓕.nestedLeviHom hQP) (𝓕.nestedLeviHom_comp hQP) (𝓕.a P)
    (𝓕.isCompatible P).splitComponent.1.2 (𝓕.isCompatible P).splitComponent.1.1.1

omit [NumberField F] in
@[simp] theorem nestedSplitComponentHom_comp {Q P : Idx} (hQP : Q ≤ P) :
    CommGroupScheme.groupHom (𝓕.nestedSplitComponentHom hQP) ≫
      𝓕.a Q ≫ 𝓕.nestedLeviHom hQP = 𝓕.a P :=
  ParabolicRootPresentation.intermediateSplitComponentFactor_comp _ _ _ _ _ _ _ _

omit [NumberField F] in
/-- The two embeddings of the split component into the containing parabolic agree. -/
theorem nestedSplitComponentHom_parabolic_comp {Q P : Idx} (hQP : Q ≤ P) :
    CommGroupScheme.groupHom (𝓕.nestedSplitComponentHom hQP) ≫
      𝓕.a Q ≫ 𝓕.l Q ≫ 𝓕.nestedParabolicHom hQP = 𝓕.a P ≫ 𝓕.l P := by
  let := (𝓕.isCompatible P).parabolic.isClosedSubgroup.mono
  let : Mono (𝓕.p P).hom.hom := Over.mono_of_mono_left _
  have heq : (CommGroupScheme.groupHom (𝓕.nestedSplitComponentHom hQP) ≫
      𝓕.a Q ≫ 𝓕.l Q ≫ 𝓕.nestedParabolicHom hQP) ≫ 𝓕.p P =
      (𝓕.a P ≫ 𝓕.l P) ≫ 𝓕.p P := by
    simp only [Category.assoc, nestedParabolicHom_comp, ← nestedLeviHom_comp 𝓕 hQP]
    rw [← Category.assoc (𝓕.a Q) (𝓕.nestedLeviHom hQP) (𝓕.l P ≫ 𝓕.p P),
      ← Category.assoc (CommGroupScheme.groupHom (𝓕.nestedSplitComponentHom hQP))
        (𝓕.a Q ≫ 𝓕.nestedLeviHom hQP) (𝓕.l P ≫ 𝓕.p P),
      nestedSplitComponentHom_comp]
  apply Grp.hom_ext
  apply (cancel_mono (𝓕.p P).hom.hom).mp
  exact congrArg (fun j : (𝓕.A P).toGrp ⟶ G => j.hom.hom) heq

/-- Actual compatible lifts of positive split-component points along `Q ≤ P`. -/
theorem exists_positiveSplitComponent_lift {Q P : Idx} (hQP : Q ≤ P)
    (a : 𝓕.positiveSplitComponent P) :
    ∃ b : 𝓕.positiveSplitComponent Q,
      map F (𝓕.P Q) (𝓕.P P) (𝓕.nestedParabolicHom hQP) b =
        (a : AdelicGroupPoints F (𝓕.P P)) := by
  obtain ⟨x, hx, hxa⟩ := a.2
  let c := 𝓕.nestedSplitComponentHom hQP
  let y := map F (𝓕.A P).toGrp (𝓕.A Q).toGrp (CommGroupScheme.groupHom c) x
  have hy : y ∈ PositiveRealTorus.intrinsicSubgroup F (𝓕.A Q) :=
    PositiveRealTorus.map_intrinsicSubgroup_le F (𝓕.A P) (𝓕.A Q) c ⟨x, hx, rfl⟩
  let b := map F (𝓕.A Q).toGrp (𝓕.P Q) (𝓕.a Q ≫ 𝓕.l Q) y
  refine ⟨⟨b, ⟨y, hy, rfl⟩⟩, ?_⟩
  change map F (𝓕.P Q) (𝓕.P P) (𝓕.nestedParabolicHom hQP) b = _
  dsimp only [b, y]
  rw [← map_comp_apply_of_hom, ← map_comp_apply_of_hom, Category.assoc,
    𝓕.nestedSplitComponentHom_parabolic_comp hQP]
  exact hxa

/-- Parameter powers on an actual point are functorial under character restriction. -/
theorem _root_.Langlands.Global.AdelicGroupPoints.parameterPower_parameterRestrict
    {H H' : GroupScheme (Spec (CommRingCat.of F))}
    (j : H' ⟶ H) (lam : ComplexCharacterParameter F H) (x : AdelicGroupPoints F H') :
    parameterPower F H' (parameterRestrict j lam) x =
      parameterPower F H lam (map F H' H j x) := by
  simp only [parameterPower, complexParameterPairing_parameterRestrict,
    characterLog_map]

/-- At compatible positive points, the raw adelic shifts are identical and the values of a
parameter of `P` and its restriction to `Q` agree. -/
theorem exists_positiveSplitComponent_lift_with_values {Q P : Idx} (hQP : Q ≤ P)
    (a : 𝓕.positiveSplitComponent P) :
    ∃ b : 𝓕.positiveSplitComponent Q,
      map F (𝓕.P Q) G (𝓕.p Q) b = map F (𝓕.P P) G (𝓕.p P) a ∧
      ∀ lam : ComplexCharacterParameter F (𝓕.P P),
        parameterPower F (𝓕.P Q) (parameterRestrict (𝓕.nestedParabolicHom hQP) lam) b =
          parameterPower F (𝓕.P P) lam a := by
  obtain ⟨b, hb⟩ := 𝓕.exists_positiveSplitComponent_lift hQP a
  refine ⟨b, ?_, fun lam => ?_⟩
  · rw [← hb, ← map_comp_apply_of_hom, 𝓕.nestedParabolicHom_comp hQP]
  · rw [parameterPower_parameterRestrict, hb]

end Langlands.Global.StandardParabolicFamily
