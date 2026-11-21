import Langlands.Global.AdelicLeadingCuspidalComponents
import Langlands.Global.EisensteinConstantTerm.Height
import Langlands.GroupScheme.SubgroupFunctor.OpenEquality

/-! # Parameter twists in nested constant terms and Levi pairings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints

namespace StandardParabolicFamily

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (P J : StandardIndex F G fam.i fam.ν)
  [IsClosedImmersion (fam.p P).hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (fam.p P) K)
  (hJP : J ≤ P)

local notation "Y" => (AdelicGroupPoints F G → ℂ)
local notation "Parameter" => ComplexCharacterParameter F (fam.P P)

include hJP in
/-- A norm-one point of the smaller Levi has zero height increment
for the height of the containing standard parabolic. -/
theorem heightPower_normOneLevi_mul (lam : Parameter) (m : normOneSubgroup F (fam.M J))
    (g : AdelicGroupPoints F G) :
    hK.heightPower lam (map F (fam.M J) G (fam.l J ≫ fam.p J) m.val * g) =
      hK.heightPower lam g := by
  have hle := (fam.le_iff_range_le J P).mp hJP
  let f := SubgroupFunctor.rangeFactor (fam.p J) (fam.p P) hle
  have hf : f ≫ fam.p P = fam.p J := SubgroupFunctor.rangeFactor_comp _ _ hle
  rw [← hf, ← Category.assoc, map_comp_apply_of_hom, IsIwasawaCompact.heightPower,
    IsIwasawaCompact.heightPower, hK.height_map_mul, characterLog_map,
    (characterLog_eq_zero_iff F (fam.M J) m.val).mpr m.property, map_zero, zero_add]

include hJP in
/-- The Iwasawa height of the containing standard parabolic is constant
on each left orbit of the smaller parabolic's adelic radical. -/
theorem heightPower_standardRadical_mul (lam : Parameter) (v : AdelicGroupPoints F (fam.U J))
    (g : AdelicGroupPoints F G) :
    hK.heightPower lam (map F (fam.U J) G (fam.iU J ≫ fam.p J) v * g) =
      hK.heightPower lam g := by
  have hle := (fam.le_iff_range_le J P).mp hJP
  let f := SubgroupFunctor.rangeFactor (fam.p J) (fam.p P) hle
  have hf : f ≫ fam.p P = fam.p J := SubgroupFunctor.rangeFactor_comp _ _ hle
  rw [← hf, ← Category.assoc]
  exact hK.heightPower_unipotent_mul (fam.isUnipotentRadical J).1.isUnipotent
    (fam.iU J ≫ f) lam v g

include hJP in
/-- The twist commutes with the smaller normalized constant term. -/
theorem constantTerm_parameterTwist (phi : Y) (lam : Parameter) :
    fam.constantTerm J (hK.parameterTwist phi lam) =
      hK.parameterTwist (fam.constantTerm J phi) lam := by
  funext g
  let U := SubgroupFunctor.range (fam.iU J ≫ fam.p J)
  have hAt (x : AdelicSubgroupPoints.RationalQuotient F G U) :
      hK.heightPower lam ((Quotient.out x :
        AdelicSubgroupPoints.adelicPoints F G U).val * g) = hK.heightPower lam g := by
    let v := (Quotient.out x : AdelicSubgroupPoints.adelicPoints F G U)
    obtain ⟨y, hy⟩ := v.property
    let y' : AdelicGroupPoints F (fam.U J) := y
    have hy' : map F (fam.U J) G (fam.iU J ≫ fam.p J) y' = v.val := hy
    change hK.heightPower lam (v.val * g) = _
    rw [← hy']
    exact fam.heightPower_standardRadical_mul P J hK hJP lam y' g
  unfold constantTerm subgroupConstantTerm
  simp only [IsIwasawaCompact.parameterTwist, hAt, integral_mul_const]

include hJP in
/-- A Levi pairing sees the twist only at its external adelic argument. -/
theorem leviPairingIntegrand_parameterTwist (phi : Y) (lam : Parameter) (g : AdelicGroupPoints F G)
    (test : AdelicGroupPoints F (fam.M J) → ℂ) :
    fam.leviPairingIntegrand J (hK.parameterTwist phi lam) g test =
      fun x => fam.leviPairingIntegrand J phi g test x * hK.heightPower lam g := by
  funext x
  unfold leviPairingIntegrand IsIwasawaCompact.parameterTwist
  rw [fam.heightPower_normOneLevi_mul P J hK hJP, mul_right_comm]

include hJP in
/-- The Levi pairing of a twisted constant term is the original scalar
pairing multiplied by the height factor at the external argument. -/
theorem leviPairing_constantTerm_parameterTwist (phi : Y) (lam : Parameter)
    (g : AdelicGroupPoints F G) (test : AdelicGroupPoints F (fam.M J) → ℂ) :
    fam.leviPairing J (fam.constantTerm J (hK.parameterTwist phi lam)) g test =
      fam.leviPairing J (fam.constantTerm J phi) g test * hK.heightPower lam g := by
  rw [fam.constantTerm_parameterTwist P J hK hJP]
  unfold leviPairing
  rw [fam.leviPairingIntegrand_parameterTwist P J hK hJP, integral_mul_const]

end StandardParabolicFamily

/-- Compatibility of the actual norm-one Levi pairings and nested
constant terms with the larger parabolic's parameter twist. -/
def StandardConstantTermTwistStatement : Prop :=
  ∀ {F : Type u} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (P J : StandardIndex F G fam.i fam.ν)
    [IsClosedImmersion (fam.p P).hom.hom.left]
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (fam.p P) K),
    J ≤ P → ∀ (phi : AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F (fam.P P)),
      fam.constantTerm J (hK.parameterTwist phi lam) =
        hK.parameterTwist (fam.constantTerm J phi) lam ∧
      ∀ (g : AdelicGroupPoints F G) (test : AdelicGroupPoints F (fam.M J) → ℂ),
        fam.leviPairing J (fam.constantTerm J (hK.parameterTwist phi lam)) g test =
          fam.leviPairing J (fam.constantTerm J phi) g test * hK.heightPower lam g

theorem standardConstantTermTwist : StandardConstantTermTwistStatement.{u} := by
  intro F _ _ G _ _ _ fam P J _ K hK hJP phi lam
  exact ⟨fam.constantTerm_parameterTwist P J hK hJP phi lam,
    fam.leviPairing_constantTerm_parameterTwist P J hK hJP phi lam⟩

end Langlands.Global
