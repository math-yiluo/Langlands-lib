import Langlands.GroupScheme.FiberwiseMonomorphism
import Langlands.GroupScheme.FiniteFibreQuasiFiniteNeighbourhood
import Langlands.GroupScheme.FiniteUniformExponent
import Langlands.GroupScheme.FiniteUnitFibreSpreading
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Torus.MultiplicativeTypeMonomorphismSpreadingStatement
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeClosedSubgroupGeometry
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeLocality
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeTorsion
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-! # Proof of multiplicative-type monomorphism spreading -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace RelativeMultiplicativeType

variable {S : Scheme.{u}} {H K : GroupScheme S}

/-- The generic point in a valuative square extends through finite ambient torsion.
Schematic dominance of the fraction-field spectrum forces the lift into the subgroup. -/
private theorem closedSubgroup_valuativeExistence (hH : IsMultiplicativeType H)
    (i : K ⟶ H) (hi : IsClosedSubgroup i) [IsAffineHom K.X.hom] [LocallyQuasiFinite K.X.hom] :
    ValuativeCriterion.Existence K.X.hom := by
  intro sq
  let j := Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K))
  let b := j ≫ sq.i₂
  let T := Over.mk (𝟙 (Spec (CommRingCat.of sq.K)))
  let x : (Over.map b).obj T ⟶ K.X := Over.homMk sq.i₁ (by
    change sq.i₁ ≫ K.X.hom = 𝟙 _ ≫ b
    simpa only [Category.id_comp] using sq.commSq.w)
  have : LocallyQuasiFinite ((baseChange b).obj K).X.hom := by
    change LocallyQuasiFinite (pullback.snd K.X.hom b)
    infer_instance
  have : QuasiCompact ((baseChange b).obj K).X.hom := by
    change QuasiCompact (pullback.snd K.X.hom b)
    infer_instance
  have : IsLocallyArtinian (Spec (CommRingCat.of sq.K)) :=
    Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
  have hfinite : IsFinite ((baseChange b).obj K).X.hom :=
    IsFinite.of_locallyQuasiFinite _
  obtain ⟨n, hn, hpow⟩ := finiteGroupSchemeUniformExponent sq.K ((baseChange b).obj K) hfinite
  let e := baseChangePointsEquiv b K T
  have hx : x ^ n = 1 := by
    simpa only [map_pow, map_one, MulEquiv.apply_symm_apply] using
      congrArg e (hpow T (e.symm x))
  have : IsCommMonObj H.X := hH.isCommMonObj
  have hxi : (x ≫ i.hom.hom) ^ (n : ℤ) = 1 := by
    rw [zpow_natCast, ← MonObj.pow_comp, hx, MonObj.one_comp]
  obtain ⟨y, hy, _⟩ := (existsUnique_torsion_lift_iff H (n : ℤ) _ _).mpr hxi
  have : IsFinite (torsion H (n : ℤ)).X.hom := (hH.torsion_geometry n hn).1
  have hclosed : UniversallyClosed (torsion H (n : ℤ)).X.hom := inferInstance
  rw [UniversallyClosed.eq_valuativeCriterion] at hclosed
  let torsionSquare : ValuativeCommSq (torsion H (n : ℤ)).X.hom := {
    R := sq.R
    K := sq.K
    i₁ := y.left
    i₂ := sq.i₂
    commSq := ⟨by
      change y.left ≫ (torsion H (n : ℤ)).X.hom = b
      have hybase := Over.w y
      change y.left ≫ (torsion H (n : ℤ)).X.hom = 𝟙 _ ≫ b at hybase
      simpa only [Category.id_comp] using hybase⟩ }
  obtain ⟨l, hl₁, hl₂⟩ := (hclosed.1 torsionSquare).exists_lift
  change j ≫ l = y.left at hl₁
  change l ≫ (torsion H (n : ℤ)).X.hom = sq.i₂ at hl₂
  let r := l ≫ (torsionι H (n : ℤ)).hom.hom.left
  have hgeneric : j ≫ r = sq.i₁ ≫ i.hom.hom.left := by
    rw [← Category.assoc, hl₁]
    exact congrArg (fun a : (Over.map b).obj T ⟶ H.X => a.left) hy
  have : IsDominant j := by
    constructor
    change DenseRange (PrimeSpectrum.comap (algebraMap sq.R sq.K))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective sq.R sq.K)]
    exact bot_le
  have : IsSchemeTheoreticallyDominant j := IsSchemeTheoreticallyDominant.of_isDominant j
  have hker : i.hom.hom.left.ker ≤ r.ker := by
    have heq : (j ≫ r).ker = r.ker := by
      rw [Scheme.Hom.ker_comp, j.ker_eq_bot, Scheme.IdealSheafData.map_bot]
    rw [← heq, hgeneric]
    exact sq.i₁.le_ker_comp _
  have : IsClosedImmersion i.hom.hom.left := hi
  let lift := IsClosedImmersion.lift i.hom.hom.left r hker
  have hfactor : lift ≫ i.hom.hom.left = r := IsClosedImmersion.lift_fac _ _ _
  refine ⟨⟨{ l := lift, fac_left := ?_, fac_right := ?_ }⟩⟩
  · change j ≫ lift = sq.i₁
    apply (cancel_mono i.hom.hom.left).mp
    rw [Category.assoc, hfactor, hgeneric]
  · change lift ≫ K.X.hom = sq.i₂
    calc
      lift ≫ K.X.hom = lift ≫ (i.hom.hom.left ≫ H.X.hom) :=
        congrArg (lift ≫ ·) (Over.w i.hom.hom).symm
      _ = r ≫ H.X.hom := by rw [← Category.assoc, hfactor]
      _ = sq.i₂ := by
        dsimp only [r]
        rw [Category.assoc, Over.w (torsionι H (n : ℤ)).hom.hom, hl₂]

/-- Every locally quasi-finite closed subgroup of a relative group of multiplicative
type is finite over the base. -/
theorem IsMultiplicativeType.isFinite_of_locallyQuasiFinite_closedSubgroup
    (hH : IsMultiplicativeType H) (i : K ⟶ H) (hi : IsClosedSubgroup i)
    [LocallyQuasiFinite K.X.hom] : IsFinite K.X.hom := by
  have : IsAffineHom K.X.hom := hH.closedSubgroup_isAffineHom i hi
  have : IsClosedImmersion i.hom.hom.left := hi
  have : LocallyOfFinitePresentation H.X.hom := hH.locallyOfFinitePresentation
  have : LocallyOfFiniteType K.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : UniversallyClosed K.X.hom := UniversallyClosed.of_valuativeCriterion _
    (closedSubgroup_valuativeExistence hH i hi)
  have : IsProper K.X.hom := ⟨⟩
  exact IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩

end RelativeMultiplicativeType

/-- Monomorphisms from groups of multiplicative type spread from a single fibre
for a separated target and are detected on all fibres for any target. -/
theorem multiplicativeTypeMonomorphismSpreading :
    MultiplicativeTypeMonomorphismSpreadingStatement.{u} := by
  intro S H G hH hbase f
  have : LocallyOfFinitePresentation H.X.hom := hH.locallyOfFinitePresentation
  have hbase' : IsLocallyNoetherian S ∨ LocallyOfFiniteType G.X.hom :=
    hbase.imp_right fun h => by
      let := h
      infer_instance
  constructor
  · intro hsep s hs
    let := hsep
    have hι : IsClosedSubgroup (kernelι f) := kernelι_isClosedImmersion f
    have : IsAffineHom (kernel f).X.hom := hH.closedSubgroup_isAffineHom (kernelι f) hι
    have : LocallyOfFinitePresentation (kernel f).X.hom :=
      locallyOfFinitePresentation_kernel_of_source f hbase'
    have hs' : IsIso ((baseChange (S.fromSpecResidueField s)).obj (kernel f)).X.hom :=
      (baseChange_kernel_hom_isIso_iff _ f).mpr hs
    obtain ⟨V, hsV, hV⟩ :=
      FiniteFibreQuasiFiniteNeighbourhood.exists_locallyQuasiFinite_neighbourhood_of_isFinite_fibre
        (kernel f) s inferInstance
    have : LocallyQuasiFinite ((baseChange V.ι).obj (kernel f)).X.hom := hV
    have hfinite : IsFinite ((baseChange V.ι).obj (kernel f)).X.hom :=
      (hH.baseChange V.ι).isFinite_of_locallyQuasiFinite_closedSubgroup
        ((baseChange V.ι).map (kernelι f)) (hι.baseChange V.ι)
    obtain ⟨U, hsU, hU⟩ :=
      FiniteUnitFibreSpreading.exists_isIso_neighbourhood_of_finite_neighbourhood
        (kernel f) s ⟨V, hsV, hfinite⟩ hs'
    exact ⟨U, hsU, (baseChange_kernel_hom_isIso_iff _ f).mp hU⟩
  · exact mono_of_residueField_fibres f hbase'

end Langlands.GroupScheme
