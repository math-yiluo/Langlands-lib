import Langlands.GroupScheme.Trigonalizable.CharacterizationProof
import Langlands.GroupScheme.Trigonalizable.SplitSolvableStatement
import Langlands.GroupScheme.Absolute.SolvableQuotientExtension
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof
import Langlands.GroupScheme.Absolute.SolvableUnipotentKernelAssembly
import Langlands.GroupScheme.FlagCoreFixedLine
import Langlands.GroupScheme.FppfQuotientTargetSmooth
import Langlands.GroupScheme.MatrixRepresentation.Reindex
import Langlands.GroupScheme.ProperPseudoComplete
import Langlands.GroupScheme.Rational.FppfQuotientAction
import Langlands.GroupScheme.Rational.PerfectFieldSectionedSolvableQuotient
import Langlands.GroupScheme.SplitSolvableFixedPointProof
import Langlands.GroupScheme.SplitSolvableSmoothExtension
import Langlands.GroupScheme.Torus.DiagonalizableSmoothConnectedCriteriaProof

/-! # Split solvability and trigonalizability -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Langlands.AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme

open ProjectiveOrbit

/-- The split-solvable fixed-point theorem supplies a stable line in every
nonzero representation over the ground field. -/
theorem IsSplitSolvableGroupScheme.isTrigonalizable
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsSplitSolvableGroupScheme G) : IsTrigonalizable G := by
  intro ι _ _ _ ρ
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := ι))
  let e : ι ≃ Fin (m + 1) := Fintype.equivFinOfCardEq hm
  let X := ambient m (CommRingCat.of k)
  have : IsProper X.hom :=
    inferInstanceAs (IsProper (RelativeProjectiveSpace.toBase (Spec (CommRingCat.of k)) m))
  have hx₀ : Nonempty (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) :=
    ⟨Over.homMk (RelativeProjectiveSpace.basisSection m (Spec (CommRingCat.of k)) 0)
      (RelativeProjectiveSpace.basisSection_toBase m (Spec (CommRingCat.of k)) 0)⟩
  obtain ⟨x, hx⟩ := splitSolvablePseudoCompleteFixedPoint k G hG X
    (isPseudoComplete_of_isProper X) hx₀ (matrixSchemeAction (ρ.reindex e))
  obtain ⟨j, P, hP⟩ := exists_pointSection_eq_basisSection x
  let w := (P : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ Pi.single j 1
  have hw : w ≠ 0 := FlagCore.mulVec_ne_zero P (basisVector_ne_zero m j)
  refine ⟨w ∘ e, ?_, ?_⟩
  · intro h
    apply hw
    funext i
    simpa only [Function.comp_apply, Equiv.apply_symm_apply, Pi.zero_apply]
      using congrFun h (e.symm i)
  · intro T g
    obtain ⟨a, ha⟩ := stabilizedLine_of_isFixed (ρ.reindex e) hx hP T g
    change ((ρ.reindex e).pointMatrix T g : Matrix _ _ _) *ᵥ
      (fun i => scalarMap T (w i)) = (a : Γ(T.left, ⊤)) •
        fun i => scalarMap T (w i) at ha
    rw [MatrixRepresentation.reindex_pointMatrix, MatrixRepresentation.reindexGL_val,
      Matrix.submatrix_mulVec_equiv] at ha
    change (fun j => ((ρ.pointMatrix T g : Matrix ι ι _) *ᵥ
      (fun i => scalarMap T (w (e i)))) (e.symm j)) = _ at ha
    refine ⟨a, funext fun i => ?_⟩
    simpa only [Function.comp_apply, Equiv.symm_apply_apply, Pi.smul_apply]
      using congrFun ha (e i)

/-- A smooth connected affine group over a perfect field is split solvable
if it has a diagonalizable fppf quotient by a closed unipotent subgroup. -/
private theorem isSplitSolvableGroupScheme_of_diagonalizable_quotient
    {k : Type u} [Field k] [PerfectField k]
    {G U : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {Λ : Type u} [AddCommGroup Λ] [AddGroup.FG Λ]
    (i : U ⟶ G) (hi : IsClosedSubgroup i) (hU : IsUnipotent U)
    (q : G ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q) :
    IsSplitSolvableGroupScheme G := by
  classical
  let Q := (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp
  obtain ⟨p, hp⟩ := ExpChar.exists k
  have : Module.Free ℤ Λ :=
    (Diagonalizable.diagonalizableSmoothConnectedCriteria k p Λ).2.2.mp
      ⟨hq.smooth_target, hq.connectedSpace⟩
  have : Module.Finite ℤ Λ := Module.Finite.iff_addGroup_fg.mpr inferInstance
  have hQ : IsSplitTorus Q :=
    Diagonalizable.isSplitTorus _ (Module.Free.chooseBasis ℤ Λ).equivFun.toAddEquiv
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffineHom U.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : LocallyOfFiniteType U.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have hG : IsSolvableGroupScheme G :=
    isSolvableGroupScheme_of_unipotent_fppfQuotient hU hq
      (isSolvableGroupScheme_of_isCommMonObj Q)
  let d := perfectFieldSplitGeometricUnipotentRadical G
  have hd := d.isGeometricUnipotentRadical.1
  let D := d.isGeometricUnipotentRadical.torusQuotient solvableTorusQuotient hG
  have : Smooth d.source.X.hom := hd.smooth
  have : ConnectedSpace d.source.X.left := hd.connectedSpace
  have : IsClosedImmersion d.inclusion.hom.hom.left := hd.isClosedSubgroup
  have : IsAffineHom d.source.X.hom := by
    rw [← Over.w d.inclusion.hom.hom]
    infer_instance
  have hrange : SubgroupFunctor.range d.inclusion = SubgroupFunctor.range i := by
    apply le_antisymm
    · rw [← hq.2.2.2]
      exact range_le_kernelι_of_comp_eq_zero d.inclusion q
        (hd.isUnipotent.hom_eq_zero_of_isTorus hQ.isTorus (d.inclusion ≫ q))
    · rw [← D.isFppfQuotient.2.2.2]
      exact range_le_kernelι_of_comp_eq_zero i D.projection
        (hU.hom_eq_zero_of_isTorus D.isTorus (i ≫ D.projection))
  rw [← hrange] at hq
  exact IsSplitSolvableGroupScheme.of_splitUnipotent_kernel_splitTorus_quotient
    d.inclusion q hd.isClosedSubgroup hq hG d.isSplitUnipotent hQ

/-- Milne 2017, Proposition 16.52. Split solvability implies trigonalizability,
with the converse over a perfect field. -/
theorem splitSolvableTrigonalizable : SplitSolvableTrigonalizableStatement.{u} := by
  intro k _ G _ _ _
  refine ⟨IsSplitSolvableGroupScheme.isTrigonalizable, ?_⟩
  intro hPerfect hG
  let : PerfectField k := hPerfect
  obtain ⟨U, i, Λ, hΛ, hΛfg, q, hi, hU, _, hq⟩ := (trigonalizableCharacterization k G).2.2.mp hG
  exact isSplitSolvableGroupScheme_of_diagonalizable_quotient i hi hU q hq

end Langlands.GroupScheme
