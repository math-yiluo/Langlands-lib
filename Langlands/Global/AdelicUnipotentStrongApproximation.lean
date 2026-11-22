import Langlands.Global.AdelicGroupProduct
import Langlands.Global.RankinSelberg.SchwartzBruhatProof.Lattice
import Langlands.Global.TriangularRationalQuotientCompact
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitProof
import Langlands.GroupScheme.Unipotent.SplitAffineSpaceProof

/-! # Strong approximation at the finite adeles for unipotent groups -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory Filter IsDedekindDomain NumberField Set Topology
open scoped CategoryTheory.MonObj

namespace Langlands.Global.AdelicGroupPoints

open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme
open CompletionPadic RankinSelbergGlobal.SchwartzBruhatProof

/-- The principal diagonal of a number field is dense in the additive finite adeles. -/
theorem denseRange_finiteAdeles_algebraMap (F : Type u) [Field F] [NumberField F] :
    DenseRange (algebraMap F (FiniteAdeles F)) := by
  classical
  intro a
  apply mem_closure_iff_nhds.mpr
  intro W hW
  have hadd : Continuous (fun b : FiniteAdeles F => b + a) := continuous_id.add continuous_const
  have hW₀ : (fun b : FiniteAdeles F => b + a) ⁻¹' W ∈ 𝓝 (0 : FiniteAdeles F) := by
    apply hadd.tendsto' 0 a (zero_add _) hW
  obtain ⟨m, hm⟩ := exists_finiteLattice_subset hW₀
  have hbad : {v : FinitePlace F | a v ∉ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.mp a.2
  let S := m.support ∪ hbad.toFinset
  obtain ⟨r, hr, hr'⟩ := Hecke.exists_approx S (fun v => a v) m
  have hmem : algebraMap F (FiniteAdeles F) r - a ∈ finiteLattice m := by
    apply (mem_finiteLattice m _).mpr
    intro v
    change algebraMap F (FiniteCompletion F v) r - a v ∈ (topologicalData v).additiveLattice (m v)
    by_cases hv : v ∈ S
    · exact hr v hv
    · have hmv : m v = 0 := Finsupp.notMem_support_iff.mp fun h => hv (Finset.mem_union_left _ h)
      have hav : a v ∈ v.adicCompletionIntegers F := by
        by_contra h
        exact hv (Finset.mem_union_right _ (hbad.mem_toFinset.mpr h))
      rw [hmv]
      exact (topologicalData v).additiveLattice 0 |>.sub_mem (hr' v hv)
        ((Hecke.mem_additiveLattice_zero_iff v (a v)).mpr hav)
  have h := hm hmem
  change algebraMap F (FiniteAdeles F) r - a + a ∈ W at h
  rw [sub_add_cancel] at h
  exact ⟨_, h, ⟨r, rfl⟩⟩

/-- The finite projection of the principal rational points of a smooth connected affine
unipotent group over a number field is dense. -/
def AdelicUnipotentStrongApproximationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (U : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine U.X.left] [Smooth U.X.hom],
    ConnectedSpace U.X.left → IsUnipotent U →
    DenseRange (fun r : RationalGroupPoints F U => finite F U (rational F U r))

theorem adelicUnipotentStrongApproximation : AdelicUnipotentStrongApproximationStatement.{u} := by
  intro F _ _ U _ _ hconn hu
  let : IsAffineHom U.X.hom := isAffineHom_of_isAffine _
  obtain ⟨n, hn⟩ := perfectFieldUnipotentSplit F U hconn hu
  obtain ⟨e⟩ := splitUnipotentAffineSpaceStatement F n U inferInstance hn
  let J := ULift.{u} (Fin n)
  let R := CommRingCat.of F
  let AF := FiniteAdeles F
  let Y := ringTest F (MvPolynomial J F)
  let isoSpec : Over.mk (𝔸(J; Spec R) ↘ Spec R) ≅ Y :=
    Over.isoMk (AffineSpace.SpecIso J R) (by
      change (AffineSpace.SpecIso J R).hom ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) = _
      rw [← AffineSpace.SpecIso_inv_over, Iso.hom_inv_id_assoc]
      rfl)
  let E : AffineCoordinateRing F U.X ≃ₐ[F] MvPolynomial J F :=
    (affineCoordinateAlgEquiv F (e ≪≫ isoSpec)).symm.trans (spectrumCoordinateAlgEquiv F _)
  let P : FiniteAdelicGroupPoints F U ≃ₜ (J → AF) :=
    (U.affinePointsAlgebraHomeomorph (CommAlgCat.of F AF)).trans
      ((AlgPoint.congr E).trans (AlgPoint.polynomialPointHomeomorph J))
  have hP (s : FiniteAdelicGroupPoints F U) (i : J) :
      P s i = U.affinePointEvaluation (CommAlgCat.of F AF) s (E.symm (MvPolynomial.X i)) := by
    change (U.affinePointsAlgebraHomeomorph (CommAlgCat.of F AF) s) _ = _
    exact U.affinePointsAlgebraHomeomorph_apply (CommAlgCat.of F AF) s _
  have hd : DenseRange (fun z : J → F => fun i => algebraMap F AF (z i)) :=
    DenseRange.piMap (fun _ : J => denseRange_finiteAdeles_algebraMap F)
  have hden : DenseRange (P.symm ∘ fun z : J → F => fun i => algebraMap F AF (z i)) :=
    P.symm.surjective.denseRange.comp hd P.symm.continuous
  refine hden.mono ?_
  rintro _ ⟨z, rfl⟩
  let φ : AffineCoordinateRing F U.X →ₐ[F] F := (MvPolynomial.aeval z).comp E.toAlgHom
  let r : RationalGroupPoints F U := (affineSchemePointEquiv F U.X F).symm (AlgPoint.ofAlgHom φ)
  refine ⟨r, P.injective ?_⟩
  rw [Function.comp_apply, P.apply_symm_apply]
  funext i
  rw [hP]
  let a := E.symm (MvPolynomial.X i)
  change U.affinePointEvaluation (CommAlgCat.of F AF) (finite F U (rational F U r)) a =
    algebraMap F AF (z i)
  have hf := U.affinePointEvaluation_map
    (CommAlgCat.ofHom (AlgHom.snd F (InfiniteAdeleRing F) AF)) (rational F U r) a
  change U.affinePointEvaluation (CommAlgCat.of F AF) (finite F U (rational F U r)) a =
    (U.affinePointEvaluation (CommAlgCat.of F (AdeleRing (𝓞 F) F)) (rational F U r) a).2 at hf
  rw [hf, affinePointEvaluation_rational]
  have hr : U.affinePointEvaluation (CommAlgCat.of F F) r a = z i := by
    rw [← U.affineSchemePointEquiv_evaluation (CommAlgCat.of F F),
      show affineSchemePointEquiv F U.X F r = AlgPoint.ofAlgHom φ from Equiv.apply_symm_apply _ _]
    change MvPolynomial.aeval z (E (E.symm (MvPolynomial.X i))) = z i
    rw [E.apply_symm_apply, MvPolynomial.aeval_X]
  exact congrArg (algebraMap F AF) hr

end Langlands.Global.AdelicGroupPoints
