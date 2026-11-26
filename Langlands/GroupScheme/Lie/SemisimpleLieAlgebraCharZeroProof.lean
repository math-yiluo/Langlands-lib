import Langlands.GroupScheme.ArtinianUniformExponent
import Langlands.GroupScheme.Lie.SemisimpleLieAlgebraCharZeroStatement
import Langlands.GroupScheme.Lie.AffineBracketAdjoint
import Langlands.GroupScheme.Lie.CenterTangent
import Langlands.GroupScheme.Reductive.CharZeroSemisimplicity.NilpotentIdeal
import Langlands.GroupScheme.Reductive.ToPseudoReductive
import Langlands.Algebra.LinearLieSemisimplicity
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Pi

/-! # Semisimplicity of the actual Lie algebra in characteristic zero -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry LieAlgebra
open scoped TensorProduct

namespace Langlands.GroupScheme.Lie

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Nilpotence of the action of the bracket with the radical descends from an algebraic
closure. The scalar extension of the radical is solvable by the derived-series formula. -/
private theorem isNilpotent_toEnd_of_mem_bracket_radical {k : Type u} [Field k] [CharZero k]
    {L : Type v} [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]
    {V : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [LieRingModule L V] [LieModule k L V]
    {x : L} (hx : x ∈ ⁅(⊤ : LieIdeal k L), radical k L⁆) :
    IsNilpotent (LieModule.toEnd k L V x) := by
  let K := AlgebraicClosure k
  let I := radical k L
  let J := I.baseChange K
  have hJ : IsSolvable J := by
    obtain ⟨n, hn⟩ := IsSolvable.solvable k I
    apply IsSolvable.mk (R := K) (k := n)
    rw [LieIdeal.derivedSeries_eq_bot_iff, derivedSeriesOfIdeal_baseChange,
      (I.derivedSeries_eq_bot_iff n).mp hn, LieSubmodule.baseChange_bot]
  have hJ_le : J ≤ radical K (K ⊗[k] L) :=
    (LieIdeal.solvable_iff_le_radical K (K ⊗[k] L) J).mp hJ
  have hxK : 1 ⊗ₜ[k] x ∈ ⁅(⊤ : LieIdeal K (K ⊗[k] L)), J⁆ := by
    rw [← LieSubmodule.baseChange_top, ← LieSubmodule.lie_baseChange]
    exact LieSubmodule.tmul_mem_baseChange_of_mem 1 hx
  have hinj : Function.Injective (Module.End.baseChangeHom k K V) :=
    LinearMap.baseChangeHom_injective k V K
  rw [← IsNilpotent.map_iff hinj]
  change IsNilpotent ((LieModule.toEnd k L V x).baseChange K)
  rw [← LieModule.toEnd_baseChange]
  exact Langlands.Algebra.isNilpotent_toEnd_of_mem_lie_radical _ _ rfl (1 ⊗ₜ[k] x)
    (LieSubmodule.mono_lie le_rfl hJ_le hxK)

/-- A finite group scheme in characteristic zero has zero tangent space. Its reduced
Artinian coordinate algebra is a product of finite separable field extensions. -/
private theorem finite_lieKernel_eq_one {k : Type u} [Field k] [CharZero k]
    (F : GroupScheme (Spec (CommRingCat.of k))) [IsFinite F.X.hom]
    (x : lieKernel F k) : x = 1 := by
  let : IsAffineHom F.X.hom := inferInstance
  let C := coordinateAlgebra F
  have hfinite : Module.Finite k C := by
    apply RingHom.finite_algebraMap.mp
    apply (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap k C))).mp
    have h : IsFinite ((coordinateIso F).hom.left ≫ F.X.hom) := inferInstance
    rw [Over.w] at h
    exact h
  have : AlgebraicGeometry.IsReduced F.X.left := AffineCartierSmoothProof.isReduced F
  have : _root_.IsReduced C :=
    (affine_isReduced_iff _).mp (isReduced_of_isOpenImmersion (coordinateIso F).hom.left)
  have : Algebra.FormallyUnramified k C :=
    ArtinianUniformExponent.formallyUnramified_of_finite_reduced k C
  let : Algebra C k := coordinateOriginAlgebra F (A := k)
  have : Subsingleton (Derivation k C k) :=
    (KaehlerDifferential.linearMapEquivDerivation k C).surjective.subsingleton
  exact (kernelDerivationEquiv F (A := k)).injective (Subsingleton.elim _ _)

section Group

variable {k : Type u} [Field k] [CharZero k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [Smooth G.X.hom] [ConnectedSpace G.X.left]

local instance : LieRing (Additive (lieKernel G k)) :=
  instAffineKernelLieRing (R := CommRingCat.of k) (A := k) G

local instance : LieAlgebra k (Additive (lieKernel G k)) :=
  instAffineKernelLieAlgebra (R := CommRingCat.of k) (A := k) G

/-- A vector in the Lie center has full tangent centralizer. Cartier smoothness and
connectedness then place it in the tangent space of the full scheme center. -/
private theorem center_eq_bot_of_hasFiniteCenter (hcenter : HasFiniteCenter G) :
    LieAlgebra.center k (Additive (lieKernel G k)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  let c := finiteCoordinates G
  have hLie : elementCentralizerLie G x.toMul = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    apply (mem_elementCentralizerLie_iff_adjointDifferential c x.toMul y.toMul).2
    change adjointDifferentialLieHom c y (c.equiv (.of (CommRingCat.of k) k) x) = 0
    rw [adjointDifferentialLieHom_apply_bracket, hx y, map_zero]
  obtain ⟨H, j, hj, hclosed⟩ := elementCentralizer_isClosedRepresentable G x.toMul
  let : IsClosedImmersion j.hom.hom.left := hclosed
  have hA : IsAffineHom H.X.hom := by
    rw [← j.hom.hom.w]
    infer_instance
  have hft : LocallyOfFiniteType H.X.hom := by
    rw [← j.hom.hom.w]
    infer_instance
  have hfull : elementCentralizer G x.toMul = ⊤ :=
    RelativeRoot.eq_top_of_smooth_closed_of_tangentSubmodule_eq_top j hj hclosed
      (affineCartierSmooth k H hA hft) hLie
  obtain ⟨Z, z, hz, hfinite⟩ := hcenter
  let y := centerTangentFactor z hz.isRepresentedBy x.toMul hfull
  have hy : targetMap z k y = x.toMul :=
    targetMap_centerTangentFactor z hz.isRepresentedBy x.toMul hfull
  rw [finite_lieKernel_eq_one Z y, map_one] at hy
  exact (LieSubmodule.mem_bot _).2
    (by simpa only [ofMul_toMul, ofMul_one] using
      congrArg (Additive.ofMul : lieKernel G k → Additive (lieKernel G k)) hy.symm)

/-- The faithful tangent representation of a reductive group kills `⁅L, rad L⁆`:
its image is a normalized family of nilpotent endomorphisms. -/
private theorem radical_le_center_of_hasTrivialUnipotentRadical
    (hrad : HasTrivialUnipotentRadical G) :
    radical k (Additive (lieKernel G k)) ≤ LieAlgebra.center k (Additive (lieKernel G k)) := by
  let L := Additive (lieKernel G k)
  obtain ⟨n, ρ, hρ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  let V := Fin n → k
  let dρ : L →ₗ⁅k⁆ Module.End k V :=
    (lieEquivMatrix' (R := k) (n := Fin n)).symm.toLieHom.comp (ρ.kernelDifferentialLieHom k)
  let : LieRingModule L V := LieRingModule.compLieHom V dρ
  let : LieModule k L V := LieModule.compLieHom V dρ
  let I : LieIdeal k L := ⁅(⊤ : LieIdeal k L), radical k L⁆
  let A : Submodule k (Module.End k V) := I.toSubmodule.map dρ.toLinearMap
  have hnil : ∀ a ∈ A, IsNilpotent a := by
    rintro _ ⟨x, hx, rfl⟩
    exact isNilpotent_toEnd_of_mem_bracket_radical (L := L) (V := V) hx
  have hsub : ∀ a ∈ A, ∃ Y : lieKernel G k, Matrix.toLin' (ρ.tangentMatrix k Y) = a := by
    rintro _ ⟨x, _, rfl⟩
    exact ⟨x.toMul, rfl⟩
  have hbr : ∀ (Y : lieKernel G k), ∀ a ∈ A,
      Matrix.toLin' (ρ.tangentMatrix k Y) * a - a * Matrix.toLin' (ρ.tangentMatrix k Y) ∈ A := by
    rintro Y _ ⟨x, hx, rfl⟩
    refine ⟨⁅Additive.ofMul Y, x⁆, I.lie_mem hx, ?_⟩
    exact (dρ.map_lie ..).trans (LieRing.of_associative_ring_bracket _ _)
  intro x hx y
  have hxy : ⁅y, x⁆ ∈ I := LieSubmodule.lie_mem_lie (LieSubmodule.mem_top y) hx
  have h : (⁅y, x⁆ : L).toMul = 1 :=
    MatrixRepresentation.eq_one_of_nilpotent_normalized hrad ρ hρ A hnil hsub hbr _
      ⟨⁅y, x⁆, hxy, rfl⟩
  simpa only [ofMul_toMul, ofMul_one] using
    congrArg (Additive.ofMul : lieKernel G k → L) h

end Group

/-- The Lie algebra of a semisimple algebraic group in characteristic zero has
trivial solvable radical, on the actual dual-number tangent carrier. -/
theorem semisimpleLieAlgebraCharZero : SemisimpleLieAlgebraCharZeroStatement.{u} := by
  intro k _ _ G _ hG
  let := hG.isConnectedReductive.smooth
  let := hG.isConnectedReductive.connectedSpace
  let : LieRing (Additive (lieKernel G k)) :=
    instAffineKernelLieRing (R := CommRingCat.of k) (A := k) G
  let : LieAlgebra k (Additive (lieKernel G k)) :=
    instAffineKernelLieAlgebra (R := CommRingCat.of k) (A := k) G
  change LieAlgebra.HasTrivialRadical k (Additive (lieKernel G k))
  refine ⟨eq_bot_iff.mpr ?_⟩
  rw [← center_eq_bot_of_hasFiniteCenter hG.hasFiniteCenter]
  exact radical_le_center_of_hasTrivialUnipotentRadical
    hG.isConnectedReductive.hasTrivialUnipotentRadical

end Langlands.GroupScheme.Lie
