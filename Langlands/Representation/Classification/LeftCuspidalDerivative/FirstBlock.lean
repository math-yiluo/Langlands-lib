import Langlands.Representation.Classification.LeftCuspidalDerivative.Criterion
import Langlands.Representation.Classification.BinaryGeometricPieceConstituentsStatement
import Langlands.Representation.Exponents.JacquetEigenvectorProof
import Langlands.Representation.Classification.CuspidalProductContragredient
import Langlands.Representation.Filtration.QuasicuspidalVanishingProof
import Langlands.Representation.Classification.NonjuxtaposedSegmentSocleDerivativeStrictMonoProof
import Langlands.Representation.CuspidalSupport.CuspidalTensorAssociationProof
import Langlands.Representation.Parabolic.NaturalFirstAdjointness

/-!
# First-block Jacquet constituents obstruct left reducedness

If the supercuspidal `A` of `GL_d` is a first-block Jacquet constituent of a finite-length
`Y` (either `Y` itself when `d = m`, or the first block of the normalized Jacquet module of
`Y` along `(d, k)`), then `Y` is not left `A`-reduced.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Classification.LeftCuspidalDerivative

universe uF uV uG uW

section Image

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- A nonzero morphism out of a finite-length representation produces an irreducible
subquotient of the source which embeds into the target. -/
theorem exists_irreducible_of_hom_ne_zero {Y X : SmoothRep.{0, uG, uW} ℂ G}
    (hY : Y.HasFiniteLength) (f : Y ⟶ X) (hf : SmoothRep.hom f ≠ 0) :
    ∃ Z : SmoothRep.{0, uG, uW} ℂ G, Z.IsIrreducible ∧ SmoothRep.IsSubquotient Z Y ∧
      SmoothRep.IsSubrepresentation Z X := by
  let Q := SmoothRep.quotient Y (SmoothRep.hom f).ker
  have hQ : Q.HasFiniteLength :=
    NonjuxtaposedStrictMono.hasFiniteLength_of_surjective (SmoothRep.mkQ Y _)
      (SmoothRep.mkQ_surjective Y _) hY
  obtain ⟨y, hy⟩ : ∃ y, SmoothRep.hom f y ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (Representation.IntertwiningMap.ext (LinearMap.ext h))
  have : Nontrivial Q := by
    refine ⟨⟨SmoothRep.hom (SmoothRep.mkQ Y (SmoothRep.hom f).ker) y, 0, fun h0 => hy ?_⟩⟩
    have hmem := (Submodule.Quotient.mk_eq_zero _).mp h0
    exact hmem
  obtain ⟨Z, hZ, j, hj⟩ := SegmentHeadSupport.exists_irreducible_subrepresentation hQ
  let L := SmoothRep.kernelLift f f le_rfl
  have hL : Function.Injective (SmoothRep.hom L) := by
    intro x x' hxx'
    obtain ⟨x, rfl⟩ := SmoothRep.mkQ_surjective Y (SmoothRep.hom f).ker x
    obtain ⟨x', rfl⟩ := SmoothRep.mkQ_surjective Y (SmoothRep.hom f).ker x'
    rw [SmoothRep.kernelLift_mkQ, SmoothRep.kernelLift_mkQ] at hxx'
    refine (Submodule.Quotient.eq _).mpr ?_
    change SmoothRep.hom f (x - x') = 0
    rw [map_sub, hxx', sub_self]
  refine ⟨Z, hZ, CuspidalProductContragredient.isSubquotient_of_injective_of_surjective j hj
    (SmoothRep.mkQ Y _) (SmoothRep.mkQ_surjective Y _), j ≫ L, ?_⟩
  rw [SmoothRep.hom_comp]
  exact hL.comp hj

end Image

section SingleBlock

open GeneralLinear

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- An admissible representation of `GL_d` having a supercuspidal `A` as a subquotient maps
onto `A` (the single-block case of the Levi cuspidal constituent theorem). -/
theorem exists_surjective_of_isSubquotient_supercuspidal {d : ℕ} (hd : 0 < d)
    (A : letI := T.topology; GeneralLinear.SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := d))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear d F.Carrier) V)
    (hρ : letI := T.topology; IsAdmissible ρ)
    (hocc : letI := T.topology; WeylBranchPieces.IsSubquotient ρ A.obj.representation) :
    letI := T.topology; ∃ q : ρ.IntertwiningMap A.obj.representation, Function.Surjective q := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let B := CuspidalSupport.LeviAdmissibility.oneBlock d hd
  have hB : B.length = 1 := rfl
  have hsurj : Function.Surjective (B.leviEmbedding F.Carrier) :=
    B.singleBlock_leviEmbedding_surjective hB F.Carrier
  have hAa : IsAdmissible (Rep.of (ρ.comp (B.leviEmbedding F.Carrier))).ρ :=
    isAdmissible_comp_continuousMulEquiv ρ (B.singleBlockLeviEquivContinuous hB F.Carrier) hρ
  have : A.obj.representation.IsIrreducible := A.property.1
  have hDi : Representation.IsIrreducible
      (Rep.of (A.obj.representation.comp (B.leviEmbedding F.Carrier))).ρ :=
    CuspidalSupport.isIrreducible_comp_of_surjective A.obj.representation
      (B.leviEmbedding F.Carrier) hsurj
  have hDc : CuspidalSupport.IsLeviCuspidal B
      (Rep.of (A.obj.representation.comp (B.leviEmbedding F.Carrier))).ρ :=
    (CuspidalSupport.singleBlockCuspidalityClause T d B hB _ A.obj.representation).mpr
      A.property.2
  have hDA : ∃ S : Subrepresentation (Rep.of (ρ.comp (B.leviEmbedding F.Carrier))).ρ,
      ∃ q : S.toRepresentation.IntertwiningMap
        (Rep.of (A.obj.representation.comp (B.leviEmbedding F.Carrier))).ρ,
        Function.Surjective q := by
    obtain ⟨S, q, hq⟩ := hocc
    exact ⟨⟨S.toSubmodule, fun g v hv => S.apply_mem_toSubmodule (B.leviEmbedding F.Carrier g) hv⟩,
      ⟨q.toLinearMap, fun g => q.isIntertwining' (B.leviEmbedding F.Carrier g)⟩, hq⟩
  obtain ⟨-, q, hq⟩ := CuspidalSupport.leviCuspidalConstituent_maps F T B
    (Rep.of (ρ.comp (B.leviEmbedding F.Carrier)))
    (Rep.of (A.obj.representation.comp (B.leviEmbedding F.Carrier))) hAa hDi hDc hDA
  refine ⟨⟨q.toLinearMap, fun g => ?_⟩, hq⟩
  obtain ⟨l, rfl⟩ := hsurj g
  exact q.isIntertwining' l

end SingleBlock

section FirstBlock

open GeneralLinear

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The one-dimensional trivial representation of `GL_0`. -/
def trivialRankZero :
    letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear 0 F.Carrier) :=
  letI := T.topology
  SmoothRep.of (Representation.trivial ℂ (GeneralLinear 0 F.Carrier) (ULift.{max uF uV} ℂ))
    (by
      intro v
      refine ⟨⊤, ?_⟩
      rw [fixedVectors, Representation.mem_invariants]
      intro k
      rfl)

/-- The case `d = m`: a supercuspidal subquotient `A` of `Y` obstructs left reducedness,
since `A` embeds into `A × 1` with the trivial representation of `GL_0`. -/
theorem not_leftReduced_of_isSubquotient_self {d : ℕ}
    (A : letI := T.topology;
      GeneralLinear.SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d))
    (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear d F.Carrier))
    (h : letI := T.topology; WeylBranchPieces.IsSubquotient Y.representation A.obj.representation) :
    ¬ LeftReduced F T A Y := by
  let := T.topology
  intro hY
  let σ₀ := trivialRankZero.{uF, uV} F T
  let X := (T.binaryNormalizedProductFunctor d 0).obj (A.obj, σ₀)
  let E := T.binaryRightZeroTensorEquiv (a := d) (b := 0) rfl (A.obj, σ₀)
  let ι₀ : A.obj →ₗ[ℂ] A.obj ⊗[ℂ] σ₀ := (TensorProduct.mk ℂ A.obj σ₀).flip (ULift.up 1)
  have hι₀ : Function.Injective ι₀ := by
    let r : A.obj ⊗[ℂ] σ₀ →ₗ[ℂ] A.obj :=
      (TensorProduct.rid ℂ A.obj).toLinearMap ∘ₗ
        LinearMap.lTensor A.obj (ULift.moduleEquiv (R := ℂ) (M := ℂ)).toLinearMap
    have hr : ∀ a : A.obj, r (a ⊗ₜ[ℂ] (ULift.up 1 : ULift.{max uF uV} ℂ)) = a := by
      intro a
      change TensorProduct.rid ℂ A.obj (a ⊗ₜ[ℂ] (1 : ℂ)) = a
      rw [TensorProduct.rid_tmul, one_smul]
    intro a b hab
    have := congrArg r hab
    change r (a ⊗ₜ[ℂ] (ULift.up 1 : ULift.{max uF uV} ℂ)) =
      r (b ⊗ₜ[ℂ] (ULift.up 1 : ULift.{max uF uV} ℂ)) at this
    rwa [hr, hr] at this
  let ι : A.obj.representation.IntertwiningMap (T.castRank (rfl : d + 0 = d) X).representation :=
    { toLinearMap := E.symm.toLinearMap ∘ₗ ι₀
      isIntertwining' := fun g => by
        ext a
        change E.symm (ι₀ (A.obj.representation g a)) = X.representation g (E.symm (ι₀ a))
        have h1 := LinearMap.congr_fun (E.symm.isIntertwining' g) (ι₀ a)
        refine Eq.trans (congrArg E.symm.toLinearMap ?_) h1
        have hg :
            GeneralLinear.reindex (R := F.Carrier) (finCongr (by omega : d + 0 = d)) g = g := by
          apply Units.ext
          ext i j
          rfl
        change A.obj.representation g a ⊗ₜ[ℂ] (ULift.up 1 : ULift.{max uF uV} ℂ) =
          A.obj.representation (GeneralLinear.reindex (R := F.Carrier)
            (finCongr (by omega : d + 0 = d)) g) a ⊗ₜ[ℂ] (ULift.up 1 : ULift.{max uF uV} ℂ)
        rw [hg] }
  have hι : Function.Injective ι := E.symm.injective.comp hι₀
  have hZY : SmoothRep.IsSubquotient A.obj Y :=
    SmoothRep.isSubquotient_iff_representation.mpr h
  exact hY A.obj A.property.1 hZY 0 rfl σ₀ ⟨SmoothRep.ofHom ι, hι⟩

/-- The case `d + k = m` with `k > 0`: if `A` is a subquotient of the first block of the
normalized Jacquet module of a finite-length `Y` along `(d, k)`, then `Y` is not left
`A`-reduced. -/
theorem not_leftReduced_of_jacquet {d k : ℕ} (hd : 0 < d) (hk : 0 < k)
    (A : letI := T.topology;
      GeneralLinear.SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d))
    (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (d + k) F.Carrier))
    (hY : letI := T.topology; Y.HasFiniteLength)
    (hocc : letI := T.topology;
      WeylBranchPieces.IsSubquotient
        ((T.normalizedJacquet (BlockShape.ofPair d k hd hk rfl) Y.representation).comp
          (MonoidHom.mulSingle
            (fun i => GeneralLinear ((BlockShape.ofPair d k hd hk rfl).size i) F.Carrier)
            (0 : Fin 2)))
        A.obj.representation) :
    ¬ LeftReduced F T A Y := by
  let := T.topology
  intro hred
  have : ∀ n : ℕ, IsTopologicalGroup (GeneralLinear n F.Carrier) :=
    fun n => T.generalLinearTopologicalGroup n
  -- Work with the reducible two-block shape, definitionally equal to `ofPair`.
  let B := Shahidi.twoBlocks d k hd hk
  have : ∀ i, IsTopologicalGroup (GeneralLinear (B.size i) F.Carrier) :=
    fun i => T.generalLinearTopologicalGroup _
  let W := T.normalizedJacquet B Y.representation
  have hocc' : WeylBranchPieces.IsSubquotient
      (W.comp (MonoidHom.mulSingle (fun i => GeneralLinear (B.size i) F.Carrier) 0))
      A.obj.representation := hocc
  have hYa : IsAdmissible Y.representation := glFiniteLengthAdmissibility F T (d + k) Y hY
  have hW : IsAdmissible W := Parabolic.isAdmissible_normalizedJacquet F T B Y.representation hYa
  have hcpt : ∀ O : OpenSubgroup (GeneralLinear (B.size 1) F.Carrier),
      ∃ K : OpenSubgroup (GeneralLinear (B.size 1) F.Carrier),
        IsCompact (K : Set (GeneralLinear (B.size 1) F.Carrier)) ∧ K ≤ O := by
    intro O
    obtain ⟨K, hKc, hKO, -⟩ := BlockShape.exists_compactOpenSubgroup_hasBlockIwahoriFactorization
      (CuspidalSupport.LeviAdmissibility.oneBlock k hk) T O.mem_nhds_one
    exact ⟨K, hKc, hKO⟩
  have hAirr : A.obj.representation.IsIrreducible := A.property.1
  obtain ⟨K, hKc, hslice⟩ := exists_secondFixedSlice_isSubquotient W hW.1 hcpt
    A.obj.representation hAirr hocc'
  obtain ⟨ψ, hψ⟩ := exists_surjective_of_isSubquotient_supercuspidal F T hd A _
    (isAdmissible_secondFixedSlice W hW K) hslice
  have : Nontrivial A.obj := by
    have : IsSimpleModule (MonoidAlgebra ℂ (GeneralLinear d F.Carrier))
        A.obj.representation.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule _).mp hAirr
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear d F.Carrier))
      A.obj.representation.asModule
  obtain ⟨φ, hφ⟩ := exists_ne_zero_of_secondFixedSlice_of_surjective W hW.1 K hKc
    A.obj.representation ψ hψ
  let σ := rightRegularRep.{uV, uF} (H := GeneralLinear k F.Carrier)
  obtain ⟨Φ, hΦ⟩ := exists_external_ne_zero_of_smooth W hW.1
    (fun i => (twoBlockFactors hd hk A.obj σ i).representation) A.property.2.1 φ hφ
    (rightRegularEval.{uV, uF} (H := GeneralLinear k F.Carrier))
    (rightRegularEval_injective.{uV, uF} (H := GeneralLinear k F.Carrier))
    (fun h s g => rightRegularEval_equivariant.{uV, uF} (H := GeneralLinear k F.Carrier) h s g)
    (fun f K hf => exists_rightRegularEval_eq.{uV, uF} (H := GeneralLinear k F.Carrier) f K hf)
  let adj := Parabolic.FirstAdjointness.equiv T B Y.isSmooth
    (σ := FiniteTensor.external fun i => (twoBlockFactors hd hk A.obj σ i).representation)
  let f₀ := adj.symm Φ
  obtain ⟨e⟩ := SegmentSocleDerivativesProof.nonempty_ofPairProductIso T hd hk A.obj σ
  let f : Y ⟶ (T.binaryNormalizedProductFunctor d k).obj (A.obj, σ) :=
    SmoothRep.ofHom f₀ ≫ e.inv
  have hf₀ : f₀ ≠ 0 := by
    intro h0
    apply hΦ
    rw [← adj.apply_symm_apply Φ]
    change adj f₀ = 0
    rw [h0]
    exact adj.map_zero
  have hf : SmoothRep.hom f ≠ 0 := by
    intro h0
    apply hf₀
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    apply SmoothRep.hom_hom_injective e.symm
    have h1 : SmoothRep.hom f v = 0 := by rw [h0]; rfl
    change SmoothRep.hom e.inv (f₀ v) = SmoothRep.hom e.inv 0
    rw [map_zero]
    exact h1
  obtain ⟨Z, hZ, hZY, hZX⟩ := exists_irreducible_of_hom_ne_zero hY f hf
  exact hred Z hZ hZY k rfl σ hZX

/-- **First-block criterion.** If the supercuspidal `A` is a first-block Jacquet constituent
of a finite-length `Y`, then `Y` is not left `A`-reduced. -/
theorem not_leftReduced_of_isFirstBlockConstituent {d m : ℕ}
    (A : letI := T.topology;
      GeneralLinear.SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d))
    (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
    (hY : letI := T.topology; Y.HasFiniteLength)
    (hA : BinaryGeometricPieces.IsFirstBlockConstituent F T Y A.obj) :
    ¬ LeftReduced F T A Y := by
  rcases hA with ⟨h, hsub⟩ | ⟨k, hd, hk, h, hocc⟩
  · subst h
    exact not_leftReduced_of_isSubquotient_self F T A Y hsub
  · subst h
    exact not_leftReduced_of_jacquet F T hd hk A Y hY hocc

end FirstBlock

end Langlands.Classification.LeftCuspidalDerivative
