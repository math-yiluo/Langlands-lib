import Langlands.GroupScheme.Absolute.LowDimensionSolvableStatement
import Langlands.GroupScheme.Absolute.BorelTransport
import Langlands.GroupScheme.Absolute.RegularCocharacterWeights
import Langlands.GroupScheme.Absolute.SolvableQuotientExtension
import Langlands.GroupScheme.Lie.SplitTorusCoordinates
import Langlands.GroupScheme.Lie.SmoothDifferential
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Langlands.GroupScheme.Reductive.PerfectFieldProof
import Langlands.GroupScheme.Reductive.SplitRankZeroIsomorphism
import Langlands.GroupScheme.Reductive.UnipotentRadicalExistenceProof
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientProof
import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.SplitReflection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Proof: connected group varieties of dimension at most two are solvable -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace LowDimensionSolvableProof

variable {k : Type u} [Field k]

/-- A nonzero character of a split torus forces a positive Lie dimension. -/
private theorem lieDimension_pos_of_character
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom T.toGrp.X.hom] (hT : IsSplitTorus T.toGrp)
    (α : characterLattice T) (hα : α ≠ 0) :
    0 < Module.finrank k (Additive (lieKernel T.toGrp k)) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := hI
  let φ : characterLattice T ≃+ (I → ℤ) :=
    (characterLattice.comapIso
      (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) e).symm.trans
      (splitTorus.characterLatticeEquiv k I)
  have hne : Nonempty I := by
    by_contra hn
    let : IsEmpty I := ⟨fun x => hn ⟨x⟩⟩
    exact hα (φ.injective (Subsingleton.elim _ _))
  let := hne
  let : IsAffineHom (splitTorus (Spec (CommRingCat.of k)) I).X.hom :=
    isAffineHom_splitTorus_spec _ I
  rw [(Lie.targetEquiv e k).finrank_eq, splitTorus.finrank_lieKernel I k]
  exact Nat.card_pos

/-- A root of a split maximal torus contributes three independent nonzero weights. -/
private theorem three_le_dimension_of_root
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom T.toGrp.X.hom]
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    {α : characterLattice T} (hα : α ∈ roots i) :
    3 ≤ Lie.dimension G := by
  classical
  have : IsClosedImmersion i.hom.hom.left := hi.2.1
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have hneg : -α ∈ roots i := neg_mem_roots_of_split_maximalTorus hG hT i hi hα
  have hdistinct : α ≠ -α := by
    intro h
    obtain ⟨I, hI, ⟨e⟩⟩ := hT
    let φ : characterLattice T ≃+ (I → ℤ) :=
      (characterLattice.comapIso
        (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) e).symm.trans
        (splitTorus.characterLatticeEquiv k I)
    apply hα.1
    apply φ.injective
    rw [map_zero]
    funext x
    have hx := congrFun (congrArg φ h) x
    rw [map_neg, Pi.neg_apply] at hx
    rw [Pi.zero_apply]
    omega
  have hzero : 1 ≤ Module.finrank k (weightSpace i 0) :=
    (lieDimension_pos_of_character hT α hα.1).trans_le
      (LinearMap.finrank_le_finrank_of_injective (Lie.zeroWeightMap_injective i))
  have hpos : 1 ≤ Module.finrank k (weightSpace i α) :=
    Submodule.one_le_finrank_iff.mpr hα.2
  have hminus : 1 ≤ Module.finrank k (weightSpace i (-α)) :=
    Submodule.one_le_finrank_iff.mpr hneg.2
  have hd : Disjoint (weightSpace i α) (weightSpace i (-α)) :=
    weightSpace_disjoint hT i hdistinct
  have hd0 : Disjoint (weightSpace i 0) (weightSpace i α ⊔ weightSpace i (-α)) := by
    have hd' := weightSpace_disjoint_iSup hT i
      (p := fun χ => χ = α ∨ χ = -α) (χ := 0) (by
        rintro (h | h)
        · exact hα.1 h.symm
        · exact hneg.1 h.symm)
    simpa only [iSup_or, iSup_sup_eq, iSup_iSup_eq_left] using hd'
  have hsum : Module.finrank k ↥(weightSpace i α ⊔ weightSpace i (-α)) =
      Module.finrank k (weightSpace i α) + Module.finrank k (weightSpace i (-α)) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (weightSpace i α) (weightSpace i (-α))
    rw [hd.eq_bot, finrank_bot, add_zero] at h
    exact h
  have hbound := Submodule.finrank_add_finrank_le_of_disjoint hd0
  change Module.finrank k (weightSpace i 0) +
    Module.finrank k ↥(weightSpace i α ⊔ weightSpace i (-α)) ≤ Lie.dimension G at hbound
  omega

/-- A connected reductive group of Lie dimension at most two is a torus. -/
private theorem solvable_of_reductive_dimension_le_two
    [IsAlgClosed k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] (hG : IsConnectedReductive G)
    (hdim : Lie.dimension G ≤ 2) : IsSolvableGroupScheme G := by
  have := hG.smooth
  obtain ⟨T, i, hi⟩ := maximalTorusExistence k G
  have hT : IsSplitTorus T.toGrp :=
    hi.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  have : IsClosedImmersion i.hom.hom.left := hi.2.1
  have : IsAffineHom T.toGrp.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have hroot : roots i = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro α hα
    have := three_le_dimension_of_root hG hT i hi hα
    omega
  have : IsIso i := hG.isIso_of_roots_eq_empty hT hi hroot
  exact (isSolvableGroupScheme_of_isCommMonObj T.toGrp).of_iso (asIso i).symm

end LowDimensionSolvableProof

/-- Milne, Corollary 17.27, using the reductive quotient and its adjoint weights. -/
theorem lowDimensionSolvable : LowDimensionSolvableStatement.{u} := by
  intro k _ _ G _ _ _ hdim
  obtain ⟨U, i, hi⟩ := unipotentRadicalExistence k G
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Smooth U.X.hom := hi.smooth
  have : IsAffineHom U.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  obtain ⟨Q, q, hq, hQ⟩ := unipotentRadicalQuotient k G U i hi
  have hred : IsConnectedReductive Q := (perfectFieldPseudoReductive k Q).mp hQ
  have := hred.smooth
  have := hred.isAffineHom
  have : Smooth q.hom.hom.left :=
    hq.smooth_of_smooth_kernel ⟨inferInstance, rfl⟩ hi.smooth
  have hle : Lie.dimension Q ≤ Lie.dimension G :=
    LinearMap.finrank_le_finrank_of_surjective
      (Lie.targetMapLinear_surjective_of_smooth q k inferInstance)
  exact isSolvableGroupScheme_of_unipotent_fppfQuotient hi.isUnipotent hq
    (LowDimensionSolvableProof.solvable_of_reductive_dimension_le_two hred
      (hle.trans hdim))

end Langlands.GroupScheme
