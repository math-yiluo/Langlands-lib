import Langlands.GroupScheme.Commutative.MultiplicativePartQuotient
import Langlands.GroupScheme.Torus.MultiplicativeTypeFieldExtensionProof
import Langlands.GroupScheme.Torus.DiagonalizableSmoothConnectedCriteriaProof
import Langlands.GroupScheme.Unipotent.HopfFixed
import Langlands.AlgebraicGeometry.SmoothReducedBase

/-! # Characters of the multiplicative part over an algebraically closed field -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RelativeRoot

namespace MultiplicativePart

/-- In a bialgebra over a field in which every nonzero finite-dimensional right-translation stable
subspace contains `1`, the only group-like element is `1`. -/
theorem eq_one_of_isGroupLikeElem {K B : Type*} [Field K] [Ring B] [Bialgebra K B]
    (hB : Unipotent.OneMemStable K B) {b : B} (hb : IsGroupLikeElem K b) : b = 1 := by
  have hact : ∀ f : Module.Dual K B, AffineLinearEmbedding.rightAct f b = f b • b := by
    intro f
    rw [AffineLinearEmbedding.rightAct_apply, hb.comul_eq_tmul_self, LinearMap.lTensor_tmul,
      TensorProduct.rid_tmul]
  have h1 : (1 : B) ∈ Submodule.span K {b} := by
    refine hB _ inferInstance (fun f v hv => ?_) ?_
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [map_smul, hact]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self b))
    · intro h
      have hb0 : b ∈ Submodule.span K {b} := Submodule.mem_span_singleton_self b
      rw [h, Submodule.mem_bot] at hb0
      have := hb.counit_eq_one
      rw [hb0, map_zero] at this
      exact zero_ne_one this
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1
  have hε := congrArg (Coalgebra.counit (R := K)) hc
  rw [map_smul, hb.counit_eq_one, smul_eq_mul, mul_one, Bialgebra.counit_one] at hε
  rw [← hc, hε, one_smul]

/-- A bialgebra injection from a bialgebra satisfying `OneMemStable` sends only `1` to a
group-like element. -/
theorem eq_one_of_map_isGroupLikeElem {K A B : Type*} [Field K] [CommRing A] [CommRing B]
    [Bialgebra K A] [Bialgebra K B] (hB : Unipotent.OneMemStable K B) (φ : B →ₐc[K] A)
    (hinj : Function.Injective φ) {b : B} (hg : IsGroupLikeElem K (φ b)) : φ b = 1 := by
  have hb : IsGroupLikeElem K b := by
    refine ⟨?_, ?_⟩
    · have := hg.counit_eq_one
      rwa [CoalgHomClass.counit_comp_apply] at this
    · apply TensorProduct.map_injective_of_flat_flat (φ : B →ₗ[K] A) (φ : B →ₗ[K] A) hinj hinj
      rw [TensorProduct.map_tmul]
      exact (CoalgHomClass.map_comp_comul_apply φ b).trans hg.comul_eq_tmul_self
  rw [eq_one_of_isGroupLikeElem hB hb, map_one]

variable {K : Type u} [Field K]

/-- **Character lifting.** Let `G` be a commutative affine group over an algebraically closed field,
`s : S ⟶ G` a closed subgroup with `S ≅ D(N)`, and `q : G ⟶ Q` an fppf quotient by `S` onto an
affine unipotent group. Every character `n` of `S` lifts to a group-like element `g` of the
coordinate Hopf algebra of `G`; its `m`-th power is `1` whenever `m • n = 0`, and `g = 1` forces
`n = 0`. -/
theorem exists_groupLike_lift [IsAlgClosed K]
    {G S Q : GroupScheme (Spec (CommRingCat.of K))}
    [IsAffine G.X.left] [IsCommMonObj G.X] [IsAffine Q.X.left]
    {N : Type u} [AddCommGroup N]
    (eS0 : S ≅ (Diagonalizable.groupScheme (CommRingCat.of K) N).toGrp)
    (s : S ⟶ G) (hs : IsClosedSubgroup s) (q : G ⟶ Q)
    (hq : IsFppfQuotient (SubgroupFunctor.range s) q) (hQ : IsUnipotent Q) (n : N) :
    ∃ g : AffineCoordinates.hopfAlgebra G, IsGroupLikeElem K g ∧
      (∀ m : ℕ, m • n = 0 → g ^ m = 1) ∧ (g = 1 → n = 0) := by
  classical
  let R := CommRingCat.of K
  let A := AffineCoordinates.hopfAlgebra G
  let B := AffineCoordinates.hopfAlgebra Q
  let eG := AffineCoordinates.hopfSpecIso G
  let eQ := AffineCoordinates.hopfSpecIso Q
  let eS : (hopfSpec R).obj (op (Diagonalizable.hopfAlgebra R N)) ≅ S :=
    Diagonalizable.hopfSpecIso R N ≪≫ eS0.symm
  let π : A ⟶ Diagonalizable.hopfAlgebra R N :=
    (hopfSpec.fullyFaithful.preimage (eS.hom ≫ s ≫ eG.symm.hom)).unop
  let φ : B ⟶ A :=
    (hopfSpec.fullyFaithful.preimage (eG.symm.inv ≫ q ≫ eQ.symm.hom)).unop
  have hπ : (hopfSpec R).map π.op = eS.hom ≫ s ≫ eG.symm.hom :=
    hopfSpec.fullyFaithful.map_preimage _
  have hφ : (hopfSpec R).map φ.op = eG.symm.inv ≫ q ≫ eQ.symm.hom :=
    hopfSpec.fullyFaithful.map_preimage _
  have hi' : IsClosedSubgroup ((hopfSpec R).map π.op) := by
    rw [hπ]
    exact IsClosedSubgroup.iso_comp eS (hs.comp_iso eG.symm)
  have hq' : IsFppfQuotient (SubgroupFunctor.range ((hopfSpec R).map π.op))
      ((hopfSpec R).map φ.op) := by
    rw [hπ, hφ, SubgroupFunctor.range_iso_comp, SubgroupFunctor.range_comp_iso,
      ← Category.assoc]
    exact (hq.comapIso eG.symm).comp_iso eQ.symm
  have hsurj : Function.Surjective π.hom :=
    CentralExtensionHopfSpec.surjective_of_isClosedSubgroup π hi'
  have hinj : Function.Injective φ.hom :=
    (CentralExtensionHopfSpec.faithfullyFlat_of_isFppfQuotient φ hq').injective
  have hinv : ∀ a : A, a ∈ GroupAlgebraCoaction.grade π.hom 0 → ∃ b : B, φ.hom b = a := by
    intro a ha
    have : IsClosedImmersion ((hopfSpec R).map π.op).hom.hom.left := hi'
    refine CentralExtensionHopfSpec.exists_eq_of_lTensor_comul_eq φ π
      (Over.mono_of_mono_left _) hq' a ?_
    rw [GroupAlgebraCoaction.mem_grade_iff, GroupAlgebraCoaction.coaction_apply] at ha
    rw [← (AddMonoidAlgebra.scalarTensorEquiv K A).symm_apply_apply
      ((π.hom : A →ₗ[K] AddMonoidAlgebra K N).lTensor A (Coalgebra.comul a)), ha,
      AddMonoidAlgebra.scalarTensorEquiv_symm_single, ← AddMonoidAlgebra.one_def]
  have hB : Unipotent.OneMemStable K B :=
    Unipotent.oneMemStable_of_isUnipotent_cogroup (AffineCoordinates.coordinateCogroup Q)
      (IsUnipotent.of_iso (AffineCoordinates.coordinateCogroupIso Q) hQ)
  -- group-like elements of degree zero are trivial
  have hzero : ∀ g : A, IsGroupLikeElem K g → g ∈ GroupAlgebraCoaction.grade π.hom 0 →
      g = 1 := by
    intro g hg hg0
    obtain ⟨b, rfl⟩ := hinv g hg0
    exact eq_one_of_map_isGroupLikeElem hB φ.hom hinj hg
  have : Coalgebra.IsCocomm K A := AffineCoordinates.hopfAlgebra_isCocomm G
  obtain ⟨g, hg, hgn⟩ := GroupAlgebraCoaction.exists_isGroupLikeElem_mem_grade π.hom
    (GroupAlgebraCoaction.grade_ne_bot_of_surjective π.hom hsurj n)
  have hpow : ∀ m : ℕ, g ^ m ∈ GroupAlgebraCoaction.grade π.hom (m • n) := by
    intro m
    induction m with
    | zero => simpa using GroupAlgebraCoaction.one_mem_grade_zero π.hom
    | succ m ih =>
      rw [pow_succ, succ_nsmul]
      exact GroupAlgebraCoaction.mul_mem_grade π.hom ih hgn
  refine ⟨g, hg, fun m hm => hzero _ hg.pow (hm ▸ hpow m), fun h1 => ?_⟩
  by_contra hn
  have h1n : (1 : A) ∈ GroupAlgebraCoaction.grade π.hom n := h1 ▸ hgn
  have hp := GroupAlgebraCoaction.proj_of_mem π.hom h1n n
  rw [GroupAlgebraCoaction.proj_of_mem π.hom (GroupAlgebraCoaction.one_mem_grade_zero π.hom) n]
    at hp
  simp only [hn, ↓reduceIte] at hp
  exact Unipotent.one_ne_zero' K A hp.symm

/-- The coordinate Hopf algebra of a smooth affine group over a field is reduced. -/
theorem isReduced_hopfAlgebra (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffine G.X.left]
    [Smooth G.X.hom] : _root_.IsReduced (AffineCoordinates.hopfAlgebra G) := by
  have : IsReduced G.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedBase.isReduced_of_smooth_over_spec
      (CommRingCat.of K) G.X.left G.X.hom
  let e' : ((hopfSpec (CommRingCat.of K)).obj (op (AffineCoordinates.hopfAlgebra G))).X.left ≅
      G.X.left :=
    (Over.forget _).mapIso ((Grp.forget _).mapIso (AffineCoordinates.hopfSpecIso G))
  have : IsOpenImmersion e'.hom := IsOpenImmersion.of_isIso e'.hom
  have h1 : IsReduced
      ((hopfSpec (CommRingCat.of K)).obj (op (AffineCoordinates.hopfAlgebra G))).X.left :=
    isReduced_of_isOpenImmersion e'.hom
  have h2 : IsReduced (Spec (CommRingCat.of (AffineCoordinates.hopfAlgebra G))) := h1
  exact (affine_isReduced_iff _).mp h2

/-- The coordinate Hopf algebra of a connected affine group has connected prime spectrum. -/
theorem connectedSpace_primeSpectrum (G : GroupScheme (Spec (CommRingCat.of K)))
    [IsAffine G.X.left] [ConnectedSpace G.X.left] :
    ConnectedSpace (PrimeSpectrum (AffineCoordinates.hopfAlgebra G)) := by
  let e' : ((hopfSpec (CommRingCat.of K)).obj (op (AffineCoordinates.hopfAlgebra G))).X.left ≅
      G.X.left :=
    (Over.forget _).mapIso ((Grp.forget _).mapIso (AffineCoordinates.hopfSpecIso G))
  have : ConnectedSpace
      ((hopfSpec (CommRingCat.of K)).obj (op (AffineCoordinates.hopfAlgebra G))).X.left :=
    e'.inv.homeomorph.surjective.connectedSpace e'.inv.continuous
  exact this

section Consequences

variable [IsAlgClosed K] {G S Q : GroupScheme (Spec (CommRingCat.of K))}
    [IsAffine G.X.left] [IsCommMonObj G.X] [IsAffine Q.X.left]
    {N : Type u} [AddCommGroup N]
    (eS0 : S ≅ (Diagonalizable.groupScheme (CommRingCat.of K) N).toGrp)
    (s : S ⟶ G) (hs : IsClosedSubgroup s) (q : G ⟶ Q)
    (hq : IsFppfQuotient (SubgroupFunctor.range s) q) (hQ : IsUnipotent Q)
include eS0 hs hq hQ

/-- If `G` is smooth, the character group of `S` has no element of order the characteristic. -/
theorem eq_zero_of_smooth [Smooth G.X.hom] (p : ℕ) [ExpChar K p] (x : N) (hx : p • x = 0) :
    x = 0 := by
  obtain ⟨g, -, hpow, h1⟩ := exists_groupLike_lift eS0 s hs q hq hQ x
  have := isReduced_hopfAlgebra G
  have : Nontrivial (AffineCoordinates.hopfAlgebra G) :=
    ⟨⟨1, 0, Unipotent.one_ne_zero' K (AffineCoordinates.hopfAlgebra G)⟩⟩
  have hinj : Function.Injective (algebraMap K (AffineCoordinates.hopfAlgebra G)) :=
    (algebraMap K (AffineCoordinates.hopfAlgebra G)).injective
  have : ExpChar (AffineCoordinates.hopfAlgebra G) p := expChar_of_injective_algebraMap hinj p
  apply h1
  have hnil : IsNilpotent (g - 1) :=
    ⟨p, by rw [sub_pow_expChar, hpow p hx, one_pow, sub_self]⟩
  exact sub_eq_zero.mp hnil.eq_zero

/-- If `G` is connected, every torsion character of `S` is killed by a power of the
characteristic exponent. -/
theorem exists_pow_nsmul_eq_zero_of_connected [ConnectedSpace G.X.left] (p : ℕ) [ExpChar K p]
    (x : N) (hx : IsOfFinAddOrder x) : ∃ n : ℕ, p ^ n • x = 0 := by
  classical
  obtain ⟨a, m, hm, hNm⟩ :=
    Diagonalizable.SmoothConnectedCriteria.exists_pow_mul_ne_zero K p hx.addOrderOf_pos.ne'
  refine ⟨a, ?_⟩
  have hmy : m • (p ^ a • x) = 0 := by
    rw [smul_smul, mul_comm, ← hNm, addOrderOf_nsmul_eq_zero]
  obtain ⟨g, hg, hpow, h1⟩ := exists_groupLike_lift eS0 s hs q hq hQ (p ^ a • x)
  have hgm : g ^ m = 1 := hpow m hmy
  let c : AffineCoordinates.hopfAlgebra G :=
    algebraMap K (AffineCoordinates.hopfAlgebra G) (m : K)⁻¹
  have hc : c * m = 1 := by
    simp only [c]
    rw [← map_natCast (algebraMap K (AffineCoordinates.hopfAlgebra G)), ← map_mul,
      inv_mul_cancel₀ hm, map_one]
  have he := Diagonalizable.SmoothConnectedCriteria.isIdempotentElem_geomSum hgm hc
  have := connectedSpace_primeSpectrum G
  rcases Diagonalizable.SmoothConnectedCriteria.eq_zero_or_one_of_connectedSpace he with
    h0 | h1'
  · exfalso
    let ε : AffineCoordinates.hopfAlgebra G →ₐ[K] K :=
      Bialgebra.counitAlgHom K (AffineCoordinates.hopfAlgebra G)
    have hεg : ε g = 1 := hg.counit_eq_one
    have hεc : ε c = (m : K)⁻¹ := ε.commutes _
    have h' := congrArg ε h0
    rw [map_mul, map_sum, map_zero, hεc] at h'
    simp only [map_pow, hεg, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one] at h'
    rw [inv_mul_cancel₀ hm] at h'
    exact one_ne_zero h'
  · apply h1
    have h2 : (g - 1) * (c * ∑ i ∈ Finset.range m, g ^ i) = 0 := by
      rw [mul_left_comm, mul_comm (g - 1), mul_sub, mul_one,
        Diagonalizable.SmoothConnectedCriteria.geomSum_mul_self hgm, sub_self, mul_zero]
    rw [h1', mul_one, sub_eq_zero] at h2
    exact h2

end Consequences

end MultiplicativePart

end Langlands.GroupScheme
