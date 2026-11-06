import Langlands.GroupScheme.Rational.MaximalLeviDynamicReduction
import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.Rational.MaximalLeviFiniteWeights
import Langlands.GroupScheme.Rational.OriginalLeviCocharacter
import Langlands.GroupScheme.Rational.CentralizerRootSupport
import Langlands.GroupScheme.Rational.MinimalParabolicSplitComponent
import Langlands.GroupScheme.Rational.ReductiveParabolicContraction
import Langlands.GroupScheme.Dynamic.ImproperParabolic
import Langlands.Geometry.Building.RealTorusDuality

/-! # A central-kernel character for the split component of a maximal parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RealTorusSpace

section Kernel

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    {A : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A character `α₀` of `A` such that every integral cocharacter of `A` in the kernel of the
lattice pairing with `α₀` becomes central in `G` through `i`. -/
def HasCentralKernelCharacter (i : A.toGrp ⟶ G) : Prop :=
  ∃ α₀ : characterLattice A, ∀ ν : cocharacterLattice A,
    latticePairing A α₀ ν = 0 → IsCentral (CommGroupScheme.groupHom ν ≫ i)

/-- On a split torus, a real character vanishing on every integral cocharacter is zero. -/
theorem eq_zero_of_pair_one_tmul_eq_zero (hA : IsSplitTorus A.toGrp) {y : Vstar A}
    (hy : ∀ ν : cocharacterLattice A, pair A y ((1 : ℝ) ⊗ₜ[ℤ] ν) = 0) : y = 0 := by
  have := isPerfPair_of_isSplitTorus hA
  apply (LinearMap.IsPerfPair.bijective_left (pair A)).injective
  rw [map_zero]
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.zero_apply]
  induction v using TensorProduct.inductionOn with
  | tmul r ν =>
    have hr : r ⊗ₜ[ℤ] ν = r • ((1 : ℝ) ⊗ₜ[ℤ] ν) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hr, map_smul, hy, smul_zero]
  | add v w hv hw => rw [map_add, hv, hw, add_zero]

/-- On a split torus, the real characters vanishing on the integral kernel of one integral
character lie on a single line. -/
theorem exists_smul_of_pair_kernel (hA : IsSplitTorus A.toGrp) (α₀ : characterLattice A) :
    ∃ e : Vstar A, ∀ y : Vstar A,
      (∀ ν : cocharacterLattice A, latticePairing A α₀ ν = 0 →
        pair A y ((1 : ℝ) ⊗ₜ[ℤ] ν) = 0) →
      ∃ c : ℝ, y = c • e := by
  by_cases hall : ∀ ν : cocharacterLattice A, latticePairing A α₀ ν = 0
  · refine ⟨0, fun y hy => ⟨0, ?_⟩⟩
    rw [smul_zero]
    exact eq_zero_of_pair_one_tmul_eq_zero hA fun ν => hy ν (hall ν)
  · simp only [not_forall] at hall
    obtain ⟨ν₀, hν₀⟩ := hall
    have hn : ((latticePairing A α₀ ν₀ : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hν₀
    refine ⟨(1 : ℝ) ⊗ₜ[ℤ] α₀, fun y hy =>
      ⟨pair A y ((1 : ℝ) ⊗ₜ[ℤ] ν₀) / (latticePairing A α₀ ν₀ : ℝ), ?_⟩⟩
    rw [← sub_eq_zero]
    apply eq_zero_of_pair_one_tmul_eq_zero hA
    intro ν
    have hw : latticePairing A α₀
        (latticePairing A α₀ ν₀ • ν - latticePairing A α₀ ν • ν₀) = 0 := by
      rw [map_sub, map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul, mul_comm, sub_self]
    have h := hy _ hw
    rw [tmul_sub, tmul_smul, tmul_smul, map_sub, map_zsmul, map_zsmul, zsmul_eq_mul,
      zsmul_eq_mul, sub_eq_zero] at h
    rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, pair_tmul_tmul,
      one_mul, one_mul, smul_eq_mul, div_mul_eq_mul_div, sub_eq_zero, eq_div_iff hn,
      mul_comm, h, mul_comm]

/-- A central-kernel character puts every real character vanishing on the central
cocharacters on the line of any nonzero such character. -/
theorem mem_span_of_hasCentralKernelCharacter (hA : IsSplitTorus A.toGrp)
    {i : A.toGrp ⟶ G} (hK : HasCentralKernelCharacter i) {x : Vstar A} (hx0 : x ≠ 0)
    (hx : ∀ ν : cocharacterLattice A, IsCentral (CommGroupScheme.groupHom ν ≫ i) →
      pair A x ((1 : ℝ) ⊗ₜ[ℤ] ν) = 0)
    (y : Vstar A)
    (hy : ∀ ν : cocharacterLattice A, IsCentral (CommGroupScheme.groupHom ν ≫ i) →
      pair A y ((1 : ℝ) ⊗ₜ[ℤ] ν) = 0) :
    y ∈ Submodule.span ℝ {x} := by
  obtain ⟨α₀, hα₀⟩ := hK
  obtain ⟨e, he⟩ := exists_smul_of_pair_kernel hA α₀
  obtain ⟨cx, hcx⟩ := he x fun ν hν => hx ν (hα₀ ν hν)
  obtain ⟨cy, hcy⟩ := he y fun ν hν => hy ν (hα₀ ν hν)
  have hcx0 : cx ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [hcx, zero_smul])
  rw [Submodule.mem_span_singleton]
  refine ⟨cy / cx, ?_⟩
  rw [hcx, hcy, smul_smul, div_mul_cancel₀ _ hcx0]

end Kernel

/-- Assume that every parabolic subgroup is a dynamic parabolic. For a maximal proper
parabolic `P` with rational Levi `M` and split component `A`, every root of `A` that is
nonzero on a presenting cocharacter of `P` is a central-kernel character. -/
theorem hasCentralKernelCharacter_of_maximal (hPD : ParabolicDynamicStatement.{u})
    {k : Type u} [Field k] {G P M : GroupScheme (Spec (CommRingCat.of k))}
    {A : CommGroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l) (hpp : ¬ IsIso p)
    (hmax : ∀ (Q' : GroupScheme (Spec (CommRingCat.of k))) (q' : Q' ⟶ G) (j : P ⟶ Q'),
      IsParabolicSubgroup q' → j ≫ q' = p → IsIso j ∨ IsIso q')
    (ha : IsSplitComponent a) :
    HasCentralKernelCharacter (a ≫ l ≫ p) := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  let : Mono p.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom M.X.hom := hl.isConnectedReductive.isAffineHom
  let : IsClosedImmersion l.hom.hom.left := hl.isClosedSubgroup
  let : Mono l.hom.hom := Over.mono_of_mono_left _
  have hm : Mono (l ≫ p).hom.hom := by
    change Mono (l.hom.hom ≫ p.hom.hom)
    infer_instance
  have hMrep : (SubgroupFunctor.range (l ≫ p)).IsRepresentedBy (l ≫ p) := ⟨hm, rfl⟩
  have hA : IsSplitTorus A.toGrp := ha.1.1.1
  obtain ⟨chi, hchi⟩ := (hPD k G hG P p hp.isClosedSubgroup).mp hp
  obtain ⟨zeta, hzP, hzZ, -⟩ :=
    hl.exists_splitComponentCocharacter_of_dynamicParabolic hG chi ⟨inferInstance, hchi⟩ ha
  let i := a ≫ l ≫ p
  have hzproper : Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) ≠ ⊤ := by
    intro htop
    apply hpp
    apply isIso_of_full_range p hzP.1
    exact hzP.2.trans (Dynamic.parabolic_eq_top_of_centralizer _ htop)
  have hroot : ∃ α₀ ∈ relativeRoots i, latticePairing A α₀ zeta ≠ 0 := by
    by_contra hnone
    refine hzproper ((isCentral_iff_dynamicCentralizer_eq_top _).mp
      (rootAnnihilatorCentrality k G A hA i zeta fun α hα => ?_))
    by_contra h
    exact hnone ⟨α, hα, h⟩
  obtain ⟨α₀, hα₀, hα₀z⟩ := hroot
  refine ⟨α₀, fun ν hν => ?_⟩
  by_contra hνc
  have hνproper : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) ≠ ⊤ :=
    fun htop => hνc ((isCentral_iff_dynamicCentralizer_eq_top _).mpr htop)
  have hle : Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) ≤
      Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) := by
    rw [hzZ]
    exact (isCentral_comp_iff_le_dynamicCentralizer hMrep a rfl ν).mp
      (ha.1.2.comp (CommGroupScheme.groupHom ν))
  have hlt : Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) <
      Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) :=
    lt_of_le_not_ge hle fun hback =>
      hα₀z (relativeRoot_pairing_eq_zero_of_centralizer_le hA i zeta ν hback hα₀ hν)
  obtain ⟨mu, hmuP, hmuZ, hmuproper⟩ :=
    exists_properCentralizerCoarsening hA i zeta ν hlt hνproper
  let Q' := Dynamic.Affine.parabolicScheme (CommGroupScheme.groupHom mu ≫ i)
  let q' : Q' ⟶ G := Dynamic.Affine.parabolicHom (CommGroupScheme.groupHom mu ≫ i)
  have hq'rep : (Dynamic.parabolic (CommGroupScheme.groupHom mu ≫ i)).IsRepresentedBy q' :=
    Dynamic.Affine.isRepresentedBy_parabolicHom _
  have hq'par : IsParabolicSubgroup q' :=
    (hPD k G hG Q' q' (Dynamic.Affine.isClosedSubgroup_parabolicHom _)).mpr
      ⟨_, hq'rep.2⟩
  have hPmu : SubgroupFunctor.range p ≤
      Dynamic.parabolic (CommGroupScheme.groupHom mu ≫ i) := hzP.2.le.trans hmuP
  let j : P ⟶ Q' := hq'rep.factorHom p hPmu
  have hj : j ≫ q' = p := hq'rep.factorHom_comp p hPmu
  rcases hmax Q' q' j hq'par hj with hjiso | hq'iso
  · let : IsIso j := hjiso
    have hPmu' : (Dynamic.parabolic (CommGroupScheme.groupHom mu ≫ i)).IsRepresentedBy p :=
      ⟨hzP.1, by
        rw [← hj]
        have hr : SubgroupFunctor.range (j ≫ q') = SubgroupFunctor.range q' := by
          simpa only [asIso_hom] using SubgroupFunctor.range_iso_comp (asIso j) q'
        exact hr.trans hq'rep.2⟩
    have hZmu := hl.centralizer_eq_of_dynamicParabolic hG
      (CommGroupScheme.groupHom mu ≫ a) (by
        simpa only [i, Category.assoc] using hPmu')
    have heq : Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) =
        Dynamic.centralizer (CommGroupScheme.groupHom mu ≫ i) := by
      simpa only [i, Category.assoc] using hzZ.trans hZmu.symm
    exact hmuZ.ne heq
  · let : IsIso q' := hq'iso
    have htop : Dynamic.parabolic (CommGroupScheme.groupHom mu ≫ i) = ⊤ :=
      hq'rep.2.symm.trans (full_range_of_isIso q')
    exact hmuproper
      ((Dynamic.parabolic_eq_top_iff_centralizer_eq_top hG.hasTrivialUnipotentRadical _).mp htop)

end Langlands.GroupScheme
