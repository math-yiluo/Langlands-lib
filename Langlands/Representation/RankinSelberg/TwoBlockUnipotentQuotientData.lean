import Langlands.Representation.RankinSelberg.TwoBlockDeformationCell
import Langlands.Representation.RankinSelberg.DeterminantSlices
import Langlands.Analysis.Local.QuotientTopology
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof

/-!
# The two-block unipotent quotient and its radical fiber average

JPSS (1983), Section 4.6, printed pages 411-412: the first unfolding passes from
equation (4), an iterated integral over `N_r \ G_r^m` and the complementary upper
radical, to the integral over `N_(t_1,t_2) \ G_r^m`, where `N_(t_1,t_2)` is the group
(5) of block diagonal matrices `diag(n_1, n_2)` with `n_i` upper unipotent.

For two blocks of sizes `m 0 + 1` and `m 1 + 1` of total rank `t + 1`, this module
constructs that subgroup `H` of `GL_(t+1)`, the actual left quotient `H \ GL_(t+1)`
with the projection to `N \ GL_(t+1)`, the radical fiber map
`(x, g) ↦ [u(x) g]_H`, its unweighted fiber integral, the descended radical average on
`N \ GL_(t+1)` and the determinant slices of `H \ GL_(t+1)`. No integrability,
quotient-measure, or Fubini statement is asserted.
-/

noncomputable section

open MeasureTheory

namespace Langlands.RankinSelberg.TwoBlockUnipotentQuotient

open GeneralLinear TwoBlockJacquet TwoBlockDeformation QuotientIntegration

universe uF uR uG

/-- The product `N_(m 0 + 1) × N_(m 1 + 1)` of the two block upper-unipotent groups. -/
abbrev BlockUnipotents (m : Fin 2 → ℕ) (R : Type uR) [CommRing R] :=
  ∀ i : Fin 2, upperUnipotent (m i + 1) R

section Algebra

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (R : Type uR) [CommRing R]

/-- A matrix of total rank `t + 1` whose lower-left block vanishes and whose two diagonal
blocks are upper unipotent is upper unipotent. -/
theorem mem_upperUnipotent_of_blocks (A : GeneralLinear (t + 1) R)
    (h10 : ∀ (a : Fin (m 1 + 1)) (b : Fin (m 0 + 1)),
      A ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 0 b) = 0)
    (hlow : ∀ (i : Fin 2) (a b : Fin (m i + 1)), b < a →
      A ((succBlockShape m h).index i a) ((succBlockShape m h).index i b) = 0)
    (hdiag : ∀ (i : Fin 2) (a : Fin (m i + 1)),
      A ((succBlockShape m h).index i a) ((succBlockShape m h).index i a) = 1) :
    A ∈ upperUnipotent (t + 1) R := by
  refine ⟨fun k l hlk => ?_, fun k => ?_⟩
  · obtain ⟨⟨i, a⟩, rfl⟩ := (succBlockShape m h).indexEquiv.surjective k
    obtain ⟨⟨j, b⟩, rfl⟩ := (succBlockShape m h).indexEquiv.surjective l
    change (succBlockShape m h).index j b < (succBlockShape m h).index i a at hlk
    change A ((succBlockShape m h).index i a) ((succBlockShape m h).index j b) = 0
    rw [Fin.lt_def] at hlk
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · rw [val_index_zero, val_index_zero] at hlk
      exact hlow 0 a b (Fin.lt_def.mpr hlk)
    · rw [val_index_zero, val_index_one] at hlk
      exact absurd hlk (by have := a.isLt; omega)
    · exact h10 a b
    · rw [val_index_one, val_index_one] at hlk
      exact hlow 1 a b (Fin.lt_def.mpr (by omega))
  · obtain ⟨⟨i, a⟩, rfl⟩ := (succBlockShape m h).indexEquiv.surjective k
    exact hdiag i a

/-- The complementary upper radical matrix `u(x) = [[1, x], [0, 1]]` is upper unipotent. -/
theorem upperRadical_mem_upperUnipotent (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    upperRadical h R x ∈ upperUnipotent (t + 1) R := by
  refine mem_upperUnipotent_of_blocks h R _ (upperRadical_index_one_zero h R x)
    (fun i a b hab => ?_) (fun i a => ?_)
  · have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · rw [upperRadical_index_zero_zero]; simp [ne_of_gt hab]
    · rw [upperRadical_index_one_one]; simp [ne_of_gt hab]
  · have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · rw [upperRadical_index_zero_zero]; simp
    · rw [upperRadical_index_one_one]; simp

/-- Upper unipotent matrices have determinant one, over every commutative ring. -/
theorem determinant_eq_one_of_mem_upperUnipotent {n : ℕ} {g : GeneralLinear n R}
    (hg : g ∈ upperUnipotent n R) : GeneralLinear.determinant g = 1 :=
  Units.ext (by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one,
      Matrix.det_of_isUpperTriangular hg.1, Finset.prod_eq_one fun i _ => hg.2 i])

/-! ### The block-diagonal upper-unipotent subgroup -/

/-- The block-diagonal embedding `(n_0, n_1) ↦ diag(n_0, n_1)` of the two block
upper-unipotent groups, through the published Levi embedding of `succBlockShape m h`. -/
def blockEmbedding : BlockUnipotents m R →* GeneralLinear (t + 1) R :=
  ((succBlockShape m h).leviEmbedding R).comp
    (MonoidHom.piMap fun i => (upperUnipotent (m i + 1) R).subtype)

/-- Representative formula: the embedding is the Levi embedding of the blocks. -/
theorem blockEmbedding_apply (n : BlockUnipotents m R) :
    blockEmbedding h R n = (succBlockShape m h).leviEmbedding R (fun i => (n i).val) :=
  rfl

/-- The entries of the diagonal block `i` of `diag(n_0, n_1)` are those of `n_i`. -/
@[simp]
theorem blockEmbedding_index_same (n : BlockUnipotents m R) (i : Fin 2) (a b : Fin (m i + 1)) :
    blockEmbedding h R n ((succBlockShape m h).index i a) ((succBlockShape m h).index i b) =
      (n i).val a b :=
  (succBlockShape m h).leviEmbedding_apply_same R _ i a b

@[simp]
theorem blockEmbedding_index_zero_one (n : BlockUnipotents m R) (a : Fin (m 0 + 1))
    (b : Fin (m 1 + 1)) :
    blockEmbedding h R n ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 b) = 0 :=
  leviEmbedding_index_zero_one h _ a b

@[simp]
theorem blockEmbedding_index_one_zero (n : BlockUnipotents m R) (a : Fin (m 1 + 1))
    (b : Fin (m 0 + 1)) :
    blockEmbedding h R n ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 0 b) = 0 :=
  leviEmbedding_index_one_zero h _ a b

theorem blockEmbedding_injective : Function.Injective (blockEmbedding h R) := by
  intro n n' hn
  have hL := (succBlockShape m h).leviEmbedding_injective R
    (show (succBlockShape m h).leviEmbedding R (fun i => (n i).val) =
      (succBlockShape m h).leviEmbedding R (fun i => (n' i).val) from hn)
  funext i
  exact Subtype.ext (congrFun hL i)

/-- `diag(n_0, n_1)` is upper unipotent. -/
theorem blockEmbedding_mem_upperUnipotent (n : BlockUnipotents m R) :
    blockEmbedding h R n ∈ upperUnipotent (t + 1) R :=
  mem_upperUnipotent_of_blocks h R _ (blockEmbedding_index_one_zero h R n)
    (fun i a b hab => by
      rw [blockEmbedding_index_same]
      exact UpperUnipotent.entry_eq_zero (n i) hab)
    (fun i a => by
      rw [blockEmbedding_index_same]
      exact UpperUnipotent.entry_diag (n i) a)

/-- The subgroup `N_(t_1,t_2)` of JPSS (4.6), (5): the actual image of the block-diagonal
embedding of the two block upper-unipotent groups. -/
def blockUnipotent : Subgroup (GeneralLinear (t + 1) R) :=
  (blockEmbedding h R).range

theorem mem_blockUnipotent_iff (g : GeneralLinear (t + 1) R) :
    g ∈ blockUnipotent h R ↔ ∃ n : BlockUnipotents m R, blockEmbedding h R n = g :=
  Iff.rfl

theorem blockEmbedding_mem (n : BlockUnipotents m R) :
    blockEmbedding h R n ∈ blockUnipotent h R :=
  ⟨n, rfl⟩

/-- `N_(t_1,t_2) ≤ N_(t+1)`. -/
theorem blockUnipotent_le_upperUnipotent : blockUnipotent h R ≤ upperUnipotent (t + 1) R := by
  rintro _ ⟨n, rfl⟩
  exact blockEmbedding_mem_upperUnipotent h R n

/-- Determinant-one law for the embedding. -/
@[simp]
theorem determinant_blockEmbedding (n : BlockUnipotents m R) :
    GeneralLinear.determinant (blockEmbedding h R n) = 1 :=
  determinant_eq_one_of_mem_upperUnipotent R (blockEmbedding_mem_upperUnipotent h R n)

theorem determinant_eq_one_of_mem_blockUnipotent {g : GeneralLinear (t + 1) R}
    (hg : g ∈ blockUnipotent h R) : GeneralLinear.determinant g = 1 :=
  determinant_eq_one_of_mem_upperUnipotent R (blockUnipotent_le_upperUnipotent h R hg)

/-- The diagonal blocks extracted by the published `unipotentLevi` recover the factors of
`diag(n_0, n_1)`. -/
theorem unipotentLevi_blockEmbedding (n : BlockUnipotents m R) (i : Fin 2) :
    unipotentLevi h ⟨blockEmbedding h R n, blockEmbedding_mem_upperUnipotent h R n⟩ i =
      (n i).val := by
  apply Units.ext
  ext a b
  exact blockEmbedding_index_same h R n i a b

/-- Intrinsic description: `H` consists of the upper unipotent matrices whose upper-right
block vanishes. -/
theorem mem_blockUnipotent_iff_corner (g : GeneralLinear (t + 1) R) :
    g ∈ blockUnipotent h R ↔ g ∈ upperUnipotent (t + 1) R ∧
      ∀ (a : Fin (m 0 + 1)) (b : Fin (m 1 + 1)),
        g ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 b) = 0 := by
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨blockEmbedding_mem_upperUnipotent h R n, blockEmbedding_index_zero_one h R n⟩
  · rintro ⟨hg, hc⟩
    refine ⟨fun i => ⟨unipotentLevi h ⟨g, hg⟩ i, unipotentLevi_mem h ⟨g, hg⟩ i⟩, ?_⟩
    apply ext_index h
    · intro a b
      rw [blockEmbedding_index_same]
      rfl
    · intro a b
      rw [blockEmbedding_index_zero_one, hc]
    · intro a b
      rw [blockEmbedding_index_one_zero]
      exact (upperUnipotent_index_one_zero h ⟨g, hg⟩ a b).symm
    · intro a b
      rw [blockEmbedding_index_same]
      rfl

/-- The multiplicative equivalence of the product of the two block unipotent groups with
`H`. The forward map is `blockEmbedding`; the inverse extracts the diagonal blocks by the
published `unipotentLevi`. -/
def blockUnipotentEquiv : BlockUnipotents m R ≃* blockUnipotent h R where
  toFun n := ⟨blockEmbedding h R n, blockEmbedding_mem h R n⟩
  invFun g i := ⟨unipotentLevi h ⟨g.val, blockUnipotent_le_upperUnipotent h R g.property⟩ i,
    unipotentLevi_mem h _ i⟩
  left_inv n := by
    funext i
    exact Subtype.ext (unipotentLevi_blockEmbedding h R n i)
  right_inv := by
    rintro ⟨_, n, rfl⟩
    apply Subtype.ext
    change blockEmbedding h R _ = blockEmbedding h R n
    congr 1
    funext i
    exact Subtype.ext (unipotentLevi_blockEmbedding h R n i)
  map_mul' n n' := Subtype.ext (map_mul (blockEmbedding h R) n n')

@[simp]
theorem blockUnipotentEquiv_apply_val (n : BlockUnipotents m R) :
    (blockUnipotentEquiv h R n).val = blockEmbedding h R n :=
  rfl

/-- Inverse formula: the `i`-th factor of `g ∈ H` is its `i`-th diagonal block. -/
@[simp]
theorem blockUnipotentEquiv_symm_apply_val (g : blockUnipotent h R) (i : Fin 2) :
    ((blockUnipotentEquiv h R).symm g i).val =
      unipotentLevi h ⟨g.val, blockUnipotent_le_upperUnipotent h R g.property⟩ i :=
  rfl

/-- Inverse formula, entrywise. -/
theorem blockUnipotentEquiv_symm_apply_apply (g : blockUnipotent h R) (i : Fin 2)
    (a b : Fin (m i + 1)) :
    ((blockUnipotentEquiv h R).symm g i).val a b =
      g.val ((succBlockShape m h).index i a) ((succBlockShape m h).index i b) :=
  rfl

/-- The factorization `u(x) n g = diag(n_0, n_1) u(n_0⁻¹ (β + x n_1)) g` of the published
`upperRadical_mul_upperUnipotent`, with a final right factor `g`; the diagonal factor
lies in `H`. -/
theorem upperRadical_mul_upperUnipotent_mul (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R)
    (n : upperUnipotent (t + 1) R) (g : GeneralLinear (t + 1) R) :
    upperRadical h R x * (n.val * g) =
      blockEmbedding h R (fun i => ⟨unipotentLevi h n i, unipotentLevi_mem h n i⟩) *
        (upperRadical h R (unipotentShift h n x) * g) := by
  rw [← mul_assoc, upperRadical_mul_upperUnipotent, mul_assoc]
  rfl

end Algebra

/-! ### Topology of the subgroup -/

section Topology

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (R : Type uR) [CommRing R]
variable [TopologicalSpace R]

section Ring

variable [IsTopologicalRing R]

omit [IsTopologicalRing R] in
theorem continuous_blockEmbedding : Continuous (blockEmbedding h R) :=
  ((succBlockShape m h).leviEmbeddingContinuous R).continuous.comp
    (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i))

/-- The published diagonal-block extraction is continuous on the upper unipotent group. -/
theorem continuous_unipotentLevi :
    Continuous (fun n : upperUnipotent (t + 1) R => unipotentLevi h n) :=
  ((succBlockShape m h).leviProjectionContinuous R).continuous.comp
    (continuous_subtype_val.subtype_mk _)

/-- The equivalence of `N_(m 0 + 1) × N_(m 1 + 1)` with `H` is a homeomorphism. -/
def blockUnipotentHomeomorph : BlockUnipotents m R ≃ₜ* blockUnipotent h R where
  toMulEquiv := blockUnipotentEquiv h R
  continuous_toFun := (continuous_blockEmbedding h R).subtype_mk _
  continuous_invFun := continuous_pi fun i =>
    (((continuous_apply i).comp (continuous_unipotentLevi h R)).comp
      (continuous_subtype_val.subtype_mk _)).subtype_mk _

@[simp]
theorem blockUnipotentHomeomorph_toMulEquiv :
    (blockUnipotentHomeomorph h R).toMulEquiv = blockUnipotentEquiv h R :=
  rfl

end Ring

variable [T2Space R]

/-- `H` is closed: it is cut out of the closed group `N_(t+1)` by the vanishing of the
upper-right block. -/
theorem isClosed_blockUnipotent :
    IsClosed (blockUnipotent h R : Set (GeneralLinear (t + 1) R)) := by
  have he : (blockUnipotent h R : Set (GeneralLinear (t + 1) R)) =
      (upperUnipotent (t + 1) R : Set (GeneralLinear (t + 1) R)) ∩
        ⋂ (a : Fin (m 0 + 1)) (b : Fin (m 1 + 1)),
          {g : GeneralLinear (t + 1) R |
            g ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 b) = 0} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    exact mem_blockUnipotent_iff_corner h R g
  rw [he]
  exact (UpperUnipotent.isClosed (R := R) (n := t + 1)).inter
    (isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_eq (GeneralLinear.entry (R := R) _ _).continuous continuous_const)

end Topology

section Canonical

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- For the canonical p-adic topology, `N_(m 0 + 1) × N_(m 1 + 1) ≃ₜ* H`. -/
def canonicalBlockUnipotentHomeomorph :
    letI := F.canonicalTopologicalData.topology
    BlockUnipotents m F.Carrier ≃ₜ* blockUnipotent h F.Carrier :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.valuativeRel
  letI := F.canonicalTopologicalData.localField
  blockUnipotentHomeomorph h F.Carrier

/-- Continuity of `(n_0, n_1) ↦ diag(n_0, n_1) ∈ H` for the canonical p-adic topology. -/
theorem continuous_blockUnipotentEquiv :
    letI := F.canonicalTopologicalData.topology
    Continuous (blockUnipotentEquiv h F.Carrier) :=
  letI := F.canonicalTopologicalData.topology
  (canonicalBlockUnipotentHomeomorph F h).continuous

/-- Continuity of the inverse `H → N_(m 0 + 1) × N_(m 1 + 1)` for the canonical p-adic
topology. -/
theorem continuous_blockUnipotentEquiv_symm :
    letI := F.canonicalTopologicalData.topology
    Continuous (blockUnipotentEquiv h F.Carrier).symm :=
  letI := F.canonicalTopologicalData.topology
  (canonicalBlockUnipotentHomeomorph F h).symm.continuous

/-- `H` is closed in `GL_(t+1)(F)` for the canonical p-adic topology. -/
theorem isClosed_blockUnipotent_canonical :
    letI := F.canonicalTopologicalData.topology
    IsClosed (blockUnipotent h F.Carrier : Set (GeneralLinear (t + 1) F.Carrier)) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.fieldT2
  exact isClosed_blockUnipotent h F.Carrier

end Canonical

/-! ### The intermediate quotient and the radical fiber map -/

/-- Left multiplication by an element of `P` does not change the left coset `P g`. -/
theorem mk_mul_of_mem {G : Type uG} [Group G] (P : Subgroup G) {u : G} (hu : u ∈ P) (g : G) :
    (Quotient.mk _ (u * g) : LeftQuotient P) = Quotient.mk _ g :=
  Quotient.sound (QuotientGroup.rightRel_apply.mpr (by
    rw [mul_inv_rev, mul_inv_cancel_left]
    exact P.inv_mem hu))

section Quotient

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (K : Type uR) [Field K]

/-- The actual intermediate left quotient `N_(t_1,t_2) \ GL_(t+1)`. -/
abbrev BlockQuotient := LeftQuotient (blockUnipotent h K)

/-- The canonical projection `H \ G → N \ G`, `[g]_H ↦ [g]_N`, by quotient descent through
`H ≤ N`. -/
def projection : BlockQuotient h K → LeftUnipotentQuotient t K :=
  descend (blockUnipotent h K) (fun g => (Quotient.mk _ g : LeftUnipotentQuotient t K))
    (fun u g => mk_mul_of_mem _ (blockUnipotent_le_upperUnipotent h K u.property) g)

@[simp]
theorem projection_mk (g : GeneralLinear (t + 1) K) :
    projection h K (Quotient.mk _ g) = Quotient.mk _ g :=
  rfl

theorem projection_surjective : Function.Surjective (projection h K) := by
  intro q
  induction q using Quotient.inductionOn with
  | h g => exact ⟨Quotient.mk _ g, rfl⟩

/-- The radical fiber map `(x, g) ↦ [u(x) g]_H` on representatives. -/
def fiberPoint (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) K) (g : GeneralLinear (t + 1) K) :
    BlockQuotient h K :=
  Quotient.mk _ (upperRadical h K x * g)

theorem fiberPoint_def (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) K)
    (g : GeneralLinear (t + 1) K) :
    fiberPoint h K x g = Quotient.mk _ (upperRadical h K x * g) :=
  rfl

/-- Every point of the fiber over `[g]_N` projects to `[g]_N`. -/
@[simp]
theorem projection_fiberPoint (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) K)
    (g : GeneralLinear (t + 1) K) :
    projection h K (fiberPoint h K x g) = Quotient.mk _ g :=
  mk_mul_of_mem _ (upperRadical_mem_upperUnipotent h K x) g

/-- Left translation of the base point by `n ∈ N` is the affine change of radical
coordinates `x ↦ n_0⁻¹ (β + x n_1)`. -/
theorem fiberPoint_upperUnipotent_mul (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) K)
    (n : upperUnipotent (t + 1) K) (g : GeneralLinear (t + 1) K) :
    fiberPoint h K x (n.val * g) = fiberPoint h K (unipotentShift h n x) g := by
  rw [fiberPoint_def, fiberPoint_def, upperRadical_mul_upperUnipotent_mul]
  exact mk_mul_of_mem _ (blockEmbedding_mem h K _) _

end Quotient

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- The intermediate quotient is Hausdorff for the canonical p-adic topology. -/
theorem t2Space_blockQuotient :
    letI := F.canonicalTopologicalData.topology
    T2Space (BlockQuotient h F.Carrier) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  exact leftQuotient_t2Space _ (isClosed_blockUnipotent_canonical F h)

/-- The projection `H \ G → N \ G` is continuous for the quotient topologies. -/
theorem continuous_projection :
    letI := F.canonicalTopologicalData.topology
    Continuous (projection h F.Carrier) := by
  let := F.canonicalTopologicalData.topology
  exact Continuous.quotient_lift continuous_quotient_mk' _

/-- The radical fiber map is jointly continuous in `(x, g)`. -/
theorem continuous_fiberPoint :
    letI := F.canonicalTopologicalData.topology
    Continuous (Function.uncurry (fiberPoint h F.Carrier)) := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup (t + 1)
  exact continuous_quotient_mk'.comp
    (((continuous_upperRadical h F.Carrier).comp continuous_fst).mul continuous_snd)

/-- The projection intertwines right translation on the two quotients. -/
theorem projection_rightTranslate :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    ∀ (g : GeneralLinear (t + 1) F.Carrier) (q : BlockQuotient h F.Carrier),
      projection h F.Carrier (rightTranslate _ g q) =
        rightTranslate _ g (projection h F.Carrier q) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  intro g q
  induction q using Quotient.inductionOn with
  | h x => rfl

/-- Right translation of the base point translates the fiber point. -/
theorem fiberPoint_mul :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    ∀ (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)
      (g g' : GeneralLinear (t + 1) F.Carrier),
      fiberPoint h F.Carrier x (g * g') = rightTranslate _ g' (fiberPoint h F.Carrier x g) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  intro x g g'
  rw [fiberPoint_def, fiberPoint_def, rightTranslate_mk, mul_assoc]

/-! ### The radical fiber integral and its descent -/

section Average

variable [MeasurableSpace F.Carrier]

/-- The unweighted radical fiber integral `g ↦ ∫ f([u(x) g]_H) dμ(x)`, the ordinary total
Bochner integral against the supplied measure on the rectangle. -/
def fiberIntegral (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
    (f : BlockQuotient h F.Carrier → ℂ) (g : GeneralLinear (t + 1) F.Carrier) : ℂ :=
  ∫ x, f (fiberPoint h F.Carrier x g) ∂μ

theorem fiberIntegral_def (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
    (f : BlockQuotient h F.Carrier → ℂ) (g : GeneralLinear (t + 1) F.Carrier) :
    fiberIntegral F h μ f g = ∫ x, f (fiberPoint h F.Carrier x g) ∂μ :=
  rfl

/-- Left `N`-invariance of the fiber integral, for every Borel additive Haar measure on the
rectangle and every scalar function, without any integrability hypothesis. -/
theorem fiberIntegral_upperUnipotent_mul :
    letI := F.canonicalTopologicalData.topology
    ∀ [BorelSpace F.Carrier]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)) [μ.IsAddHaarMeasure]
      (f : BlockQuotient h F.Carrier → ℂ) (n : upperUnipotent (t + 1) F.Carrier)
      (g : GeneralLinear (t + 1) F.Carrier),
      fiberIntegral F h μ f (n.val * g) = fiberIntegral F h μ f g := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ μ _ f n g
  have : SecondCountableTopology F.Carrier := T.secondCountableTopology
  simp only [fiberIntegral_def, fiberPoint_upperUnipotent_mul]
  exact integral_comp_unipotentShift F h μ n (fun y => f (fiberPoint h F.Carrier y g))

/-- Right translation of the base point is right translation of the integrand. -/
theorem fiberIntegral_mul :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    ∀ (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
      (f : BlockQuotient h F.Carrier → ℂ) (g g' : GeneralLinear (t + 1) F.Carrier),
      fiberIntegral F h μ f (g * g') =
        fiberIntegral F h μ (fun r => f (rightTranslate _ g' r)) g := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  intro μ f g g'
  simp only [fiberIntegral_def, fiberPoint_mul]

/-- The radical average on the actual quotient `N \ GL_(t+1)`: the actual descent of the
left-`N`-invariant fiber integral. No coset representative is chosen. -/
def radicalAverage :
    letI := F.canonicalTopologicalData.topology
    ∀ [BorelSpace F.Carrier]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)) [μ.IsAddHaarMeasure],
      (BlockQuotient h F.Carrier → ℂ) → LeftUnipotentQuotient t F.Carrier → ℂ := by
  letI := F.canonicalTopologicalData.topology
  intro _ μ _ f
  exact descend _ (fiberIntegral F h μ f)
    (fun n g => fiberIntegral_upperUnipotent_mul F h μ f n g)

/-- Representative evaluation of the radical average. -/
theorem radicalAverage_mk :
    letI := F.canonicalTopologicalData.topology
    ∀ [BorelSpace F.Carrier]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)) [μ.IsAddHaarMeasure]
      (f : BlockQuotient h F.Carrier → ℂ) (g : GeneralLinear (t + 1) F.Carrier),
      radicalAverage F h μ f (Quotient.mk _ g) = ∫ x, f (fiberPoint h F.Carrier x g) ∂μ := by
  let := F.canonicalTopologicalData.topology
  intro _ μ _ f g
  rfl

/-- Right translation on `N \ GL_(t+1)` corresponds to right translation of the function on
`H \ GL_(t+1)`. -/
theorem radicalAverage_rightTranslate :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    ∀ [BorelSpace F.Carrier]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)) [μ.IsAddHaarMeasure]
      (f : BlockQuotient h F.Carrier → ℂ) (g : GeneralLinear (t + 1) F.Carrier)
      (q : LeftUnipotentQuotient t F.Carrier),
      radicalAverage F h μ f (rightTranslate _ g q) =
        radicalAverage F h μ (fun r => f (rightTranslate _ g r)) q := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  intro _ μ _ f g q
  induction q using Quotient.inductionOn with
  | h x =>
    rw [rightTranslate_mk, radicalAverage_mk, radicalAverage_mk]
    exact fiberIntegral_mul F h μ f x g

end Average

/-! ### Determinant slices -/

/-- The determinant slice of `H \ GL_(t+1)`: the preimage under `projection` of the published
slice `N \ G^k = {ord(det g) = k}`. -/
def determinantSlice (k : ℤ) : Set (BlockQuotient h F.Carrier) :=
  projection h F.Carrier ⁻¹' RankinSelberg.determinantSlice F.canonicalTopologicalData t k

theorem mem_determinantSlice {k : ℤ} {q : BlockQuotient h F.Carrier} :
    q ∈ determinantSlice F h k ↔
      projection h F.Carrier q ∈ RankinSelberg.determinantSlice F.canonicalTopologicalData t k :=
  Iff.rfl

/-- Representative condition `ord(det g) = k`, for the published normalized order. -/
theorem mk_mem_determinantSlice {k : ℤ} {g : GeneralLinear (t + 1) F.Carrier} :
    (Quotient.mk _ g : BlockQuotient h F.Carrier) ∈ determinantSlice F h k ↔
      F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) = k :=
  Iff.rfl

theorem isClopen_determinantSlice (k : ℤ) :
    letI := F.canonicalTopologicalData.topology
    IsClopen (determinantSlice F h k) := by
  let := F.canonicalTopologicalData.topology
  exact (RankinSelberg.isClopen_determinantSlice F.canonicalTopologicalData t k).preimage
    (continuous_projection F h)

/-- Every slice is measurable for any Borel structure on the intermediate quotient. -/
theorem measurableSet_determinantSlice (k : ℤ) :
    letI := F.canonicalTopologicalData.topology
    ∀ [MeasurableSpace (BlockQuotient h F.Carrier)] [BorelSpace (BlockQuotient h F.Carrier)],
      MeasurableSet (determinantSlice F h k) := by
  let := F.canonicalTopologicalData.topology
  intro _ _
  exact (isClopen_determinantSlice F h k).isOpen.measurableSet

/-- The determinant order of `[u(x) g]_N` is that of `[g]_N`. -/
@[simp]
theorem determinantOrder_projection_fiberPoint (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    determinantOrder F.canonicalTopologicalData t (projection h F.Carrier (fiberPoint h F.Carrier x g)) =
      determinantOrder F.canonicalTopologicalData t (Quotient.mk _ g) := by
  rw [projection_fiberPoint]

/-- `[u(x) g]_H` lies in the slice of order `k` exactly when `[g]_N` does. -/
theorem fiberPoint_mem_determinantSlice_iff (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) (k : ℤ) :
    fiberPoint h F.Carrier x g ∈ determinantSlice F h k ↔
      (Quotient.mk _ g : LeftUnipotentQuotient t F.Carrier) ∈
        RankinSelberg.determinantSlice F.canonicalTopologicalData t k := by
  rw [mem_determinantSlice, projection_fiberPoint]

theorem pairwise_disjoint_determinantSlice :
    Pairwise (Function.onFun Disjoint (determinantSlice F h)) :=
  fun _ _ hkl => (RankinSelberg.disjoint_determinantSlice F.canonicalTopologicalData t hkl).preimage
    (projection h F.Carrier)

@[simp]
theorem iUnion_determinantSlice : ⋃ k, determinantSlice F h k = Set.univ := by
  simp only [determinantSlice, ← Set.preimage_iUnion, RankinSelberg.iUnion_determinantSlice,
    Set.preimage_univ]

end Padic

end Langlands.RankinSelberg.TwoBlockUnipotentQuotient
