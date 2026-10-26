import Langlands.Representation.Parabolic.OppositeJacquetFiniteGenerationStatement
import Langlands.Representation.Parabolic.QuotientCompactProof
import Langlands.Representation.Induction.CompactQuotientProof
import Langlands.Group.GL.ReverseBlocks
import Mathlib.RepresentationTheory.Subrepresentation

/-! Finite generation of the actual normalized opposite Jacquet module. -/

noncomputable section

namespace Langlands.Parabolic

universe uF uV

namespace OppositeJacquetFiniteGeneration

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- The opposite coinvariant map, with the bundled opposite Jacquet module as target. -/
def mk (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)) :
    A →ₗ[ℂ] CuspidalJacquetMultiplicity.oppositeJacquet T B A :=
  Jacquet.mk A.ρ (B.oppositeUnipotentSubgroup F.Carrier)

theorem mk_surjective (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)) :
    Function.Surjective (mk T B A) :=
  Jacquet.mk_surjective _ _

/-- The coinvariant map ignores the action of the opposite unipotent radical. -/
theorem mk_apply_of_mem (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    {g : GeneralLinear n F.Carrier} (hg : g ∈ B.oppositeUnipotentSubgroup F.Carrier) (v : A) :
    mk T B A (A.ρ g v) = mk T B A v :=
  Jacquet.mk_apply_subgroup A.ρ _ ⟨g, hg⟩ v

/-- A Levi element acts on a class by a unit scalar times the class of its matrix action. -/
theorem exists_unit_smul_mk (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (m : B.Levi F.Carrier) (v : A) :
    ∃ c : ℂˣ, (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ m (mk T B A v) =
      (c : ℂ) • mk T B A (A.ρ (B.leviEmbedding F.Carrier m) v) :=
  ⟨Jacquet.inverseHalfCharacter
      ((T.leviModulus B).comp (B.leviEquiv F.Carrier).symm.toMonoidHom)⁻¹
      (B.leviEquiv F.Carrier m), rfl⟩

/-- Subrepresentations of the opposite Jacquet module are stable under the
matrix action of the Levi on representatives. -/
theorem mk_levi_mem (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (S : Subrepresentation (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ)
    (m : B.Levi F.Carrier) {v : A} (hv : mk T B A v ∈ S) :
    mk T B A (A.ρ (B.leviEmbedding F.Carrier m) v) ∈ S := by
  obtain ⟨c, hc⟩ := exists_unit_smul_mk T B A m v
  have h : mk T B A (A.ρ (B.leviEmbedding F.Carrier m) v) =
      ((c⁻¹ : ℂˣ) : ℂ) • (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ m
        (mk T B A v) := by
    rw [hc, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  rw [h]
  exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule m hv)

/-- Subrepresentations of the opposite Jacquet module are stable under the
action of the opposite parabolic on representatives. -/
theorem mk_oppositeParabolic_mem (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (S : Subrepresentation (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ)
    {q : GeneralLinear n F.Carrier} (hq : q ∈ B.oppositeParabolic F.Carrier) {v : A}
    (hv : mk T B A v ∈ S) : mk T B A (A.ρ q v) ∈ S := by
  let q' : B.oppositeParabolic F.Carrier := ⟨q, hq⟩
  let u := B.oppositeUnipotentPart F.Carrier q'
  let m := B.oppositeLeviProjection F.Carrier q'
  have hfac : u.val.val * B.leviEmbedding F.Carrier m = q :=
    congrArg Subtype.val ((B.oppositeDecomposition F.Carrier).left_inv q')
  have hu : u.val.val ∈ B.oppositeUnipotentSubgroup F.Carrier :=
    Subgroup.mem_map_of_mem _ u.property
  rw [← hfac, map_mul, Module.End.mul_apply, mk_apply_of_mem T B A hu]
  exact mk_levi_mem T B A S m hv

variable [TopologicalSpace (GeneralLinear n F.Carrier)]
  [IsTopologicalGroup (GeneralLinear n F.Carrier)]

/-- Compactness of the upper quotient for the reversed shape gives a finite
cover of the group by double cosets `P̄ * i * K` of the original opposite parabolic. -/
theorem exists_finset_oppositeDoubleCoset_cover
    [CompactSpace (Induction.LeftQuotient (B.reverse.parabolic F.Carrier))]
    (K : OpenSubgroup (GeneralLinear n F.Carrier)) :
    ∃ t : Finset (GeneralLinear n F.Carrier), ∀ x : GeneralLinear n F.Carrier,
      ∃ i ∈ t, ∃ q ∈ B.oppositeParabolic F.Carrier, ∃ k ∈ K, x = q * i * k := by
  classical
  let w := B.reverseMatrix F.Carrier
  let c := MulAut.conj w
  have hc : Continuous c.toMonoidHom := by
    have h : (c.toMonoidHom : GeneralLinear n F.Carrier → GeneralLinear n F.Carrier) =
        fun g => w * g * w⁻¹ := by
      funext g
      rfl
    rw [h]
    exact (continuous_const.mul continuous_id).mul continuous_const
  let K' : OpenSubgroup (GeneralLinear n F.Carrier) := K.comap c.toMonoidHom hc
  obtain ⟨t, ht⟩ :=
    Induction.exists_finset_doubleCoset_cover (B.reverse.parabolic F.Carrier) K'
  refine ⟨t.image c, fun x => ?_⟩
  obtain ⟨i, hi, q, hq, k, hk, hx⟩ := ht (c.symm x)
  refine ⟨c i, Finset.mem_image_of_mem _ hi, c q,
    (B.reverseMatrix_conj_mem_oppositeParabolic_iff F.Carrier q).mpr hq, c k,
    OpenSubgroup.mem_comap.mp hk, ?_⟩
  rw [← map_mul, ← map_mul, ← hx, MulEquiv.apply_symm_apply]

/-- Compactness of the parabolic quotient turns finitely many smooth ambient
generators into finitely many generators of the normalized opposite Jacquet module. -/
theorem finite_of_compactQuotient
    [CompactSpace (Induction.LeftQuotient (B.reverse.parabolic F.Carrier))]
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)) (hA : IsSmooth A.ρ)
    (hfg : Module.Finite (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) A.ρ.asModule) :
    Module.Finite (MonoidAlgebra ℂ (B.Levi F.Carrier))
      (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ.asModule := by
  classical
  obtain ⟨s, hs⟩ := hfg.fg_top
  have hcover : ∀ v : A, ∃ t : Finset (GeneralLinear n F.Carrier),
      ∀ S : Subrepresentation (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ,
        (∀ i ∈ t, mk T B A (A.ρ i v) ∈ S) →
        ∀ g, mk T B A (A.ρ g v) ∈ S := by
    intro v
    obtain ⟨K, hK⟩ := hA v
    obtain ⟨t, ht⟩ := exists_finset_oppositeDoubleCoset_cover B K
    refine ⟨t, ?_⟩
    intro S hS g
    obtain ⟨i, hi, q, hq, k, hk, rfl⟩ := ht g
    have hk' : A.ρ k v = v := hK ⟨k, hk⟩
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hk']
    exact mk_oppositeParabolic_mem T B A S hq (hS i hi)
  choose t ht using hcover
  let y : Finset (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ.asModule :=
    s.biUnion fun v => (t v).image fun i => mk T B A (A.ρ i v)
  let N := Submodule.span (MonoidAlgebra ℂ (B.Levi F.Carrier))
    (y : Set (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ.asModule)
  let S := Subrepresentation.ofSubmodule' N
  have hmem : ∀ v ∈ s, ∀ g, mk T B A (A.ρ g v) ∈ S := by
    intro v hv
    apply ht v S
    intro i hi
    change mk T B A (A.ρ i v) ∈ N
    apply Submodule.subset_span
    exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image_of_mem _ hi⟩
  let C : Subrepresentation A.ρ :=
    { toSubmodule := ⨅ g, S.toSubmodule.comap ((mk T B A).comp (A.ρ g))
      apply_mem_toSubmodule := by
        intro g v hv
        rw [Submodule.mem_iInf] at hv ⊢
        intro a
        change mk T B A (A.ρ a (A.ρ g v)) ∈ S
        rw [← Module.End.mul_apply, ← map_mul]
        exact hv (a * g) }
  have hle : Submodule.span (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
      (s : Set A.ρ.asModule) ≤ C.asSubmodule := by
    apply Submodule.span_le.mpr
    intro v hv
    change (show A from v) ∈ C.toSubmodule
    exact (Submodule.mem_iInf _).mpr (hmem v hv)
  have hN : N = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    obtain ⟨v, rfl⟩ := mk_surjective T B A x
    have hv : v ∈ C.asSubmodule := hle (hs.symm ▸ Submodule.mem_top)
    change v ∈ C.toSubmodule at hv
    have hv1 := (Submodule.mem_iInf _).mp hv 1
    change mk T B A (A.ρ 1 v) ∈ S at hv1
    change mk T B A v ∈ S
    simpa only [map_one, Module.End.one_apply] using hv1
  exact ⟨⟨y, hN⟩⟩

end OppositeJacquetFiniteGeneration

/-- Smooth finite generation is preserved by every actual normalized opposite
GL Jacquet functor, including rank zero and arbitrary carrier universe. -/
theorem oppositeJacquetFiniteGeneration :
    OppositeJacquetFiniteGenerationStatement.{uF, uV} := by
  intro p hp F T n B
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro A hA hfg
  let : CompactSpace (Induction.LeftQuotient (B.reverse.parabolic F.Carrier)) :=
    parabolicQuotientCompact F T B.reverse
  exact OppositeJacquetFiniteGeneration.finite_of_compactQuotient T B A hA hfg

end Langlands.Parabolic
