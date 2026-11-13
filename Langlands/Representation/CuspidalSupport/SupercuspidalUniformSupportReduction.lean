import Langlands.Representation.CuspidalSupport.RationalNormKernelSupportGeometry
import Langlands.Representation.CuspidalSupport.UniformAdmissibilityStatements
import Langlands.Representation.CuspidalSupport.RationalNormKernelFiniteRestrictionProof
import Langlands.Representation.Exponents.RepresentedCompactRestrictionSupercuspidal
import Langlands.Representation.CompactCoefficient.TotalCompactness
import Langlands.Representation.Compact.CharZeroAverage
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Plancherel.RationalCharacterTopology

/-! # Renard VI.2.4, conditional on the Chapter V structure -/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.CompactCoefficientClass

universe uG uV

section Generic

variable {H : Type uG} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- In a topological group with one compact open subgroup, every open subgroup
contains a compact open subgroup. -/
theorem exists_isCompact_openSubgroup_le (L₀ : OpenSubgroup H)
    (hL₀ : IsCompact (L₀ : Set H)) (U : OpenSubgroup H) :
    ∃ L : OpenSubgroup H, IsCompact (L : Set H) ∧ L ≤ U :=
  ⟨U ⊓ L₀, hL₀.of_isClosed_subset (U ⊓ L₀).isClosed (fun _ hx => hx.2), inf_le_left⟩

/-- A smooth representation with compact smooth-dual coefficients that is spanned by
irreducible subrepresentations has its level-`K` inverse coefficients in every set
that contains the level-`K` inverse coefficients of all compact irreducible
representations. The `K`-fixed vector is averaged component by component. -/
theorem support_subset_of_iSup_eq_top
    (hcof : ∀ U : OpenSubgroup H, ∃ L : OpenSubgroup H, IsCompact (L : Set H) ∧ L ≤ U)
    (A : SmoothRep.{0, uG, uV} ℂ H)
    (hA : HasCompactSmoothDualCoefficients A.representation)
    {I : Type*} (W : I → Subrepresentation A.representation)
    (hW : ∀ i, Representation.IsIrreducible (W i).toRepresentation)
    (hspan : (⨆ i, (W i).toSubmodule) = ⊤)
    (K : OpenSubgroup H) (hK : IsCompact (K : Set H)) {C : Set H}
    (hC : ∀ (D : IrreducibleCompactCoefficientRep.{uG, uV} H)
      (v : D.obj), v ∈ fixedVectors D.obj.representation K.toSubgroup →
      ∀ ℓ : Module.Dual ℂ D.obj,
        (∀ k ∈ K.toSubgroup, ∀ w, ℓ (D.obj.representation k w) = ℓ w) →
        Function.support (fun g : H => ℓ (D.obj.representation g⁻¹ v)) ⊆ C)
    (w : A) (hw : w ∈ fixedVectors A.representation K.toSubgroup)
    (ℓ : Module.Dual ℂ A)
    (hℓ : ∀ k ∈ K.toSubgroup, ∀ y, ℓ (A.representation k y) = ℓ y) :
    Function.support (fun g : H => ℓ (A.representation g⁻¹ w)) ⊆ C := by
  classical
  let avg := Compact.CharZero.averageMap A.representation A.isSmooth K hK
  have key : ∀ x : A,
      Function.support (fun g : H => ℓ (A.representation g⁻¹ (avg x))) ⊆ C := by
    intro x
    have hx : x ∈ ⨆ i, (W i).toSubmodule := by
      rw [hspan]
      exact Submodule.mem_top
    refine Submodule.iSup_induction (fun i => (W i).toSubmodule)
      (motive := fun x =>
        Function.support (fun g : H => ℓ (A.representation g⁻¹ (avg x))) ⊆ C)
      hx ?_ ?_ ?_
    · intro i x hx
      let S := SmoothRep.subrepresentation A (W i)
      let D : IrreducibleCompactCoefficientRep.{uG, uV} H :=
        ⟨S, hW i, hasCompactSmoothDualCoefficients_subrepresentation hcof A hA (W i)⟩
      let j := SmoothRep.hom (SmoothRep.subtype A (W i))
      let y : S := ⟨x, hx⟩
      have hcomm := Compact.CharZero.averageMap_commute S.representation A.representation
        S.isSmooth A.isSmooth K hK j
      have hax : avg x = j (Compact.CharZero.averageMap S.representation S.isSmooth K hK y) :=
        (LinearMap.congr_fun hcomm y).symm
      rw [hax]
      have hfix := Compact.CharZero.averageMap_mem_fixedVectors S.representation S.isSmooth
        K hK y
      have hinv : ∀ k ∈ K.toSubgroup, ∀ z : S,
          (ℓ ∘ₗ j.toLinearMap) (S.representation k z) = (ℓ ∘ₗ j.toLinearMap) z :=
        fun k hk z => hℓ k hk (j z)
      exact hC D _ hfix (ℓ ∘ₗ j.toLinearMap) hinv
    · intro g hg
      simp at hg
    · intro x y hx hy g hg
      simp only [map_add] at hg
      exact (Set.union_subset hx hy) (Function.support_add _ _ hg)
  have := key w
  rwa [show avg w = w from Compact.CharZero.averageMap_id _ _ K hK w hw] at this

section Levels

variable {G' : Type uG} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']

/-- Every compact open subgroup `K` and element `r` give a compact open subgroup
`L ≤ K` with `r L r⁻¹ ⊆ K`, namely `K ∩ r⁻¹ K r`. -/
theorem exists_conj_level (K : OpenSubgroup G') (hK : IsCompact (K : Set G')) (r : G') :
    ∃ L : OpenSubgroup G', IsCompact (L : Set G') ∧ L ≤ K ∧
      ∀ x ∈ L, r * x * r⁻¹ ∈ K := by
  let f : G' →* G' := (MulAut.conj r).toMonoidHom
  have hf : Continuous f := (continuous_const.mul continuous_id).mul continuous_const
  exact ⟨K ⊓ K.comap f hf,
    hK.of_isClosed_subset (K ⊓ K.comap f hf).isClosed (fun _ hx => hx.1), inf_le_left,
    fun x hx => hx.2⟩

omit [IsTopologicalGroup G'] in
/-- The pullback of a compact open subgroup contained in a subgroup `H` to `H` is
compact. -/
theorem isCompact_comap_subtype (H : Subgroup G') (L : OpenSubgroup G')
    (hL : IsCompact (L : Set G')) (hLH : L.toSubgroup ≤ H) :
    IsCompact ((L.comap H.subtype continuous_subtype_val : OpenSubgroup H) : Set H) := by
  rw [Subtype.isCompact_iff]
  convert hL using 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hLH hx⟩, hx, rfl⟩

end Levels

end Generic

end Langlands.CompactCoefficientClass

namespace Langlands.CuspidalSupport

universe u v

open GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily

/-- Renard VI.2.4 follows from the four Chapter V structural statements used by the
Library's norm-kernel support and compact-restriction theorems: the parabolic-dynamic
statement, the standard-cocharacter statement, the relative root system and the
joint special-compact basis existence statement. -/
def SupercuspidalUniformCoefficientSupportReductionStatement : Prop :=
  GroupScheme.ParabolicDynamicStatement.{u} → GroupScheme.StandardCocharacterStatement.{u} →
    GroupScheme.RelativeRootSystemStatement.{u} →
      BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{u} →
        SupercuspidalUniformCoefficientSupportStatement.{u, v}

/-- Proof of `SupercuspidalUniformCoefficientSupportReductionStatement`. -/
theorem supercuspidalUniformCoefficientSupportReduction :
    SupercuspidalUniformCoefficientSupportReductionStatement.{u, v} := by
  classical
  intro hPD hStandard hRoot hJoint k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := pointTopology
  intro _ _ K hK
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  let H := Plancherel.rationalCommonNormKernel G
  let Z := Subgroup.center (rationalPoints G)
  have : (H ⊔ Z).FiniteIndex := rationalCommonNormKernel_sup_center_finiteIndex k G hG
  have hKH : K.toSubgroup ≤ H :=
    Plancherel.compactSubgroup_le_rationalCommonNormKernel G K.toSubgroup hK
  obtain ⟨T, i, ν, hi, hν⟩ := exists_maximalSplitTorus_genericCocharacter hG
  have := hi.isSplitSubtorus.mono
  have hRoots := hRoot k G hG T i hi
  have hU := isClosed_unipotent_of_isNonarchimedeanLocalField i ν
  have hsupp := rationalNormKernelUniformSupport_of_joint.{u, v} hJoint k G hG T i hi ν hν
    hStandard hRoots hU
  let Q := rationalPoints G ⧸ (H ⊔ Z)
  let rep : Q → rationalPoints G := fun q => q.out
  have hlev : ∀ q : Q, ∃ L : OpenSubgroup (rationalPoints G),
      IsCompact (L : Set (rationalPoints G)) ∧ L ≤ K ∧
        ∀ x ∈ L, rep q * x * (rep q)⁻¹ ∈ K :=
    fun q => CompactCoefficientClass.exists_conj_level K hK (rep q)
  choose L hLc hLK hLconj using hlev
  let LH : Q → OpenSubgroup H := fun q => (L q).comap H.subtype continuous_subtype_val
  have hLHc : ∀ q, IsCompact ((LH q : Set H)) := fun q =>
    CompactCoefficientClass.isCompact_comap_subtype H (L q) (hLc q)
      ((OpenSubgroup.toSubgroup_le.2 (hLK q)).trans hKH)
  have hCex : ∀ q, CompactCoefficientClass.HasUniformFixedLevelCoefficientSupport.{u, v}
      (LH q).toSubgroup := fun q => hsupp (LH q) (hLHc q)
  choose C hCc hC using hCex
  let S : Set (rationalPoints G) :=
    ⋃ q, (fun x : H => rep q * (x : rationalPoints G)⁻¹) '' C q
  have hS : IsCompact S := isCompact_iUnion fun q =>
    (hCc q).image (continuous_const.mul continuous_subtype_val.inv)
  refine ⟨S * (K : Set (rationalPoints G)) * (Z : Set (rationalPoints G)),
    (K.isOpen.mul_left).mul_right, ⟨S * (K : Set (rationalPoints G)), hS.mul hK, subset_rfl⟩, ?_⟩
  intro A hAirr hsc w hw ℓ hℓ g hg
  -- decompose `g = rep q * a * z` with `a ∈ ⁰G` and `z` central
  obtain ⟨⟨y, hy⟩, hgy⟩ := QuotientGroup.mk_out_eq_mul (H ⊔ Z) g
  have hy' : y⁻¹ ∈ ((H ⊔ Z : Subgroup (rationalPoints G)) : Set (rationalPoints G)) :=
    (H ⊔ Z).inv_mem hy
  rw [Subgroup.mul_normal H Z] at hy'
  obtain ⟨a, ha, z, hz, haz⟩ := hy'
  have haz' : a * z = y⁻¹ := haz
  let q : Q := (g : Q)
  have hg_eq : g = rep q * a * z := by
    rw [mul_assoc, haz']
    change g = Quotient.out (g : Q) * y⁻¹
    rw [hgy]
    simp
  -- the representation-theoretic data on `⁰G`
  let AH := SmoothRep.restrictSubgroup H A
  have hA : HasCompactSmoothDualCoefficients AH.representation :=
    RepresentedParabolic.compactRestriction_of_isSupercuspidal hPD hStandard hRoot hJoint hG
      A hsc
  obtain ⟨-, -, m, W, hW, hspan⟩ := rationalNormKernelFiniteRestriction.{u, v} k G hG A hAirr
  let KH : OpenSubgroup H := K.comap H.subtype continuous_subtype_val
  have hKHc : IsCompact (KH : Set H) :=
    CompactCoefficientClass.isCompact_comap_subtype H K hK hKH
  have hcof := CompactCoefficientClass.exists_isCompact_openSubgroup_le KH hKHc
  let w' : A := A.representation z w
  have hzc : ∀ x : rationalPoints G, x * z = z * x := fun x => Subgroup.mem_center_iff.1 hz x
  have hw' : w' ∈ fixedVectors AH.representation (LH q).toSubgroup := by
    intro x
    have hxK : (x : H).val ∈ K := hLK q x.2
    change A.representation (x : H).val (A.representation z w) = A.representation z w
    rw [← Module.End.mul_apply, ← map_mul, hzc, map_mul, Module.End.mul_apply]
    exact congrArg _ (hw ⟨_, hxK⟩)
  let ℓ' : Module.Dual ℂ A := ℓ ∘ₗ A.representation (rep q)
  have hℓ' : ∀ x ∈ (LH q).toSubgroup, ∀ y : A,
      ℓ' (AH.representation x y) = ℓ' y := by
    intro x hx y
    have hc := hℓ _ (hLconj q _ hx) (A.representation (rep q) y)
    change ℓ (A.representation (rep q) (A.representation x.val y)) =
      ℓ (A.representation (rep q) y)
    rw [← hc, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel_right]
    rfl
  have hsub := CompactCoefficientClass.support_subset_of_iSup_eq_top hcof AH hA W hW hspan
    (LH q) (hLHc q) (hC q) w' hw' ℓ' hℓ'
  let a' : H := ⟨a, ha⟩
  have hmem : a'⁻¹ ∈ C q := by
    apply hsub
    change ℓ (A.representation (rep q) (A.representation (a'⁻¹)⁻¹.val
      (A.representation z w))) ≠ 0
    rw [inv_inv]
    change ℓ (A.representation (rep q) (A.representation a (A.representation z w))) ≠ 0
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ← hg_eq]
    exact hg
  have hS' : rep q * a ∈ S := by
    refine Set.mem_iUnion.2 ⟨q, a'⁻¹, hmem, ?_⟩
    simp [a']
  rw [hg_eq]
  exact Set.mul_mem_mul (by simpa using Set.mul_mem_mul hS' K.one_mem) hz
