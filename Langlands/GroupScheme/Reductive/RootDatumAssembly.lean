import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.GroupScheme.Reductive.RootDatum
import Langlands.GroupScheme.Rational.RootReflectionAssembly
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.Rational.RelativeWeylRootKernel
import Langlands.GroupScheme.Absolute.RegularPerturbation
import Mathlib.LinearAlgebra.RootSystem.Reduced

/-! # Assembling the root datum of a split maximal torus from integral reflection data -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.LinearAlgebra.RationalSpan

namespace RootPairing

variable {J M N : Type*} [Finite J] [AddCommGroup M] [AddCommGroup N]

/-- A finite root pairing over `ℤ` in which no root is twice a root is reduced. -/
theorem isReduced_of_two_smul_notMem (P : RootPairing J ℤ M N)
    (h : ∀ j, (2 : ℤ) • P.root j ∉ Set.range P.root) : P.IsReduced := by
  have : Module.IsReflexive ℤ M := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive ℤ N := .of_isPerfPair P.toLinearMap.flip
  have hno : ∀ x y, P.root x ≠ (2 : ℤ) • P.root y := fun x y hxy => h y ⟨x, hxy⟩
  have hno' : ∀ x y, P.root x ≠ (-2 : ℤ) • P.root y := by
    intro x y hxy
    apply hno x (P.reflectionPerm y y)
    rw [hxy, root_reflectionPerm, reflection_apply_self, smul_neg, neg_smul]
  refine ⟨fun i j hlin => ?_⟩
  have hcw := (P.coxeterWeight_eq_four_iff_not_linearIndependent).mpr hlin
  unfold coxeterWeight at hcw
  obtain ⟨a, ha⟩ : ∃ a, P.pairing i j = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, P.pairing j i = b := ⟨_, rfl⟩
  rw [ha, hb] at hcw
  have h₁ : a ≤ 4 := Int.le_of_dvd (by norm_num) ⟨b, hcw.symm⟩
  have h₂ : -4 ≤ a := by
    have : -a ≤ 4 := Int.le_of_dvd (by norm_num) ⟨-b, by rw [← hcw]; ring⟩
    omega
  interval_cases a <;> try omega
  · obtain rfl : b = -1 := by omega
    exact absurd ((P.pairing_neg_one_neg_four_iff j i).mp ⟨hb, ha⟩) (hno' i j)
  · obtain rfl : b = -2 := by omega
    exact Or.inr ((P.pairing_neg_two_neg_two_iff i j).mp ⟨ha, hb⟩)
  · obtain rfl : b = -4 := by omega
    exact absurd ((P.pairing_neg_one_neg_four_iff i j).mp ⟨ha, hb⟩) (hno' j i)
  · obtain rfl : b = 4 := by omega
    exact absurd ((P.pairing_one_four_iff i j).mp ⟨ha, hb⟩) (hno j i)
  · obtain rfl : b = 2 := by omega
    exact Or.inl (by rw [(P.pairing_two_two_iff i j).mp ⟨ha, hb⟩])
  · obtain rfl : b = 1 := by omega
    exact absurd ((P.pairing_one_four_iff j i).mp ⟨hb, ha⟩) (hno i j)

end RootPairing

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

variable (i : T.toGrp ⟶ G) [IsAffineHom G.X.hom] [Mono i.hom.hom.left]

open RelativeRootSystem

/-- A normalizing point acting on characters by the reflection formula along an actual root
`γ` with cocharacter `c` sends each actual root vector to the root vector of its image. -/
theorem preReflection_rootVector_of_weylAction {γ : characterLattice T}
    (hγ : γ ∈ relativeRoots i) {n : normalizerPoints i} {c : cocharacterLattice T}
    (h : ∀ χ, weylAction i n χ = χ - latticePairing T χ c • γ) (δ : relativeRoots i) :
    Module.preReflection (rootVector i ⟨γ, hγ⟩) (corootFunctional i c) (rootVector i δ) =
      rootVector i ⟨weylAction i n δ.val, weylAction_mapsTo_relativeRoots i n δ.property⟩ := by
  apply Subtype.ext
  change toRat δ.val - corootFunctional i c (rootVector i δ) • toRat γ = _
  rw [corootFunctional_rootVector]
  change _ = toRat (weylAction i n δ.val)
  rw [h, map_sub, map_zsmul, Int.cast_smul_eq_zsmul]

/-- **Uniqueness of the coroot.** For a split torus with finitely many actual roots, whose roots
and restricted group characters span the rational character space, two normalizing points
acting by the reflection formula along the same actual root `γ`, with cocharacters `c₁`, `c₂`
pairing to two with `γ`, have `c₁ = c₂`. -/
theorem coroot_eq_of_weylAction (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite)
    (hspan : Submodule.span ℚ
      (toRat '' (relativeRoots i ∪ Set.range (torusCharacterRestrict i))) = ⊤)
    {γ : characterLattice T} (hγ : γ ∈ relativeRoots i) {n₁ n₂ : normalizerPoints i}
    {c₁ c₂ : cocharacterLattice T} (hc₁ : latticePairing T γ c₁ = 2)
    (hc₂ : latticePairing T γ c₂ = 2)
    (h₁ : ∀ χ, weylAction i n₁ χ = χ - latticePairing T χ c₁ • γ)
    (h₂ : ∀ χ, weylAction i n₂ χ = χ - latticePairing T χ c₂ • γ) : c₁ = c₂ := by
  have : Finite (relativeRoots i) := hfinite.to_subtype
  have hf : corootFunctional i c₁ = corootFunctional i c₂ := by
    refine Module.Dual.eq_of_preReflection_mapsTo (x := rootVector i ⟨γ, hγ⟩)
      (Set.finite_range (rootVector i)) (span_range_rootVector i) ?_ ?_ ?_ ?_
    · rw [corootFunctional_rootVector, hc₁]
      norm_num
    · rintro _ ⟨δ, rfl⟩
      exact ⟨_, (preReflection_rootVector_of_weylAction i hγ h₁ δ).symm⟩
    · rw [corootFunctional_rootVector, hc₂]
      norm_num
    · rintro _ ⟨δ, rfl⟩
      exact ⟨_, (preReflection_rootVector_of_weylAction i hγ h₂ δ).symm⟩
  have hroot : ∀ δ ∈ relativeRoots i, latticePairing T δ c₁ = latticePairing T δ c₂ := by
    intro δ hδ
    have h := LinearMap.congr_fun hf (rootVector i ⟨δ, hδ⟩)
    rw [corootFunctional_rootVector, corootFunctional_rootVector] at h
    exact_mod_cast h
  have hprod : ∀ χ, weylAction i (n₁ * n₂) χ =
      χ + (latticePairing T χ c₂ - latticePairing T χ c₁) • γ := by
    intro χ
    rw [map_mul, LinearEquiv.mul_apply, h₂, h₁]
    simp only [map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hc₁]
    module
  have hone : weylAction i (n₁ * n₂) = 1 := by
    refine hT.weylAction_eq_one_of_fixed_roots i hspan (n₁ * n₂) fun δ hδ => ?_
    rw [hprod, hroot δ hδ, sub_self, zero_smul, add_zero]
  have hpair : ∀ χ, latticePairing T χ c₁ = latticePairing T χ c₂ := by
    intro χ
    have h := hprod χ
    rw [hone] at h
    change χ = _ at h
    have h' : (latticePairing T χ c₂ - latticePairing T χ c₁) • γ = 0 := by
      have h'' := congrArg (· - χ) h
      simpa using h''.symm
    have h'' := congrArg (fun x => latticePairing T x c₁) h'
    simp only [map_zsmul, map_zero, LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul,
      hc₁] at h''
    linarith
  have := hT.isPerfPair_latticePairing
  exact (LinearMap.IsPerfPair.bijective_right (latticePairing T)).injective
    (LinearMap.ext hpair)

/-- The permutation of the actual roots induced by the Weyl action of a normalizing point. -/
def weylRootPerm (n : normalizerPoints i) : Equiv.Perm (relativeRoots i) where
  toFun α := ⟨weylAction i n α.val, weylAction_mapsTo_relativeRoots i n α.property⟩
  invFun α := ⟨weylAction i n⁻¹ α.val, weylAction_mapsTo_relativeRoots i n⁻¹ α.property⟩
  left_inv α := by
    apply Subtype.ext
    change weylAction i n⁻¹ (weylAction i n α.val) = α.val
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv α := by
    apply Subtype.ext
    change weylAction i n (weylAction i n⁻¹ α.val) = α.val
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl

@[simp]
theorem coe_weylRootPerm (n : normalizerPoints i) (α : relativeRoots i) :
    (weylRootPerm i n α : characterLattice T) = weylAction i n α.val :=
  rfl

namespace RelativeRootReflectionData

variable {i} (D : RelativeRootReflectionData i)

/-- The action of a reflection representative is an involution of the character lattice. -/
theorem weylAction_representative_involutive (α : relativeRoots i) (χ : characterLattice T) :
    weylAction i (D.representative α) (weylAction i (D.representative α) χ) = χ := by
  simp only [D.action, map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, D.pair_self]
  module

theorem weylAction_inv_representative (α : relativeRoots i) (χ : characterLattice T) :
    weylAction i (D.representative α)⁻¹ χ = weylAction i (D.representative α) χ := by
  apply (weylAction i (D.representative α)).injective
  rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    D.weylAction_representative_involutive]
  rfl

/-- The cocharacter `s_α^∨(β^∨) = β^∨ - ⟨α, β^∨⟩ α^∨` attached to two actual roots. -/
def reflectedCoroot (α β : relativeRoots i) : cocharacterLattice T :=
  D.coroot β - latticePairing T α.val (D.coroot β) • D.coroot α

/-- Conjugating the representative of `β` by the representative of `α` acts by the reflection
formula along `s_α(β)` with the cocharacter `s_α^∨(β^∨)`. -/
theorem weylAction_conj (α β : relativeRoots i) (χ : characterLattice T) :
    weylAction i (D.representative α * D.representative β * (D.representative α)⁻¹) χ =
      χ - latticePairing T χ (D.reflectedCoroot α β) •
        weylAction i (D.representative α) β.val := by
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    D.weylAction_inv_representative, D.action β, map_sub, map_zsmul,
    D.weylAction_representative_involutive]
  congr 2
  rw [D.action α χ, reflectedCoroot]
  simp only [map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem pairing_reflectedCoroot (α β : relativeRoots i) :
    latticePairing T (weylAction i (D.representative α) β.val) (D.reflectedCoroot α β) = 2 := by
  rw [D.action α, reflectedCoroot]
  simp only [map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    D.pair_self]
  ring

/-- **Stability of the coroots.** The coroot of `s_α(β)` is `s_α^∨(β^∨)`. -/
theorem coroot_weylRootPerm (hT : IsSplitTorus T.toGrp) (hfinite : (relativeRoots i).Finite)
    (hspan : Submodule.span ℚ
      (toRat '' (relativeRoots i ∪ Set.range (torusCharacterRestrict i))) = ⊤)
    (α β : relativeRoots i) :
    D.coroot (weylRootPerm i (D.representative α) β) = D.reflectedCoroot α β := by
  have hγ := weylAction_mapsTo_relativeRoots i (D.representative α) β.property
  have h₁ : ∀ χ, weylAction i (D.representative (weylRootPerm i (D.representative α) β)) χ =
      χ - latticePairing T χ (D.coroot (weylRootPerm i (D.representative α) β)) •
        weylAction i (D.representative α) β.val :=
    D.action (weylRootPerm i (D.representative α) β)
  have hc₁ : latticePairing T (weylAction i (D.representative α) β.val)
      (D.coroot (weylRootPerm i (D.representative α) β)) = 2 :=
    D.pair_self (weylRootPerm i (D.representative α) β)
  exact coroot_eq_of_weylAction i hT hfinite hspan hγ hc₁ (D.pairing_reflectedCoroot α β) h₁
    (D.weylAction_conj α β)

/-- The coroots of reflection data are injective on the actual roots. -/
theorem coroot_injective (hT : IsSplitTorus T.toGrp) (hfinite : (relativeRoots i).Finite) :
    Function.Injective D.coroot :=
  fun _ _ h => D.corootFunctional_injective hT hfinite (congrArg (corootFunctional i) h)

/-- The root datum on the actual character and cocharacter lattices built from integral
reflection data: index type the actual roots, roots the roots themselves, coroots the
reflection cocharacters, pairing `latticePairing T`, and reflection permutations the Weyl
actions of the representatives. -/
def rootDatum (hT : IsSplitTorus T.toGrp) (hfinite : (relativeRoots i).Finite)
    (hspan : Submodule.span ℚ
      (toRat '' (relativeRoots i ∪ Set.range (torusCharacterRestrict i))) = ⊤) :
    RootDatum (relativeRoots i) (characterLattice T) (cocharacterLattice T) where
  toLinearMap := latticePairing T
  isPerfPair_toLinearMap := hT.isPerfPair_latticePairing
  root := Function.Embedding.subtype _
  coroot := ⟨D.coroot, D.coroot_injective hT hfinite⟩
  root_coroot_two α := D.pair_self α
  reflectionPerm α := weylRootPerm i (D.representative α)
  reflectionPerm_root α β := (D.action α β.val).symm
  reflectionPerm_coroot α β := (D.coroot_weylRootPerm hT hfinite hspan α β).symm

variable (hT : IsSplitTorus T.toGrp) (hfinite : (relativeRoots i).Finite)
  (hspan : Submodule.span ℚ
    (toRat '' (relativeRoots i ∪ Set.range (torusCharacterRestrict i))) = ⊤)

@[simp]
theorem rootDatum_toLinearMap : (D.rootDatum hT hfinite hspan).toLinearMap = latticePairing T :=
  rfl

@[simp]
theorem rootDatum_root (α : relativeRoots i) : (D.rootDatum hT hfinite hspan).root α = α.val :=
  rfl

@[simp]
theorem rootDatum_coroot (α : relativeRoots i) :
    (D.rootDatum hT hfinite hspan).coroot α = D.coroot α :=
  rfl

theorem rootDatum_reflection (α : relativeRoots i) :
    (D.rootDatum hT hfinite hspan).reflection α = weylAction i (D.representative α) := by
  apply LinearEquiv.ext
  intro χ
  rw [D.action, RootPairing.reflection_apply]
  rfl

/-- The assembled root datum is the root datum of `i`. -/
theorem isRootDatumOf_rootDatum : IsRootDatumOf i (D.rootDatum hT hfinite hspan) := by
  refine ⟨rfl, ?_, fun α => ⟨(D.representative α).val, normalizingAut i (D.representative α),
    isNormalizingPoint_normalizingAut i _, ?_⟩⟩
  · change Set.range (Subtype.val : relativeRoots i → characterLattice T) = roots i
    rw [Subtype.range_coe]
    rfl
  · rw [D.rootDatum_reflection]
    rfl

/-- If no actual root is twice an actual root, the assembled root datum is reduced. -/
theorem isReduced_rootDatum
    (hred : ∀ α ∈ relativeRoots i, (2 : ℤ) • α ∉ relativeRoots i) :
    (D.rootDatum hT hfinite hspan).IsReduced := by
  have : Finite (relativeRoots i) := hfinite.to_subtype
  refine RootPairing.isReduced_of_two_smul_notMem _ fun α ⟨β, hβ⟩ => ?_
  apply hred α.val α.property
  have hβ' : β.val = (2 : ℤ) • α.val := hβ
  rw [← hβ']
  exact β.property

/-- If any two linearly dependent actual roots agree up to sign, the assembled root datum is
reduced. -/
theorem isReduced_rootDatum_of_eq_or_eq_neg
    (hred : ∀ α ∈ relativeRoots i, ∀ β ∈ relativeRoots i,
      ¬ LinearIndependent ℤ ![α, β] → α = β ∨ α = -β) :
    (D.rootDatum hT hfinite hspan).IsReduced :=
  ⟨fun α β h => hred α.val α.property β.val β.property h⟩

end RelativeRootReflectionData

/-- **Conditional existence of the root datum.** For a split maximal torus of a connected
reductive group, integral reflection data, the joint spanning of roots and restricted group
characters, and the absence of roots twice a root give a finite reduced root datum of `i`. -/
theorem exists_rootDatum_of_reflectionData (hG : IsConnectedReductive G)
    (hT : IsSplitTorus T.toGrp) (D : RelativeRootReflectionData i)
    (hspan : Submodule.span ℚ
      (toRat '' (relativeRoots i ∪ Set.range (torusCharacterRestrict i))) = ⊤)
    (hred : ∀ α ∈ roots i, (2 : ℤ) • α ∉ roots i) :
    ∃ (J : Type u) (_ : Finite J)
      (P : RootDatum J (characterLattice T) (cocharacterLattice T)),
      IsRootDatumOf i P ∧ P.IsReduced := by
  have := hG.smooth
  have hfinite := hT.finite_relativeRoots i
  exact ⟨relativeRoots i, hfinite.to_subtype, D.rootDatum hT hfinite hspan,
    D.isRootDatumOf_rootDatum hT hfinite hspan, D.isReduced_rootDatum hT hfinite hspan hred⟩

/-- **Conditional existence of the root datum**, with reducedness supplied in the form of
`RootPairing.IsReduced`: linearly dependent actual roots agree up to sign. -/
theorem exists_rootDatum_of_reflectionData_of_eq_or_eq_neg (hG : IsConnectedReductive G)
    (hT : IsSplitTorus T.toGrp) (D : RelativeRootReflectionData i)
    (hspan : Submodule.span ℚ
      (toRat '' (relativeRoots i ∪ Set.range (torusCharacterRestrict i))) = ⊤)
    (hred : ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β] → α = β ∨ α = -β) :
    ∃ (J : Type u) (_ : Finite J)
      (P : RootDatum J (characterLattice T) (cocharacterLattice T)),
      IsRootDatumOf i P ∧ P.IsReduced := by
  have := hG.smooth
  have hfinite := hT.finite_relativeRoots i
  exact ⟨relativeRoots i, hfinite.to_subtype, D.rootDatum hT hfinite hspan,
    D.isRootDatumOf_rootDatum hT hfinite hspan,
    D.isReduced_rootDatum_of_eq_or_eq_neg hT hfinite hspan hred⟩

end Langlands.GroupScheme
