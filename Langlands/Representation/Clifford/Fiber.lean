import Langlands.Representation.Clifford.Classes

/-!
# Types over one class of a normal subgroup with procyclic quotient
-/

noncomputable section

namespace Langlands.Clifford

open Representation FiniteRepresentation

universe uG uV uW

namespace Fixed

/-- Equal representations are equivalent. -/
def equivOfEq' {K : Type*} [Group K] {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ σ : Representation ℂ K V} (h : ρ = σ) : Representation.Equiv ρ σ := by
  subst h
  exact Representation.Equiv.refl ρ

end Fixed

section Helpers

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- An open subgroup of a compact group has finite index. -/
theorem finiteIndex_of_isOpen {H : Subgroup G} (hH : IsOpen (H : Set G)) : H.FiniteIndex := by
  have := Subgroup.quotient_finite_of_isOpen H hH
  exact Subgroup.finiteIndex_of_finite_quotient

/-- An open subgroup of a compact group is compact. -/
theorem compactSpace_of_isOpen {H : Subgroup G} (hH : IsOpen (H : Set G)) : CompactSpace H :=
  isCompact_iff_compactSpace.mp (H.isClosed_of_isOpen hH).isCompact

/-- A character with open kernel on a compact group has finite order. -/
theorem exists_pow_eq_one_of_isOpen_ker {K : Type*} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] (χ : K →* ℂˣ) (hχ : IsOpen (χ.ker : Set K)) :
    ∃ n : ℕ, 0 < n ∧ ∀ k : K, χ k ^ n = 1 := by
  have := Subgroup.quotient_finite_of_isOpen χ.ker hχ
  have : χ.ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine ⟨χ.ker.index, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero, fun k => ?_⟩
  rw [← map_pow]
  exact χ.ker.pow_index_mem k

end Helpers

section TameOrder

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {N : Subgroup G}

omit [IsTopologicalGroup G] in
/-- When every commutator lies in `N` and every open subgroup containing `N` has index prime to
`p`, a tame character of an open subgroup containing `N` is killed by an exponent prime to `p`
(positive when `p ≠ 1`). -/
theorem tameCharacters_order (hab : CommutatorsIn N) {p : ℕ}
    (hcop : ∀ U : Subgroup G, N ≤ U → IsOpen (U : Set G) → Nat.Coprime U.index p)
    {H : Subgroup G} (hNH : N ≤ H) (hHo : IsOpen (H : Set G)) {χ : H →* ℂˣ}
    (hχ : χ ∈ tameCharacters N H) :
    ∃ m : ℕ, Nat.Coprime m p ∧ ∀ h : H, χ h ^ m = 1 := by
  let K : Subgroup G := χ.ker.map H.subtype
  have hNK : N ≤ K := fun n hn =>
    ⟨⟨n, hNH hn⟩, hχ.1 (show (⟨n, hNH hn⟩ : H) ∈ N.subgroupOf H from hn), rfl⟩
  have hKo : IsOpen (K : Set G) := hHo.isOpenMap_subtype_val _ hχ.2
  have : K.Normal := normal_of_le hab hNK
  refine ⟨K.index, hcop K hNK hKo, fun h => ?_⟩
  obtain ⟨k, hk, hkh⟩ := K.pow_index_mem (h : G)
  have : k = h ^ K.index := Subtype.ext (by simpa using hkh)
  rw [← map_pow, ← this]
  exact hk

end TameOrder

section Phi

variable {G : Type uG} [Group G] [TopologicalSpace G] [CompactSpace G]
  [NonarchimedeanGroup G] {N : Subgroup G} [N.Normal]

instance stabilizer_finiteIndex (A : WildObj.{uG, uW} N) :
    (MulAction.stabilizer G (wildClass A)).FiniteIndex :=
  finiteIndex_of_isOpen (isOpen_stabilizer A)

variable (A : WildObj.{uG, uW} N)
  (θ : Representation ℂ (MulAction.stabilizer G (wildClass A)) A.1)

omit [CompactSpace G] in
theorem restrict_twist_eq (hθ : θ.comp (Subgroup.inclusion (le_stabilizer _)) = A.1.representation)
    {χ : MulAction.stabilizer G (wildClass A) →* ℂˣ}
    (hχ : N.subgroupOf (MulAction.stabilizer G (wildClass A)) ≤ χ.ker) :
    (Langlands.twist χ θ).comp (Subgroup.inclusion (le_stabilizer _)) = A.1.representation := by
  ext n v
  change (χ (Subgroup.inclusion (le_stabilizer _) n) : ℂ) •
    θ (Subgroup.inclusion (le_stabilizer _) n) v = A.1.representation n v
  rw [hχ (show Subgroup.inclusion (le_stabilizer _) n ∈ N.subgroupOf _ from n.2), Units.val_one,
    one_smul, ← hθ]
  rfl

omit [CompactSpace G] in
theorem isIrreducible_twist_of_restrict
    (hθ : θ.comp (Subgroup.inclusion (le_stabilizer _)) = A.1.representation)
    {χ : MulAction.stabilizer G (wildClass A) →* ℂˣ}
    (hχ : N.subgroupOf (MulAction.stabilizer G (wildClass A)) ≤ χ.ker) :
    (Langlands.twist χ θ).IsIrreducible := by
  apply Langlands.FiniteRepresentation.SplitDegree.isIrreducible_of_comp _ (Subgroup.inclusion (le_stabilizer _))
  rw [restrict_twist_eq A θ hθ hχ]
  exact A.2.1

omit [CompactSpace G] in
theorem conjugatesDisjoint_twist
    (hθ : θ.comp (Subgroup.inclusion (le_stabilizer _)) = A.1.representation)
    {χ χ' : MulAction.stabilizer G (wildClass A) →* ℂˣ}
    (hχ : N.subgroupOf (MulAction.stabilizer G (wildClass A)) ≤ χ.ker)
    (hχ' : N.subgroupOf (MulAction.stabilizer G (wildClass A)) ≤ χ'.ker) :
    ConjugatesDisjoint (MulAction.stabilizer G (wildClass A)) N (le_stabilizer _)
      (Langlands.twist χ θ) (Langlands.twist χ' θ) :=
  conjugatesDisjoint_of_stabilizer
    (Fixed.equivOfEq' (restrict_twist_eq A θ hθ hχ))
    (Fixed.equivOfEq' (restrict_twist_eq A θ hθ hχ'))

omit [CompactSpace G] in
theorem ker_twist_ge {χ : MulAction.stabilizer G (wildClass A) →* ℂˣ} :
    χ.ker ⊓ θ.ker ≤ (Langlands.twist χ θ).ker := by
  intro h hh
  change (χ h : ℂ) • θ h = 1
  rw [MonoidHom.mem_ker.mp hh.1, MonoidHom.mem_ker.mp hh.2, Units.val_one, one_smul]

variable (hθ : θ.comp (Subgroup.inclusion (le_stabilizer _)) = A.1.representation)
  (hθo : IsOpen (θ.ker : Set (MulAction.stabilizer G (wildClass A))))

omit [CompactSpace G] in
include hθo in
theorem isOpen_ker_twist {χ : MulAction.stabilizer G (wildClass A) →* ℂˣ}
    (hχ : χ ∈ tameCharacters N (MulAction.stabilizer G (wildClass A))) :
    IsOpen ((Langlands.twist χ θ).ker : Set (MulAction.stabilizer G (wildClass A))) :=
  Subgroup.isOpen_mono (ker_twist_ge A θ) (hχ.2.inter hθo)

/-- For an extension `θ` of `A` to the stabilizer of its class, with open kernel, and a tame
character `χ` of the stabilizer, the continuous irreducible representation of the compact
nonarchimedean group `G` coinduced from the twist of `θ` by `χ`. -/
def phiObj (χ : MulAction.stabilizer G (wildClass A) →* ℂˣ)
    (hχ : χ ∈ tameCharacters N (MulAction.stabilizer G (wildClass A))) :
    TypeObj.{uG, uW} G :=
  ⟨coindObj _ (Langlands.twist χ θ), by
    rw [isContinuous_iff_isOpen_ker]
    change IsOpen ((coindRep _ (Langlands.twist χ θ)).ker : Set G)
    rw [ker_coindRep]
    exact isOpen_ker_induce _ (isOpen_stabilizer A)
      (FiniteRepresentation.of (Langlands.twist χ θ)) (isOpen_ker_twist A θ hθo hχ), by
    have := A.2.1
    have : Nontrivial A.1 :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ N) (Representation.asModule A.1.representation)
    exact isIrreducible_of_equiv (coindObjEquiv _ _)
      (coind_isIrreducible (isIrreducible_twist_of_restrict A θ hθ hχ.1)
        (conjugatesDisjoint_twist A θ hθ hχ.1 hχ.1))⟩

/-- The coinduced type lies over `A`: evaluation at one restricted to `N`. -/
theorem over_phiObj (χ : MulAction.stabilizer G (wildClass A) →* ℂˣ)
    (hχ : χ ∈ tameCharacters N (MulAction.stabilizer G (wildClass A))) :
    Over N (phiObj A θ hθ hθo χ hχ) A := by
  let τ := Langlands.twist χ θ
  let e := coindObjEquiv (MulAction.stabilizer G (wildClass A)) τ
  have hτ := restrict_twist_eq A θ hθ hχ.1
  let T : IntertwiningMap ((coindObj (MulAction.stabilizer G (wildClass A)) τ).representation.comp N.subtype) A.1.representation :=
    { toLinearMap := ((LinearMap.proj 1).comp (coindV (MulAction.stabilizer G (wildClass A)).subtype τ).subtype).comp
        e.symm.toLinearMap
      isIntertwining' := fun n => by
        apply LinearMap.ext
        intro v
        change (e.symm ((coindObj (MulAction.stabilizer G (wildClass A)) τ).representation n v)).1 1 =
          A.1.representation n ((e.symm v).1 1)
        rw [show e.symm ((coindObj (MulAction.stabilizer G (wildClass A)) τ).representation n v) =
            τ.coind (MulAction.stabilizer G (wildClass A)).subtype n (e.symm v) from
          Representation.IntertwiningMap.isIntertwining _ _ e.symm.toIntertwiningMap _ v]
        change (e.symm v).1 (1 * (n : G)) = _
        have h1 := (e.symm v).2 (Subgroup.inclusion (le_stabilizer _) n) 1
        rw [mul_one] at h1
        rw [one_mul]
        refine h1.trans ?_
        exact congrArg (fun T => T ((e.symm v).1 1)) (congrArg (fun f => f n) hτ) }
  refine ⟨T, fun h0 => ?_⟩
  have := A.2.1
  have : Nontrivial A.1 :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ N) (Representation.asModule A.1.representation)
  obtain ⟨a, ha⟩ := exists_ne (0 : A.1)
  apply ha
  have h1 := congrArg (fun F : IntertwiningMap _ _ => F (e (extendByZero (MulAction.stabilizer G (wildClass A)) τ a))) h0
  change (e.symm (e (extendByZero (MulAction.stabilizer G (wildClass A)) τ a))).1 1 = 0 at h1
  rw [Representation.Equiv.symm_apply_apply, extendByZero_apply_one] at h1
  exact h1

omit [CompactSpace G] in
include hθ in
theorem comp_subgroupOf_subtype :
    θ.comp (N.subgroupOf (MulAction.stabilizer G (wildClass A))).subtype =
      A.1.representation.comp
        (Subgroup.subgroupOfEquivOfLe (le_stabilizer (wildClass A))).toMonoidHom := by
  ext x v
  rw [← hθ]
  rfl

omit [CompactSpace G] in
include hθ in
theorem isIrreducible_comp_subgroupOf :
    Representation.IsIrreducible
      (θ.comp (N.subgroupOf (MulAction.stabilizer G (wildClass A))).subtype) := by
  rw [comp_subgroupOf_subtype A θ hθ]
  have := A.2.1
  exact Langlands.CuspidalSupport.isIrreducible_comp_of_surjective A.1.representation _
    (Subgroup.subgroupOfEquivOfLe (le_stabilizer (wildClass A))).surjective

/-- The coinduced types attached to distinct tame characters are distinct. -/
theorem phiObj_injective {χ χ' : MulAction.stabilizer G (wildClass A) →* ℂˣ}
    (hχ : χ ∈ tameCharacters N (MulAction.stabilizer G (wildClass A)))
    (hχ' : χ' ∈ tameCharacters N (MulAction.stabilizer G (wildClass A)))
    (h : typeClass (phiObj A θ hθ hθo χ hχ) = typeClass (phiObj A θ hθ hθo χ' hχ')) :
    χ = χ' := by
  obtain ⟨E⟩ := (typeClass_eq_iff _ _).mp h
  let τ := Langlands.twist χ θ
  let τ' := Langlands.twist χ' θ
  let e := coindObjEquiv (MulAction.stabilizer G (wildClass A)) τ
  let e' := coindObjEquiv (MulAction.stabilizer G (wildClass A)) τ'
  let F := (e'.symm.toIntertwiningMap.comp E.toIntertwiningMap).comp e.toIntertwiningMap
  have := A.2.1
  have : Nontrivial A.1 :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ N) (Representation.asModule A.1.representation)
  have hF : F ≠ 0 := by
    intro h0
    obtain ⟨a, ha⟩ := exists_ne (0 : A.1)
    apply ha
    have h1 := congrArg (fun F' : IntertwiningMap _ _ =>
      F' (extendByZero (MulAction.stabilizer G (wildClass A)) τ a)) h0
    change e'.symm (E (e (extendByZero (MulAction.stabilizer G (wildClass A)) τ a))) = 0 at h1
    have h2 := (e'.symm.toLinearEquiv.map_eq_zero_iff).mp h1
    have h3 := (E.toLinearEquiv.map_eq_zero_iff).mp h2
    have h4 := (e.toLinearEquiv.map_eq_zero_iff).mp h3
    have h5 := congrArg (fun f : coindV (MulAction.stabilizer G (wildClass A)).subtype τ =>
      f.1 1) h4
    simp only [extendByZero_apply_one] at h5
    exact h5
  obtain ⟨T, hT⟩ := exists_ne_zero_of_coind (conjugatesDisjoint_twist A θ hθ hχ.1 hχ'.1) F hF
  obtain ⟨eq⟩ := Langlands.FiniteRepresentation.SplitDegree.nonempty_equiv_of_ne_zero _ _ (isIrreducible_twist_of_restrict A θ hθ hχ.1)
    (isIrreducible_twist_of_restrict A θ hθ hχ'.1) T hT
  exact eq_of_twist_equiv _ θ (isIrreducible_comp_subgroupOf A θ hθ) hχ.1 hχ'.1 eq

/-- When every commutator lies in `N`, every type over `A` is one of the coinduced types. -/
theorem exists_phiObj_eq (hab : CommutatorsIn N) (B : TypeObj.{uG, uW} G) (hB : Over N B A) :
    ∃ (χ : MulAction.stabilizer G (wildClass A) →* ℂˣ)
      (hχ : χ ∈ tameCharacters N (MulAction.stabilizer G (wildClass A))),
      typeClass B = typeClass (phiObj A θ hθ hθo χ hχ) := by
  obtain ⟨T, hT⟩ := hB
  let H := MulAction.stabilizer G (wildClass A)
  let N' : Subgroup H := N.subgroupOf H
  have : N'.Normal := Subgroup.Normal.subgroupOf ‹N.Normal› H
  have hcomp := comp_subgroupOf_subtype A θ hθ
  let P : IntertwiningMap ((B.1.representation.comp H.subtype).comp N'.subtype)
      (θ.comp N'.subtype) :=
    { toLinearMap := T.toLinearMap
      isIntertwining' := fun x => by
        have h1 := T.isIntertwining' (Subgroup.subgroupOfEquivOfLe (le_stabilizer _) x)
        rw [hcomp]
        exact h1 }
  have hP : P ≠ 0 := fun h0 => hT (by
    apply Representation.IntertwiningMap.ext
    have h1 := congrArg Representation.IntertwiningMap.toLinearMap h0
    exact h1)
  have hcomm : ∀ x y : H, x * y * x⁻¹ * y⁻¹ ∈ N' := fun x y => hab x y
  obtain ⟨χ, hχN, T', hT'⟩ :=
    exists_twist_intertwining N' hcomm (B.1.representation.comp H.subtype) θ P hP
  have hker : (B.1.representation.ker.comap H.subtype) ⊓ θ.ker ≤ χ.ker := by
    intro h hh
    obtain ⟨w, hw⟩ : ∃ w, T' w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hT' (Representation.IntertwiningMap.ext (LinearMap.ext hcon))
    have h1 := Representation.IntertwiningMap.isIntertwining _ _ T' h w
    have hB1 : B.1.representation (h : G) = 1 := MonoidHom.mem_ker.mp hh.1
    have hθ1 : θ h = 1 := MonoidHom.mem_ker.mp hh.2
    change T' (B.1.representation (h : G) w) = (χ h : ℂ) • θ h (T' w) at h1
    rw [hB1, hθ1, Module.End.one_apply, Module.End.one_apply] at h1
    apply Units.ext
    have h2 : ((χ h : ℂ) - 1) • T' w = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hw
  have hBo : IsOpen (B.1.representation.ker : Set G) :=
    (isContinuous_iff_isOpen_ker B.1).mp B.2.1
  have hχ : χ ∈ tameCharacters N H :=
    ⟨hχN, Subgroup.isOpen_mono hker ((hBo.preimage continuous_subtype_val).inter hθo)⟩
  refine ⟨χ, hχ, ?_⟩
  apply (typeClass_eq_iff _ _).mpr
  let F : IntertwiningMap B.1.representation (phiObj A θ hθ hθo χ hχ).1.representation :=
    (coindObjEquiv H (Langlands.twist χ θ)).toIntertwiningMap.comp (coindLift H _ T')
  have hF : F ≠ 0 := by
    intro h0
    apply coindLift_ne_zero H hT'
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    have h1 := congrArg (fun F' : IntertwiningMap _ _ => F' v) h0
    change coindObjEquiv H (Langlands.twist χ θ) (coindLift H _ T' v) = 0 at h1
    exact (LinearEquiv.map_eq_zero_iff _).mp h1
  exact Langlands.FiniteRepresentation.SplitDegree.nonempty_equiv_of_ne_zero _ _ B.2.2 (phiObj A θ hθ hθo χ hχ).2.2 F hF

end Phi

section PhiPullback

variable {G : Type uG} [Group G] [TopologicalSpace G] [CompactSpace G]
  [NonarchimedeanGroup G] {N : Subgroup G} [N.Normal]
variable (A : WildObj.{uG, uW} N)
  (θ : Representation ℂ (MulAction.stabilizer G (wildClass A)) A.1)
  (hθ : θ.comp (Subgroup.inclusion (le_stabilizer _)) = A.1.representation)
  (hθo : IsOpen (θ.ker : Set (MulAction.stabilizer G (wildClass A))))
  (α : G ≃ₜ* G) (hN : ∀ x, x ∈ N ↔ α x ∈ N)
  (hfix : wildPullback α hN (wildClass A) = wildClass A)

omit [CompactSpace G] in
theorem continuous_restrictAut_stabilizer :
    Continuous (restrictAut α.toMulEquiv (mem_stabilizer_iff_of_fixed α hN hfix)) :=
  (α.continuous.comp continuous_subtype_val).subtype_mk _

omit [CompactSpace G] in
include hfix in
theorem comp_restrictAut_mem {χ : MulAction.stabilizer G (wildClass A) →* ℂˣ}
    (hχ : χ ∈ tameCharacters N (MulAction.stabilizer G (wildClass A))) :
    χ.comp (restrictAut α.toMulEquiv (mem_stabilizer_iff_of_fixed α hN hfix)) ∈
      tameCharacters N (MulAction.stabilizer G (wildClass A)) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · exact hχ.1 (show restrictAut α.toMulEquiv _ x ∈ N.subgroupOf _ from (hN _).mp hx)
  · change IsOpen ((restrictAut α.toMulEquiv (mem_stabilizer_iff_of_fixed α hN hfix)) ⁻¹'
      (χ.ker : Set (MulAction.stabilizer G (wildClass A))))
    exact hχ.2.preimage (continuous_restrictAut_stabilizer A α hN hfix)

/-- Let `α` be a continuous automorphism preserving `N` whose pullback fixes the class of `A`, and
suppose `θ ∘ α` is equivalent to `θ` on the stabilizer. Pulling back a coinduced type along `α`
replaces its character `χ` by `χ ∘ α`. -/
theorem typeClass_pullback_phiObj
    (Eθ : Representation.Equiv
      (θ.comp (restrictAut α.toMulEquiv (mem_stabilizer_iff_of_fixed α hN hfix))) θ)
    {χ : MulAction.stabilizer G (wildClass A) →* ℂˣ}
    (hχ : χ ∈ tameCharacters N (MulAction.stabilizer G (wildClass A))) :
    typeClass (typeObjPullback α (phiObj A θ hθ hθo χ hχ)) =
      typeClass (phiObj A θ hθ hθo _ (comp_restrictAut_mem A α hN hfix hχ)) := by
  apply (typeClass_eq_iff _ _).mpr
  set r := restrictAut α.toMulEquiv (mem_stabilizer_iff_of_fixed α hN hfix)
  let τ := Langlands.twist χ θ
  let e1 := equivComp (coindObjEquiv (MulAction.stabilizer G (wildClass A)) τ).symm
    α.toMulEquiv.toMonoidHom
  let e2 := coindCompEquiv τ α.toMulEquiv (mem_stabilizer_iff_of_fixed α hN hfix)
  have h3 : τ.comp r = Langlands.twist (χ.comp r) (θ.comp r) := by
    ext h v
    rfl
  let e3 : Representation.Equiv (τ.comp r) (Langlands.twist (χ.comp r) θ) :=
    (Fixed.equivOfEq' h3).trans (Langlands.twistEquiv (χ.comp r) Eθ)
  let e4 := coindObjEquiv (MulAction.stabilizer G (wildClass A)) (Langlands.twist (χ.comp r) θ)
  exact ⟨e1.trans (e2.trans ((coindEquivOfEquiv _ e3).trans e4))⟩

include hθ hθo in
/-- Let `θ` be an extension of `A` to the stabilizer of its class, with open kernel and determinant
of `p`-power order. Suppose every commutator lies in `N`, every open subgroup containing `N` has
index prime to `p`, and `A` has dimension `p ^ a`. Then for every continuous automorphism `α`
preserving `N` whose pullback fixes the class of `A`, `θ ∘ α` is equivalent to `θ`. -/
theorem nonempty_equiv_comp_restrictAut (hab : CommutatorsIn N) {p a : ℕ}
    (hcop : ∀ U : Subgroup G, N ≤ U → IsOpen (U : Set G) → Nat.Coprime U.index p)
    (hdim : Module.finrank ℂ A.1 = p ^ a) {s : ℕ}
    (hdet : ∀ h : MulAction.stabilizer G (wildClass A), detChar θ h ^ p ^ s = 1) :
    Nonempty (Representation.Equiv
      (θ.comp (restrictAut α.toMulEquiv (mem_stabilizer_iff_of_fixed α hN hfix))) θ) := by
  set r := restrictAut α.toMulEquiv (mem_stabilizer_iff_of_fixed α hN hfix)
  let H := MulAction.stabilizer G (wildClass A)
  let N' : Subgroup H := N.subgroupOf H
  have : N'.Normal := Subgroup.Normal.subgroupOf ‹N.Normal› H
  let eN := Subgroup.subgroupOfEquivOfLe (le_stabilizer (wildClass A))
  obtain ⟨F⟩ := (wildClass_eq_iff _ _).mp hfix
  have e1 : (θ.comp r).comp N'.subtype =
      (A.1.representation.comp (restrictAut α.toMulEquiv hN)).comp eN.toMonoidHom := by
    ext x v
    rw [← hθ]
    rfl
  have e2 := comp_subgroupOf_subtype A θ hθ
  let e : Representation.Equiv ((θ.comp r).comp N'.subtype) (θ.comp N'.subtype) :=
    (Fixed.equivOfEq' e1).trans ((equivComp F eN.toMonoidHom).trans (Fixed.equivOfEq' e2.symm))
  have hcomm : ∀ x y : H, x * y * x⁻¹ * y⁻¹ ∈ N' := fun x y => hab x y
  obtain ⟨χ, hχN, ⟨E⟩⟩ :=
    exists_twist_equiv N' hcomm θ (θ.comp r) (isIrreducible_comp_subgroupOf A θ hθ) e
  have := A.2.1
  have : Nontrivial A.1 :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ N) (Representation.asModule A.1.representation)
  have hker : (θ.comp r).ker ⊓ θ.ker ≤ χ.ker := by
    intro h hh
    obtain ⟨w, hw⟩ := exists_ne (0 : A.1)
    have h1 := Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap h w
    change E (θ (r h) w) = (χ h : ℂ) • θ h (E w) at h1
    have hr1 : θ (r h) = 1 := MonoidHom.mem_ker.mp hh.1
    rw [hr1, MonoidHom.mem_ker.mp hh.2, Module.End.one_apply, Module.End.one_apply] at h1
    apply Units.ext
    have hEw : E w ≠ 0 := by
      intro h0
      exact hw ((LinearEquiv.map_eq_zero_iff E.toLinearEquiv).mp h0)
    have h2 : ((χ h : ℂ) - 1) • E w = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hEw
  have hro : IsOpen ((θ.comp r).ker : Set H) := by
    change IsOpen (r ⁻¹' (θ.ker : Set H))
    exact hθo.preimage (continuous_restrictAut_stabilizer A α hN hfix)
  have hχ : χ ∈ tameCharacters N H := ⟨hχN, Subgroup.isOpen_mono hker (hro.inter hθo)⟩
  obtain ⟨m, hm, hχm⟩ :=
    tameCharacters_order hab hcop (le_stabilizer _) (isOpen_stabilizer A) hχ
  have h2 : ∀ h : H, detChar (Langlands.twist χ θ) h ^ p ^ s = 1 := by
    intro h
    rw [← detChar_eq_of_equiv E, detChar_comp, MonoidHom.comp_apply]
    exact hdet (r h)
  have hχ1 := eq_one_of_detChar_pPower hdim hm hχm hdet h2
  rw [hχ1, twist_one] at E
  exact ⟨E⟩

end PhiPullback

section Normalized

variable {G : Type uG} [Group G] [TopologicalSpace G] [CompactSpace G]
  [NonarchimedeanGroup G] {N : Subgroup G} [N.Normal]

/-- In a compact nonarchimedean group, when every commutator lies in `N`,
`CyclicOpenQuotients N` holds, `A` has dimension `p ^ a` for a prime `p`, and every character of
`N` with open kernel has `p`-power order, `A` has an extension to the stabilizer of its class with
open kernel and determinant of `p`-power order. -/
theorem exists_normalized_extension (hab : CommutatorsIn N) (hcyc : CyclicOpenQuotients N)
    {p a : ℕ} (hp : p.Prime) (A : WildObj.{uG, uW} N) (hdim : Module.finrank ℂ A.1 = p ^ a)
    (hdetN : ∀ χ : N →* ℂˣ, IsOpen (χ.ker : Set N) → ∃ b : ℕ, ∀ n : N, χ n ^ p ^ b = 1) :
    ∃ θ : Representation ℂ (MulAction.stabilizer G (wildClass A)) A.1,
      θ.comp (Subgroup.inclusion (le_stabilizer _)) = A.1.representation ∧
      IsOpen (θ.ker : Set (MulAction.stabilizer G (wildClass A))) ∧
      ∃ s : ℕ, ∀ h, detChar θ h ^ p ^ s = 1 := by
  obtain ⟨θ₀, hθ₀, hθ₀o⟩ := exists_extension_stabilizer hab hcyc A
  have : CompactSpace (MulAction.stabilizer G (wildClass A)) :=
    compactSpace_of_isOpen (isOpen_stabilizer A)
  have hfin := exists_pow_eq_one_of_isOpen_ker (detChar θ₀)
    (Subgroup.isOpen_mono (ker_le_ker_detChar θ₀) hθ₀o)
  have hAo : IsOpen ((detChar A.1.representation).ker : Set N) :=
    Subgroup.isOpen_mono (ker_le_ker_detChar A.1.representation) A.2.2
  obtain ⟨b, hb⟩ := hdetN _ hAo
  have hN : ∃ b : ℕ, ∀ y : N.subgroupOf (MulAction.stabilizer G (wildClass A)),
      detChar θ₀ y ^ p ^ b = 1 := by
    refine ⟨b, fun y => ?_⟩
    have h1 : detChar θ₀ y = detChar A.1.representation
        (Subgroup.subgroupOfEquivOfLe (le_stabilizer (wildClass A)) y) := by
      have h2 := congrArg (fun f => detChar f y) (comp_subgroupOf_subtype A θ₀ hθ₀)
      simp only [detChar_comp, MonoidHom.comp_apply] at h2
      exact h2
    rw [h1]
    exact hb _
  obtain ⟨γ, hγN, hγker, s, hs⟩ := exists_twist_detChar_pPower _ hp θ₀ hdim hfin hN
  refine ⟨Langlands.twist γ θ₀, restrict_twist_eq A θ₀ hθ₀ hγN, ?_, s, hs⟩
  exact Subgroup.isOpen_mono (fun h hh => ker_twist_ge A θ₀ ⟨hγker hh, hh⟩) hθ₀o

end Normalized

section Count

variable {G : Type uG} [Group G] [TopologicalSpace G] [CompactSpace G]
  [NonarchimedeanGroup G] {N : Subgroup G} [N.Normal]

omit [TopologicalSpace G] [CompactSpace G] [NonarchimedeanGroup G] [N.Normal] in
theorem dep_congr {β : Sort*} {P : (G →* ℂˣ) → Prop} (f : ∀ a, P a → β) {a a' : G →* ℂˣ}
    (h : a = a') (ha : P a) (ha' : P a') : f a ha = f a' ha' := by
  subst h
  rfl

theorem dep_congr' {K : Type*} [Group K] {β : Sort*} {P : (K →* ℂˣ) → Prop}
    (f : ∀ a, P a → β) {a a' : K →* ℂˣ} (h : a = a') (ha : P a) (ha' : P a') :
    f a ha = f a' ha' := by
  subst h
  rfl

omit [CompactSpace G] [NonarchimedeanGroup G] [N.Normal] in
/-- Characters are invariant under inner automorphisms. -/
theorem char_comp_conj_trans [IsTopologicalGroup G] (ψ : G →* ℂˣ) (h : G) (α : G ≃ₜ* G) :
    ψ.comp ((conjCts h).trans α).toMulEquiv.toMonoidHom = ψ.comp α.toMulEquiv.toMonoidHom := by
  ext1 x
  change ψ (α (h * x * h⁻¹)) = ψ (α x)
  rw [map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (ψ (α h)), mul_assoc,
    mul_inv_cancel, mul_one]

/-- **Fiber count.** Let `G` be compact and nonarchimedean, let every commutator lie in `N`, let
`CyclicOpenQuotients N` hold, and let `p` be a prime such that every open subgroup containing `N`
has index prime to `p`, every `d` prime to `p` is such an index, every class of `N` has rank a power
of `p`, and every character of `N` with open kernel has `p`-power order. For a continuous
automorphism `α` preserving `N` and a class `c` of `N` whose pullback by `α` lies in the orbit of
`c`, the `α`-fixed types lying over `c` are as many as the `α`-fixed tame characters of `G`. -/
theorem encard_fixed_liesOver (hab : CommutatorsIn N) (hcyc : CyclicOpenQuotients N)
    {p : ℕ} (hp : p.Prime)
    (hcop : ∀ U : Subgroup G, N ≤ U → IsOpen (U : Set G) → Nat.Coprime U.index p)
    (hexists : ∀ d : ℕ, Nat.Coprime d p →
      ∃ U : Subgroup G, N ≤ U ∧ IsOpen (U : Set G) ∧ U.index = d)
    (hdim : ∀ c : OpenKernelIrreducibleClasses.{uG, uW} N,
      ∃ a : ℕ, openKernelIrreducibleRank N c = p ^ a)
    (hdetN : ∀ χ : N →* ℂˣ, IsOpen (χ.ker : Set N) → ∃ b : ℕ, ∀ n : N, χ n ^ p ^ b = 1)
    (α : G ≃ₜ* G) (hN : ∀ x, x ∈ N ↔ α x ∈ N) (c : OpenKernelIrreducibleClasses.{uG, uW} N)
    (hc : ∃ h : G, wildPullback α hN c = h • c) :
    {x : TypeClasses.{uG, uW} G | typePullback α x = x ∧ LiesOver N x c}.encard =
      {ψ ∈ tameCharactersTop N | ψ.comp α.toMulEquiv.toMonoidHom = ψ}.encard := by
  obtain ⟨A, hA⟩ := Quotient.exists_rep c
  have hcA : c = wildClass A := hA.symm
  subst hcA
  obtain ⟨h, hh⟩ := hc
  let α' : G ≃ₜ* G := (conjCts h).trans α
  have hconj : ∀ x, x ∈ N ↔ conjCts h x ∈ N := fun x => by
    rw [conjCts_apply]
    exact ⟨fun hx => ‹N.Normal›.conj_mem x hx h, fun hx => by
      convert ‹N.Normal›.conj_mem' _ hx h using 1
      group⟩
  have hN' : ∀ x, x ∈ N ↔ α' x ∈ N := fun x => (hconj x).trans (hN _)
  have hfix : wildPullback α' hN' (wildClass A) = wildClass A := by
    change wildPullback ((conjCts h).trans α) hN' (wildClass A) = wildClass A
    rw [wildPullback_trans (conjCts h) α hconj hN hN', hh, wildPullback_smul,
      wildPullback_conjCts]
    have : (conjCts h).symm h = h := by
      change h⁻¹ * h * h = h
      group
    rw [this, smul_inv_smul]
  obtain ⟨a, ha⟩ := hdim (wildClass A)
  have hdimA : Module.finrank ℂ A.1 = p ^ a := ha
  obtain ⟨θ, hθ, hθo, s, hdet⟩ := exists_normalized_extension hab hcyc hp A hdimA hdetN
  obtain ⟨Eθ⟩ := nonempty_equiv_comp_restrictAut A θ hθ hθo α' hN' hfix hab hcop hdimA hdet
  have hH := mem_stabilizer_iff_of_fixed α' hN' hfix
  have hNH : N ≤ MulAction.stabilizer G (wildClass A) := le_stabilizer _
  have hHo : IsOpen ((MulAction.stabilizer G (wildClass A) : Subgroup G) : Set G) := isOpen_stabilizer A
  let S₁ := {χ ∈ tameCharacters N (MulAction.stabilizer G (wildClass A)) | χ.comp (restrictAut α'.toMulEquiv hH) = χ}
  have hpull : ∀ (χ : MulAction.stabilizer G (wildClass A) →* ℂˣ) (hχ : χ ∈ tameCharacters N (MulAction.stabilizer G (wildClass A))),
      typePullback α (typeClass (phiObj A θ hθ hθo χ hχ)) =
        typeClass (phiObj A θ hθ hθo _ (comp_restrictAut_mem A α' hN' hfix hχ)) := by
    intro χ hχ
    rw [← typePullback_conj_trans h α, typePullback_mk]
    exact typeClass_pullback_phiObj A θ hθ hθo α' hN' hfix Eθ hχ
  -- the coinduced types
  let f₁ : S₁ → {x : TypeClasses.{uG, uW} G | typePullback α x = x ∧
      LiesOver N x (wildClass A)} := fun χ =>
    ⟨typeClass (phiObj A θ hθ hθo χ.1 χ.2.1), by
      refine ⟨?_, (liesOver_iff _ _).mpr (over_phiObj A θ hθ hθo χ.1 χ.2.1)⟩
      rw [hpull χ.1 χ.2.1]
      exact congrArg typeClass (dep_congr' (phiObj A θ hθ hθo) χ.2.2 _ _)⟩
  have hf₁ : Function.Bijective f₁ := by
    constructor
    · rintro ⟨χ, hχ⟩ ⟨χ', hχ'⟩ heq
      exact Subtype.ext (phiObj_injective A θ hθ hθo hχ.1 hχ'.1 (congrArg Subtype.val heq))
    · rintro ⟨x, hx1, hx2⟩
      obtain ⟨B, hB⟩ := Quotient.exists_rep x
      have hxB : x = typeClass B := hB.symm
      subst hxB
      obtain ⟨χ, hχ, heq⟩ :=
        exists_phiObj_eq A θ hθ hθo hab B ((liesOver_iff B A).mp hx2)
      have hfixχ : χ.comp (restrictAut α'.toMulEquiv hH) = χ := by
        refine phiObj_injective A θ hθ hθo (comp_restrictAut_mem A α' hN' hfix hχ) hχ ?_
        rw [← hpull χ hχ, ← heq, hx1]
      exact ⟨⟨χ, hχ, hfixχ⟩, Subtype.ext heq.symm⟩
  -- the power characters
  have hpc : ∀ (χ : MulAction.stabilizer G (wildClass A) →* ℂˣ) (hχ : χ ∈ tameCharacters N (MulAction.stabilizer G (wildClass A))),
      (powChar hab hNH χ hχ.1).comp α.toMulEquiv.toMonoidHom =
        powChar hab hNH _ (comp_restrictAut_mem A α' hN' hfix hχ).1 := by
    intro χ hχ
    rw [powChar_comp_restrictAut hab hNH α'.toMulEquiv hH hχ.1, ← char_comp_conj_trans _ h α]
  let f₂ : S₁ → {ψ ∈ tameCharactersTop N | ψ.comp α.toMulEquiv.toMonoidHom = ψ} := fun χ =>
    ⟨powChar hab hNH χ.1 χ.2.1.1, powChar_mem_tameCharactersTop hab hNH χ.2.1, by
      rw [hpc χ.1 χ.2.1]
      exact powChar_congr hab hNH χ.2.2 _ _⟩
  have hf₂ : Function.Bijective f₂ := by
    constructor
    · rintro ⟨χ, hχ⟩ ⟨χ', hχ'⟩ heq
      exact Subtype.ext (powChar_injective hab hNH hcyc hHo hχ.1 hχ'.1
        (congrArg Subtype.val heq))
    · rintro ⟨ψ, hψ, hψα⟩
      obtain ⟨χ, hχ, heq⟩ :=
        exists_powChar_eq hab hNH hcyc hp.ne_one hcop hexists hHo hψ
      have hfixχ : χ.comp (restrictAut α'.toMulEquiv hH) = χ := by
        refine powChar_injective hab hNH hcyc hHo (comp_restrictAut_mem A α' hN' hfix hχ) hχ ?_
        rw [← hpc χ hχ, heq, hψα]
      exact ⟨⟨χ, hχ, hfixχ⟩, Subtype.ext heq⟩
  rw [← Set.encard_congr (Equiv.ofBijective f₁ hf₁), Set.encard_congr (Equiv.ofBijective f₂ hf₂)]

end Count

end Langlands.Clifford
