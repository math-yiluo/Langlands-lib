import Langlands.Global.Arithmetic.GeneralPositionInductionProof

/-! # Exact stabilizers and conjugate restricted characters -/

noncomputable section

universe uG uC

namespace Langlands.Global.GeneralPosition

variable {G : Type uG} [Group G] {C : Type uC} [Group C]

/-- Two conjugates of a character with exact stabilizer `H` agree precisely
when the corresponding right cosets agree. -/
theorem conjugateCharacters_eq_iff (N H : Subgroup G) [N.Normal]
    (ψ : N →* C)
    (hexact : ∀ g : G,
      ψ.comp (MulAut.conjNormal g⁻¹).toMonoidHom = ψ ↔ g ∈ H)
    (a b : G) :
    ψ.comp (MulAut.conjNormal a).toMonoidHom =
      ψ.comp (MulAut.conjNormal b).toMonoidHom ↔ a * b⁻¹ ∈ H := by
  constructor
  · intro hab
    apply (hexact (a * b⁻¹)).mp
    ext n
    have hn := DFunLike.congr_fun hab (MulAut.conjNormal a⁻¹ n)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hn ⊢
    have ha : MulAut.conjNormal a (MulAut.conjNormal a⁻¹ n) = n := by
      apply Subtype.ext
      simp
    have hb : MulAut.conjNormal b (MulAut.conjNormal a⁻¹ n) =
        MulAut.conjNormal (a * b⁻¹)⁻¹ n := by
      apply Subtype.ext
      simp [mul_assoc]
    rw [ha, hb] at hn
    exact hn.symm
  · intro hab
    have he := (hexact (a * b⁻¹)).mpr hab
    ext n
    have hn := DFunLike.congr_fun he (MulAut.conjNormal a n)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hn ⊢
    have hb : MulAut.conjNormal (a * b⁻¹)⁻¹ (MulAut.conjNormal a n) =
        MulAut.conjNormal b n := by
      apply Subtype.ext
      simp [mul_assoc]
    rw [hb] at hn
    exact hn.symm

/-- Conjugating a restricted character conjugates its exact stabilizer. -/
theorem conjugateCharacter_stabilizer (N H : Subgroup G) [N.Normal]
    (ψ : N →* C)
    (hexact : ∀ g : G,
      ψ.comp (MulAut.conjNormal g⁻¹).toMonoidHom = ψ ↔ g ∈ H)
    (g a : G) :
    (ψ.comp (MulAut.conjNormal g⁻¹).toMonoidHom).comp
        (MulAut.conjNormal a⁻¹).toMonoidHom =
      ψ.comp (MulAut.conjNormal g⁻¹).toMonoidHom ↔ a ∈ conjugate H g := by
  have he : (ψ.comp (MulAut.conjNormal g⁻¹).toMonoidHom).comp
        (MulAut.conjNormal a⁻¹).toMonoidHom =
      ψ.comp (MulAut.conjNormal (g⁻¹ * a⁻¹)).toMonoidHom := by
    ext n
    apply congrArg ψ
    apply Subtype.ext
    simp [mul_assoc]
  rw [he, conjugateCharacters_eq_iff N H ψ hexact]
  change (g⁻¹ * a⁻¹) * (g⁻¹)⁻¹ ∈ H ↔ (MulAut.conj g⁻¹) a ∈ H
  simp only [MulAut.conj_apply, inv_inv]
  have hi : g⁻¹ * a⁻¹ * g = (g⁻¹ * a * g)⁻¹ := by
    simp [mul_assoc]
  rw [hi, inv_mem_iff]

/-- Exactness separates characters on distinct right cosets. -/
theorem exactStabilizer_separation (N H : Subgroup G) [N.Normal]
    (ψ : N →* C)
    (hexact : ∀ g : G,
      ψ.comp (MulAut.conjNormal g⁻¹).toMonoidHom = ψ ↔ g ∈ H)
    (x y : G)
    (hxy : FiniteRepresentation.Induction.coset H x ≠
      FiniteRepresentation.Induction.coset H y) :
    ∃ n : N, ψ (MulAut.conjNormal x n) ≠ ψ (MulAut.conjNormal y n) := by
  by_contra! heq
  have hchars : ψ.comp (MulAut.conjNormal x).toMonoidHom =
      ψ.comp (MulAut.conjNormal y).toMonoidHom := MonoidHom.ext heq
  have hmem := (conjugateCharacters_eq_iff N H ψ hexact x y).mp hchars
  apply hxy
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  simpa using H.inv_mem hmem

/-- A normal subgroup contained in `H` is contained in every conjugate of `H`. -/
theorem normal_le_conjugate (N H : Subgroup G) [N.Normal] (hNH : N ≤ H)
    (g : G) : N ≤ conjugate H g := by
  intro n hn
  change (MulAut.conj g⁻¹) n ∈ H
  simpa only [MulAut.conj_apply, inv_inv] using
    hNH (Subgroup.Normal.conj_mem (inferInstance : N.Normal) n hn g⁻¹)

/-- The normal subgroup inside `K` lies in the actual Mackey inducing subgroup. -/
theorem normal_subgroupOf_le_conjugate (N H K : Subgroup G) [N.Normal]
    (hNH : N ≤ H) (g : G) :
    N.subgroupOf K ≤ (conjugate H g).subgroupOf K := by
  intro n hn
  exact normal_le_conjugate N H hNH g hn

/-- The character on the normal subgroup of a Mackey constituent is the
restriction of the conjugated original character. -/
theorem mackeyCharacter_restriction (N H K : Subgroup G) [N.Normal]
    (hNH : N ≤ H) (χ : H →* C) (g : G) (n : N.subgroupOf K) :
    ((χ.comp (conjugateRestriction H K g)).comp
      (Subgroup.inclusion (normal_subgroupOf_le_conjugate N H K hNH g))) n =
    (χ.comp (Subgroup.inclusion hNH))
      (MulAut.conjNormal g⁻¹ ⟨((n : K) : G), n.property⟩) := by
  apply congrArg χ
  apply Subtype.ext
  rfl

/-- Exact stabilizers separate all normal-subgroup characters in every actual
Mackey constituent, whenever `K` contains `N`. -/
theorem mackeyCharacter_separation (N H K : Subgroup G) [N.Normal]
    (hNH : N ≤ H) (hNK : N ≤ K) (χ : H →* C)
    (hexact : ∀ a : G,
      (χ.comp (Subgroup.inclusion hNH)).comp
          (MulAut.conjNormal a⁻¹).toMonoidHom =
        χ.comp (Subgroup.inclusion hNH) ↔ a ∈ H)
    (g : G) (x y : K)
    (hxy : FiniteRepresentation.Induction.coset ((conjugate H g).subgroupOf K) x ≠
      FiniteRepresentation.Induction.coset ((conjugate H g).subgroupOf K) y) :
    ∃ n : N.subgroupOf K,
      ((χ.comp (conjugateRestriction H K g)).comp
        (Subgroup.inclusion (normal_subgroupOf_le_conjugate N H K hNH g)))
          (MulAut.conjNormal x n) ≠
      ((χ.comp (conjugateRestriction H K g)).comp
        (Subgroup.inclusion (normal_subgroupOf_le_conjugate N H K hNH g)))
          (MulAut.conjNormal y n) := by
  by_contra! heq
  have hchars : (χ.comp (Subgroup.inclusion hNH)).comp
        (MulAut.conjNormal (g⁻¹ * (x : G))).toMonoidHom =
      (χ.comp (Subgroup.inclusion hNH)).comp
        (MulAut.conjNormal (g⁻¹ * (y : G))).toMonoidHom := by
    ext n
    let nK : N.subgroupOf K := ⟨⟨n, hNK n.property⟩, n.property⟩
    have hn := heq nK
    rw [mackeyCharacter_restriction, mackeyCharacter_restriction] at hn
    have hx : MulAut.conjNormal g⁻¹
        ⟨((MulAut.conjNormal x nK : K) : G),
          (MulAut.conjNormal x nK).property⟩ =
        MulAut.conjNormal (g⁻¹ * (x : G)) n := by
      apply Subtype.ext
      simp [nK, mul_assoc]
    have hy : MulAut.conjNormal g⁻¹
        ⟨((MulAut.conjNormal y nK : K) : G),
          (MulAut.conjNormal y nK).property⟩ =
        MulAut.conjNormal (g⁻¹ * (y : G)) n := by
      apply Subtype.ext
      simp [nK, mul_assoc]
    rw [hx, hy] at hn
    exact hn
  have hmem := (conjugateCharacters_eq_iff N H
    (χ.comp (Subgroup.inclusion hNH)) hexact _ _).mp hchars
  have hconj : (x : G) * (y : G)⁻¹ ∈ conjugate H g := by
    change (MulAut.conj g⁻¹) ((x : G) * (y : G)⁻¹) ∈ H
    simpa only [MulAut.conj_apply, inv_inv, mul_inv_rev, mul_assoc] using hmem
  apply hxy
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  have hxyK : x * y⁻¹ ∈ (conjugate H g).subgroupOf K := hconj
  simpa only [mul_inv_rev, inv_inv] using
    ((conjugate H g).subgroupOf K).inv_mem hxyK

/-- The exact stabilizer criterion for the actual induced character. -/
theorem induce_irreducible_of_exactStabilizer (N H : Subgroup G)
    [H.FiniteIndex] [N.Normal] (hNH : N ≤ H) (χ : H →* ℂˣ)
    (hexact : ∀ a : G,
      (χ.comp (Subgroup.inclusion hNH)).comp
          (MulAut.conjNormal a⁻¹).toMonoidHom =
        χ.comp (Subgroup.inclusion hNH) ↔ a ∈ H) :
    (FiniteRepresentation.induce H
      (FiniteRepresentation.characterLine.{uG, 0} χ)).IsIrreducible :=
  induce_irreducible_of_separation H N hNH χ
    (exactStabilizer_separation N H (χ.comp (Subgroup.inclusion hNH)) hexact)

/-- Harris's exact stabilizer makes every actual Mackey constituent irreducible
for every subgroup containing the normal subgroup, and every group element. -/
theorem mackeyConstituent_irreducible_of_exactStabilizer (N H K : Subgroup G)
    [H.FiniteIndex] [N.Normal] (hNH : N ≤ H) (hNK : N ≤ K) (χ : H →* ℂˣ)
    (hexact : ∀ a : G,
      (χ.comp (Subgroup.inclusion hNH)).comp
          (MulAut.conjNormal a⁻¹).toMonoidHom =
        χ.comp (Subgroup.inclusion hNH) ↔ a ∈ H) (g : G) :
    (mackeyConstituent H K (FiniteRepresentation.characterLine.{uG, 0} χ)
      g).IsIrreducible := by
  change (FiniteRepresentation.induce ((conjugate H g).subgroupOf K)
    (FiniteRepresentation.characterLine.{uG, 0}
      (χ.comp (conjugateRestriction H K g)))).IsIrreducible
  exact induce_irreducible_of_separation ((conjugate H g).subgroupOf K)
    (N.subgroupOf K) (normal_subgroupOf_le_conjugate N H K hNH g)
    (χ.comp (conjugateRestriction H K g))
    (mackeyCharacter_separation N H K hNH hNK χ hexact g)

end Langlands.Global.GeneralPosition
