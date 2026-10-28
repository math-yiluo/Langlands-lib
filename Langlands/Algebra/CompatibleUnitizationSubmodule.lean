import Langlands.Algebra.CompatibleSubmodule
import Langlands.Algebra.CompatibleUnitization

/-!
# Stable subspaces, restrictions and quotients of the unitized action

Renard (9 July 2026), I.2.1 on printed p. 14 and the opening of B.II on printed p. 272. For a
compatible action `ρ : A →ₙₐ[k] Module.End k M`, the stable `k`-subspaces of `ρ` are exactly
the submodules of `M` for the unitized action `CompatibleUnitization.module ρ`, with the same
carriers. The restricted and quotient unitized actions are the unitizations of the restricted
and quotient original actions, through the same elements and the same quotient map.
-/

namespace Langlands.Algebra

namespace CompatibleUnitization

open Unitization

universe u v w

variable {k : Type u} {A : Type v} {M : Type w}
  [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
  [AddCommGroup M] [Module k M]

section OrderIso

variable (ρ : A →ₙₐ[k] Module.End k M)

/-- The submodule of the unitized action with the same carrier as a stable subspace. -/
def toUnitizedSubmodule (S : CompatibleSubmodule ρ) :
    letI := module ρ; Submodule (Unitization k A) M :=
  letI := module ρ
  { carrier := S.toSubmodule
    add_mem' := S.toSubmodule.add_mem
    zero_mem' := S.toSubmodule.zero_mem
    smul_mem' x m hm := by
      rw [smul_eq]
      exact S.toSubmodule.add_mem (S.toSubmodule.smul_mem _ hm)
        ((S.mem_toSubmodule).2 (S.action_mem x.snd ((S.mem_toSubmodule).1 hm))) }

/-- The stable subspace with the same carrier as a submodule of the unitized action. -/
def ofUnitizedSubmodule (p : letI := module ρ; Submodule (Unitization k A) M) :
    CompatibleSubmodule ρ :=
  letI := module ρ
  letI := isScalarTower ρ
  CompatibleSubmodule.ofStable (p.restrictScalars k) fun a m hm => by
    have h := p.smul_mem (a : Unitization k A) hm
    rwa [inr_smul] at h

/-- Stable `k`-subspaces of `ρ` are the submodules of the unitized action, with the same
carriers. -/
def submoduleOrderIso :
    CompatibleSubmodule ρ ≃o (letI := module ρ; Submodule (Unitization k A) M) :=
  letI := module ρ
  { toFun := toUnitizedSubmodule ρ
    invFun := ofUnitizedSubmodule ρ
    left_inv _ := CompatibleSubmodule.ext fun _ => Iff.rfl
    right_inv _ := rfl
    map_rel_iff' {S T} := by
      rw [← CompatibleSubmodule.toSubmodule_le_toSubmodule]
      exact Iff.rfl }

variable {ρ}

/-- Membership in the unitized submodule of a stable subspace. -/
@[simp] theorem mem_submoduleOrderIso {S : CompatibleSubmodule ρ} {m : M} :
    (letI := module ρ; m ∈ submoduleOrderIso ρ S) ↔ m ∈ S :=
  Iff.rfl

/-- Membership in the stable subspace of a unitized submodule. -/
@[simp] theorem mem_submoduleOrderIso_symm {p : letI := module ρ; Submodule (Unitization k A) M}
    {m : M} : m ∈ (submoduleOrderIso ρ).symm p ↔ (letI := module ρ; m ∈ p) :=
  Iff.rfl

/-- The carrier of the unitized submodule is the carrier of the stable subspace. -/
theorem coe_submoduleOrderIso (S : CompatibleSubmodule ρ) :
    (letI := module ρ; (submoduleOrderIso ρ S : Set M)) = (S.toSubmodule : Set M) :=
  rfl

/-- Forgetting the unitized scalars returns the stable subspace. -/
theorem restrictScalars_submoduleOrderIso (S : CompatibleSubmodule ρ) :
    (letI := module ρ; letI := isScalarTower ρ; (submoduleOrderIso ρ S).restrictScalars k) =
      S.toSubmodule :=
  rfl

/-- The stable subspace of a unitized submodule is its restriction of scalars to `k`. -/
theorem toSubmodule_submoduleOrderIso_symm (p : letI := module ρ; Submodule (Unitization k A) M) :
    ((submoduleOrderIso ρ).symm p).toSubmodule =
      (letI := module ρ; letI := isScalarTower ρ; p.restrictScalars k) :=
  CompatibleSubmodule.ofStable_toSubmodule _ _

@[simp] theorem submoduleOrderIso_symm_apply_apply (S : CompatibleSubmodule ρ) :
    (submoduleOrderIso ρ).symm (submoduleOrderIso ρ S) = S :=
  (submoduleOrderIso ρ).symm_apply_apply S

@[simp] theorem submoduleOrderIso_apply_symm_apply
    (p : letI := module ρ; Submodule (Unitization k A) M) :
    submoduleOrderIso ρ ((submoduleOrderIso ρ).symm p) = p :=
  (submoduleOrderIso ρ).apply_symm_apply p

/-- The inclusion order is unchanged. -/
theorem submoduleOrderIso_le_iff {S T : CompatibleSubmodule ρ} :
    (letI := module ρ; submoduleOrderIso ρ S ≤ submoduleOrderIso ρ T) ↔ S ≤ T :=
  (submoduleOrderIso ρ).le_iff_le

@[simp] theorem submoduleOrderIso_bot :
    (letI := module ρ; submoduleOrderIso ρ ⊥ = (⊥ : Submodule (Unitization k A) M)) :=
  letI := module ρ
  (submoduleOrderIso ρ).map_bot

@[simp] theorem submoduleOrderIso_top :
    (letI := module ρ; submoduleOrderIso ρ ⊤ = (⊤ : Submodule (Unitization k A) M)) :=
  letI := module ρ
  (submoduleOrderIso ρ).map_top

@[simp] theorem submoduleOrderIso_symm_bot :
    (submoduleOrderIso ρ).symm (letI := module ρ; (⊥ : Submodule (Unitization k A) M)) = ⊥ :=
  letI := module ρ
  (submoduleOrderIso ρ).symm.map_bot

@[simp] theorem submoduleOrderIso_symm_top :
    (submoduleOrderIso ρ).symm (letI := module ρ; (⊤ : Submodule (Unitization k A) M)) = ⊤ :=
  letI := module ρ
  (submoduleOrderIso ρ).symm.map_top

theorem submoduleOrderIso_inf (S T : CompatibleSubmodule ρ) :
    (letI := module ρ; submoduleOrderIso ρ (S ⊓ T) = submoduleOrderIso ρ S ⊓ submoduleOrderIso ρ T) :=
  letI := module ρ
  (submoduleOrderIso ρ).map_inf S T

theorem submoduleOrderIso_sup (S T : CompatibleSubmodule ρ) :
    (letI := module ρ; submoduleOrderIso ρ (S ⊔ T) = submoduleOrderIso ρ S ⊔ submoduleOrderIso ρ T) :=
  letI := module ρ
  (submoduleOrderIso ρ).map_sup S T

theorem submoduleOrderIso_sInf (s : Set (CompatibleSubmodule ρ)) :
    (letI := module ρ; submoduleOrderIso ρ (sInf s) = ⨅ S ∈ s, submoduleOrderIso ρ S) :=
  letI := module ρ
  (submoduleOrderIso ρ).map_sInf s

theorem submoduleOrderIso_sSup (s : Set (CompatibleSubmodule ρ)) :
    (letI := module ρ; submoduleOrderIso ρ (sSup s) = ⨆ S ∈ s, submoduleOrderIso ρ S) :=
  letI := module ρ
  (submoduleOrderIso ρ).map_sSup s

theorem submoduleOrderIso_iInf {ι : Sort*} (S : ι → CompatibleSubmodule ρ) :
    (letI := module ρ; submoduleOrderIso ρ (⨅ i, S i) = ⨅ i, submoduleOrderIso ρ (S i)) :=
  letI := module ρ
  (submoduleOrderIso ρ).map_iInf S

theorem submoduleOrderIso_iSup {ι : Sort*} (S : ι → CompatibleSubmodule ρ) :
    (letI := module ρ; submoduleOrderIso ρ (⨆ i, S i) = ⨆ i, submoduleOrderIso ρ (S i)) :=
  letI := module ρ
  (submoduleOrderIso ρ).map_iSup S

end OrderIso

section Restrict

variable {ρ : A →ₙₐ[k] Module.End k M} (S : CompatibleSubmodule ρ)

/-- The unitized action homomorphism of `ρ` maps a stable subspace into itself. -/
theorem endHom_mem (x : Unitization k A) {m : M} (hm : m ∈ S.toSubmodule) :
    endHom ρ x m ∈ S.toSubmodule :=
  letI := module ρ
  (submoduleOrderIso ρ S).smul_mem x hm

/-- Unitizing the restricted original action restricts the unitized action homomorphism. -/
theorem endHom_restrictAction (x : Unitization k A) :
    endHom S.restrictAction x = (endHom ρ x).restrict fun _ hm => endHom_mem S x hm :=
  rfl

/-- The unitization of the restricted original action, on underlying elements. -/
theorem restrictAction_smul_coe (x : Unitization k A) (m : S.toSubmodule) :
    ((letI := module S.restrictAction; x • m : S.toSubmodule) : M) =
      (letI := module ρ; x • (m : M)) :=
  rfl

/-- The unitization of the restricted original action is the restricted unitized action: the
identity on elements, as a unitized linear equivalence. -/
def restrictEquiv :
    letI := module ρ
    letI := module S.restrictAction
    S.toSubmodule ≃ₗ[Unitization k A] submoduleOrderIso ρ S :=
  letI := module ρ
  letI := module S.restrictAction
  { toFun m := ⟨m, m.2⟩
    invFun m := ⟨m, m.2⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
    left_inv _ := rfl
    right_inv _ := rfl }

@[simp] theorem coe_restrictEquiv_apply (m : S.toSubmodule) :
    ((letI := module ρ; letI := module S.restrictAction;
      restrictEquiv S m : submoduleOrderIso ρ S) : M) = m :=
  rfl

@[simp] theorem coe_restrictEquiv_symm_apply (m : letI := module ρ; submoduleOrderIso ρ S) :
    (((letI := module ρ; letI := module S.restrictAction;
      (restrictEquiv S).symm m) : S.toSubmodule) : M) = m :=
  rfl

/-- The inclusions agree: the unitized inclusion after `restrictEquiv` is the `k`-linear
inclusion of the stable subspace. -/
theorem subtype_restrictEquiv (m : S.toSubmodule) :
    (letI := module ρ; letI := module S.restrictAction;
      (submoduleOrderIso ρ S).subtype (restrictEquiv S m)) = S.toSubmodule.subtype m :=
  rfl

end Restrict

section Quotient

variable {ρ : A →ₙₐ[k] Module.End k M} (S : CompatibleSubmodule ρ)

/-- Unitizing the quotient original action descends the unitized action homomorphism. -/
theorem endHom_quotientAction (x : Unitization k A) :
    endHom S.quotientAction x =
      S.toSubmodule.mapQ S.toSubmodule (endHom ρ x) fun _ hm => endHom_mem S x hm := by
  ext m
  rfl

/-- The unitization of the quotient original action, through the quotient map. -/
theorem quotientAction_smul_mkQ (x : Unitization k A) (m : M) :
    (letI := module S.quotientAction; x • S.toSubmodule.mkQ m) =
      S.toSubmodule.mkQ (letI := module ρ; x • m) :=
  rfl

/-- The unitization of the quotient original action is the quotient unitized action: the
identity on the classes of the same elements, as a unitized linear equivalence. -/
def quotientEquiv :
    letI := module ρ
    letI := module S.quotientAction
    (M ⧸ S.toSubmodule) ≃ₗ[Unitization k A] M ⧸ submoduleOrderIso ρ S :=
  letI := module ρ
  letI := module S.quotientAction
  letI := isScalarTower ρ
  { Submodule.Quotient.restrictScalarsEquiv k (submoduleOrderIso ρ S) with
    map_smul' _ q := Submodule.Quotient.induction_on _ q fun _ => rfl }

@[simp] theorem quotientEquiv_mkQ (m : M) :
    (letI := module ρ; letI := module S.quotientAction;
      quotientEquiv S (S.toSubmodule.mkQ m)) =
      (letI := module ρ; (submoduleOrderIso ρ S).mkQ m) :=
  rfl

@[simp] theorem quotientEquiv_symm_mkQ (m : M) :
    (letI := module ρ; letI := module S.quotientAction;
      (quotientEquiv S).symm ((submoduleOrderIso ρ S).mkQ m)) = S.toSubmodule.mkQ m :=
  rfl

end Quotient

section ZeroAction

variable {k : Type u} {A : Type v} {M : Type w}
  [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
  [AddCommGroup M] [Module k M]

/-- For the zero original action, every `k`-subspace is a submodule of the unitized action,
with the same carrier. -/
def zeroSubmoduleOrderIso :
    Submodule k M ≃o
      (letI := module (0 : A →ₙₐ[k] Module.End k M); Submodule (Unitization k A) M) :=
  (CompatibleSubmodule.zeroOrderIso (A := A)).symm.trans
    (submoduleOrderIso (0 : A →ₙₐ[k] Module.End k M))

@[simp] theorem mem_zeroSubmoduleOrderIso {S : Submodule k M} {m : M} :
    (letI := module (0 : A →ₙₐ[k] Module.End k M); m ∈ zeroSubmoduleOrderIso (A := A) S) ↔ m ∈ S :=
  Iff.rfl

end ZeroAction

/-! ### The zero action of `ℂ` on the nonzero complex vector space `ℂ` -/

section Complex

/-- The zero subspace and the whole space are unitized submodules, and they differ. -/
example :
    (letI := module (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ);
      submoduleOrderIso 0 ⊥ = (⊥ : Submodule (Unitization ℂ ℂ) ℂ) ∧
        submoduleOrderIso 0 ⊤ = (⊤ : Submodule (Unitization ℂ ℂ) ℂ) ∧
        (⊥ : Submodule (Unitization ℂ ℂ) ℂ) ≠ ⊤) :=
  letI := module (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ)
  ⟨submoduleOrderIso_bot, submoduleOrderIso_top, bot_ne_top⟩

/-- The quotient by the whole space is permitted, and it is zero. -/
example :
    Subsingleton (letI := module (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ);
      ℂ ⧸ submoduleOrderIso (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ) ⊤) :=
  letI := module (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ)
  Submodule.Quotient.subsingleton_iff.2 submoduleOrderIso_top

/-- On the whole space, the unitization of the restricted zero action is multiplication by the
scalar coordinate, and `1 : ℂ` still acts by zero. -/
example (x : Unitization ℂ ℂ)
    (m : (⊤ : CompatibleSubmodule (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ)).toSubmodule) :
    ((letI := module (⊤ : CompatibleSubmodule (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ)).restrictAction;
      x • m : (⊤ : CompatibleSubmodule (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ)).toSubmodule) : ℂ) =
        x.fst * m ∧
    ((letI := module (⊤ : CompatibleSubmodule (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ)).restrictAction;
      ((1 : ℂ) : Unitization ℂ ℂ) • m :
        (⊤ : CompatibleSubmodule (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ)).toSubmodule) : ℂ) = 0 :=
  ⟨(restrictAction_smul_coe _ x m).trans (zero_smul_eq x (m : ℂ)),
    (restrictAction_smul_coe _ _ m).trans (zero_inr_smul 1 (m : ℂ))⟩

end Complex

/-! ### Field specialization

A field `K`, a possibly noncommutative and nonunital associative `K`-algebra `A` with bilinear
multiplication, and a `K`-vector space in an independent universe. -/

section Field

variable {K : Type u} {A : Type v} {V : Type w}
  [Field K] [NonUnitalRing A] [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
  [AddCommGroup V] [Module K V] (ρ : A →ₙₐ[K] Module.End K V)

example : CompatibleSubmodule ρ ≃o (letI := module ρ; Submodule (Unitization K A) V) :=
  submoduleOrderIso ρ

example (S : CompatibleSubmodule ρ) :
    letI := module ρ
    letI := module S.restrictAction
    S.toSubmodule ≃ₗ[Unitization K A] submoduleOrderIso ρ S :=
  restrictEquiv S

example (S : CompatibleSubmodule ρ) :
    letI := module ρ
    letI := module S.quotientAction
    (V ⧸ S.toSubmodule) ≃ₗ[Unitization K A] V ⧸ submoduleOrderIso ρ S :=
  quotientEquiv S

end Field

end CompatibleUnitization

end Langlands.Algebra
