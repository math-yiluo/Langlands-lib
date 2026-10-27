import Langlands.Algebra.CompatibleNonUnitalAction
import Mathlib.Algebra.Module.Submodule.Invariant
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Basic.Complex.Basic

/-!
# Stable subspaces, restricted actions and quotient actions of a compatible action

Renard (9 July 2026): module conventions on printed pp. 5–6, I.2.1 on printed p. 14, and the
reduction at the start of the proof of the Schur lemma B.II on printed p. 272. For an actual
compatible action `ρ : A →ₙₐ[k] Module.End k M` of a possibly noncommutative and nonunital
algebra, this module bundles the actual `k`-subspaces of `M` stable under every `ρ a`, with
their complete lattice inherited from `Submodule k M`, and constructs the restricted and
quotient actions, kernels, images, inverse and direct images, restrictions and descents of
linear intertwiners. Ambient actions and intertwiners are obtained through the published
bridge `Langlands.Algebra.CompatibleNonUnitalAction`. No unit, unit law, nondegeneracy,
simplicity, exactness or finiteness is assumed or asserted.
-/

set_option autoImplicit false

namespace Langlands.Algebra

universe u v w x y

section Stability

variable {k : Type u} {A : Type v} {M : Type w}
  [CommRing k] [NonUnitalRing A] [Module k A] [AddCommGroup M] [Module k M]

/-- Stability of an actual `k`-subspace under a compatible action: every `ρ a` maps `S`
into `S`. -/
def IsStableSubmodule (ρ : A →ₙₐ[k] Module.End k M) (S : Submodule k M) : Prop :=
  ∀ (a : A) (m : M), m ∈ S → ρ a m ∈ S

variable {ρ : A →ₙₐ[k] Module.End k M} {S T : Submodule k M}

theorem isStableSubmodule_iff_le_comap :
    IsStableSubmodule ρ S ↔ ∀ a : A, S ≤ S.comap (ρ a) :=
  ⟨fun h a m hm => h a m hm, fun h a _ hm => h a hm⟩

theorem isStableSubmodule_iff_map_le :
    IsStableSubmodule ρ S ↔ ∀ a : A, S.map (ρ a) ≤ S := by
  simp only [Submodule.map_le_iff_le_comap, isStableSubmodule_iff_le_comap]

/-- Stability is membership in Mathlib's invariant-subspace sublattice of every `ρ a`. -/
theorem isStableSubmodule_iff_mem_invtSubmodule :
    IsStableSubmodule ρ S ↔ ∀ a : A, S ∈ Module.End.invtSubmodule (ρ a) :=
  isStableSubmodule_iff_le_comap

namespace IsStableSubmodule

theorem bot : IsStableSubmodule ρ (⊥ : Submodule k M) :=
  isStableSubmodule_iff_mem_invtSubmodule.2 fun a => Module.End.invtSubmodule.bot_mem (ρ a)

theorem top : IsStableSubmodule ρ (⊤ : Submodule k M) :=
  isStableSubmodule_iff_mem_invtSubmodule.2 fun a => Module.End.invtSubmodule.top_mem (ρ a)

theorem inf (hS : IsStableSubmodule ρ S) (hT : IsStableSubmodule ρ T) :
    IsStableSubmodule ρ (S ⊓ T) :=
  isStableSubmodule_iff_mem_invtSubmodule.2 fun a =>
    Module.End.invtSubmodule.inf_mem (isStableSubmodule_iff_mem_invtSubmodule.1 hS a)
      (isStableSubmodule_iff_mem_invtSubmodule.1 hT a)

theorem sup (hS : IsStableSubmodule ρ S) (hT : IsStableSubmodule ρ T) :
    IsStableSubmodule ρ (S ⊔ T) :=
  isStableSubmodule_iff_mem_invtSubmodule.2 fun a =>
    Module.End.invtSubmodule.sup_mem (isStableSubmodule_iff_mem_invtSubmodule.1 hS a)
      (isStableSubmodule_iff_mem_invtSubmodule.1 hT a)

theorem sInf {s : Set (Submodule k M)} (hs : ∀ S ∈ s, IsStableSubmodule ρ S) :
    IsStableSubmodule ρ (sInf s) := fun a m hm =>
  Submodule.mem_sInf.2 fun S hS => hs S hS a m (Submodule.mem_sInf.1 hm S hS)

theorem sSup {s : Set (Submodule k M)} (hs : ∀ S ∈ s, IsStableSubmodule ρ S) :
    IsStableSubmodule ρ (sSup s) :=
  isStableSubmodule_iff_le_comap.2 fun a => sSup_le fun S hS =>
    (isStableSubmodule_iff_le_comap.1 (hs S hS) a).trans (Submodule.comap_mono (le_sSup hS))

end IsStableSubmodule

end Stability

/-- An actual `k`-subspace of `M` stable under the compatible action `ρ`. -/
structure CompatibleSubmodule {k : Type u} {A : Type v} {M : Type w}
    [CommRing k] [NonUnitalRing A] [Module k A] [AddCommGroup M] [Module k M]
    (ρ : A →ₙₐ[k] Module.End k M) extends Submodule k M where
  /-- Stability of the underlying subspace under every `ρ a`. -/
  action_mem' : ∀ (a : A) (m : M), m ∈ carrier → ρ a m ∈ carrier

attribute [coe] CompatibleSubmodule.toSubmodule

namespace CompatibleSubmodule

section Lattice

variable {k : Type u} {A : Type v} {M : Type w}
  [CommRing k] [NonUnitalRing A] [Module k A] [AddCommGroup M] [Module k M]
  {ρ : A →ₙₐ[k] Module.End k M}

instance : SetLike (CompatibleSubmodule ρ) M where
  coe S := S.carrier
  coe_injective S T h := by
    cases S
    cases T
    congr
    exact SetLike.coe_injective h

/-- The inherited inclusion order. -/
instance : PartialOrder (CompatibleSubmodule ρ) := .ofSetLike (CompatibleSubmodule ρ) M

instance : AddSubgroupClass (CompatibleSubmodule ρ) M where
  add_mem {S} _ _ := S.add_mem'
  zero_mem S := S.zero_mem'
  neg_mem {S} m hm := show -m ∈ S.toSubmodule from neg_mem hm

instance : SMulMemClass (CompatibleSubmodule ρ) k M where
  smul_mem {S} c _ hm := S.smul_mem' c hm

instance (priority := mid) : CoeOut (CompatibleSubmodule ρ) (Submodule k M) :=
  ⟨toSubmodule⟩

variable (S T : CompatibleSubmodule ρ)

@[simp, norm_cast] theorem coe_toSubmodule : (S.toSubmodule : Set M) = S := rfl

@[simp] theorem mem_toSubmodule {m : M} : m ∈ S.toSubmodule ↔ m ∈ S := Iff.rfl

theorem mem_carrier {m : M} : m ∈ S.carrier ↔ m ∈ S := Iff.rfl

/-- Bundle an actual stable subspace. -/
def ofStable (S : Submodule k M) (hS : IsStableSubmodule ρ S) : CompatibleSubmodule ρ where
  toSubmodule := S
  action_mem' := hS

@[simp] theorem ofStable_toSubmodule (S : Submodule k M) (hS : IsStableSubmodule ρ S) :
    (ofStable S hS).toSubmodule = S := rfl

@[simp] theorem mem_ofStable {S : Submodule k M} {hS : IsStableSubmodule ρ S} {m : M} :
    m ∈ ofStable S hS ↔ m ∈ S := Iff.rfl

theorem isStable : IsStableSubmodule ρ S.toSubmodule := S.action_mem'

theorem action_mem (a : A) {m : M} (hm : m ∈ S) : ρ a m ∈ S := S.action_mem' a m hm

theorem le_comap_action (a : A) : S.toSubmodule ≤ S.toSubmodule.comap (ρ a) :=
  fun _ hm => S.action_mem a hm

theorem toSubmodule_injective :
    Function.Injective (toSubmodule : CompatibleSubmodule ρ → Submodule k M) := by
  intro S T h
  cases S
  cases T
  congr

/-- Extensionality by membership. -/
@[ext] theorem ext {S T : CompatibleSubmodule ρ} (h : ∀ m, m ∈ S ↔ m ∈ T) : S = T :=
  SetLike.ext h

@[simp] theorem toSubmodule_inj {S T : CompatibleSubmodule ρ} :
    S.toSubmodule = T.toSubmodule ↔ S = T :=
  toSubmodule_injective.eq_iff

@[simp, norm_cast] theorem toSubmodule_le_toSubmodule {S T : CompatibleSubmodule ρ} :
    S.toSubmodule ≤ T.toSubmodule ↔ S ≤ T := Iff.rfl

@[simp, norm_cast] theorem toSubmodule_lt_toSubmodule {S T : CompatibleSubmodule ρ} :
    S.toSubmodule < T.toSubmodule ↔ S < T := Iff.rfl

/-- The subspaces underlying bundled stable subspaces are exactly the stable subspaces. -/
theorem exists_toSubmodule_eq_iff (S : Submodule k M) :
    (∃ T : CompatibleSubmodule ρ, T.toSubmodule = S) ↔ IsStableSubmodule ρ S :=
  ⟨by rintro ⟨T, rfl⟩; exact T.isStable, fun h => ⟨ofStable S h, rfl⟩⟩

/-! ### Lattice operations, computed on underlying subspaces -/

instance : Bot (CompatibleSubmodule ρ) := ⟨ofStable ⊥ IsStableSubmodule.bot⟩

instance : Top (CompatibleSubmodule ρ) := ⟨ofStable ⊤ IsStableSubmodule.top⟩

instance : Min (CompatibleSubmodule ρ) :=
  ⟨fun S T => ofStable (S.toSubmodule ⊓ T.toSubmodule) (S.isStable.inf T.isStable)⟩

instance : Max (CompatibleSubmodule ρ) :=
  ⟨fun S T => ofStable (S.toSubmodule ⊔ T.toSubmodule) (S.isStable.sup T.isStable)⟩

instance : InfSet (CompatibleSubmodule ρ) :=
  ⟨fun s => ofStable (sInf (toSubmodule '' s))
    (IsStableSubmodule.sInf (by rintro _ ⟨S, -, rfl⟩; exact S.isStable))⟩

instance : SupSet (CompatibleSubmodule ρ) :=
  ⟨fun s => ofStable (sSup (toSubmodule '' s))
    (IsStableSubmodule.sSup (by rintro _ ⟨S, -, rfl⟩; exact S.isStable))⟩

@[simp, norm_cast] theorem bot_toSubmodule :
    (⊥ : CompatibleSubmodule ρ).toSubmodule = ⊥ := rfl

@[simp, norm_cast] theorem top_toSubmodule :
    (⊤ : CompatibleSubmodule ρ).toSubmodule = ⊤ := rfl

@[simp, norm_cast] theorem inf_toSubmodule :
    (S ⊓ T).toSubmodule = S.toSubmodule ⊓ T.toSubmodule := rfl

@[simp, norm_cast] theorem sup_toSubmodule :
    (S ⊔ T).toSubmodule = S.toSubmodule ⊔ T.toSubmodule := rfl

@[simp] theorem sInf_toSubmodule (s : Set (CompatibleSubmodule ρ)) :
    (sInf s).toSubmodule = sInf (toSubmodule '' s) := rfl

@[simp] theorem sSup_toSubmodule (s : Set (CompatibleSubmodule ρ)) :
    (sSup s).toSubmodule = sSup (toSubmodule '' s) := rfl

theorem sInf_toSubmodule_eq_iInf (s : Set (CompatibleSubmodule ρ)) :
    (sInf s).toSubmodule = ⨅ S ∈ s, S.toSubmodule :=
  sInf_image

theorem sSup_toSubmodule_eq_iSup (s : Set (CompatibleSubmodule ρ)) :
    (sSup s).toSubmodule = ⨆ S ∈ s, S.toSubmodule :=
  sSup_image

/-- The complete lattice of stable subspaces, transported from `Submodule k M`. -/
instance : CompleteLattice (CompatibleSubmodule ρ) :=
  toSubmodule_injective.completeLattice toSubmodule .rfl .rfl (fun _ _ => rfl) (fun _ _ => rfl)
    sSup_toSubmodule_eq_iSup sInf_toSubmodule_eq_iInf rfl rfl

/-- Forgetting to the underlying subspace is an actual complete lattice homomorphism: it
preserves arbitrary infima and suprema. -/
def toSubmoduleHom : CompleteLatticeHom (CompatibleSubmodule ρ) (Submodule k M) where
  toFun := toSubmodule
  map_sInf' _ := rfl
  map_sSup' _ := rfl

@[simp] theorem toSubmoduleHom_apply : toSubmoduleHom S = S.toSubmodule := rfl

@[simp] theorem iInf_toSubmodule {ι : Sort*} (S : ι → CompatibleSubmodule ρ) :
    (⨅ i, S i).toSubmodule = ⨅ i, (S i).toSubmodule :=
  map_iInf toSubmoduleHom S

@[simp] theorem iSup_toSubmodule {ι : Sort*} (S : ι → CompatibleSubmodule ρ) :
    (⨆ i, S i).toSubmodule = ⨆ i, (S i).toSubmodule :=
  map_iSup toSubmoduleHom S

@[simp] theorem mem_bot {m : M} : m ∈ (⊥ : CompatibleSubmodule ρ) ↔ m = 0 :=
  Submodule.mem_bot k

@[simp] theorem mem_top (m : M) : m ∈ (⊤ : CompatibleSubmodule ρ) :=
  Submodule.mem_top

@[simp] theorem mem_inf {m : M} : m ∈ S ⊓ T ↔ m ∈ S ∧ m ∈ T := Iff.rfl

/-- The carrier of a sum consists of the sums of a vector of `S` and a vector of `T`. -/
theorem mem_sup {m : M} : m ∈ S ⊔ T ↔ ∃ y ∈ S, ∃ z ∈ T, y + z = m :=
  Submodule.mem_sup

@[simp] theorem mem_sInf {s : Set (CompatibleSubmodule ρ)} {m : M} :
    m ∈ sInf s ↔ ∀ S ∈ s, m ∈ S := by
  rw [← mem_toSubmodule, sInf_toSubmodule_eq_iInf]
  simp [Submodule.mem_iInf]

@[simp] theorem mem_iInf {ι : Sort*} {S : ι → CompatibleSubmodule ρ} {m : M} :
    m ∈ ⨅ i, S i ↔ ∀ i, m ∈ S i := by
  rw [← mem_toSubmodule, iInf_toSubmodule, Submodule.mem_iInf]
  rfl

/-- The carrier of an arbitrary supremum is the span of the union of the carriers. -/
theorem sSup_toSubmodule_eq_span (s : Set (CompatibleSubmodule ρ)) :
    (sSup s).toSubmodule = Submodule.span k (⋃ S ∈ s, (S : Set M)) := by
  rw [sSup_toSubmodule_eq_iSup, Submodule.span_iUnion₂]
  simp only [← coe_toSubmodule, Submodule.span_eq]

/-- The carrier of an indexed supremum is the span of the union of the carriers. -/
theorem iSup_toSubmodule_eq_span {ι : Sort*} (S : ι → CompatibleSubmodule ρ) :
    (⨆ i, S i).toSubmodule = Submodule.span k (⋃ i, (S i : Set M)) := by
  rw [iSup_toSubmodule, Submodule.iSup_eq_span]
  rfl

/-- Vectors of an indexed supremum are the finite sums of vectors of the members. -/
theorem mem_iSup_iff_exists_finsupp {ι : Type*} (S : ι → CompatibleSubmodule ρ) (m : M) :
    m ∈ ⨆ i, S i ↔ ∃ f : ι →₀ M, (∀ i, f i ∈ S i) ∧ (f.sum fun _ x => x) = m := by
  rw [← mem_toSubmodule, iSup_toSubmodule]
  exact Submodule.mem_iSup_iff_exists_finsupp _ m

/-! ### Comparison with the ambient stable additive subgroups -/

/-- The stable additive subgroup underlying `S`, for the ambient action
`NonUnitalModule.ofLinearEndHom ρ`. This map is injective and monotone; it is not surjective in
general, because a stable additive subgroup need not be a `k`-subspace. -/
def toNonUnitalSubmodule :
    letI := NonUnitalModule.ofLinearEndHom ρ
    NonUnitalSubmodule A M :=
  letI := NonUnitalModule.ofLinearEndHom ρ
  { toAddSubgroup := S.toSubmodule.toAddSubgroup
    smul_mem' := fun a _ hm => S.action_mem a hm }

@[simp] theorem mem_toNonUnitalSubmodule {m : M} :
    (letI := NonUnitalModule.ofLinearEndHom ρ
     m ∈ S.toNonUnitalSubmodule) ↔ m ∈ S := Iff.rfl

theorem toNonUnitalSubmodule_le_iff :
    (letI := NonUnitalModule.ofLinearEndHom ρ
     S.toNonUnitalSubmodule ≤ T.toNonUnitalSubmodule) ↔ S ≤ T := Iff.rfl

theorem toNonUnitalSubmodule_injective :
    Function.Injective (fun S : CompatibleSubmodule ρ => S.toNonUnitalSubmodule) := by
  intro S T h
  ext m
  exact (mem_toNonUnitalSubmodule S).symm.trans
    ((SetLike.ext_iff.1 h m).trans (mem_toNonUnitalSubmodule T))

end Lattice

/-! ### Restricted and quotient actions -/

section Actions

variable {k : Type u} {A : Type v} {M : Type w}
  [CommRing k] [NonUnitalRing A] [Module k A] [AddCommGroup M] [Module k M]
  {ρ : A →ₙₐ[k] Module.End k M} (S : CompatibleSubmodule ρ)

/-- The actual restriction of `ρ` to a stable subspace. -/
def restrictAction : A →ₙₐ[k] Module.End k S.toSubmodule where
  toFun a := (ρ a).restrict (S.isStable a)
  map_smul' c a := LinearMap.ext fun m => Subtype.ext <|
    congrArg (fun f : Module.End k M => f m) (map_smul ρ c a)
  map_zero' := LinearMap.ext fun m => Subtype.ext <|
    congrArg (fun f : Module.End k M => f m) (map_zero ρ)
  map_add' a b := LinearMap.ext fun m => Subtype.ext <|
    congrArg (fun f : Module.End k M => f m) (map_add ρ a b)
  map_mul' a b := LinearMap.ext fun m => Subtype.ext <|
    congrArg (fun f : Module.End k M => f m) (map_mul ρ a b)

/-- The restricted action formula. -/
@[simp] theorem restrictAction_apply_coe (a : A) (m : S.toSubmodule) :
    ((S.restrictAction a m : S.toSubmodule) : M) = ρ a m := rfl

theorem restrictAction_apply (a : A) (m : S.toSubmodule) :
    S.restrictAction a m = ⟨ρ a m, S.action_mem a m.2⟩ := rfl

theorem restrictAction_eq_restrict (a : A) :
    S.restrictAction a = (ρ a).restrict (S.isStable a) := rfl

/-- Well-definedness on cosets: congruent vectors have congruent images. -/
theorem action_sub_mem (a : A) {m m' : M} (h : m - m' ∈ S) : ρ a m - ρ a m' ∈ S := by
  rw [← map_sub]
  exact S.action_mem a h

/-- Well-definedness of the quotient formula. -/
theorem mkQ_action_eq_of_mkQ_eq (a : A) {m m' : M}
    (h : S.toSubmodule.mkQ m = S.toSubmodule.mkQ m') :
    S.toSubmodule.mkQ (ρ a m) = S.toSubmodule.mkQ (ρ a m') := by
  simp only [Submodule.mkQ_apply, Submodule.Quotient.eq] at h ⊢
  exact S.action_sub_mem a h

/-- The actual action on the vector-space quotient `M ⧸ S`. -/
def quotientAction : A →ₙₐ[k] Module.End k (M ⧸ S.toSubmodule) where
  toFun a := S.toSubmodule.mapQ S.toSubmodule (ρ a) (S.le_comap_action a)
  map_smul' c a := Submodule.linearMap_qext _ <| LinearMap.ext fun m => by
    change S.toSubmodule.mkQ (ρ (c • a) m) = c • S.toSubmodule.mkQ (ρ a m)
    rw [map_smul, LinearMap.smul_apply, map_smul]
  map_zero' := Submodule.linearMap_qext _ <| LinearMap.ext fun m => by
    change S.toSubmodule.mkQ (ρ 0 m) = 0
    rw [map_zero, LinearMap.zero_apply, map_zero]
  map_add' a b := Submodule.linearMap_qext _ <| LinearMap.ext fun m => by
    change S.toSubmodule.mkQ (ρ (a + b) m) =
      S.toSubmodule.mkQ (ρ a m) + S.toSubmodule.mkQ (ρ b m)
    rw [map_add, LinearMap.add_apply, map_add]
  map_mul' a b := Submodule.linearMap_qext _ <| LinearMap.ext fun m => by
    change S.toSubmodule.mkQ (ρ (a * b) m) = S.toSubmodule.mkQ (ρ a (ρ b m))
    rw [map_mul, Module.End.mul_apply]

/-- The quotient action formula `ρ_{M/S}(a)(m + S) = ρ(a)(m) + S`. -/
theorem quotientAction_apply_mkQ (a : A) (m : M) :
    S.quotientAction a (S.toSubmodule.mkQ m) = S.toSubmodule.mkQ (ρ a m) := rfl

@[simp] theorem quotientAction_apply_mk (a : A) (m : M) :
    S.quotientAction a (Submodule.Quotient.mk m) = Submodule.Quotient.mk (ρ a m) := rfl

theorem quotientAction_eq_mapQ (a : A) :
    S.quotientAction a = S.toSubmodule.mapQ S.toSubmodule (ρ a) (S.le_comap_action a) := rfl

theorem quotientAction_comp_mkQ (a : A) :
    S.quotientAction a ∘ₗ S.toSubmodule.mkQ = S.toSubmodule.mkQ ∘ₗ ρ a :=
  Submodule.mapQ_mkQ S.toSubmodule S.toSubmodule (ρ a) (h := S.le_comap_action a)

/-- The quotient formula determines the quotient action. -/
theorem eq_quotientAction (a : A) (φ : Module.End k (M ⧸ S.toSubmodule))
    (hφ : ∀ m, φ (S.toSubmodule.mkQ m) = S.toSubmodule.mkQ (ρ a m)) :
    φ = S.quotientAction a :=
  Submodule.linearMap_qext _ (LinearMap.ext hφ)

/-- The actual subtype inclusion as a linear intertwiner. -/
def subtypeIntertwiner : LinearIntertwiner S.restrictAction ρ where
  toLinearMap := S.toSubmodule.subtype
  map_action' _ _ := rfl

@[simp] theorem subtypeIntertwiner_apply (m : S.toSubmodule) :
    S.subtypeIntertwiner m = m := rfl

@[simp] theorem subtypeIntertwiner_toLinearMap :
    S.subtypeIntertwiner.toLinearMap = S.toSubmodule.subtype := rfl

theorem subtype_restrictAction (a : A) (m : S.toSubmodule) :
    S.toSubmodule.subtype (S.restrictAction a m) = ρ a (S.toSubmodule.subtype m) := rfl

theorem subtype_comp_restrictAction (a : A) :
    S.toSubmodule.subtype ∘ₗ S.restrictAction a = ρ a ∘ₗ S.toSubmodule.subtype := rfl

/-- The actual quotient projection as a linear intertwiner. -/
def mkQIntertwiner : LinearIntertwiner ρ S.quotientAction where
  toLinearMap := S.toSubmodule.mkQ
  map_action' _ _ := rfl

@[simp] theorem mkQIntertwiner_apply (m : M) :
    S.mkQIntertwiner m = S.toSubmodule.mkQ m := rfl

@[simp] theorem mkQIntertwiner_toLinearMap :
    S.mkQIntertwiner.toLinearMap = S.toSubmodule.mkQ := rfl

theorem mkQ_action (a : A) (m : M) :
    S.toSubmodule.mkQ (ρ a m) = S.quotientAction a (S.toSubmodule.mkQ m) := rfl

/-! ### The corresponding ambient actions, through the published bridge -/

/-- The ambient action of `A` on `S` given by `restrictAction`. Not an instance. -/
abbrev restrictNonUnitalModule : NonUnitalModule A S.toSubmodule :=
  NonUnitalModule.ofLinearEndHom S.restrictAction

theorem restrictNonUnitalModule_smul_coe (a : A) (m : S.toSubmodule) :
    (((letI := S.restrictNonUnitalModule; a • m) : S.toSubmodule) : M) = ρ a m := rfl

theorem restrictNonUnitalModule_isScalarTower :
    letI := S.restrictNonUnitalModule
    IsScalarTower k A S.toSubmodule :=
  NonUnitalModule.ofLinearEndHom_isScalarTower S.restrictAction

theorem restrictNonUnitalModule_smulCommClass :
    letI := S.restrictNonUnitalModule
    SMulCommClass k A S.toSubmodule :=
  NonUnitalModule.ofLinearEndHom_smulCommClass S.restrictAction

/-- The ambient action of `A` on `M ⧸ S` given by `quotientAction`. Not an instance. -/
abbrev quotientNonUnitalModule : NonUnitalModule A (M ⧸ S.toSubmodule) :=
  NonUnitalModule.ofLinearEndHom S.quotientAction

theorem quotientNonUnitalModule_smul_mk (a : A) (m : M) :
    (letI := S.quotientNonUnitalModule
     a • (Submodule.Quotient.mk m : M ⧸ S.toSubmodule)) = Submodule.Quotient.mk (ρ a m) := rfl

theorem quotientNonUnitalModule_isScalarTower :
    letI := S.quotientNonUnitalModule
    IsScalarTower k A (M ⧸ S.toSubmodule) :=
  NonUnitalModule.ofLinearEndHom_isScalarTower S.quotientAction

theorem quotientNonUnitalModule_smulCommClass :
    letI := S.quotientNonUnitalModule
    SMulCommClass k A (M ⧸ S.toSubmodule) :=
  NonUnitalModule.ofLinearEndHom_smulCommClass S.quotientAction

/-- The subtype inclusion as an actual ambient intertwiner, with underlying map `S.subtype`. -/
def subtypeNonUnitalModuleHom :
    letI := S.restrictNonUnitalModule
    letI := NonUnitalModule.ofLinearEndHom ρ
    NonUnitalModuleHom A S.toSubmodule M :=
  S.subtypeIntertwiner.toNonUnitalModuleHom

theorem subtypeNonUnitalModuleHom_apply (m : S.toSubmodule) :
    (letI := S.restrictNonUnitalModule
     letI := NonUnitalModule.ofLinearEndHom ρ
     S.subtypeNonUnitalModuleHom m) = (m : M) := rfl

/-- The quotient projection as an actual ambient intertwiner, with underlying map `S.mkQ`. -/
def mkQNonUnitalModuleHom :
    letI := NonUnitalModule.ofLinearEndHom ρ
    letI := S.quotientNonUnitalModule
    NonUnitalModuleHom A M (M ⧸ S.toSubmodule) :=
  S.mkQIntertwiner.toNonUnitalModuleHom

theorem mkQNonUnitalModuleHom_apply (m : M) :
    (letI := NonUnitalModule.ofLinearEndHom ρ
     letI := S.quotientNonUnitalModule
     S.mkQNonUnitalModuleHom m) = S.toSubmodule.mkQ m := rfl

end Actions

end CompatibleSubmodule

/-! ### Kernels, images, inverse and direct images -/

section Images

variable {k : Type u} {A : Type v} {M : Type w} {N : Type x} {P : Type y}
  [CommRing k] [NonUnitalRing A] [Module k A]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N] [AddCommGroup P] [Module k P]
  {ρ : A →ₙₐ[k] Module.End k M} {σ : A →ₙₐ[k] Module.End k N}
  {τ : A →ₙₐ[k] Module.End k P}

namespace LinearIntertwiner

/-- The stable kernel of a linear intertwiner. -/
def ker (f : LinearIntertwiner ρ σ) : CompatibleSubmodule ρ :=
  CompatibleSubmodule.ofStable (LinearMap.ker f.toLinearMap) fun a m hm => by
    rw [LinearMap.mem_ker] at hm ⊢
    rw [f.map_action', hm, map_zero]

@[simp] theorem ker_toSubmodule (f : LinearIntertwiner ρ σ) :
    f.ker.toSubmodule = LinearMap.ker f.toLinearMap := rfl

@[simp] theorem mem_ker (f : LinearIntertwiner ρ σ) {m : M} : m ∈ f.ker ↔ f m = 0 :=
  LinearMap.mem_ker

/-- The stable image of a linear intertwiner. -/
def range (f : LinearIntertwiner ρ σ) : CompatibleSubmodule σ :=
  CompatibleSubmodule.ofStable (LinearMap.range f.toLinearMap) fun a n hn => by
    obtain ⟨m, rfl⟩ := LinearMap.mem_range.1 hn
    exact LinearMap.mem_range.2 ⟨ρ a m, f.map_action' a m⟩

@[simp] theorem range_toSubmodule (f : LinearIntertwiner ρ σ) :
    f.range.toSubmodule = LinearMap.range f.toLinearMap := rfl

@[simp] theorem mem_range (f : LinearIntertwiner ρ σ) {n : N} : n ∈ f.range ↔ ∃ m, f m = n :=
  LinearMap.mem_range

theorem mem_range_self (f : LinearIntertwiner ρ σ) (m : M) : f m ∈ f.range :=
  LinearMap.mem_range_self f.toLinearMap m

end LinearIntertwiner

namespace CompatibleSubmodule

/-- The stable inverse image of a stable subspace under a linear intertwiner. -/
def comap (f : LinearIntertwiner ρ σ) (T : CompatibleSubmodule σ) : CompatibleSubmodule ρ :=
  ofStable (T.toSubmodule.comap f.toLinearMap) fun a m hm => by
    rw [Submodule.mem_comap] at hm ⊢
    rw [f.map_action']
    exact T.action_mem a hm

/-- The stable direct image of a stable subspace under a linear intertwiner. -/
def map (f : LinearIntertwiner ρ σ) (S : CompatibleSubmodule ρ) : CompatibleSubmodule σ :=
  ofStable (S.toSubmodule.map f.toLinearMap) fun a n hn => by
    obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.1 hn
    exact Submodule.mem_map.2 ⟨ρ a m, S.action_mem a hm, f.map_action' a m⟩

@[simp] theorem comap_toSubmodule (f : LinearIntertwiner ρ σ) (T : CompatibleSubmodule σ) :
    (T.comap f).toSubmodule = T.toSubmodule.comap f.toLinearMap := rfl

@[simp] theorem map_toSubmodule (f : LinearIntertwiner ρ σ) (S : CompatibleSubmodule ρ) :
    (S.map f).toSubmodule = S.toSubmodule.map f.toLinearMap := rfl

@[simp] theorem mem_comap {f : LinearIntertwiner ρ σ} {T : CompatibleSubmodule σ} {m : M} :
    m ∈ T.comap f ↔ f m ∈ T := Iff.rfl

@[simp] theorem mem_map {f : LinearIntertwiner ρ σ} {S : CompatibleSubmodule ρ} {n : N} :
    n ∈ S.map f ↔ ∃ m ∈ S, f m = n :=
  Submodule.mem_map

theorem map_le_iff_le_comap {f : LinearIntertwiner ρ σ} {S : CompatibleSubmodule ρ}
    {T : CompatibleSubmodule σ} : S.map f ≤ T ↔ S ≤ T.comap f :=
  Submodule.map_le_iff_le_comap

theorem gc_map_comap (f : LinearIntertwiner ρ σ) : GaloisConnection (map f) (comap f) :=
  fun _ _ => map_le_iff_le_comap

theorem map_mono (f : LinearIntertwiner ρ σ) : Monotone (map f) := (gc_map_comap f).monotone_l

theorem comap_mono (f : LinearIntertwiner ρ σ) : Monotone (comap f) :=
  (gc_map_comap f).monotone_u

@[simp] theorem comap_id (S : CompatibleSubmodule ρ) : S.comap (LinearIntertwiner.id ρ) = S :=
  rfl

theorem comap_comp (g : LinearIntertwiner σ τ) (f : LinearIntertwiner ρ σ)
    (U : CompatibleSubmodule τ) : U.comap (g.comp f) = (U.comap g).comap f := rfl

@[simp] theorem map_id (S : CompatibleSubmodule ρ) : S.map (LinearIntertwiner.id ρ) = S :=
  toSubmodule_injective (Submodule.map_id S.toSubmodule)

theorem map_comp (g : LinearIntertwiner σ τ) (f : LinearIntertwiner ρ σ)
    (S : CompatibleSubmodule ρ) : S.map (g.comp f) = (S.map f).map g :=
  toSubmodule_injective (Submodule.map_comp f.toLinearMap g.toLinearMap S.toSubmodule)

theorem ker_eq_comap_bot (f : LinearIntertwiner ρ σ) :
    f.ker = (⊥ : CompatibleSubmodule σ).comap f :=
  ext fun m => by simp

theorem range_eq_map_top (f : LinearIntertwiner ρ σ) :
    f.range = (⊤ : CompatibleSubmodule ρ).map f :=
  ext fun n => by simp

/-- The kernel of the quotient projection is `S`. -/
@[simp] theorem ker_mkQIntertwiner (S : CompatibleSubmodule ρ) : S.mkQIntertwiner.ker = S :=
  toSubmodule_injective (Submodule.ker_mkQ S.toSubmodule)

/-- The image of the subtype inclusion is `S`. -/
@[simp] theorem range_subtypeIntertwiner (S : CompatibleSubmodule ρ) :
    S.subtypeIntertwiner.range = S :=
  toSubmodule_injective (Submodule.range_subtype S.toSubmodule)

end CompatibleSubmodule

/-! ### Restriction and descent of linear intertwiners -/

namespace LinearIntertwiner

/-- Restriction of an intertwiner to stable subspaces `S → T` with `f(S) ⊆ T`. -/
def restrict (f : LinearIntertwiner ρ σ) {S : CompatibleSubmodule ρ}
    {T : CompatibleSubmodule σ} (h : S ≤ T.comap f) :
    LinearIntertwiner S.restrictAction T.restrictAction where
  toLinearMap := f.toLinearMap.restrict fun _ hm => h hm
  map_action' a m := Subtype.ext (f.map_action' a m)

@[simp] theorem restrict_apply_coe (f : LinearIntertwiner ρ σ) {S : CompatibleSubmodule ρ}
    {T : CompatibleSubmodule σ} (h : S ≤ T.comap f) (m : S.toSubmodule) :
    ((f.restrict h m : T.toSubmodule) : N) = f m := rfl

theorem restrict_toLinearMap (f : LinearIntertwiner ρ σ) {S : CompatibleSubmodule ρ}
    {T : CompatibleSubmodule σ} (h : S ≤ T.comap f) :
    (f.restrict h).toLinearMap = f.toLinearMap.restrict fun _ hm => h hm := rfl

theorem subtypeIntertwiner_comp_restrict (f : LinearIntertwiner ρ σ)
    {S : CompatibleSubmodule ρ} {T : CompatibleSubmodule σ} (h : S ≤ T.comap f) :
    T.subtypeIntertwiner.comp (f.restrict h) = f.comp S.subtypeIntertwiner := rfl

theorem restrict_id (S : CompatibleSubmodule ρ) (h : S ≤ S.comap (id ρ)) :
    (id ρ).restrict h = id S.restrictAction := rfl

theorem restrict_comp (g : LinearIntertwiner σ τ) (f : LinearIntertwiner ρ σ)
    {S : CompatibleSubmodule ρ} {T : CompatibleSubmodule σ} {U : CompatibleSubmodule τ}
    (hf : S ≤ T.comap f) (hg : T ≤ U.comap g) (hgf : S ≤ U.comap (g.comp f)) :
    (g.comp f).restrict hgf = (g.restrict hg).comp (f.restrict hf) := rfl

/-- Restriction of the source to a stable subspace. -/
def domRestrict (f : LinearIntertwiner ρ σ) (S : CompatibleSubmodule ρ) :
    LinearIntertwiner S.restrictAction σ :=
  f.comp S.subtypeIntertwiner

@[simp] theorem domRestrict_apply (f : LinearIntertwiner ρ σ) (S : CompatibleSubmodule ρ)
    (m : S.toSubmodule) : f.domRestrict S m = f m := rfl

theorem domRestrict_toLinearMap (f : LinearIntertwiner ρ σ) (S : CompatibleSubmodule ρ) :
    (f.domRestrict S).toLinearMap = f.toLinearMap.domRestrict S.toSubmodule := rfl

/-- Restriction of the target to a stable subspace containing every value. -/
def codRestrict (f : LinearIntertwiner ρ σ) (T : CompatibleSubmodule σ) (h : ∀ m, f m ∈ T) :
    LinearIntertwiner ρ T.restrictAction where
  toLinearMap := LinearMap.codRestrict T.toSubmodule f.toLinearMap h
  map_action' a m := Subtype.ext (f.map_action' a m)

@[simp] theorem codRestrict_apply_coe (f : LinearIntertwiner ρ σ) (T : CompatibleSubmodule σ)
    (h : ∀ m, f m ∈ T) (m : M) : ((f.codRestrict T h m : T.toSubmodule) : N) = f m := rfl

theorem codRestrict_toLinearMap (f : LinearIntertwiner ρ σ) (T : CompatibleSubmodule σ)
    (h : ∀ m, f m ∈ T) :
    (f.codRestrict T h).toLinearMap = LinearMap.codRestrict T.toSubmodule f.toLinearMap h := rfl

theorem subtypeIntertwiner_comp_codRestrict (f : LinearIntertwiner ρ σ)
    (T : CompatibleSubmodule σ) (h : ∀ m, f m ∈ T) :
    T.subtypeIntertwiner.comp (f.codRestrict T h) = f := rfl

/-- Corestriction to the stable image. -/
def rangeRestrict (f : LinearIntertwiner ρ σ) : LinearIntertwiner ρ f.range.restrictAction :=
  f.codRestrict f.range f.mem_range_self

theorem rangeRestrict_toLinearMap (f : LinearIntertwiner ρ σ) :
    f.rangeRestrict.toLinearMap = f.toLinearMap.rangeRestrict := rfl

theorem subtypeIntertwiner_comp_rangeRestrict (f : LinearIntertwiner ρ σ) :
    f.range.subtypeIntertwiner.comp f.rangeRestrict = f := rfl

/-- Descent of an intertwiner to the quotients `M ⧸ S → N ⧸ T` when `f(S) ⊆ T`. -/
def mapQ (f : LinearIntertwiner ρ σ) (S : CompatibleSubmodule ρ) (T : CompatibleSubmodule σ)
    (h : S ≤ T.comap f) : LinearIntertwiner S.quotientAction T.quotientAction where
  toLinearMap := S.toSubmodule.mapQ T.toSubmodule f.toLinearMap h
  map_action' a x := by
    induction x using Submodule.Quotient.induction_on with
    | H m => exact congrArg Submodule.Quotient.mk (f.map_action' a m)

@[simp] theorem mapQ_apply_mk (f : LinearIntertwiner ρ σ) (S : CompatibleSubmodule ρ)
    (T : CompatibleSubmodule σ) (h : S ≤ T.comap f) (m : M) :
    f.mapQ S T h (Submodule.Quotient.mk m) = Submodule.Quotient.mk (f m) := rfl

theorem mapQ_apply_mkQ (f : LinearIntertwiner ρ σ) (S : CompatibleSubmodule ρ)
    (T : CompatibleSubmodule σ) (h : S ≤ T.comap f) (m : M) :
    f.mapQ S T h (S.toSubmodule.mkQ m) = T.toSubmodule.mkQ (f m) := rfl

theorem mapQ_toLinearMap (f : LinearIntertwiner ρ σ) (S : CompatibleSubmodule ρ)
    (T : CompatibleSubmodule σ) (h : S ≤ T.comap f) :
    (f.mapQ S T h).toLinearMap = S.toSubmodule.mapQ T.toSubmodule f.toLinearMap h := rfl

theorem mapQ_comp_mkQIntertwiner (f : LinearIntertwiner ρ σ) (S : CompatibleSubmodule ρ)
    (T : CompatibleSubmodule σ) (h : S ≤ T.comap f) :
    (f.mapQ S T h).comp S.mkQIntertwiner = T.mkQIntertwiner.comp f := rfl

theorem mapQ_id (S : CompatibleSubmodule ρ) (h : S ≤ S.comap (id ρ)) :
    (id ρ).mapQ S S h = id S.quotientAction := by
  ext x
  induction x using Submodule.Quotient.induction_on with
  | H m => rfl

theorem mapQ_comp (g : LinearIntertwiner σ τ) (f : LinearIntertwiner ρ σ)
    (S : CompatibleSubmodule ρ) (T : CompatibleSubmodule σ) (U : CompatibleSubmodule τ)
    (hf : S ≤ T.comap f) (hg : T ≤ U.comap g) (hgf : S ≤ U.comap (g.comp f)) :
    (g.comp f).mapQ S U hgf = (g.mapQ T U hg).comp (f.mapQ S T hf) := by
  ext x
  induction x using Submodule.Quotient.induction_on with
  | H m => rfl

/-- Descent of an intertwiner to `M ⧸ S → N` when `S` lies in its kernel. -/
def liftQ (f : LinearIntertwiner ρ σ) (S : CompatibleSubmodule ρ) (h : S ≤ f.ker) :
    LinearIntertwiner S.quotientAction σ where
  toLinearMap := S.toSubmodule.liftQ f.toLinearMap h
  map_action' a x := by
    induction x using Submodule.Quotient.induction_on with
    | H m => exact f.map_action' a m

@[simp] theorem liftQ_apply_mk (f : LinearIntertwiner ρ σ) (S : CompatibleSubmodule ρ)
    (h : S ≤ f.ker) (m : M) : f.liftQ S h (Submodule.Quotient.mk m) = f m := rfl

theorem liftQ_apply_mkQ (f : LinearIntertwiner ρ σ) (S : CompatibleSubmodule ρ)
    (h : S ≤ f.ker) (m : M) : f.liftQ S h (S.toSubmodule.mkQ m) = f m := rfl

theorem liftQ_toLinearMap (f : LinearIntertwiner ρ σ) (S : CompatibleSubmodule ρ)
    (h : S ≤ f.ker) : (f.liftQ S h).toLinearMap = S.toSubmodule.liftQ f.toLinearMap h := rfl

theorem liftQ_comp_mkQIntertwiner (f : LinearIntertwiner ρ σ) (S : CompatibleSubmodule ρ)
    (h : S ≤ f.ker) : (f.liftQ S h).comp S.mkQIntertwiner = f := rfl

theorem comp_liftQ (g : LinearIntertwiner σ τ) (f : LinearIntertwiner ρ σ)
    (S : CompatibleSubmodule ρ) (h : S ≤ f.ker) (hgf : S ≤ (g.comp f).ker) :
    g.comp (f.liftQ S h) = (g.comp f).liftQ S hgf := by
  ext x
  induction x using Submodule.Quotient.induction_on with
  | H m => rfl

end LinearIntertwiner

end Images

/-! ### The zero original action -/

section Zero

variable {k : Type u} {A : Type v} {M : Type w}
  [CommRing k] [NonUnitalRing A] [Module k A] [AddCommGroup M] [Module k M]

/-- Under the zero original action every subspace is stable. -/
theorem isStableSubmodule_zero (S : Submodule k M) :
    IsStableSubmodule (0 : A →ₙₐ[k] Module.End k M) S :=
  fun _ _ _ => S.zero_mem

/-- Under the zero original action the bundled stable subspaces are all subspaces. -/
def CompatibleSubmodule.zeroOrderIso :
    CompatibleSubmodule (0 : A →ₙₐ[k] Module.End k M) ≃o Submodule k M where
  toFun := CompatibleSubmodule.toSubmodule
  invFun S := CompatibleSubmodule.ofStable S (isStableSubmodule_zero S)
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- The restricted zero action is zero. -/
theorem CompatibleSubmodule.restrictAction_zero
    (S : CompatibleSubmodule (0 : A →ₙₐ[k] Module.End k M)) : S.restrictAction = 0 :=
  NonUnitalAlgHom.ext fun _ => LinearMap.ext fun _ => Subtype.ext rfl

/-- The quotient zero action is zero. -/
theorem CompatibleSubmodule.quotientAction_zero
    (S : CompatibleSubmodule (0 : A →ₙₐ[k] Module.End k M)) : S.quotientAction = 0 :=
  NonUnitalAlgHom.ext fun _ => Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)

/-- On a nonzero space the lattice of stable subspaces of the zero action is nontrivial. -/
theorem CompatibleSubmodule.bot_ne_top_zero [Nontrivial M] :
    (⊥ : CompatibleSubmodule (0 : A →ₙₐ[k] Module.End k M)) ≠ ⊤ := fun h =>
  bot_ne_top (congrArg CompatibleSubmodule.toSubmodule h)

end Zero

/-! ### Complex specialization: `A = k = M = ℂ` with the zero original action -/

section ComplexZero

open CompatibleSubmodule

/-- Every complex subspace of `ℂ` is stable under the zero original action of `ℂ`. -/
example (S : Submodule ℂ ℂ) : IsStableSubmodule (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ) S :=
  isStableSubmodule_zero S

/-- The restricted and quotient original actions are zero. -/
example (S : CompatibleSubmodule (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ)) :
    S.restrictAction = 0 ∧ S.quotientAction = 0 :=
  ⟨restrictAction_zero S, quotientAction_zero S⟩

/-- The original action is distinct from scalar multiplication. -/
example : (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ) 1 1 = 0 ∧ (1 : ℂ) • (1 : ℂ) ≠ 0 :=
  ⟨rfl, by simp⟩

/-- The zero subspace and the whole subspace (zero quotient) are permitted. -/
example : Subsingleton (⊥ : CompatibleSubmodule (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ)).toSubmodule ∧
    Subsingleton (ℂ ⧸ (⊤ : CompatibleSubmodule (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ)).toSubmodule) :=
  ⟨inferInstanceAs (Subsingleton (⊥ : Submodule ℂ ℂ)),
    Submodule.Quotient.subsingleton_iff.2 rfl⟩

/-- The lattice is nontrivial on the nonzero space `ℂ`. -/
example : (⊥ : CompatibleSubmodule (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ)) ≠ ⊤ :=
  bot_ne_top_zero

/-- Under `restrictNonUnitalModule` the notation `a • m` is the zero original action, while
without it `a • m` is the vector scalar multiplication. -/
example :
    (letI := (⊤ : CompatibleSubmodule (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ)).restrictNonUnitalModule
     (1 : ℂ) • (⟨1, Submodule.mem_top⟩ :
      (⊤ : CompatibleSubmodule (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ)).toSubmodule)) = 0 ∧
    (1 : ℂ) • (⟨1, Submodule.mem_top⟩ :
      (⊤ : CompatibleSubmodule (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ)).toSubmodule) ≠ 0 :=
  ⟨rfl, fun h => one_ne_zero
    (show (1 : ℂ) = 0 from congrArg Subtype.val ((one_smul ℂ _).symm.trans h))⟩

/-- Stable additive subgroups are not identified with stable subspaces: `ℤ · 1 ⊆ ℂ` is stable
under the zero original action, but it is not a complex subspace, so it is not the stable
additive subgroup underlying any `CompatibleSubmodule`. -/
example : ¬ Function.Surjective
    (fun S : CompatibleSubmodule (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ) => S.toNonUnitalSubmodule) := by
  intro hsurj
  obtain ⟨S, hS⟩ := hsurj
    (letI := NonUnitalModule.ofLinearEndHom (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ)
     { toAddSubgroup := AddSubgroup.zmultiples (1 : ℂ)
       smul_mem' := fun _ _ _ => (AddSubgroup.zmultiples (1 : ℂ)).zero_mem })
  have hmem (z : ℂ) : z ∈ S ↔ z ∈ AddSubgroup.zmultiples (1 : ℂ) :=
    letI := NonUnitalModule.ofLinearEndHom (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ)
    Iff.of_eq (congrArg (fun T => z ∈ T) hS)
  have hI : Complex.I ∈ S := by
    simpa using S.toSubmodule.smul_mem Complex.I ((hmem 1).2 (AddSubgroup.mem_zmultiples 1))
  obtain ⟨n, hn⟩ := (hmem _).1 hI
  simpa using congrArg Complex.im hn

end ComplexZero

/-! ### Source-facing field interface

A field `K`, a possibly noncommutative and nonunital associative `K`-algebra `A` with bilinear
multiplication, and `K`-vector spaces of arbitrary dimension in independent universes. -/

section FieldInterface

variable {K : Type u} {A : Type v} {M : Type w} {N : Type x}
  [Field K] [NonUnitalRing A] [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  (ρ : A →ₙₐ[K] Module.End K M) (σ : A →ₙₐ[K] Module.End K N)

/-- Item 1 at a field: the stable subspaces form a complete lattice, preserved by forgetting. -/
example : CompleteLattice (CompatibleSubmodule ρ) := inferInstance

example (s : Set (CompatibleSubmodule ρ)) :
    (sSup s).toSubmodule = ⨆ S ∈ s, S.toSubmodule ∧
      (sInf s).toSubmodule = ⨅ S ∈ s, S.toSubmodule :=
  ⟨CompatibleSubmodule.sSup_toSubmodule_eq_iSup s,
    CompatibleSubmodule.sInf_toSubmodule_eq_iInf s⟩

/-- Item 2 at a field: restricted and quotient formulas. -/
example (S : CompatibleSubmodule ρ) (a : A) (m : S.toSubmodule) (m' : M) :
    ((S.restrictAction a m : S.toSubmodule) : M) = ρ a m ∧
      S.quotientAction a (S.toSubmodule.mkQ m') = S.toSubmodule.mkQ (ρ a m') :=
  ⟨rfl, rfl⟩

/-- Item 2 at a field: the ambient actions through the bridge and their scalar compatibility. -/
example (S : CompatibleSubmodule ρ) :
    (letI := S.restrictNonUnitalModule
     IsScalarTower K A S.toSubmodule ∧ SMulCommClass K A S.toSubmodule) ∧
    (letI := S.quotientNonUnitalModule
     IsScalarTower K A (M ⧸ S.toSubmodule) ∧ SMulCommClass K A (M ⧸ S.toSubmodule)) :=
  ⟨⟨S.restrictNonUnitalModule_isScalarTower, S.restrictNonUnitalModule_smulCommClass⟩,
    ⟨S.quotientNonUnitalModule_isScalarTower, S.quotientNonUnitalModule_smulCommClass⟩⟩

/-- Item 3 at a field: kernel and image memberships, restriction and descent. -/
example (f : LinearIntertwiner ρ σ) (m : M) (n : N) :
    (m ∈ f.ker ↔ f m = 0) ∧ (n ∈ f.range ↔ ∃ m, f m = n) :=
  ⟨f.mem_ker, f.mem_range⟩

example (f : LinearIntertwiner ρ σ) (S : CompatibleSubmodule ρ) (T : CompatibleSubmodule σ)
    (h : S ≤ T.comap f) (m : M) :
    f.mapQ S T h (S.toSubmodule.mkQ m) = T.toSubmodule.mkQ (f m) := rfl

example (f : LinearIntertwiner ρ σ) (S : CompatibleSubmodule ρ) (T : CompatibleSubmodule σ)
    (h : S ≤ T.comap f) (hK : S ≤ f.ker) (m : S.toSubmodule) (m' : M) :
    ((f.restrict h m : T.toSubmodule) : N) = f m ∧ f.liftQ S hK (S.toSubmodule.mkQ m') = f m' :=
  ⟨rfl, rfl⟩

end FieldInterface

end Langlands.Algebra
