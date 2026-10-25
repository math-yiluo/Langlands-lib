import Langlands.Representation.Classification.ConstituentRelations
import Langlands.Representation.Category.Subquotients
import Langlands.Weil.Representation.IsomorphismInvarianceProof

/-!
# Canonical heads and socles

For a representation `ρ` on `V` over a field `k`, the head kernel is the common
kernel of all irreducible quotient maps of `ρ` with targets in the universe of `V`,
and the head is the actual quotient representation by the head kernel. For a
complex representation `ρ`, the socle is the sum of the images of all irreducible
embeddings into `ρ` with sources in that universe, and the socle representation is
the actual restriction to the socle. Both are defined for every `ρ`, without
choices.

When `ρ` has an irreducible head in the sense of `IsIrreducibleHead`, the head is
one, and every irreducible head of `ρ` is equivalent to it; dually for socles. No
existence of a head or socle is asserted.
-/

noncomputable section

namespace Langlands.Classification

universe uk uG uV

variable {G : Type uG} [Group G]

section Head

variable {k : Type uk} [Field k] {V : Type uV} [AddCommGroup V] [Module k V]

/-- The head kernel of `ρ`: the vectors killed by every irreducible quotient map of
`ρ` whose target has its carrier in the universe of `V`. -/
def headKernel (ρ : Representation k G V) : Subrepresentation ρ where
  toSubmodule :=
    { carrier := {v | ∀ (W : Type uV) [AddCommGroup W] [Module k W]
        (π : Representation k G W), Representation.IsIrreducible π →
        ∀ q : ρ.IntertwiningMap π, Function.Surjective q → q v = 0}
      add_mem' := fun {a b} ha hb W _ _ π hπ q hq => by
        rw [map_add, ha W π hπ q hq, hb W π hπ q hq, add_zero]
      zero_mem' := fun W _ _ π _ q _ => map_zero q
      smul_mem' := fun c v hv W _ _ π hπ q hq => by
        rw [map_smul, hv W π hπ q hq, smul_zero] }
  apply_mem_toSubmodule g v hv W _ _ π hπ q hq := by
    rw [q.isIntertwining, hv W π hπ q hq, map_zero]

theorem mem_headKernel_iff (ρ : Representation k G V) (v : V) :
    v ∈ (headKernel ρ).toSubmodule ↔
      ∀ (W : Type uV) [AddCommGroup W] [Module k W]
        (π : Representation k G W), Representation.IsIrreducible π →
        ∀ q : ρ.IntertwiningMap π, Function.Surjective q → q v = 0 :=
  Iff.rfl

theorem headKernel_stable (ρ : Representation k G V) (g : G) :
    (headKernel ρ).toSubmodule ≤ (headKernel ρ).toSubmodule.comap (ρ g) :=
  fun _ hv => (headKernel ρ).apply_mem_toSubmodule g hv

/-- The head of `ρ`: the actual quotient representation by the head kernel. -/
def head (ρ : Representation k G V) :
    Representation k G (V ⧸ (headKernel ρ).toSubmodule) :=
  ρ.quotient (headKernel ρ).toSubmodule (headKernel_stable ρ)

/-- The canonical quotient map onto the head. -/
def toHead (ρ : Representation k G V) : ρ.IntertwiningMap (head ρ) where
  toLinearMap := (headKernel ρ).toSubmodule.mkQ
  isIntertwining' _ := rfl

@[simp]
theorem toHead_apply (ρ : Representation k G V) (v : V) :
    toHead ρ v = Submodule.Quotient.mk v :=
  rfl

theorem toHead_surjective (ρ : Representation k G V) :
    Function.Surjective (toHead ρ) :=
  Submodule.mkQ_surjective _

theorem ker_toHead (ρ : Representation k G V) :
    LinearMap.ker (toHead ρ).toLinearMap = (headKernel ρ).toSubmodule :=
  Submodule.ker_mkQ _

/-- The head kernel lies in the kernel of every irreducible quotient map. -/
theorem headKernel_le_ker {ρ : Representation k G V} {W : Type uV} [AddCommGroup W]
    [Module k W] (π : Representation k G W) (hπ : Representation.IsIrreducible π)
    (q : ρ.IntertwiningMap π) (hq : Function.Surjective q) :
    (headKernel ρ).toSubmodule ≤ LinearMap.ker q.toLinearMap :=
  fun _ hv => hv W π hπ q hq

/-- An irreducible quotient map whose kernel is the head kernel identifies the head
with its target. -/
def headEquivOfSurjective {ρ : Representation k G V} {W : Type*} [AddCommGroup W]
    [Module k W] {π : Representation k G W} (q : ρ.IntertwiningMap π)
    (hq : Function.Surjective q)
    (hK : (headKernel ρ).toSubmodule = LinearMap.ker q.toLinearMap) :
    (head ρ).Equiv π :=
  Representation.Equiv.mk
    ((Submodule.quotEquivOfEq _ _ hK).trans
      (q.toLinearMap.quotKerEquivOfSurjective hq))
    fun g => by
      apply Submodule.linearMap_qext
      ext v
      exact Representation.IntertwiningMap.isIntertwining _ _ q g v

@[simp]
theorem headEquivOfSurjective_apply {ρ : Representation k G V} {W : Type*}
    [AddCommGroup W] [Module k W] {π : Representation k G W}
    (q : ρ.IntertwiningMap π) (hq : Function.Surjective q)
    (hK : (headKernel ρ).toSubmodule = LinearMap.ker q.toLinearMap) (v : V) :
    headEquivOfSurjective q hq hK (toHead ρ v) = q v :=
  rfl

end Head

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

section IrreducibleHead

/-- `ρ` has an irreducible head with carrier in the universe of `V`. -/
def HasIrreducibleHead (ρ : Representation ℂ G V) : Prop :=
  ∃ (W : Type uV) (_ : AddCommGroup W) (_ : Module ℂ W) (π : Representation ℂ G W),
    IsIrreducibleHead ρ π

variable {ρ : Representation ℂ G V} {W : Type uV} [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ G W}

/-- If `π` is an irreducible head of `ρ`, the head kernel is the kernel of every
irreducible quotient map of `ρ`. -/
theorem IsIrreducibleHead.headKernel_eq (h : IsIrreducibleHead ρ π)
    {W' : Type uV} [AddCommGroup W'] [Module ℂ W'] (π' : Representation ℂ G W')
    (hπ' : Representation.IsIrreducible π') (q' : ρ.IntertwiningMap π')
    (hq' : Function.Surjective q') :
    (headKernel ρ).toSubmodule = LinearMap.ker q'.toLinearMap := by
  obtain ⟨-, q, -, huniq⟩ := h
  refine le_antisymm (headKernel_le_ker π' hπ' q' hq') fun v hv W'' _ _ π'' hπ'' q'' hq'' => ?_
  have hv' : v ∈ LinearMap.ker q''.toLinearMap := by
    rw [huniq W'' π'' hπ'' q'' hq'', ← huniq W' π' hπ' q' hq']
    exact hv
  exact hv'

/-- Every irreducible head of `ρ` is equivalent to the head of `ρ`. -/
theorem IsIrreducibleHead.nonempty_headEquiv (h : IsIrreducibleHead ρ π) :
    Nonempty ((head ρ).Equiv π) := by
  obtain ⟨hπ, q, hq, -⟩ := id h
  exact ⟨headEquivOfSurjective q hq (h.headKernel_eq π hπ q hq)⟩

/-- If `ρ` has an irreducible head, its head is one. -/
theorem IsIrreducibleHead.isIrreducibleHead_head (h : IsIrreducibleHead ρ π) :
    IsIrreducibleHead ρ (head ρ) := by
  obtain ⟨e⟩ := h.nonempty_headEquiv
  refine ⟨(Weil.IsomorphismInvariance.irreducible_iff e).mpr h.1, toHead ρ,
    toHead_surjective ρ, ?_⟩
  intro W' _ _ π' hπ' q' hq'
  rw [ker_toHead, h.headKernel_eq π' hπ' q' hq']

/-- The head of `ρ` is an irreducible head exactly when `ρ` has one. -/
theorem isIrreducibleHead_head_iff (ρ : Representation ℂ G V) :
    IsIrreducibleHead ρ (head ρ) ↔ HasIrreducibleHead ρ :=
  ⟨fun h => ⟨_, _, _, head ρ, h⟩, fun ⟨_, _, _, _, h⟩ => h.isIrreducibleHead_head⟩

end IrreducibleHead

section Socle

/-- The images of the irreducible embeddings into `ρ` whose sources have carriers in
the universe of `V`. -/
def irreducibleImages (ρ : Representation ℂ G V) : Set (Submodule ℂ V) :=
  {S | ∃ (W : Type uV) (_ : AddCommGroup W) (_ : Module ℂ W)
    (π : Representation ℂ G W) (j : π.IntertwiningMap ρ),
    Representation.IsIrreducible π ∧ Function.Injective j ∧
      LinearMap.range j.toLinearMap = S}

/-- The socle of `ρ`: the sum of the images of its irreducible embeddings. -/
def socle (ρ : Representation ℂ G V) : Subrepresentation ρ where
  toSubmodule := sSup (irreducibleImages ρ)
  apply_mem_toSubmodule g := by
    have hle : sSup (irreducibleImages ρ) ≤ (sSup (irreducibleImages ρ)).comap (ρ g) := by
      refine sSup_le ?_
      rintro S ⟨W, _, _, π, j, hπ, hj, rfl⟩ w hw
      have hS : LinearMap.range j.toLinearMap ∈ irreducibleImages ρ :=
        ⟨W, _, _, π, j, hπ, hj, rfl⟩
      exact le_sSup hS (j.range.apply_mem_toSubmodule g hw)
    exact fun v hv => hle hv

/-- The image of every irreducible embedding lies in the socle. -/
theorem range_le_socle {ρ : Representation ℂ G V} {W : Type uV} [AddCommGroup W]
    [Module ℂ W] (π : Representation ℂ G W) (hπ : Representation.IsIrreducible π)
    (j : π.IntertwiningMap ρ) (hj : Function.Injective j) :
    LinearMap.range j.toLinearMap ≤ (socle ρ).toSubmodule :=
  le_sSup ⟨W, _, _, π, j, hπ, hj, rfl⟩

/-- The socle representation: the actual restriction of `ρ` to its socle. -/
def socleRepresentation (ρ : Representation ℂ G V) :
    Representation ℂ G (socle ρ).toSubmodule :=
  (socle ρ).toRepresentation

/-- The canonical inclusion of the socle. -/
def ofSocle (ρ : Representation ℂ G V) : (socleRepresentation ρ).IntertwiningMap ρ where
  toLinearMap := (socle ρ).toSubmodule.subtype
  isIntertwining' _ := rfl

@[simp]
theorem ofSocle_apply (ρ : Representation ℂ G V) (v : (socle ρ).toSubmodule) :
    ofSocle ρ v = v :=
  rfl

theorem ofSocle_injective (ρ : Representation ℂ G V) :
    Function.Injective (ofSocle ρ) :=
  Subtype.val_injective

theorem range_ofSocle (ρ : Representation ℂ G V) :
    LinearMap.range (ofSocle ρ).toLinearMap = (socle ρ).toSubmodule :=
  Submodule.range_subtype _

/-- `ρ` has an irreducible socle with carrier in the universe of `V`. -/
def HasIrreducibleSocle (ρ : Representation ℂ G V) : Prop :=
  ∃ (W : Type uV) (_ : AddCommGroup W) (_ : Module ℂ W) (π : Representation ℂ G W),
    IsIrreducibleSocle ρ π

/-- An irreducible embedding whose image is the socle identifies its source with the
socle representation. -/
def socleEquivOfInjective {ρ : Representation ℂ G V} {W : Type*} [AddCommGroup W]
    [Module ℂ W] {π : Representation ℂ G W} (j : π.IntertwiningMap ρ)
    (hj : Function.Injective j)
    (hS : (socle ρ).toSubmodule = LinearMap.range j.toLinearMap) :
    π.Equiv (socleRepresentation ρ) :=
  Representation.Equiv.mk
    ((LinearEquiv.ofInjective j.toLinearMap hj).trans (LinearEquiv.ofEq _ _ hS.symm))
    fun g => by
      ext w
      exact Representation.IntertwiningMap.isIntertwining _ _ j g w

@[simp]
theorem ofSocle_socleEquivOfInjective {ρ : Representation ℂ G V} {W : Type*}
    [AddCommGroup W] [Module ℂ W] {π : Representation ℂ G W}
    (j : π.IntertwiningMap ρ) (hj : Function.Injective j)
    (hS : (socle ρ).toSubmodule = LinearMap.range j.toLinearMap) (w : W) :
    ofSocle ρ (socleEquivOfInjective j hj hS w) = j w :=
  rfl

variable {ρ : Representation ℂ G V} {W : Type uV} [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ G W}

/-- If `π` is an irreducible socle of `ρ`, the socle is the image of every
irreducible embedding into `ρ`. -/
theorem IsIrreducibleSocle.socle_eq (h : IsIrreducibleSocle ρ π)
    {W' : Type uV} [AddCommGroup W'] [Module ℂ W'] (π' : Representation ℂ G W')
    (hπ' : Representation.IsIrreducible π') (j' : π'.IntertwiningMap ρ)
    (hj' : Function.Injective j') :
    (socle ρ).toSubmodule = LinearMap.range j'.toLinearMap := by
  obtain ⟨-, j, -, huniq⟩ := h
  refine le_antisymm (sSup_le ?_) (range_le_socle π' hπ' j' hj')
  rintro S ⟨W'', _, _, π'', j'', hπ'', hj'', rfl⟩
  rw [huniq W'' π'' hπ'' j'' hj'', ← huniq W' π' hπ' j' hj']

/-- Every irreducible socle of `ρ` is equivalent to the socle representation. -/
theorem IsIrreducibleSocle.nonempty_socleEquiv (h : IsIrreducibleSocle ρ π) :
    Nonempty (π.Equiv (socleRepresentation ρ)) := by
  obtain ⟨hπ, j, hj, -⟩ := id h
  exact ⟨socleEquivOfInjective j hj (h.socle_eq π hπ j hj)⟩

/-- If `ρ` has an irreducible socle, its socle representation is one. -/
theorem IsIrreducibleSocle.isIrreducibleSocle_socleRepresentation
    (h : IsIrreducibleSocle ρ π) : IsIrreducibleSocle ρ (socleRepresentation ρ) := by
  obtain ⟨e⟩ := h.nonempty_socleEquiv
  refine ⟨(Weil.IsomorphismInvariance.irreducible_iff e).mp h.1, ofSocle ρ,
    ofSocle_injective ρ, ?_⟩
  intro W' _ _ π' hπ' j' hj'
  rw [range_ofSocle, h.socle_eq π' hπ' j' hj']

/-- The socle representation is an irreducible socle exactly when `ρ` has one. -/
theorem isIrreducibleSocle_socleRepresentation_iff (ρ : Representation ℂ G V) :
    IsIrreducibleSocle ρ (socleRepresentation ρ) ↔ HasIrreducibleSocle ρ :=
  ⟨fun h => ⟨_, _, _, socleRepresentation ρ, h⟩,
    fun ⟨_, _, _, _, h⟩ => h.isIrreducibleSocle_socleRepresentation⟩

end Socle

end Langlands.Classification

namespace Langlands.SmoothRep

universe uk uG uV

open CategoryTheory

variable {G : Type uG} [Group G] [TopologicalSpace G]

section Head

variable {k : Type uk} [Field k] (A : SmoothRep.{uk, uG, uV} k G)

/-- The head of a smooth representation: its actual quotient by the head kernel. -/
def headQuotient : SmoothRep.{uk, uG, uV} k G :=
  quotient A (Classification.headKernel A.representation)

theorem headQuotient_representation :
    A.headQuotient.representation = Classification.head A.representation :=
  rfl

/-- The canonical quotient map onto the head. -/
def toHeadQuotient : A ⟶ A.headQuotient :=
  mkQ A (Classification.headKernel A.representation)

theorem toHeadQuotient_surjective : Function.Surjective (hom A.toHeadQuotient) :=
  mkQ_surjective A _

end Head

variable (A : SmoothRep.{0, uG, uV} ℂ G)

/-- The socle of a smooth representation: its actual restriction to the socle. -/
def socleSubrepresentation : SmoothRep.{0, uG, uV} ℂ G :=
  subrepresentation A (Classification.socle A.representation)

theorem socleSubrepresentation_representation :
    A.socleSubrepresentation.representation =
      Classification.socleRepresentation A.representation :=
  rfl

/-- The canonical inclusion of the socle. -/
def ofSocleSubrepresentation : A.socleSubrepresentation ⟶ A :=
  subtype A (Classification.socle A.representation)

theorem ofSocleSubrepresentation_injective :
    Function.Injective (hom A.ofSocleSubrepresentation) :=
  subtype_injective A _

variable {A}

/-- The head of `A` is an irreducible head exactly when `A` has one. -/
theorem isIrreducibleHead_headQuotient_iff :
    Classification.IsIrreducibleHead A.representation A.headQuotient.representation ↔
      Classification.HasIrreducibleHead A.representation :=
  Classification.isIrreducibleHead_head_iff A.representation

/-- The socle of `A` is an irreducible socle exactly when `A` has one. -/
theorem isIrreducibleSocle_socleSubrepresentation_iff :
    Classification.IsIrreducibleSocle A.representation
        A.socleSubrepresentation.representation ↔
      Classification.HasIrreducibleSocle A.representation :=
  Classification.isIrreducibleSocle_socleRepresentation_iff A.representation

/-- Every smooth irreducible head of `A` is isomorphic to the head of `A`. -/
theorem nonempty_iso_headQuotient {B : SmoothRep.{0, uG, uV} ℂ G}
    (h : Classification.IsIrreducibleHead A.representation B.representation) :
    Nonempty (B ≅ A.headQuotient) :=
  h.nonempty_headEquiv.map fun e => (mkIso e).symm

/-- Every smooth irreducible socle of `A` is isomorphic to the socle of `A`. -/
theorem nonempty_iso_socleSubrepresentation {B : SmoothRep.{0, uG, uV} ℂ G}
    (h : Classification.IsIrreducibleSocle A.representation B.representation) :
    Nonempty (B ≅ A.socleSubrepresentation) :=
  h.nonempty_socleEquiv.map mkIso

end Langlands.SmoothRep
