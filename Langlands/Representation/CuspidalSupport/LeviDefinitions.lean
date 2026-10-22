import Langlands.Representation.Geometric.WeylDefinitions
import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.Smooth.Transfer.PullbackProof

/-! Actual cuspidality and Weyl transport for product Levi representations. -/

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric CategoryTheory

universe uF uV uW

variable {F : Type uF} [Field F] {n : ℕ}
  (B C : BlockShape n)
  {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Quasicuspidality on the actual product Levi, tested on every proper
standard block refinement. The quotient is the actual unipotent coinvariant
module; neither smoothness nor admissibility is built into this predicate. -/
def IsLeviQuasicuspidal (ρ : Representation ℂ (B.Levi F) V) : Prop :=
  ∀ S : BlockRefinement B, refinedParabolic F B S ≠ ⊤ →
    Subsingleton (Jacquet.Coinvariants ρ (refinedUnipotent F B S))

/-- Quasicuspidality is invariant under an actual intertwining equivalence,
including between representations in different carrier universes. -/
theorem isLeviQuasicuspidal_iff_of_equiv
    {ρ : Representation ℂ (B.Levi F) V}
    {σ : Representation ℂ (B.Levi F) W} (e : ρ.Equiv σ) :
    IsLeviQuasicuspidal B ρ ↔ IsLeviQuasicuspidal B σ := by
  constructor
  · intro h S hS
    exact (Jacquet.coinvariants_subsingleton_iff e _).mp (h S hS)
  · intro h S hS
    exact (Jacquet.coinvariants_subsingleton_iff e _).mpr (h S hS)

/-- BZ77's cuspidal condition on a product Levi is admissible
quasicuspidality. Admissibility includes smoothness; irreducibility is separate. -/
def IsLeviCuspidal [TopologicalSpace F]
    (ρ : Representation ℂ (B.Levi F) V) : Prop :=
  IsAdmissible ρ ∧ IsLeviQuasicuspidal B ρ

theorem isLeviCuspidal_iff_of_equiv [TopologicalSpace F]
    {ρ : Representation ℂ (B.Levi F) V}
    {σ : Representation ℂ (B.Levi F) W} (e : ρ.Equiv σ) :
    IsLeviCuspidal B ρ ↔ IsLeviCuspidal B σ :=
  and_congr (isAdmissible_iff_of_equiv e)
    (isLeviQuasicuspidal_iff_of_equiv B e)

/-- The actual permutation matrix conjugates the whole embedded source Levi
onto the embedded target Levi. No association theorem is assumed. -/
def ConjugatesLevi (w : Equiv.Perm (Fin n)) : Prop :=
  (B.leviSubgroup F).map
    (MulAut.conj (permutation n F w)).toMonoidHom = C.leviSubgroup F

/-- The genuine finite set `W(M,N)` of permutations conjugating the Levis. -/
abbrev ConjugatingPermutations :=
  {w : Equiv.Perm (Fin n) // ConjugatesLevi (F := F) B C w}

instance : Finite (ConjugatingPermutations (F := F) B C) :=
  inferInstanceAs
    (Finite {w : Equiv.Perm (Fin n) // ConjugatesLevi (F := F) B C w})

/-- The actual conjugation equivalence on product Levis, obtained by
embedding, conjugating, and applying the inverse target embedding. -/
def leviConjugation (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := F) B C w) : B.Levi F ≃* C.Levi F :=
  (B.leviEquiv F).trans
    (((MulAut.conj (permutation n F w)).subgroupMap (B.leviSubgroup F)).trans
      ((MulEquiv.subgroupCongr hw).trans (C.leviEquiv F).symm))

/-- The constructed equivalence is actual matrix conjugation. -/
theorem leviConjugation_embedding (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := F) B C w) (m : B.Levi F) :
    C.leviEmbedding F (leviConjugation B C w hw m) =
      permutation n F w * B.leviEmbedding F m * (permutation n F w)⁻¹ := by
  let t : C.leviSubgroup F := MulEquiv.subgroupCongr hw
    ((MulAut.conj (permutation n F w)).subgroupMap (B.leviSubgroup F)
      (B.leviEquiv F m))
  change ((C.leviEquiv F) ((C.leviEquiv F).symm t) : GeneralLinear n F) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- Inverse transport is inverse matrix conjugation. -/
theorem leviConjugation_symm_embedding (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := F) B C w) (m : C.Levi F) :
    B.leviEmbedding F ((leviConjugation B C w hw).symm m) =
      (permutation n F w)⁻¹ * C.leviEmbedding F m * permutation n F w := by
  have h := leviConjugation_embedding B C w hw
    ((leviConjugation B C w hw).symm m)
  rw [MulEquiv.apply_symm_apply] at h
  have h' := congrArg (fun g => (permutation n F w)⁻¹ * g * permutation n F w) h
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right,
    inv_mul_cancel, mul_one] using h'.symm

section Topology

variable [TopologicalSpace F] [IsTopologicalRing F]

theorem continuous_leviConjugation (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := F) B C w) :
    Continuous (leviConjugation B C w hw) := by
  have h : Continuous (fun m : B.Levi F =>
      ((C.leviEquiv F) (leviConjugation B C w hw m) : GeneralLinear n F)) := by
    change Continuous (fun m => C.leviEmbedding F (leviConjugation B C w hw m))
    simp_rw [leviConjugation_embedding]
    exact (continuous_const.mul (B.leviEmbeddingContinuous F).continuous).mul continuous_const
  have hs : Continuous (fun m : B.Levi F =>
      (C.leviEquiv F) (leviConjugation B C w hw m)) := h.subtype_mk _
  have hcomp := (C.leviEquivContinuous F).symm.continuous.comp hs
  change Continuous (fun m => (C.leviEquiv F).symm
    ((C.leviEquiv F) (leviConjugation B C w hw m))) at hcomp
  simpa only [MulEquiv.symm_apply_apply] using hcomp

theorem continuous_leviConjugation_symm (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := F) B C w) :
    Continuous (leviConjugation B C w hw).symm := by
  have h : Continuous (fun m : C.Levi F =>
      ((B.leviEquiv F) ((leviConjugation B C w hw).symm m) : GeneralLinear n F)) := by
    change Continuous (fun m => B.leviEmbedding F ((leviConjugation B C w hw).symm m))
    simp_rw [leviConjugation_symm_embedding]
    exact (continuous_const.mul (C.leviEmbeddingContinuous F).continuous).mul continuous_const
  have hs : Continuous (fun m : C.Levi F =>
      (B.leviEquiv F) ((leviConjugation B C w hw).symm m)) := h.subtype_mk _
  have hcomp := (B.leviEquivContinuous F).symm.continuous.comp hs
  change Continuous (fun m => (B.leviEquiv F).symm
    ((B.leviEquiv F) ((leviConjugation B C w hw).symm m))) at hcomp
  simpa only [MulEquiv.symm_apply_apply] using hcomp

end Topology

/-- Transport of an actual source-Levi representation to the target Levi.
The inverse conjugation is used in its action, as in BZ77 section 1.7. -/
def transport (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := F) B C w)
    (ρ : Representation ℂ (B.Levi F) V) :
    Representation ℂ (C.Levi F) V :=
  ρ.comp (leviConjugation B C w hw).symm.toMonoidHom

/-- An intertwiner is transported by retaining its underlying linear map. -/
def transportMap (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := F) B C w)
    {ρ : Representation ℂ (B.Levi F) V}
    {σ : Representation ℂ (B.Levi F) W} (f : ρ.IntertwiningMap σ) :
    (transport B C w hw ρ).IntertwiningMap (transport B C w hw σ) where
  toLinearMap := f.toLinearMap
  isIntertwining' m := f.isIntertwining' ((leviConjugation B C w hw).symm m)

@[simp]
theorem transportMap_apply (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := F) B C w)
    {ρ : Representation ℂ (B.Levi F) V}
    {σ : Representation ℂ (B.Levi F) W}
    (f : ρ.IntertwiningMap σ) (v : V) :
    transportMap B C w hw f v = f v := rfl

section Smooth

variable [TopologicalSpace F] [IsTopologicalRing F]

theorem isSmooth_transport (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := F) B C w)
    {ρ : Representation ℂ (B.Levi F) V} (hρ : IsSmooth ρ) :
    IsSmooth (transport B C w hw ρ) :=
  isSmooth_comp (leviConjugation B C w hw).symm.toMonoidHom
    (continuous_leviConjugation_symm B C w hw) hρ

/-- Weyl transport on the actual smooth categories, with the same
underlying linear maps and proved functor laws. -/
def transportFunctor (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := F) B C w) :
    SmoothRep.{0, uF, uV} ℂ (B.Levi F) ⥤ SmoothRep.{0, uF, uV} ℂ (C.Levi F) where
  obj A := SmoothRep.of (transport B C w hw A.representation)
    (isSmooth_transport B C w hw A.isSmooth)
  map f := SmoothRep.ofHom (transportMap B C w hw (SmoothRep.hom f))
  map_id _ := rfl
  map_comp _ _ := rfl

end Smooth

/-- BZ77 association of standard Levi subgroups, expressed by actual
permutation conjugation of their embedded matrix subgroups. -/
def LevisAssociated : Prop :=
  Nonempty (ConjugatingPermutations (F := F) B C)

/-- BZ77 association of representations: an actual transported representation
is intertwined isomorphically with the target representation. -/
def RepresentationsAssociated
    (ρ : Representation ℂ (B.Levi F) V)
    (σ : Representation ℂ (C.Levi F) W) : Prop :=
  ∃ (w : Equiv.Perm (Fin n)) (hw : ConjugatesLevi (F := F) B C w),
    Nonempty ((transport B C w hw ρ).Equiv σ)

/-- Actual minimal permutations which conjugate the entire source Levi onto
the target Levi. Their parametrization of right Weyl cosets is a theorem
obligation, not a field of this subtype. -/
abbrev MinimalConjugatingPermutations :=
  {w : MinimalRepresentatives B C // ConjugatesLevi (F := F) B C w.val}

instance : Finite (MinimalConjugatingPermutations (F := F) B C) :=
  inferInstanceAs
    (Finite {w : MinimalRepresentatives B C // ConjugatesLevi (F := F) B C w.val})

/-- The finite set of minimal conjugating permutations carrying the given
source representation to one isomorphic to the target. -/
abbrev AssociatingPermutations
    (ρ : Representation ℂ (B.Levi F) V)
    (σ : Representation ℂ (C.Levi F) W) :=
  {w : MinimalConjugatingPermutations (F := F) B C //
    Nonempty ((transport B C w.val.val w.property ρ).Equiv σ)}

instance (ρ : Representation ℂ (B.Levi F) V)
    (σ : Representation ℂ (C.Levi F) W) :
    Finite (AssociatingPermutations B C ρ σ) :=
  inferInstanceAs (Finite {w : MinimalConjugatingPermutations (F := F) B C //
    Nonempty ((transport B C w.val.val w.property ρ).Equiv σ)})

end Langlands.CuspidalSupport
