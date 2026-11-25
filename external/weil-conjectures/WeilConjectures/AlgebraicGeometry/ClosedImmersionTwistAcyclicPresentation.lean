/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import all WeilConjectures.AlgebraicGeometry.ProjectiveFiniteCohomologyPresentation
import WeilConjectures.AlgebraicGeometry.NonnegativeProjectiveTwistVanishing
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.Cohomology.Exact

/-! # A finite-twist presentation with an eventually acyclic middle term -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- A coherent closed-immersion pushforward has a presentation whose middle term
has zero positive cohomology after sufficiently large twists.
Source: Stacks Project, Tag 01YS (4), finite-twist presentation in the descending proof.
(blueprint: lem-pc-d2-closed-immersion-twist-acyclic-presentation)

Proof: Projective space over A is locally Noetherian. A closed immersion sends the
quasi-coherent finitely presented F to a coherent module G. Choose a surjection B → G
from a finite sum of negative twists O(-m_j), with m_j natural numbers, and let K be
its kernel. Kernels of maps of coherent modules on a locally Noetherian scheme are
coherent. The kernel sequence gives S and its third term is G. Take b to be the maximum
of the finitely many m_j (zero for the empty family). For t ≥ b, tensoring each summand
by O(t) gives O(t-m_j), whose positive cohomology is zero by the monomial Cech
calculation over A. Tensoring preserves finite sums, and cohomology is additive, so
B tensor O(t) also has zero degree-q cohomology. The comparison of ordinary sheaf
cohomology with module right-derived sections gives the stated IsZero. This argument
also covers N=0 and the zero module; it uses no next-degree vanishing hypothesis. -/
theorem exists_closedImmersion_twist_acyclic_presentation
    (A : Type u) [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} {N : ℕ}
    (i : X ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of A))) [IsClosedImmersion i]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation]
    (q : ℕ) (hq : 0 < q) :
    ∃ S : ShortComplex (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of A))).Modules,
      S.ShortExact ∧ Nonempty (S.X₃ ≅ (pushforward i).obj F) ∧
      S.X₁.IsQuasicoherent ∧ S.X₁.IsFinitePresentation ∧
      ∃ b : ℕ, ∀ t : ℕ, b ≤ t →
        IsZero ((RingedSpace.moduleCohomology
          (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of A))).toRingedSpace q).obj
          (tensorObj S.X₂
            (ProjectiveSpace.twist (ULift.{u} (Fin (N + 1))) (Spec (.of A)) t))) := by
  classical
  let n := ULift.{u} (Fin (N + 1))
  have : IsLocallyNoetherian ℙ(n; Spec (.of A)) :=
    LocallyOfFiniteType.isLocallyNoetherian (ℙ(n; Spec (.of A)) ↘ Spec (.of A))
  obtain ⟨hG₁, hG₂⟩ := closed_pushforward_coherent_independent i F
  have := hG₁
  have := hG₂
  obtain ⟨ι, hι, m, f, hf, hK₁, hK₂⟩ :=
    exists_epi_sigma_twist_affine n ((pushforward i).obj F)
  let : Finite ι := hι
  have : Epi f := hf
  obtain ⟨b, hb⟩ := (Set.finite_range m).bddAbove
  refine ⟨ShortComplex.kernelSequence f,
    ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact f) inferInstance hf,
    ⟨Iso.refl _⟩, hK₁, hK₂, b, ?_⟩
  intro t ht
  let T := ProjectiveSpace.twist n (Spec (.of A)) t
  let B := fun a : ι ↦ ProjectiveSpace.twist n (Spec (.of A)) (-(m a : ℤ))
  have hB (a : ι) : Subsingleton ((tensorObj (B a) T).H q) := by
    have hm : (m a : ℤ) ≤ (t : ℤ) :=
      Nat.cast_le.mpr (le_trans (hb ⟨a, rfl⟩) ht)
    have hz := isZero_moduleCohomology_projective_twist_of_nonneg A N
      (-(m a : ℤ) + t) (by omega) q hq
    obtain ⟨e, _⟩ := exists_moduleCohomology_source_comparison ℙ(n; Spec (.of A)) q
    have : Subsingleton
        ((ProjectiveSpace.twist n (Spec (.of A)) (-(m a : ℤ) + t)).H q) := by
      have := (ModuleCat.isZero_iff_subsingleton).mp hz
      exact (e _).symm.toEquiv.subsingleton
    obtain ⟨et⟩ := ProjectiveSpace.nonempty_tensorObj_twist_iso n (Spec (.of A))
      (-(m a : ℤ)) t
    exact subsingleton_H_of_iso et.symm q
  let : ∀ a, Subsingleton ((tensorObj (B a) T).H q) := hB
  have hsum : Subsingleton ((∐ fun a ↦ tensorObj (B a) T).H q) :=
    subsingleton_H_sigma (fun a ↦ tensorObj (B a) T) q
  have hsum' : Subsingleton ((tensorObj (∐ B) T).H q) :=
    @subsingleton_H_of_iso _ _ _ (PreservesCoproduct.iso (tensorRight T) B).symm q hsum
  obtain ⟨e, _⟩ := exists_moduleCohomology_source_comparison ℙ(n; Spec (.of A)) q
  exact (ModuleCat.isZero_iff_subsingleton).mpr
    (@Equiv.subsingleton _ _ (e (tensorObj (∐ B) T)).toEquiv hsum')

end AlgebraicGeometry.Scheme.Modules
