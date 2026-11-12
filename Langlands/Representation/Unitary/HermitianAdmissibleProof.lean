import Langlands.Representation.Unitary.HermitianRepresentationStatements
import Langlands.Representation.Smooth.Contragredient.CompactDualityProof
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Topology.LocallyProfiniteProof
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.Defs

/-! # Admissible duality and uniqueness for hermitian forms -/

noncomputable section

universe u v w

namespace Langlands.Renard.CompactRepresentation

namespace HermitianProof

def basisConjugation (V : Type v) [AddCommGroup V] [Module ℂ V] : V ≃ₗ⋆[ℂ] V :=
  let b := Module.Free.chooseBasis ℂ V
  (b.repr.trans (Finsupp.mapRange.linearEquiv (starLinearEquiv ℂ : ℂ ≃ₗ⋆[ℂ] ℂ))).trans
    b.repr.symm

theorem conjugateLinear_surjective
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type w} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (f : V →ₗ⋆[ℂ] W) (hf : Function.Injective f)
    (hdim : Module.finrank ℂ V = Module.finrank ℂ W) : Function.Surjective f := by
  let j := basisConjugation V
  let F : V →ₗ[ℂ] W := f.comp j.toLinearMap
  have hF : Function.Surjective F :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
      (hf.comp j.injective)
  intro w
  obtain ⟨v, hv⟩ := hF w
  exact ⟨j v, hv⟩

section Pairing

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type v} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
  (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
  (hinv : ∀ (g : G) (x y : V), B (ρ g x) (ρ g y) = B x y)

include hinv

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem pairing_dual_action (g : G) (x : V) :
    ρ.dual g (B x) = B (ρ g x) := by
  ext y
  change B x (ρ g⁻¹ y) = B (ρ g x) y
  simpa only [ρ.self_inv_apply] using (hinv g x (ρ g⁻¹ y)).symm

def pairingToSmoothDual (hs : IsSmooth ρ) : V →ₗ⋆[ℂ] SmoothDual ρ where
  toFun x := ⟨B x, by
    obtain ⟨K, hK⟩ := hs x
    refine ⟨K, fun k => ?_⟩
    change ρ.dual k.val (B x) = B x
    rw [pairing_dual_action ρ B hinv]
    exact congrArg B (hK k)⟩
  map_add' x y := Subtype.ext (B.map_add x y)
  map_smul' c x := Subtype.ext (B.map_smulₛₗ c x)

theorem pairingToSmoothDual_action (hs : IsSmooth ρ) (g : G) (x : V) :
    pairingToSmoothDual ρ B hinv hs (ρ g x) =
      smoothContragredient ρ g (pairingToSmoothDual ρ B hinv hs x) :=
  Subtype.ext (pairing_dual_action ρ B hinv g x).symm

omit [IsTopologicalGroup G] in
theorem pairingToSmoothDual_injective (hs : IsSmooth ρ)
    (hnd : ∀ x : V, (∀ y, B x y = 0) → x = 0) :
    Function.Injective (pairingToSmoothDual ρ B hinv hs) := by
  apply (injective_iff_map_eq_zero _).2
  intro x hx
  apply hnd x
  intro y
  exact congrArg (fun ℓ : SmoothDual ρ => ℓ.val y) hx

theorem pairingToSmoothDual_surjective
    (hcof : ∀ H : OpenSubgroup G, ∃ K : OpenSubgroup G,
      IsCompact (K : Set G) ∧ K ≤ H)
    (ha : IsAdmissible ρ) (hnd : ∀ x : V, (∀ y, B x y = 0) → x = 0) :
    Function.Surjective (pairingToSmoothDual ρ B hinv ha.1) := by
  let F := pairingToSmoothDual ρ B hinv ha.1
  have hF := pairingToSmoothDual_injective ρ B hinv ha.1 hnd
  intro ℓ
  obtain ⟨H, hH⟩ := ℓ.property
  obtain ⟨K, hK, hKH⟩ := hcof H
  let U := fixedVectors ρ K.toSubgroup
  let D := fixedVectors (smoothContragredient ρ) K.toSubgroup
  let R := smoothDualFixedRestriction ρ K.toSubgroup
  have hR := smoothDualFixedRestriction_bijective ρ ha.1 K hK
  let FK : U →ₗ⋆[ℂ] D :=
    { toFun := fun x => ⟨F x, fun k => by
        change smoothContragredient ρ k.val (F x.val) = F x.val
        rw [← pairingToSmoothDual_action]
        exact congrArg F (x.property k)⟩
      map_add' := fun x y => Subtype.ext (F.map_add x y)
      map_smul' := fun c x => Subtype.ext (F.map_smulₛₗ c x) }
  let : FiniteDimensional ℂ U := ha.2 K
  have hFR : Function.Injective (R.comp FK) := by
    intro x y hxy
    apply Subtype.ext
    apply hF
    exact congrArg Subtype.val (hR.1 hxy)
  have hsur := conjugateLinear_surjective (R.comp FK) hFR (by
    exact Subspace.dual_finrank_eq.symm)
  let ℓK : D := ⟨ℓ, fun k => Subtype.ext (hH ⟨k.val, hKH k.property⟩)⟩
  obtain ⟨x, hx⟩ := hsur (R ℓK)
  exact ⟨x.val, congrArg Subtype.val (hR.1 hx)⟩

def pairingEquiv
    (hcof : ∀ H : OpenSubgroup G, ∃ K : OpenSubgroup G,
      IsCompact (K : Set G) ∧ K ≤ H)
    (ha : IsAdmissible ρ) (hnd : ∀ x : V, (∀ y, B x y = 0) → x = 0) :
    V ≃ₗ⋆[ℂ] SmoothDual ρ :=
  LinearEquiv.ofBijective (pairingToSmoothDual ρ B hinv ha.1)
    ⟨pairingToSmoothDual_injective ρ B hinv ha.1 hnd,
      pairingToSmoothDual_surjective ρ B hinv hcof ha hnd⟩

end Pairing

theorem compactOpenCofinal
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] :
    ∀ H : OpenSubgroup G, ∃ K : OpenSubgroup G,
      IsCompact (K : Set G) ∧ K ≤ H := by
  intro H
  exact ((Topology.LocallyProfiniteProof.vanDantzig G).mp
    Topology.isLocallyProfinite_of_mathlib).2 H H.mem_nhds_one

end HermitianProof

open HermitianProof

/-- An admissible invariant nondegenerate hermitian form gives the specified
conjugate-linear equivariant equivalence with the smooth dual. -/
theorem selfDualOfHermitian : SelfDualOfHermitianStatement.{u, v} := by
  intro G _ _ _ _ _ _ π ha B _hherm hnd hinv
  refine ⟨pairingEquiv π.representation B hinv (compactOpenCofinal G) ha hnd,
    fun _ _ => rfl, ?_⟩
  exact pairingToSmoothDual_action π.representation B hinv ha.1

/-- Schur's lemma makes any two nondegenerate invariant hermitian forms on
an irreducible admissible representation nonzero real scalar multiples. -/
theorem hermitianFormUniqueness : HermitianFormUniquenessStatement.{u, v} := by
  intro G _ _ _ _ _ _ π hi ha
  dsimp only
  intro B B' hB hB'
  let e := pairingEquiv π.representation B hB.2.2 (compactOpenCofinal G) ha hB.2.1
  let e' := pairingEquiv π.representation B' hB'.2.2 (compactOpenCofinal G) ha hB'.2.1
  let T : π ≃ₗ[ℂ] π := e'.trans e.symm
  have hTe (x : π) : e (T x) = e' x := e.apply_symm_apply (e' x)
  have hTact (g : G) (x : π) : T (π.representation g x) = π.representation g (T x) := by
    apply e.injective
    rw [hTe]
    change pairingToSmoothDual π.representation B' hB'.2.2 ha.1 (π.representation g x) =
      pairingToSmoothDual π.representation B hB.2.2 ha.1 (π.representation g (T x))
    rw [pairingToSmoothDual_action, pairingToSmoothDual_action]
    exact congrArg (smoothContragredient π.representation g) (hTe x).symm
  let f : π.representation.IntertwiningMap π.representation :=
    T.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _ hTact
  obtain ⟨z, hz, _⟩ := admissibleSchur_scalarEndomorphism π.representation ha hi f
  have hscalar (x y : π) : B' x y = starRingEnd ℂ z * B x y := by
    have hTx : T x = z • x := congrArg (fun f : π.representation.IntertwiningMap
      π.representation => f x) hz
    calc
      B' x y = B (T x) y := (congrArg (fun ℓ : SmoothDual π.representation => ℓ.val y)
        (hTe x)).symm
      _ = starRingEnd ℂ z * B x y := by rw [hTx]; simp
  let := hi
  let : Nontrivial π := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π.representation.asModule
  obtain ⟨x, hx⟩ := exists_ne (0 : π)
  obtain ⟨y, hxy⟩ : ∃ y, B x y ≠ 0 := by
    by_contra! h
    exact hx (hB.2.1 x h)
  have hz0 : starRingEnd ℂ z ≠ 0 := by
    intro hz0
    apply hx
    apply hB'.2.1 x
    intro w
    rw [hscalar, hz0, zero_mul]
  have hzreal : starRingEnd ℂ z = starRingEnd ℂ (starRingEnd ℂ z) := by
    apply mul_right_cancel₀ hxy
    calc
      starRingEnd ℂ z * B x y = B' x y := (hscalar x y).symm
      _ = starRingEnd ℂ (B' y x) := by rw [hB'.1]
      _ = starRingEnd ℂ (starRingEnd ℂ z) * B x y := by
        rw [hscalar, map_mul, hB.1]; simp
  have hre : (((starRingEnd ℂ z).re : ℝ) : ℂ) = starRingEnd ℂ z :=
    Complex.conj_eq_iff_re.mp hzreal.symm
  refine ⟨(starRingEnd ℂ z).re, ?_, ?_⟩
  · intro hzero
    apply hz0
    rw [← hre, hzero, Complex.ofReal_zero]
  · intro a b
    rw [hscalar, hre]

end Langlands.Renard.CompactRepresentation
