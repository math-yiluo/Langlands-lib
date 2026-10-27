import Langlands.Representation.Whittaker.UnipotentOrbitStatement
import Langlands.Representation.Geometric.PadicParabolicBruhatProof
import Langlands.Representation.Geometric.ClosedSubgroupOrbitOrdering
import Langlands.Group.GL.CountabilityProof
import Langlands.Group.GL.CompactOpen
import Langlands.Group.GL.TriangularParabolic

/-! Full upper-unipotent orbit classification and exact ordered representatives. -/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear

universe uF

private theorem singletonLevi_conjugate_mem_parabolic
    {R : Type uF} [CommRing R] {n : ℕ} (B : BlockShape n)
    (m : (BlockShape.singletons n).Levi R) (w : Equiv.Perm (Fin n)) :
    permutation n R w * (BlockShape.singletons n).leviEmbedding R m *
        (permutation n R w)⁻¹ ∈ B.parabolic R := by
  apply B.mem_parabolic_of_isUpperTriangular
  intro i j hji
  rw [permutation_conjugate_entry]
  have hij : w⁻¹ i ≠ w⁻¹ j :=
    fun h => (ne_of_gt hji) ((Equiv.injective _) h)
  have hd :=
    (BlockShape.singletons n).leviEmbedding_apply_ne R m (0 : Fin 1) (0 : Fin 1) hij
  rw [BlockShape.singletons_index (w⁻¹ i) 0,
    BlockShape.singletons_index (w⁻¹ j) 0] at hd
  exact hd

private theorem singletonParabolic_factor
    {R : Type uF} [CommRing R] {n : ℕ}
    (b : (BlockShape.singletons n).parabolic R) :
    ∃ (m : (BlockShape.singletons n).Levi R) (u : upperUnipotent n R),
      (b : GeneralLinear n R) =
        (BlockShape.singletons n).leviEmbedding R m * (u : GeneralLinear n R) := by
  let C := BlockShape.singletons n
  let m := C.leviProjection R b
  let d := C.leviInParabolic R m
  let v : C.unipotentRadical R := ⟨d⁻¹ * b, by
    change C.leviProjection R (d⁻¹ * b) = 1
    simp [d, m]⟩
  refine ⟨m, (BlockShape.upperUnipotentEquivRadical R).symm v, ?_⟩
  change (b : GeneralLinear n R) = (d : GeneralLinear n R) *
    ((d : GeneralLinear n R)⁻¹ * (b : GeneralLinear n R))
  simp

private theorem fullUnipotent_bijective_of_parabolic
    {R : Type uF} [CommRing R] {n : ℕ} (B : BlockShape n)
    (h : Function.Bijective
      (Geometric.parabolicDoubleCoset R B (BlockShape.singletons n))) :
    Function.Bijective
      (fun w : Geometric.MinimalRepresentatives B (BlockShape.singletons n) =>
        DoubleCoset.mk (B.parabolic R) (upperUnipotent n R)
          (permutation n R w.val)⁻¹) := by
  let C := BlockShape.singletons n
  constructor
  · intro v w hvw
    apply h.1
    obtain ⟨a, ha, b, hb, heq⟩ := DoubleCoset.eq.mp hvw
    apply DoubleCoset.eq.mpr
    exact ⟨a, ha, b, (BlockShape.singletons_mem_parabolic_iff R b).mpr hb.1, heq⟩
  · intro q
    obtain ⟨g, rfl⟩ := Quotient.exists_rep q
    obtain ⟨w, hw⟩ := h.2 (DoubleCoset.mk (B.parabolic R) (C.parabolic R) g)
    obtain ⟨a, ha, b, hb, heq⟩ := DoubleCoset.eq.mp hw
    obtain ⟨m, u, hfactor⟩ := singletonParabolic_factor (⟨b, hb⟩ : C.parabolic R)
    change b = C.leviEmbedding R m * (u : GeneralLinear n R) at hfactor
    refine ⟨w, DoubleCoset.eq.mpr ?_⟩
    refine ⟨a * ((permutation n R w.val)⁻¹ * C.leviEmbedding R m *
        permutation n R w.val), (B.parabolic R).mul_mem ha ?_,
      u, u.property, ?_⟩
    · simpa only [map_inv, inv_inv] using
        singletonLevi_conjugate_mem_parabolic B m w.val⁻¹
    · rw [heq, hfactor]
      simp only [mul_assoc, mul_inv_cancel_left]

/-- The actual inverse minimal permutation matrices classify full upper-unipotent
double cosets and can be stored in an ordering with open initial unions. -/
theorem unipotentOrbit : UnipotentOrbitStatement.{uF} := by
  intro p hp F
  let := F.canonicalTopologicalData.topology
  intro n B
  let T := F.canonicalTopologicalData
  let := T.generalLinearTopologicalGroup (n + 1)
  let := T.fieldT2
  let := T.generalLinearT2Space (n + 1)
  let := T.generalLinearLocallyCompactSpace (n + 1)
  let := T.generalLinearNonarchimedean (n + 1)
  let := T.generalLinearSigmaCompactSpace (n + 1)
  let P := B.parabolic F.Carrier
  let U := upperUnipotent (n + 1) F.Carrier
  have h := fullUnipotent_bijective_of_parabolic B
    (Geometric.padicParabolicBruhat p F (n + 1) (Nat.succ_pos n) B
      (BlockShape.singletons (n + 1)))
  refine ⟨h, ?_⟩
  let : Finite (DoubleCoset.Quotient (P : Set (GeneralLinear (n + 1) F.Carrier))
      (U : Set (GeneralLinear (n + 1) F.Carrier))) :=
    Finite.of_surjective _ h.2
  obtain ⟨m, ⟨s⟩⟩ := Geometric.closedSubgroupOrbitOrdering
    (GeneralLinear (n + 1) F.Carrier) P U (B.isClosed_parabolic F.Carrier)
    (UpperUnipotent.isClosed (R := F.Carrier)) inferInstance
  obtain ⟨e, t, ht⟩ := s.classifiedRepresentatives
    (fun w : Geometric.MinimalRepresentatives B (BlockShape.singletons (n + 1)) =>
      permutation (n + 1) F.Carrier w.val) h
  exact ⟨m, t, e, ht⟩

end Langlands.Whittaker
