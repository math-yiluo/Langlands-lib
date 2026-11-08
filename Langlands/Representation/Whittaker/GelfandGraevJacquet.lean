import Langlands.Representation.RankinSelberg.SupercuspidalCompleteness.JacquetStatement
import Langlands.Representation.Whittaker.GelfandGraevJacquetOpenStatement
import Langlands.Representation.Whittaker.GelfandGraevJacquetVanishing
import Langlands.Representation.Whittaker.GelfandGraevJacquetCollapse
import Langlands.Representation.Whittaker.GelfandGraevJacquetOrbits
import Langlands.Representation.Geometric.ClosedSubgroupMackeyProof
import Langlands.Representation.Geometric.CosetOrbitHomeomorph
import Langlands.Representation.Geometric.WeylMinimalRepresentativeProof
import Langlands.Representation.Twist.ContinuousCharacterProof
import Langlands.Group.GL.TriangularParabolic
import Langlands.Group.GL.UpperUnipotentCompactContainmentProof
import Langlands.Group.GL.CompactOpen

/-!
# The Jacquet module of the Gelfand–Graev representation

Let `P` be a standard block parabolic of `G = GL_(n+1)(F)` with Levi `M` and unipotent radical
`U`. Restricted to `P`, the Gelfand–Graev representation `c-Ind_N^G ψ` has the Mackey filtration
indexed by `N \ G / P`. Every piece except the open one has zero `U`-coinvariants, so the
normalized Jacquet module of `c-Ind_N^G ψ` is that of the open piece. Given the identification of
the open piece, it is the Gelfand–Graev representation of `M`.
-/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear Geometric HarmonicAnalysis

universe uF

section Radical

variable {R : Type*} [CommRing R] {n : ℕ} (B : BlockShape n)

/-- The unipotent radical of a standard block parabolic consists of upper unitriangular
matrices. -/
theorem unipotentRadical_val_mem_upperUnipotent (g : B.unipotentRadical R) :
    ((g : B.parabolic R) : Langlands.GeneralLinear n R) ∈ upperUnipotent n R := by
  have hrad := (B.mem_unipotentRadical_iff R g.val).mp g.property
  have hpar := (B.mem_parabolic_iff R g.val.val).mp g.val.property
  refine ⟨?_, ?_⟩
  · intro x y hyx
    obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective x
    obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective y
    change g.val.val (B.index i a) (B.index j b) = 0
    change B.index j b < B.index i a at hyx
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact absurd hyx (not_lt.mpr (B.index_lt_index_of_block_lt hij a b).le)
    · have hba : b < a := (Geometric.index_strictMono B i).lt_iff_lt.mp hyx
      rw [hrad i a b]
      exact ite_eq_right_iff.mpr (fun h => absurd h (ne_of_gt hba))
    · exact hpar i j a b hji
  · intro x
    obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective x
    change g.val.val (B.index i a) (B.index i a) = 1
    rw [hrad i a a]
    exact ite_eq_left_iff.mpr (fun h => absurd rfl h)

end Radical

/-- Every compact subset of the unipotent radical of a standard block parabolic lies in a compact
open subgroup. -/
theorem unipotentRadical_compactContainment (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    {n : ℕ} (B : BlockShape n) :
    letI := F.canonicalTopologicalData.topology
    ∀ C : Set (B.unipotentRadical F.Carrier), IsCompact C →
      ∃ K : OpenSubgroup (B.unipotentRadical F.Carrier),
        IsCompact (K : Set (B.unipotentRadical F.Carrier)) ∧
          C ⊆ (K : Set (B.unipotentRadical F.Carrier)) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.fieldT2
  let := F.canonicalTopologicalData.moduleTopology
  let : IsTopologicalRing F.Carrier := IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  intro C hC
  let ι : B.unipotentRadical F.Carrier →* upperUnipotent n F.Carrier :=
    { toFun := fun g => ⟨g.val.val, unipotentRadical_val_mem_upperUnipotent B g⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hιc : Continuous ι :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  let e : B.unipotentRadical F.Carrier → Langlands.GeneralLinear n F.Carrier :=
    fun g => g.val.val
  have he : Topology.IsClosedEmbedding e :=
    ((B.isClosed_parabolic F.Carrier).isClosedEmbedding_subtypeVal).comp
      ((B.isClosed_unipotentRadical F.Carrier).isClosedEmbedding_subtypeVal)
  obtain ⟨K, hK, hCK⟩ := upperUnipotentCompactContainment p inferInstance F
    F.canonicalTopologicalData n (ι '' C) (hC.image hιc)
  refine ⟨OpenSubgroup.comap ι hιc K, ?_, fun x hx => hCK ⟨x, hx, rfl⟩⟩
  have hpre : ((OpenSubgroup.comap ι hιc K : OpenSubgroup (B.unipotentRadical F.Carrier)) :
      Set (B.unipotentRadical F.Carrier)) =
      e ⁻¹' (Subtype.val '' (K : Set (upperUnipotent n F.Carrier))) := by
    ext x
    constructor
    · intro hx
      exact ⟨ι x, hx, rfl⟩
    · rintro ⟨k, hk, hkx⟩
      have hk' : k = ι x := Subtype.ext hkx
      rw [hk'] at hk
      exact hk
  rw [hpre]
  exact he.isCompact_preimage (hK.image continuous_subtype_val)

/-- A scalar character with open kernel is a smooth representation. -/
theorem isSmooth_characterRepresentation_of_isOpen_ker {H : Type*} [Group H]
    [TopologicalSpace H] (θ : H →* ℂˣ) (hθ : IsOpen (θ.ker : Set H)) :
    IsSmooth (characterRepresentation θ) :=
  fun v => ⟨⟨θ.ker, hθ⟩, by
    rw [fixedVectors, Representation.mem_invariants]
    intro k
    change (θ k.val : ℂ) • v = v
    rw [MonoidHom.mem_ker.mp k.property, Units.val_one, one_smul]⟩

/-- The Jacquet module of the Gelfand–Graev representation, assuming the identification of the
open orbit piece. -/
theorem gelfandGraevJacquet_of_openPiece (hOpen : GelfandGraevOpenPieceStatement.{uF}) :
    RankinSelberg.SupercuspidalCompleteness.GelfandGraevJacquetStatement.{uF} := by
  intro p hp F ψ n B
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (n + 1)
  let := T.generalLinearNonarchimedean (n + 1)
  let := T.generalLinearLocallyCompactSpace (n + 1)
  let := T.generalLinearSigmaCompactSpace (n + 1)
  let := T.generalLinearT2Space (n + 1)
  let := T.upperUnipotentNonarchimedean (n + 1)
  let := B.parabolicLocallyCompactSpace F.Carrier
  let N := upperUnipotent (n + 1) F.Carrier
  let P := B.parabolic F.Carrier
  let U := B.unipotentRadical F.Carrier
  let χ := gelfandGraevCharacterRepresentation ψ n
  have hχ : IsSmooth χ :=
    isSmooth_characterRepresentation_of_isOpen_ker _
      (isOpen_ker_of_continuous_complex_character _ (standardCharacterContinuous ψ n).continuous)
  have hN : IsClosed (N : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) :=
    UpperUnipotent.isClosed
  have hP : IsClosed (P : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) :=
    B.isClosed_parabolic F.Carrier
  obtain ⟨m, s, j, hrep, hwit⟩ := gelfandGraevOrbitData p F ψ n B
  let A : SmoothRep.{0, uF, 0} ℂ N := SmoothRep.of χ hχ
  let ambient := (restrictedCompactInduction (R := ℂ) N P).obj A
  let sf := s.supportFiltration (R := ℂ)
  let fs : ObjectRepFiltration ambient m :=
    ObjectRepFiltration.ofSubrepresentations (fun k => (sf.step k).obj A)
      (sf.monotone A) (sf.zero A) (sf.top A)
  -- The graded pieces of the support filtration are the Mackey orbit pieces.
  have hgr (i : Fin m) : Nonempty (Representation.Equiv (fs.gradedRepresentation i).ρ
      (Induction.compactInduced (orbitStabilizer N P (s.representative i))
        (χ.comp (stabilizerToInducing N P (s.representative i))))) := by
    obtain ⟨eg⟩ := closedSubgroupMackeyFiltration
      (Langlands.GeneralLinear (n + 1) F.Carrier) N P hN hP m s i
    exact ⟨Representation.equivOfIso (eg.app A)⟩
  have hUcpt := unipotentRadical_compactContainment p F B
  -- The pieces of the non-open orbits have no `U`-coinvariants.
  have hvan : ∀ i, i ≠ j →
      Subsingleton (Jacquet.Coinvariants (fs.gradedRepresentation i).ρ U) := by
    intro i hi
    obtain ⟨x, hxU, hxψ⟩ := hwit i hi
    obtain ⟨e⟩ := hgr i
    have : Subsingleton (Jacquet.Coinvariants
        (Induction.compactInduced (orbitStabilizer N P (s.representative i))
          (χ.comp (stabilizerToInducing N P (s.representative i)))) U) :=
      subsingleton_coinvariants_compactInduced_of_scalar U _
        (isClosed_orbitStabilizer N P (s.representative i) hN) hUcpt _ x hxU
        ((standardCharacter ψ n (stabilizerToInducing N P (s.representative i) x) : ℂˣ) : ℂ)
        (fun h => hxψ (Units.ext h)) (fun w => rfl)
    exact subsingleton_coinvariants_of_equiv U e
  have hUfin : ∀ t : Finset U, ∃ K : OpenSubgroup U, IsCompact (K : Set U) ∧ ∀ g ∈ t, g ∈ K := by
    intro t
    obtain ⟨K, hK, htK⟩ := hUcpt (t : Set U) t.finite_toSet.isCompact
    exact ⟨K, hK, fun g hg => htK hg⟩
  have hambient : IsSmooth (ambient.ρ.comp U.subtype) :=
    isSmooth_comp U.subtype continuous_subtype_val
      (isSmooth_comp P.subtype continuous_subtype_val (Induction.compactInduced_smooth N χ))
  let δ := B.topModulus (T.leviModulus B)
  let ecol := coinvariantsFiltrationEquiv U hUfin hambient fs j hvan ⊤
    B.top_le_normalizer_unipotentRadical δ
  obtain ⟨ej⟩ := hgr j
  let ep := normalizedEquivOfModulus U ⊤ B.top_le_normalizer_unipotentRadical δ ej
  have hopen (w : Langlands.GeneralLinear (n + 1) F.Carrier)
      (hw : w = B.reverseMatrix F.Carrier) :
      Nonempty (Representation.Equiv (parabolicNormalizedJacquet T B
        (Induction.compactInduced (orbitStabilizer N P w) (χ.comp (stabilizerToInducing N P w))))
        (leviGelfandGraev B ψ.complex)) := by
    subst hw
    exact hOpen p F ψ n B
  obtain ⟨eo⟩ := hopen (s.representative j) hrep
  exact ⟨((representationEquivComp ecol B.leviToTop).trans
    (representationEquivComp ep B.leviToTop)).trans eo⟩

end Langlands.Whittaker
