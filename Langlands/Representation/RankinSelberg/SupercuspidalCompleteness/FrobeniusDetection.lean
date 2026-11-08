import Langlands.Representation.RankinSelberg.SupercuspidalCompleteness.CuspidalDetection
import Langlands.Representation.RankinSelberg.SupercuspidalCompleteness.Conversion
import Langlands.Representation.RankinSelberg.SupercuspidalCompleteness.JacquetStatement
import Langlands.Representation.CuspidalSupport.MinimalJacquetProof
import Langlands.Representation.Parabolic.NaturalFirstAdjointness

/-!
# A Frobenius map detecting a nonzero Gelfand–Graev vector

Assuming the Jacquet module of the Gelfand–Graev representation along a standard block parabolic
is the Gelfand–Graev representation of the Levi, every nonzero Gelfand–Graev vector `h` is detected
by an intertwiner into the normalized induction of an external tensor product of irreducible
supercuspidal representations.
-/

noncomputable section

namespace Langlands.RankinSelberg.SupercuspidalCompleteness

open GeneralLinear Whittaker CuspidalSupport Induction HarmonicAnalysis

universe uF uW

section Cyclic

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- A subrepresentation of a cyclic representation containing the generator is everything. -/
theorem orbitSpan_eq_top_of_generator_mem (ρ : Representation ℂ G V) (v : V)
    (U : Subrepresentation (Cyclic.orbitSpan ρ v).toRepresentation)
    (hU : Cyclic.generator ρ v ∈ U) : U = ⊤ := by
  apply eq_top_iff.mpr
  rintro ⟨w, hw⟩ -
  change w ∈ FiniteVectors.orbitSpan ρ v at hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨g, rfl⟩ := hw
    exact U.apply_mem_toSubmodule g hU
  | zero => exact U.toSubmodule.zero_mem
  | add a b ha hb iha ihb => exact U.toSubmodule.add_mem iha ihb
  | smul c a ha iha => exact U.toSubmodule.smul_mem c iha

/-- The induced map of cyclic subrepresentations is surjective. -/
theorem cyclicMap_surjective (ρ : Representation ℂ G V) {σ : Representation ℂ G W}
    (v : V) (f : ρ.IntertwiningMap σ) : Function.Surjective (Cyclic.map ρ v f) := by
  have h := orbitSpan_eq_top_of_generator_mem σ (f v) (Cyclic.map ρ v f).range
    ⟨Cyclic.generator ρ v, rfl⟩
  intro w
  have hw : w ∈ (Cyclic.map ρ v f).range := by rw [h]; exact Submodule.mem_top
  exact hw

end Cyclic

section Frobenius

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

set_option maxHeartbeats 1600000 in
/-- Granting the Jacquet module of the Gelfand–Graev representation, every nonzero Gelfand–Graev
vector is detected by an intertwiner into the normalized induction of an external tensor product
of irreducible supercuspidal representations, with carriers in an arbitrary universe. -/
theorem exists_frobenius_ne_zero (hJ : GelfandGraevJacquetStatement.{uF})
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (n : ℕ) :
    letI := F.canonicalTopologicalData.topology
    letI := topologicalRing F.canonicalTopologicalData
    ∀ h : GelfandGraevFunctions ψ n, h ≠ 0 →
      ∃ (B : BlockShape (n + 1))
        (A : ∀ i : Fin B.length, SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := B.size i))
        (Tf : (gelfandGraev ψ n).IntertwiningMap
          (F.canonicalTopologicalData.normalizedProductInduced B
            (fun i => (A i).obj.representation))),
        Tf h ≠ 0 := by
  classical
  let T := F.canonicalTopologicalData
  let := T.topology
  let := topologicalRing T
  intro h hh
  let ρ := gelfandGraev ψ n
  have hρ : IsSmooth ρ := compactInduced_smooth _ _
  let Vs : SmoothRep.{0, uF, uF} ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) := SmoothRep.of ρ hρ
  let Hs := Cyclic.orbitSpan ρ h
  let A := SmoothRep.subrepresentation Vs Hs
  have : Nontrivial A := ⟨⟨Cyclic.generator ρ h, 0, (Cyclic.generator_ne_zero ρ h).mpr hh⟩⟩
  obtain ⟨B, hJnt, hJq⟩ := minimalNonzeroJacquet.{uF, uF} p F T (n + 1) A this
  let J := (T.normalizedJacquetFunctor B).obj A
  obtain ⟨x, hx⟩ := exists_ne (0 : J)
  obtain ⟨a, rfl⟩ := B.jacquetMk_surjective A.representation x
  -- the inclusion of the cyclic span and its Jacquet map
  let ι : A.representation.IntertwiningMap ρ :=
    { toLinearMap := Hs.toSubmodule.subtype
      isIntertwining' _ := LinearMap.ext fun _ => rfl }
  let jι := T.normalizedJacquetMap B ι
  have hjι : Function.Injective jι := by
    let := T.leviTopologicalGroup B
    let P := B.parabolic F.Carrier
    let U := B.unipotentRadical F.Carrier
    have hsm : IsSmooth ((ρ.comp P.subtype).comp U.subtype) :=
      isSmooth_comp U.subtype continuous_subtype_val
        (isSmooth_comp P.subtype continuous_subtype_val hρ)
    exact coinvariants_map_injective_of_smooth (Parabolic.unipotentFiniteContainment F T B)
      (Jacquet.restrictMap (Jacquet.restrictMap ι P) U) (Submodule.injective_subtype _) hsm
  let xbar := jι (B.jacquetMk A.representation a)
  have hxbar : xbar ≠ 0 := by
    intro h0
    apply hx
    exact hjι (h0.trans (map_zero jι).symm)
  -- quasicuspidality of the span of the image
  have hqx : IsLeviQuasicuspidal B
      (Cyclic.orbitSpan J.representation (B.jacquetMk A.representation a)).toRepresentation :=
    isLeviQuasicuspidal_subrepresentation B F T J _ hJq
  have hqxbar : IsLeviQuasicuspidal B
      (Cyclic.orbitSpan (T.normalizedJacquet B ρ) xbar).toRepresentation :=
    isLeviQuasicuspidal_of_surjective B (Cyclic.map _ _ jι) (cyclicMap_surjective _ _ jι) hqx
  -- transport to the Levi Gelfand–Graev representation
  obtain ⟨e⟩ := hJ p F ψ n B
  have hex : e xbar ≠ 0 := by
    intro h0
    exact hxbar (e.injective (h0.trans (map_zero e).symm))
  have hqe : IsLeviQuasicuspidal B
      (Cyclic.orbitSpan (leviGelfandGraev B ψ.complex) (e xbar)).toRepresentation :=
    isLeviQuasicuspidal_of_surjective B (Cyclic.map _ _ e.toIntertwiningMap)
      (cyclicMap_surjective _ _ e.toIntertwiningMap) hqxbar
  obtain ⟨Afam, Φ, hΦ⟩ := leviGelfandGraev_cuspidalDetection.{uF, uW} T B ψ.complex
    (Nat.succ_pos n) (e xbar) hex hqe
  let A' := Φ.comp e.toIntertwiningMap
  have hA' : A' xbar ≠ 0 := hΦ
  let := T.generalLinearTopologicalGroup (n + 1)
  refine ⟨B, Afam, Parabolic.FirstAdjointness.frobenius T B hρ A', ?_⟩
  intro h0
  apply hA'
  -- the Jacquet evaluation vanishes on the whole cyclic span of `h`
  let Lv : GelfandGraevFunctions ψ n →ₗ[ℂ] _ := A'.toLinearMap.comp (B.jacquetMk ρ)
  have hgen : ∀ g, Lv (ρ g h) = 0 := by
    intro g
    have h1 := Parabolic.FirstAdjointness.frobenius_eval T B hρ A' h g
    have h2 := congrArg (fun f => Induction.eval (B.parabolic F.Carrier) _ f g) h0
    exact h1.symm.trans (h2.trans rfl)
  have hvan : ∀ w ∈ Hs.toSubmodule, Lv w = 0 := by
    intro w hw
    change w ∈ FiniteVectors.orbitSpan ρ h at hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨g, rfl⟩ := hw
      exact hgen g
    | zero => exact map_zero _
    | add u v _ _ hu hv => rw [map_add, hu, hv, add_zero]
    | smul c u _ hu => rw [map_smul, hu, smul_zero]
  exact hvan a.val a.property

end Frobenius

end Langlands.RankinSelberg.SupercuspidalCompleteness
