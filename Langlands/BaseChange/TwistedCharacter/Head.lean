import Langlands.BaseChange.TwistedCharacter.Devissage
import Langlands.BaseChange.TwistedCharacter.EquivariantLine
import Langlands.Representation.Classification.CanonicalConstituents

/-! # Twisted traces and the canonical head of a smooth representation -/

noncomputable section

namespace Langlands.BaseChange

open Classification HarmonicAnalysis MeasureTheory

universe uG uV

section Algebra

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}

private theorem map_headKernel_le (θ : G ≃* G) (A : ρ.Equiv (ρ.comp θ.toMonoidHom)) :
    (headKernel ρ).toSubmodule.map A.toLinearMap ≤ (headKernel ρ).toSubmodule := by
  rw [Submodule.map_le_iff_le_comap]
  intro v hv
  change A v ∈ (headKernel ρ).toSubmodule
  rw [mem_headKernel_iff] at hv ⊢
  intro W _ _ π hπ q hq
  let qθ : Representation.IntertwiningMap (ρ.comp θ.toMonoidHom) (π.comp θ.toMonoidHom) :=
    ⟨q.toLinearMap, fun g => q.isIntertwining' (θ g)⟩
  exact hv W (π.comp θ.toMonoidHom)
    ((CuspidalSupport.isIrreducible_comp_mulEquiv_iff π θ).mpr hπ)
    (qθ.comp A.toIntertwiningMap) (hq.comp A.surjective)

/-- A twisting isomorphism maps the canonical head kernel onto itself. -/
theorem map_headKernel_eq (θ : G ≃* G) (A : ρ.Equiv (ρ.comp θ.toMonoidHom)) :
    (headKernel ρ).toSubmodule.map A.toLinearMap = (headKernel ρ).toSubmodule := by
  refine le_antisymm (map_headKernel_le θ A) ?_
  intro v hv
  exact ⟨A.symm v, map_headKernel_le θ.symm (inverseTwistingEquiv θ A) ⟨v, hv, rfl⟩,
    A.apply_symm_apply v⟩

end Algebra

section Trace

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
  (θ : G ≃* G) (L : Submodule ℂ (Distribution G))

/-- If a subspace contains the twisted trace of an admissible finite-length representation
and the twisted traces of all irreducible subquotients of its head kernel, it contains
the twisted trace of its irreducible head with any twisting isomorphism. -/
theorem twistedDistribution_mem_of_irreducibleHead
    (B : SmoothRep.{0,uG,uV} ℂ G) (hB : B.IsAdmissible) (hBfin : B.HasFiniteLength)
    (A : B.representation.Equiv (B.representation.comp θ.toMonoidHom))
    (hA : twistedDistribution μ B.representation hB A.toLinearMap ∈ L)
    (π : SmoothRep.{0,uG,uV} ℂ G) (hπ : π.IsAdmissible)
    (hhead : IsIrreducibleHead B.representation π.representation)
    (Aπ : π.representation.Equiv (π.representation.comp θ.toMonoidHom))
    (hspan : ∀ (D : SmoothRep.{0,uG,uV} ℂ G) (hD : D.IsAdmissible), D.IsIrreducible →
      SmoothRep.IsSubquotient D (B.subrepresentation (headKernel B.representation)) →
      ∀ AD : D.representation.Equiv (D.representation.comp θ.toMonoidHom),
        twistedDistribution μ D.representation hD AD.toLinearMap ∈ L) :
    twistedDistribution μ π.representation hπ Aπ.toLinearMap ∈ L := by
  let S := headKernel B.representation
  let K := B.subrepresentation S
  let Q := B.headQuotient
  let i := SmoothRep.hom (B.subtype S)
  let q := SmoothRep.hom B.toHeadQuotient
  have hi := B.subtype_injective S
  have hq := B.toHeadQuotient_surjective
  have hseq : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap := by
    change LinearMap.range S.toSubmodule.subtype = LinearMap.ker S.toSubmodule.mkQ
    rw [Submodule.range_subtype, Submodule.ker_mkQ]
  have hcofinal (U : OpenSubgroup G) :
      ∃ J : OpenSubgroup G, IsCompact (J : Set G) ∧ J ≤ U := by
    obtain ⟨J, hJU, hJ, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ U
    exact ⟨J, hJ, hJU⟩
  obtain ⟨hK, hQ⟩ := (isAdmissible_iff_of_shortExact hcofinal i q hi hq hseq B.isSmooth).mp hB
  have hS := map_headKernel_eq θ A
  let AK := subrepresentationTwistingEquiv θ S A hS
  let AQ := quotientTwistingEquiv θ S A hS
  have hKfin : K.HasFiniteLength := hBfin.of_injective
    (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ i) hi
  have hKL := twistedDistribution_mem_of_finiteLength μ θ L K hK hKfin AK hspan
  have hT : twistedDistribution μ B.representation hB A.toLinearMap =
      twistedDistribution μ K.representation hK AK.toLinearMap +
        twistedDistribution μ Q.representation hQ AQ.toLinearMap :=
    twistedDistribution_shortExact μ hK hB hQ i q hi hq hseq
      AK.toLinearMap A.toLinearMap AQ.toLinearMap rfl rfl
  have hQL : twistedDistribution μ Q.representation hQ AQ.toLinearMap ∈ L := by
    rw [hT] at hA
    simpa only [add_sub_cancel_left] using L.sub_mem hA hKL
  obtain ⟨e⟩ := hhead.nonempty_headEquiv
  have hQirr : Q.representation.IsIrreducible := hhead.isIrreducibleHead_head.1
  obtain ⟨c, hc⟩ := exists_twistedDistribution_eq_smul_of_equiv μ θ hQ hQirr hπ e AQ Aπ
  rw [hc]
  exact L.smul_mem c hQL

end Trace

end Langlands.BaseChange
