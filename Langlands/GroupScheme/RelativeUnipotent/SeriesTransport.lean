import Langlands.GroupScheme.RelativeUnipotent.Basic
import Langlands.GroupScheme.Rational.SplitUnipotentTransport

/-! # Transport of finite vector-bundle series between representatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeUnipotent

variable {S : Scheme.{u}} {H H' : GroupScheme S}

/-- A vector-bundle normal series transports without changing its length. -/
theorem HasVectorBundleSeries.of_iso (e : H ≅ H') {n : ℕ}
    (h : HasVectorBundleSeries n H) : HasVectorBundleSeries n H' := by
  cases n with
  | zero =>
    apply SubgroupFunctor.ext
    intro T
    ext x
    rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
    constructor
    · intro _
      have hx : x ≫ e.inv.hom.hom ∈ (SubgroupFunctor.range (𝟙 H)).carrier T :=
        SubgroupFunctor.mem_range.mpr
          ⟨x ≫ e.inv.hom.hom, by
            change (x ≫ e.inv.hom.hom) ≫ 𝟙 H.X = _
            exact Category.comp_id _⟩
      rw [h, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx
      apply (isoPointsEquiv e.symm T).injective
      simpa only [isoPointsEquiv_apply, Iso.symm_hom, MonObj.one_comp] using hx
    · rintro rfl
      exact Subgroup.one_mem _
  | succ n =>
    obtain ⟨K, V, j, q, hj, hsmooth, hnormal, hquot, hvector, hseries⟩ := h
    refine ⟨K, V, j ≫ e.hom, e.inv ≫ q, ?_, hsmooth, ?_, ?_,
      hvector, hseries⟩
    · have : IsIso e.hom.hom.hom.left :=
        (inferInstance : IsIso (((Grp.forget (Over S)) ⋙ Over.forget S).map e.hom))
      have : IsClosedImmersion j.hom.hom.left := hj
      change IsClosedImmersion (j.hom.hom.left ≫ e.hom.hom.hom.left)
      infer_instance
    · rw [SubgroupFunctor.range_comp_iso]
      exact hnormal.comap e.inv
    · rw [SubgroupFunctor.range_comp_iso]
      exact hquot.comapIso e

/-- A finite vector-bundle series is invariant under group-scheme isomorphism. -/
theorem HasFiniteVectorBundleSeries.of_iso (e : H ≅ H')
    (h : HasFiniteVectorBundleSeries H) : HasFiniteVectorBundleSeries H' := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, hn.of_iso e⟩

/-- Transport a length-and-proof witness, preserving its chosen length. -/
def seriesWitnessOfIso (e : H ≅ H')
    (w : {n : ℕ // HasVectorBundleSeries n H}) :
    {n : ℕ // HasVectorBundleSeries n H'} :=
  ⟨w.val, w.property.of_iso e⟩

@[simp] lemma seriesWitnessOfIso_val (e : H ≅ H')
    (w : {n : ℕ // HasVectorBundleSeries n H}) :
    (seriesWitnessOfIso e w).val = w.val := rfl

/-- Every representative of the same all-test subgroup has a finite series
as soon as one representative does. -/
theorem hasFiniteVectorBundleSeries_of_representatives
    {G : GroupScheme S} {F : SubgroupFunctor G}
    {j : H ⟶ G} {j' : H' ⟶ G}
    (hj : F.IsRepresentedBy j) (hj' : F.IsRepresentedBy j')
    (h : HasFiniteVectorBundleSeries H) : HasFiniteVectorBundleSeries H' :=
  h.of_iso (hj.isoOfIsRepresentedBy hj')

end Langlands.GroupScheme.RelativeUnipotent
