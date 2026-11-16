import Langlands.Geometry.Analytic.EtaleOpenMap.FiniteBanachLyingOver
import Langlands.Geometry.Analytic.AffinoidPointwiseEtale
import Langlands.Geometry.Analytic.GeneralizedAffinoid.Noetherian
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # The image of a finite Banach map at a flat point -/

noncomputable section

universe u v w

namespace Langlands.Analytic.BoundedAlgHom

open Filter
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {R : Type v} [NormedCommRing R] [NormedAlgebra K R]
  {S : Type w} [NormedCommRing S] [NormedAlgebra K S]

omit [IsUltrametricDist K] in
/-- Over a Noetherian base, flatness at a point gives an element nonzero at
its image which annihilates the kernel of the ring map. -/
theorem IsFlatAtPoint.exists_annihilator_kernel [IsNoetherianRing R]
    {f : BoundedAlgHom K R S} {y : BanachSpectrum S} (hy : f.IsFlatAtPoint y) :
    ∃ r : R, (BanachSpectrum.comap f.toBoundedRingHom y) r ≠ 0 ∧
      ∀ a ∈ RingHom.ker f.toAlgHom.toRingHom, r * a = 0 := by
  classical
  let p := (BanachSpectrum.comap f.toBoundedRingHom y).kernel
  let q := y.kernel
  let g := Localization.localRingHom p q f.toAlgHom.toRingHom (f.kernel_comap y)
  have hg : g.Flat := hy
  have hinj : Function.Injective g := by
    let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) := g.toAlgebra
    have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) := hg
    have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) :=
      inferInstanceAs (IsLocalHom g)
    have : Module.FaithfullyFlat (Localization.AtPrime p) (Localization.AtPrime q) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact FaithfulSMul.algebraMap_injective _ _
  obtain ⟨s, hs⟩ := (isNoetherianRing_iff_ideal_fg R).mp inferInstance
    (RingHom.ker f.toAlgHom.toRingHom)
  have hz (x : s) : algebraMap R (Localization.AtPrime p) x.1 = 0 := by
    apply hinj
    rw [map_zero]
    change Localization.localRingHom p q f.toAlgHom.toRingHom (f.kernel_comap y)
      (algebraMap R (Localization.AtPrime p) x.1) = 0
    rw [Localization.localRingHom_to_map]
    have hx : f x.1 = 0 := hs.le (Ideal.subset_span x.2)
    change (algebraMap S (Localization.AtPrime q)) (f x.1) = 0
    rw [hx, map_zero]
  choose m hm using fun x =>
    (IsLocalization.map_eq_zero_iff p.primeCompl (Localization.AtPrime p) x.1).mp (hz x)
  let r : p.primeCompl := ∏ i : s, m i
  refine ⟨r.1, r.2, ?_⟩
  have hr : r.1 ∈ (RingHom.ker f.toAlgHom.toRingHom).annihilator := by
    rw [← hs, Submodule.mem_annihilator_span]
    intro a
    change (∏ i : s, m i).1 * a.1 = 0
    simp only [SubmonoidClass.coe_finsetProd]
    rw [Fintype.prod_eq_mul_prod_compl (show s from a)]
    rw [mul_assoc, mul_left_comm, hm, mul_zero]
  exact Submodule.mem_annihilator.mp hr

/-- The spectral image of a finite Banach map over a Noetherian base contains
a neighborhood of the image of any flat point. -/
theorem IsFlatAtPoint.range_comap_mem_nhds [IsNoetherianRing R]
    {f : BoundedAlgHom K R S} (hfin : f.IsFiniteBanach) {y : BanachSpectrum S}
    (hy : f.IsFlatAtPoint y) :
    Set.range (BanachSpectrum.comap f.toBoundedRingHom) ∈
      𝓝 (BanachSpectrum.comap f.toBoundedRingHom y) := by
  obtain ⟨r, hr, hann⟩ := hy.exists_annihilator_kernel
  have hO : {x : BanachSpectrum R | x r ≠ 0} ∈
      𝓝 (BanachSpectrum.comap f.toBoundedRingHom y) :=
    (isClosed_eq (BanachSpectrum.evaluation r).continuous continuous_const).isOpen_compl.mem_nhds hr
  refine Filter.mem_of_superset hO fun x hx => ?_
  apply BanachSpectrum.exists_comap_eq_of_isFiniteBanach f hfin x
  intro a ha
  change x a = 0
  have hmul : x r * x a = 0 := by rw [← map_mul, hann a ha, map_zero]
  exact (mul_eq_zero.mp hmul).resolve_left hx

end Langlands.Analytic.BoundedAlgHom
