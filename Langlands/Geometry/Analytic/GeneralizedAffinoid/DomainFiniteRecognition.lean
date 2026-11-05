import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBaseChange
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBoundedMapGluing
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCancellation

/-! # Full domain recognition from an actual finite domain cover -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover

open CategoryTheory Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : PresentedAffinoidAlgebra K} (c : FiniteCover (Domain.whole K A))
  (f : BoundedAlgHom K B A)
  (hinj : Function.Injective (BanachSpectrum.comap f.toBoundedRingHom))
  (hlocal : ∀ i, Represents K ((c.obj i).baseMap.comp f)
    (Set.range (BanachSpectrum.comap ((c.obj i).baseMap.comp f).toBoundedRingHom)))

/-- The unchanged component algebra is a full domain over the new base
when the actual composite map satisfies the full affinoid-test property. -/
def recognitionComponent (i : Fin c.size) : Domain K B where
  algebra := (c.obj i).algebra
  baseMap := (c.obj i).baseMap.comp f
  locus := Set.range (BanachSpectrum.comap ((c.obj i).baseMap.comp f).toBoundedRingHom)
  represents := hlocal i

include hinj hlocal in
/-- Spectral injectivity supplies image containment; two full universal
properties then prove equality of the entire bounded algebra maps. -/
theorem hom_eq_of_local_over_base (i : Fin c.size) (R : PresentedAffinoidAlgebra K)
    (g : BoundedAlgHom K A R) (k : BoundedAlgHom K (c.obj i).algebra R)
    (heq : g.comp f = (k.comp (c.obj i).baseMap).comp f) :
    g = k.comp (c.obj i).baseMap := by
  have hg : HasImageIn K g (c.obj i).locus := by
    intro x
    have hx : BanachSpectrum.comap g.toBoundedRingHom x =
        BanachSpectrum.comap (k.comp (c.obj i).baseMap).toBoundedRingHom x := by
      apply hinj
      exact BanachSpectrum.ext fun b =>
        congrArg (fun q : BoundedAlgHom K B R => x (q b)) heq
    rw [hx]
    exact (c.obj i).represents.hasImageIn (BanachSpectrum.comap k.toBoundedRingHom x)
  obtain ⟨δ, hδ, _⟩ := (c.obj i).represents.2.2 R g hg
  have hδk : δ = k := by
    apply (hlocal i).hom_ext R
    rw [← BoundedAlgHom.comp_assoc, hδ]
    exact heq
  exact hδ.symm.trans (congrArg (fun q : BoundedAlgHom K (c.obj i).algebra R =>
    q.comp (c.obj i).baseMap) hδk)

variable (R : PresentedAffinoidAlgebra K) (φ : BoundedAlgHom K B R)
  (hφ : HasImageIn K φ (Set.range (BanachSpectrum.comap f.toBoundedRingHom)))

/-- The local target domains pull back to an actual finite full-domain
cover of the unchanged test algebra whenever its image lies in the source. -/
def recognitionTestCover : FiniteCover (Domain.whole K R) where
  size := c.size
  obj i := Domain.pullback φ (c.recognitionComponent f hlocal i)
  map i := ⟨(Domain.pullback φ (c.recognitionComponent f hlocal i)).baseMap, rfl⟩
  covers x _ := by
    obtain ⟨y, hy⟩ := hφ x
    obtain ⟨i, hi⟩ := c.covers y (Set.mem_univ y)
    obtain ⟨z, hz⟩ := (c.obj i).represents.2.1.symm ▸ hi
    refine ⟨i, z, ?_⟩
    change BanachSpectrum.comap f.toBoundedRingHom
      (BanachSpectrum.comap (c.obj i).baseMap.toBoundedRingHom z) =
      BanachSpectrum.comap φ.toBoundedRingHom x
    rw [hz]
    exact hy

/-- Each local factor is the actual second pushout leg composed with
the original source restriction. -/
def recognitionLocalFactor (i : Fin c.size) :
    BoundedAlgHom K A ((c.recognitionTestCover f hlocal R φ hφ).obj i).algebra :=
  (Domain.pullbackMap φ (c.recognitionComponent f hlocal i)).comp (c.obj i).baseMap

theorem recognitionLocalFactor_comp (i : Fin c.size) :
    (c.recognitionLocalFactor f hlocal R φ hφ i).comp f =
      ((c.recognitionTestCover f hlocal R φ hφ).obj i).baseMap.comp φ :=
  Domain.pullbackMap_comp_baseMap φ (c.recognitionComponent f hlocal i)

include hinj in
/-- Full-map local cancellation proves compatibility after every actual
full-domain test into any two members of the test cover. -/
theorem recognitionLocalFactor_compatible :
    (c.recognitionTestCover f hlocal R φ hφ).BoundedMapCompatible
      (c.recognitionLocalFactor f hlocal R φ hφ) := by
  intro i j T p q
  let g := p.restriction.comp (c.recognitionLocalFactor f hlocal R φ hφ i)
  let k := q.restriction.comp (Domain.pullbackMap φ (c.recognitionComponent f hlocal j))
  apply c.hom_eq_of_local_over_base f hinj hlocal j T.algebra g k
  change p.restriction.comp
      ((c.recognitionLocalFactor f hlocal R φ hφ i).comp f) =
    q.restriction.comp
      ((c.recognitionLocalFactor f hlocal R φ hφ j).comp f)
  rw [c.recognitionLocalFactor_comp f hlocal R φ hφ i,
    c.recognitionLocalFactor_comp f hlocal R φ hφ j,
    ← BoundedAlgHom.comp_assoc, p.comp_baseMap,
    ← BoundedAlgHom.comp_assoc, q.comp_baseMap]

/-- Glue the full compatible local factors in the unchanged target
algebra, retaining the proved global norm bound. -/
def recognitionFactor : BoundedAlgHom K A R :=
  (c.recognitionTestCover f hlocal R φ hφ).glueBoundedAlgHom
    (c.recognitionLocalFactor f hlocal R φ hφ)
    (c.recognitionLocalFactor_compatible f hinj hlocal R φ hφ)

theorem recognitionFactor_comp :
    (c.recognitionFactor f hinj hlocal R φ hφ).comp f = φ := by
  apply BoundedAlgHom.ext
  intro b
  apply (c.recognitionTestCover f hlocal R φ hφ).algebra_ext_of_restrict_eq
  intro i
  have h := congrArg (fun q : BoundedAlgHom K A
      ((c.recognitionTestCover f hlocal R φ hφ).obj i).algebra => q (f b))
    ((c.recognitionTestCover f hlocal R φ hφ).restriction_comp_glueBoundedAlgHom
      (c.recognitionLocalFactor f hlocal R φ hφ)
      (c.recognitionLocalFactor_compatible f hinj hlocal R φ hφ) i)
  exact h.trans (congrArg (fun q : BoundedAlgHom K B
    ((c.recognitionTestCover f hlocal R φ hφ).obj i).algebra => q b)
      (c.recognitionLocalFactor_comp f hlocal R φ hφ i))

theorem recognitionFactor_unique (ψ : BoundedAlgHom K A R) (hψ : ψ.comp f = φ) :
    ψ = c.recognitionFactor f hinj hlocal R φ hφ := by
  apply (c.recognitionTestCover f hlocal R φ hφ).glueBoundedAlgHom_unique
  intro i
  apply c.hom_eq_of_local_over_base f hinj hlocal i
    ((c.recognitionTestCover f hlocal R φ hφ).obj i).algebra
  change ((c.recognitionTestCover f hlocal R φ hφ).obj i).baseMap.comp (ψ.comp f) =
    (c.recognitionLocalFactor f hlocal R φ hφ i).comp f
  rw [hψ, c.recognitionLocalFactor_comp f hlocal R φ hφ i]

include hinj hlocal in
/-- A spectrally injective map is a full domain representation if its
composites with an actual finite full-domain cover are full representations. -/
theorem represents_of_finiteCover :
    Represents K f (Set.range (BanachSpectrum.comap f.toBoundedRingHom)) := by
  refine ⟨(isCompact_range (BanachSpectrum.comapContinuous
    f.toBoundedRingHom).continuous).isClosed, rfl, ?_⟩
  intro R φ hφ
  exact ⟨c.recognitionFactor f hinj hlocal R φ hφ,
    c.recognitionFactor_comp f hinj hlocal R φ hφ,
    fun ψ hψ => c.recognitionFactor_unique f hinj hlocal R φ hφ ψ hψ⟩

/-- The recognized full domain retains exactly the given algebra and
bounded structural map. Only its full-test proof is newly constructed. -/
def domainOfFiniteCover : Domain K B where
  algebra := A
  baseMap := f
  locus := Set.range (BanachSpectrum.comap f.toBoundedRingHom)
  represents := c.represents_of_finiteCover f hinj hlocal

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover
