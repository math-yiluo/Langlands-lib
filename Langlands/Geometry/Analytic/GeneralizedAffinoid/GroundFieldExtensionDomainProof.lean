import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtensionRationalChart
import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtensionDomainStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainRationalCoverProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainLocalization
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartBaseChange

/-! # Ground field extension preserves affinoid domains -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension

open Set

section Spectrum

variable {K : Type u} [NormedField K]

theorem comap_comp {A B C : Type*} [NormedCommRing A] [NormedCommRing B] [NormedCommRing C]
    [Algebra K A] [Algebra K B] [Algebra K C]
    (g : BoundedAlgHom K B C) (f : BoundedAlgHom K A B) (x : BanachSpectrum C) :
    BanachSpectrum.comap (g.comp f).toBoundedRingHom x =
      BanachSpectrum.comap f.toBoundedRingHom (BanachSpectrum.comap g.toBoundedRingHom x) :=
  BanachSpectrum.ext fun _ => rfl

variable [IsUltrametricDist K] [CompleteSpace K]

/-- A representing map has an injective spectrum map. -/
theorem comap_injective_of_represents {A B : PresentedAffinoidAlgebra K}
    {g : BoundedAlgHom K A B} {U : Set (BanachSpectrum A)} (hg : Represents K g U) :
    Function.Injective (BanachSpectrum.comap g.toBoundedRingHom) :=
  fun _ _ hxy => Domain.spectrumMap_injective (⟨B, g, U, hg⟩ : Domain K A) hxy

/-- A representing map represents the range of its spectrum map. -/
theorem represents_range {A B : PresentedAffinoidAlgebra K}
    {g : BoundedAlgHom K A B} {U : Set (BanachSpectrum A)} (hg : Represents K g U) :
    Represents K g (range (BanachSpectrum.comap g.toBoundedRingHom)) :=
  (congrArg (Represents K g) hg.2.1).mpr hg

end Spectrum

section MapEquiv

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (L : Type v) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  {A B : PresentedAffinoidAlgebra K}

/-- Ground field extension of a bounded algebra equivalence. -/
def mapEquiv (e : BoundedAlgEquiv K A B) :
    BoundedAlgEquiv L (algebra K L A) (algebra K L B) :=
  BoundedAlgEquiv.ofHomInv (map K L e.toBoundedAlgHom) (map K L e.symm.toBoundedAlgHom)
    (fun x => by
      have h : e.symm.toBoundedAlgHom.comp e.toBoundedAlgHom = BoundedAlgHom.id K A :=
        BoundedAlgHom.ext fun a => e.symm_apply_apply a
      calc map K L e.symm.toBoundedAlgHom (map K L e.toBoundedAlgHom x)
          = map K L (e.symm.toBoundedAlgHom.comp e.toBoundedAlgHom) x := by
            rw [map_comp]; rfl
        _ = x := by rw [h, map_id]; rfl)
    (fun y => by
      have h : e.toBoundedAlgHom.comp e.symm.toBoundedAlgHom = BoundedAlgHom.id K B :=
        BoundedAlgHom.ext fun b => e.apply_symm_apply b
      calc map K L e.toBoundedAlgHom (map K L e.symm.toBoundedAlgHom y)
          = map K L (e.toBoundedAlgHom.comp e.symm.toBoundedAlgHom) y := by
            rw [map_comp]; rfl
        _ = y := by rw [h, map_id]; rfl)

theorem mapEquiv_toBoundedAlgHom (e : BoundedAlgEquiv K A B) :
    (mapEquiv K L e).toBoundedAlgHom = map K L e.toBoundedAlgHom :=
  BoundedAlgHom.ext fun _ => rfl

end MapEquiv

section Pullback

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : PresentedAffinoidAlgebra K} {i : BoundedAlgHom K A B} {V : Set (BanachSpectrum A)}
  (hV : Represents K i V) (D : RationalChart K A) (α : BoundedAlgHom K B D.algebra)
  (hα : α.comp i = D.baseMap)

include hα in
/-- The arrow `α` lands in the locus of the pulled-back chart. -/
theorem hasImageIn_pullback :
    HasImageIn K α (RationalChart.pullback i D).locus := by
  intro x
  rw [RationalChart.pullback_locus]
  change BanachSpectrum.comap i.toBoundedRingHom
    (BanachSpectrum.comap α.toBoundedRingHom x) ∈ D.locus
  rw [← comap_comp, hα]
  exact D.represents.hasImageIn x

/-- The map from the pulled-back chart algebra back to the chart algebra. -/
def pullbackInverse : BoundedAlgHom K (RationalChart.pullback i D).algebra D.algebra :=
  ((RationalChart.pullback i D).represents.2.2 D.algebra α
    (hasImageIn_pullback D α hα)).exists.choose

theorem pullbackInverse_comp_baseMap :
    (pullbackInverse D α hα).comp (RationalChart.pullback i D).baseMap = α :=
  ((RationalChart.pullback i D).represents.2.2 D.algebra α
    (hasImageIn_pullback D α hα)).exists.choose_spec

theorem pullbackInverse_comp_pullbackMap :
    (pullbackInverse D α hα).comp (RationalChart.pullbackMap i D) =
      BoundedAlgHom.id K D.algebra := by
  apply D.represents.hom_ext D.algebra
  change (pullbackInverse D α hα).comp ((RationalChart.pullbackMap i D).comp D.baseMap) =
    D.baseMap
  rw [RationalChart.pullbackMap_comp_baseMap, ← BoundedAlgHom.comp_assoc,
    pullbackInverse_comp_baseMap, hα]

include hV hα in
theorem pullbackMap_comp_arrow :
    (RationalChart.pullbackMap i D).comp α = (RationalChart.pullback i D).baseMap := by
  apply hV.hom_ext (RationalChart.pullback i D).algebra
  change (RationalChart.pullbackMap i D).comp (α.comp i) = _
  rw [hα, RationalChart.pullbackMap_comp_baseMap]

include hV in
theorem pullbackMap_comp_pullbackInverse :
    (RationalChart.pullbackMap i D).comp (pullbackInverse D α hα) =
      BoundedAlgHom.id K (RationalChart.pullback i D).algebra := by
  apply (RationalChart.pullback i D).represents.hom_ext (RationalChart.pullback i D).algebra
  change (RationalChart.pullbackMap i D).comp
      ((pullbackInverse D α hα).comp (RationalChart.pullback i D).baseMap) =
    (RationalChart.pullback i D).baseMap
  rw [pullbackInverse_comp_baseMap, pullbackMap_comp_arrow hV D α hα]

/-- The chart algebra of `D` and that of its pullback along `i` are equivalent
when `D` lies over the domain represented by `i`. -/
def pullbackEquiv :
    BoundedAlgEquiv K D.algebra (RationalChart.pullback i D).algebra :=
  BoundedAlgEquiv.ofHomInv (RationalChart.pullbackMap i D) (pullbackInverse D α hα)
    (fun x => congrArg (fun φ : BoundedAlgHom K D.algebra D.algebra => φ x)
      (pullbackInverse_comp_pullbackMap D α hα))
    (fun y => congrArg (fun φ : BoundedAlgHom K (RationalChart.pullback i D).algebra
      (RationalChart.pullback i D).algebra => φ y)
      (pullbackMap_comp_pullbackInverse hV D α hα))

theorem pullback_baseMap_comp :
    (RationalChart.pullback i D).baseMap.comp i =
      (pullbackEquiv hV D α hα).toBoundedAlgHom.comp D.baseMap :=
  (RationalChart.pullbackMap_comp_baseMap i D).symm.trans
    (congrArg (fun φ => BoundedAlgHom.comp φ D.baseMap)
      (BoundedAlgHom.ext fun _ => rfl))

end Pullback

section Extension

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type v) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  {A B : PresentedAffinoidAlgebra K} {i : BoundedAlgHom K A B} {V : Set (BanachSpectrum A)}
  (hV : Represents K i V)

include hV in
/-- The extended pulled-back chart composed with the extended map represents
the range of its spectrum map. -/
theorem represents_local (D : RationalChart K A) (α : BoundedAlgHom K B D.algebra)
    (hα : α.comp i = D.baseMap) :
    Represents L ((map K L (RationalChart.pullback i D).baseMap).comp (map K L i))
      (range (BanachSpectrum.comap
        ((map K L (RationalChart.pullback i D).baseMap).comp (map K L i)).toBoundedRingHom)) := by
  have h := (represents_map_baseMap K L D).postcomp_equiv (mapEquiv K L (pullbackEquiv hV D α hα))
  rw [mapEquiv_toBoundedAlgHom, ← map_comp, ← pullback_baseMap_comp hV D α hα, map_comp] at h
  exact represents_range h

variable {n : ℕ} (D : Fin n → RationalChart K A) (α : ∀ k, BoundedAlgHom K B (D k).algebra)
  (hα : ∀ k, (α k).comp i = (D k).baseMap) (hcov : ∀ x ∈ V, ∃ k, x ∈ (D k).locus)

omit [CompleteSpace K] in
/-- The membership of a point of `B_L` in the extended pulled-back chart only
depends on its image in the spectrum of `A`. -/
theorem mem_pullback_locus_iff (k : Fin n) (y : BanachSpectrum (algebra K L B)) :
    spectrumProjection K L B y ∈ (RationalChart.pullback i (D k)).locus ↔
      spectrumProjection K L A (BanachSpectrum.comap (map K L i).toBoundedRingHom y) ∈
        (D k).locus := by
  rw [RationalChart.pullback_locus, spectrumProjection_naturality]
  rfl

/-- The ground field extensions of the pulled-back charts cover `B_L`. -/
def extendedCover : Domain.FiniteCover (Domain.whole L (algebra K L B)) where
  size := n
  obj k :=
    { algebra := algebra K L (RationalChart.pullback i (D k)).algebra
      baseMap := map K L (RationalChart.pullback i (D k)).baseMap
      locus := spectrumProjection K L B ⁻¹' (RationalChart.pullback i (D k)).locus
      represents := represents_map_baseMap K L (RationalChart.pullback i (D k)) }
  map k := Domain.inclusionOfSubset _ _ (subset_univ _)
  covers y _ := by
    have hy : spectrumProjection K L A (BanachSpectrum.comap (map K L i).toBoundedRingHom y) ∈ V := by
      rw [spectrumProjection_naturality]
      exact hV.hasImageIn _
    obtain ⟨k, hk⟩ := hcov _ hy
    exact ⟨k, (mem_pullback_locus_iff K L D k y).2 hk⟩

include hV hα hcov in
/-- The spectrum map of the extended map is injective. -/
theorem comap_map_injective :
    Function.Injective (BanachSpectrum.comap (map K L i).toBoundedRingHom) := by
  intro y₁ y₂ hy
  have hy₁ : spectrumProjection K L A (BanachSpectrum.comap (map K L i).toBoundedRingHom y₁) ∈ V := by
    rw [spectrumProjection_naturality]
    exact hV.hasImageIn _
  obtain ⟨k, hk⟩ := hcov _ hy₁
  have hR := represents_map_baseMap K L (RationalChart.pullback i (D k))
  have h₁ : y₁ ∈ range (BanachSpectrum.comap
      (map K L (RationalChart.pullback i (D k)).baseMap).toBoundedRingHom) := by
    rw [hR.2.1]
    exact (mem_pullback_locus_iff K L D k y₁).2 hk
  have h₂ : y₂ ∈ range (BanachSpectrum.comap
      (map K L (RationalChart.pullback i (D k)).baseMap).toBoundedRingHom) := by
    rw [hR.2.1]
    exact (mem_pullback_locus_iff K L D k y₂).2 (hy ▸ hk)
  obtain ⟨w₁, rfl⟩ := h₁
  obtain ⟨w₂, rfl⟩ := h₂
  have hinj := comap_injective_of_represents (represents_local K L hV (D k) (α k) (hα k))
  rw [← comap_comp, ← comap_comp] at hy
  rw [hinj hy]

include hV hα hcov in
/-- The spectrum map of the extended map has image the preimage of `V`. -/
theorem range_comap_map :
    range (BanachSpectrum.comap (map K L i).toBoundedRingHom) =
      spectrumProjection K L A ⁻¹' V := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    change spectrumProjection K L A (BanachSpectrum.comap (map K L i).toBoundedRingHom y) ∈ V
    rw [spectrumProjection_naturality]
    exact hV.hasImageIn _
  · intro hz
    obtain ⟨k, hk⟩ := hcov _ hz
    have hR := represents_map_baseMap K L (D k)
    have hz' : z ∈ range (BanachSpectrum.comap (map K L (D k).baseMap).toBoundedRingHom) := by
      rw [hR.2.1]
      exact hk
    obtain ⟨w, rfl⟩ := hz'
    refine ⟨BanachSpectrum.comap (map K L (α k)).toBoundedRingHom w, ?_⟩
    rw [← comap_comp, ← map_comp, hα k]

include hV hα hcov in
theorem represents_of_rationalCover :
    Represents L (map K L i) (spectrumProjection K L A ⁻¹' V) := by
  have h := (extendedCover K L hV D hcov).represents_of_finiteCover (map K L i)
    (comap_map_injective K L hV D α hα hcov)
    (fun k => represents_local K L hV (D k) (α k) (hα k))
  rw [range_comap_map K L hV D α hα hcov] at h
  exact h

end Extension

/-- Ground field extension preserves affinoid domains. -/
theorem domainPreservation : DomainPreservationStatement.{u, v} := by
  intro K _ _ _ L _ _ _ _ A B i V hV
  obtain ⟨n, D, h, hcov⟩ := Domain.finiteRationalCover K A ⟨B, i, V, hV⟩
  exact represents_of_rationalCover K L hV D (fun k => (h k).restriction)
    (fun k => (h k).comp_baseMap) hcov

end Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension
