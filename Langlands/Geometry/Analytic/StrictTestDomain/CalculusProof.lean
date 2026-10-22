import Langlands.Geometry.Analytic.StrictTestDomain.CalculusStatement

/-! # Universal-property calculus for strict-test domain representations -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

private theorem spectrum_comp {P Q R : PresentedStrictAffinoidAlgebra K}
    (i : BoundedAlgHom K P Q) (j : BoundedAlgHom K Q R) (x : BanachSpectrum R) :
    BanachSpectrum.comap (j.comp i).toBoundedRingHom x =
      BanachSpectrum.comap i.toBoundedRingHom
        (BanachSpectrum.comap j.toBoundedRingHom x) := by
  apply BanachSpectrum.ext
  intro a
  rfl

/-- A representing map has its spectrum image in the represented subset. -/
theorem Represents.hasImageIn {P Q : PresentedStrictAffinoidAlgebra K}
    {i : BoundedAlgHom K P Q} {U : Set (BanachSpectrum P)}
    (hi : Represents K i U) : HasImageIn K i U := by
  intro x
  rw [← hi.2.1]
  exact ⟨x, rfl⟩

/-- The bounded identity represents the whole spectrum. -/
theorem represents_id (P : PresentedStrictAffinoidAlgebra K) :
    Represents K (BoundedAlgHom.id K P) Set.univ := by
  refine ⟨isClosed_univ, ?_, ?_⟩
  · apply Set.eq_univ_of_forall
    intro x
    exact ⟨x, BanachSpectrum.ext fun _ => rfl⟩
  · intro R φ _
    exact ⟨φ, BoundedAlgHom.comp_id φ, fun ψ hψ => by simpa using hψ⟩

private theorem inverse_comp (Q Q' : PresentedStrictAffinoidAlgebra K)
    (e : BoundedAlgEquiv K Q Q') :
    e.symm.toBoundedAlgHom.comp e.toBoundedAlgHom = BoundedAlgHom.id K Q := by
  ext a
  exact e.symm_apply_apply a

/-- Postcomposition with a bounded equivalence preserves representation. -/
theorem Represents.postcomp_equiv {P Q Q' : PresentedStrictAffinoidAlgebra K}
    {i : BoundedAlgHom K P Q} {U : Set (BanachSpectrum P)}
    (hi : Represents K i U) (e : BoundedAlgEquiv K Q Q') :
    Represents K (e.toBoundedAlgHom.comp i) U := by
  refine ⟨hi.1, ?_, ?_⟩
  · rw [← hi.2.1]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨e.spectrumHomeomorph y, (spectrum_comp i e.toBoundedAlgHom y).symm⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨z, hz⟩ := e.spectrumHomeomorph.surjective y
      exact ⟨z, (spectrum_comp i e.toBoundedAlgHom z).trans
        (congrArg (BanachSpectrum.comap i.toBoundedRingHom) hz)⟩
  · intro R φ hφ
    obtain ⟨ψ, hψ, huniq⟩ := hi.2.2 R φ hφ
    refine ⟨ψ.comp e.symm.toBoundedAlgHom, ?_, ?_⟩
    · change (ψ.comp e.symm.toBoundedAlgHom).comp (e.toBoundedAlgHom.comp i) = φ
      rw [BoundedAlgHom.comp_assoc ψ, ← BoundedAlgHom.comp_assoc e.symm.toBoundedAlgHom,
        inverse_comp, BoundedAlgHom.id_comp]
      exact hψ
    · intro χ hχ
      have hχψ : χ.comp e.toBoundedAlgHom = ψ :=
        huniq _ (by simpa only [BoundedAlgHom.comp_assoc] using hχ)
      apply BoundedAlgHom.ext
      intro a
      have h := congrArg (fun f : BoundedAlgHom K Q R => f (e.symm a)) hχψ
      simpa using h

/-- Bounded-equivalence postcomposition preserves and reflects representation. -/
theorem represents_postcomp_equiv_iff (P Q Q' : PresentedStrictAffinoidAlgebra K)
    (i : BoundedAlgHom K P Q) (e : BoundedAlgEquiv K Q Q')
    (U : Set (BanachSpectrum P)) :
    Represents K (e.toBoundedAlgHom.comp i) U ↔ Represents K i U := by
  constructor
  · intro h
    have h' := h.postcomp_equiv e.symm
    rw [← BoundedAlgHom.comp_assoc, inverse_comp, BoundedAlgHom.id_comp] at h'
    exact h'
  · exact fun h => h.postcomp_equiv e

private theorem equiv_ext {Q Q' : PresentedStrictAffinoidAlgebra K}
    {e d : BoundedAlgEquiv K Q Q'} (h : e.toBoundedAlgHom = d.toBoundedAlgHom) :
    e = d := by
  cases e
  cases d
  congr 1
  apply AlgEquiv.ext
  intro a
  exact congrArg (fun f : BoundedAlgHom K Q Q' => f a) h

/-- Two representations of the same subset admit a unique bounded comparison. -/
theorem represents_unique_comparison (P Q Q' : PresentedStrictAffinoidAlgebra K)
    (i : BoundedAlgHom K P Q) (i' : BoundedAlgHom K P Q')
    (U : Set (BanachSpectrum P)) (hi : Represents K i U) (hi' : Represents K i' U) :
    ∃! e : BoundedAlgEquiv K Q Q', e.toBoundedAlgHom.comp i = i' := by
  obtain ⟨f, hf, hfunique⟩ := hi.2.2 Q' i' hi'.hasImageIn
  obtain ⟨g, hg, _⟩ := hi'.2.2 Q i hi.hasImageIn
  have hgf : g.comp f = BoundedAlgHom.id K Q := by
    apply (hi.2.2 Q i hi.hasImageIn).unique
    · rw [BoundedAlgHom.comp_assoc, hf, hg]
    · exact BoundedAlgHom.id_comp i
  have hfg : f.comp g = BoundedAlgHom.id K Q' := by
    apply (hi'.2.2 Q' i' hi'.hasImageIn).unique
    · rw [BoundedAlgHom.comp_assoc, hg, hf]
    · exact BoundedAlgHom.id_comp i'
  let e := BoundedAlgEquiv.ofHomInv f g
    (fun a => congrArg (fun h : BoundedAlgHom K Q Q => h a) hgf)
    (fun a => congrArg (fun h : BoundedAlgHom K Q' Q' => h a) hfg)
  have he : e.toBoundedAlgHom = f := by ext a; rfl
  refine ⟨e, ?_, ?_⟩
  · change e.toBoundedAlgHom.comp i = i'
    rw [he]
    exact hf
  · intro d hd
    apply equiv_ext
    rw [he]
    exact hfunique _ hd

/-- Successive representations over an inverse image represent the intersection.
This theorem assumes both representing maps; it constructs no arbitrary pullback. -/
theorem represents_comp_inter (P Q R : PresentedStrictAffinoidAlgebra K)
    (i : BoundedAlgHom K P Q) (j : BoundedAlgHom K Q R)
    (U W : Set (BanachSpectrum P)) (hW : IsClosed W)
    (hi : Represents K i U)
    (hj : Represents K j (BanachSpectrum.comap i.toBoundedRingHom ⁻¹' W)) :
    Represents K (j.comp i) (U ∩ W) := by
  refine ⟨hi.1.inter hW, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨z, rfl⟩
      rw [spectrum_comp]
      exact ⟨hi.hasImageIn _, hj.hasImageIn z⟩
    · intro hx
      obtain ⟨y, hy⟩ := hi.2.1.symm ▸ hx.1
      have hyW : y ∈ BanachSpectrum.comap i.toBoundedRingHom ⁻¹' W := by
        change BanachSpectrum.comap i.toBoundedRingHom y ∈ W
        rw [hy]
        exact hx.2
      obtain ⟨z, hz⟩ := hj.2.1.symm ▸ hyW
      exact ⟨z, by rw [spectrum_comp, hz, hy]⟩
  · intro S φ hφ
    obtain ⟨ψ, hψ, hψunique⟩ := hi.2.2 S φ (fun x => (hφ x).1)
    have hψimage : HasImageIn K ψ (BanachSpectrum.comap i.toBoundedRingHom ⁻¹' W) := by
      intro x
      change BanachSpectrum.comap i.toBoundedRingHom
        (BanachSpectrum.comap ψ.toBoundedRingHom x) ∈ W
      rw [← spectrum_comp, hψ]
      exact (hφ x).2
    obtain ⟨χ, hχ, hχunique⟩ := hj.2.2 S ψ hψimage
    refine ⟨χ, ?_, ?_⟩
    · change χ.comp (j.comp i) = φ
      rw [← BoundedAlgHom.comp_assoc, hχ, hψ]
    · intro θ hθ
      apply hχunique
      apply hψunique
      simpa only [BoundedAlgHom.comp_assoc] using hθ

/-- The four clauses of the published strict-test calculus statement. -/
theorem calculus : CalculusStatement.{u} := by
  intro K _ _ _
  exact ⟨represents_id, represents_postcomp_equiv_iff,
    represents_unique_comparison, represents_comp_inter⟩

end Langlands.Analytic.StrictTestDomain
