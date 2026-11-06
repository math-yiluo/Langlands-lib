import Langlands.Geometry.Analytic.AtlasDomainMapAgreement

/-! # Bounded factorization through a local intersection with a common witness -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.LocalDomain

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}

/-- A proved full local-domain presentation of the literal intersection.
This records the two actual bounded inclusion restrictions. -/
structure IntersectionData (S T : LocalDomain a) where
  obj : LocalDomain a
  left : obj ⟶ S
  right : obj ⟶ T
  locus_eq : obj.locus = S.locus ∩ T.locus

namespace IntersectionData

variable {S T U V M : LocalDomain a} (d : IntersectionData S T)

/-- The actual coproduct presentation map of an intersection. -/
def presentationMap :
    BoundedAlgHom K (AffinoidCoproduct.algebra K S.algebra T.algebra) d.obj.algebra :=
  AffinoidCoproduct.lift K d.obj.algebra S.algebra T.algebra
    d.left.restriction d.right.restriction

@[simp]
theorem presentationMap_comp_leftMap :
    d.presentationMap.comp (AffinoidCoproduct.leftMap K S.algebra T.algebra) =
      d.left.restriction :=
  AffinoidCoproduct.lift_comp_leftMap _ _ _ _ _ _

@[simp]
theorem presentationMap_comp_rightMap :
    d.presentationMap.comp (AffinoidCoproduct.rightMap K S.algebra T.algebra) =
      d.right.restriction :=
  AffinoidCoproduct.lift_comp_rightMap _ _ _ _ _ _

/-- Two maps over the unchanged containers factor through the actual
intersection if they agree with maps from a common full local domain.
The conclusion identifies the complete bounded maps, including nilpotents. -/
theorem exists_factor_of_witness
    (s : S ⟶ U) (t : T ⟶ V) (mU : M ⟶ U) (mV : M ⟶ V)
    (R : PresentedAffinoidAlgebra K)
    (α : BoundedAlgHom K S.algebra R) (β : BoundedAlgHom K T.algebra R)
    (γ : BoundedAlgHom K M.algebra R)
    (hU : α.comp s.restriction = γ.comp mU.restriction)
    (hV : β.comp t.restriction = γ.comp mV.restriction) :
    ∃ θ : BoundedAlgHom K d.obj.algebra R,
      θ.comp d.left.restriction = α ∧ θ.comp d.right.restriction = β := by
  have hpoint (x : BanachSpectrum R) :
      S.ambientMap (BanachSpectrum.comap α.toBoundedRingHom x) =
        T.ambientMap (BanachSpectrum.comap β.toBoundedRingHom x) := by
    have hu : BanachSpectrum.comap s.restriction.toBoundedRingHom
        (BanachSpectrum.comap α.toBoundedRingHom x) =
        BanachSpectrum.comap mU.restriction.toBoundedRingHom
          (BanachSpectrum.comap γ.toBoundedRingHom x) := by
      change BanachSpectrum.comap (α.comp s.restriction).toBoundedRingHom x =
        BanachSpectrum.comap (γ.comp mU.restriction).toBoundedRingHom x
      rw [hU]
    have hv : BanachSpectrum.comap t.restriction.toBoundedRingHom
        (BanachSpectrum.comap β.toBoundedRingHom x) =
        BanachSpectrum.comap mV.restriction.toBoundedRingHom
          (BanachSpectrum.comap γ.toBoundedRingHom x) := by
      change BanachSpectrum.comap (β.comp t.restriction).toBoundedRingHom x =
        BanachSpectrum.comap (γ.comp mV.restriction).toBoundedRingHom x
      rw [hV]
    calc
      _ = U.ambientMap (s.spectrumMap (BanachSpectrum.comap α.toBoundedRingHom x)) :=
        (s.ambientMap_naturality _).symm
      _ = U.ambientMap (mU.spectrumMap (BanachSpectrum.comap γ.toBoundedRingHom x)) :=
        congrArg U.ambientMap hu
      _ = M.ambientMap (BanachSpectrum.comap γ.toBoundedRingHom x) :=
        mU.ambientMap_naturality _
      _ = V.ambientMap (mV.spectrumMap (BanachSpectrum.comap γ.toBoundedRingHom x)) :=
        (mV.ambientMap_naturality _).symm
      _ = V.ambientMap (t.spectrumMap (BanachSpectrum.comap β.toBoundedRingHom x)) :=
        congrArg V.ambientMap hv.symm
      _ = _ := t.ambientMap_naturality _
  have himage : HasImageIn K α (S.ambientMap ⁻¹' d.obj.locus) := by
    intro x
    change S.ambientMap (BanachSpectrum.comap α.toBoundedRingHom x) ∈ d.obj.locus
    rw [d.locus_eq]
    refine ⟨S.range_ambientMap ▸ Set.mem_range_self _, ?_⟩
    rw [hpoint x]
    exact T.range_ambientMap ▸ Set.mem_range_self _
  obtain ⟨θ, hθ, _⟩ := d.left.represents.2.2 R α himage
  refine ⟨θ, hθ, ?_⟩
  apply t.represents.hom_ext R
  have hθU : θ.comp (d.left ≫ s).restriction = γ.comp mU.restriction := by
    rw [Inclusion.restriction_comp, ← BoundedAlgHom.comp_assoc, hθ, hU]
  have hθV := restriction_eq_of_common_container (d.left ≫ s) mU
    (d.right ≫ t) mV R θ γ hθU
  exact hθV.trans hV.symm

end IntersectionData
end Langlands.Analytic.IndexedAffinoidAtlas.LocalDomain
