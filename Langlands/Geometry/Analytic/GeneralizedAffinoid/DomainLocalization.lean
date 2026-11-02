import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainSpectrumProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainEmbeddedLocalization
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainTopology

/-! # Unconditional localization of full presented affinoid domains -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : PresentedAffinoidAlgebra K}

/-- Full representations compose: spectral injectivity of the outer
representation is now supplied by the proved full-domain embedding theorem. -/
theorem Represents.comp {i : BoundedAlgHom K A B} {j : BoundedAlgHom K B C}
    {U : Set (BanachSpectrum A)} {V : Set (BanachSpectrum B)}
    (hi : Represents K i U) (hj : Represents K j V) :
    Represents K (j.comp i) (BanachSpectrum.comap i.toBoundedRingHom '' V) :=
  hi.comp_of_injective hj
    (Domain.spectrumEmbedding K A (⟨B, i, U, hi⟩ : Domain K A)).injective

namespace Domain

variable (U : Domain K A)

/-- Injectivity of the stored structural spectrum map for every full domain. -/
theorem spectrumMap_injective : Function.Injective U.spectrumMap :=
  (spectrumEmbedding K A U).injective

/-- The actual structural corestriction is a homeomorphism onto the
represented locus, with its subspace topology. -/
def locusHomeomorph : BanachSpectrum U.algebra ≃ₜ U.locus :=
  (Equiv.ofBijective U.spectrumToLocus
    ⟨fun _ _ h => U.spectrumMap_injective (congrArg Subtype.val h),
      U.spectrumToLocus_surjective⟩).toHomeomorphOfContinuousClosed
        U.spectrumToLocus.continuous U.spectrumToLocus_isClosedMap

@[simp]
theorem locusHomeomorph_apply (x : BanachSpectrum U.algebra) :
    U.locusHomeomorph x = U.spectrumToLocus x := rfl

@[simp]
theorem locusHomeomorph_apply_coe (x : BanachSpectrum U.algebra) :
    (U.locusHomeomorph x : BanachSpectrum A) = U.spectrumMap x := rfl

/-- The homeomorphisms retain the actual bounded restriction's spectrum map. -/
theorem locusHomeomorph_naturality {V : Domain K A} (f : U ⟶ V)
    (x : BanachSpectrum U.algebra) :
    V.locusHomeomorph (f.spectrumMap x) = f.locusMap (U.locusHomeomorph x) :=
  f.spectrumToLocus_naturality x

/-- The actual spectrum realization and represented-locus functor are
naturally isomorphic by their structural corestrictions. -/
def spectrumToLocusNatIso :
    toTopologicalSpace K A ≅ locusFunctor K A :=
  NatIso.ofComponents (fun V => TopCat.isoOfHomeo V.locusHomeomorph)
    (by
      intro V W f
      apply TopCat.ext
      intro x
      exact f.spectrumToLocus_naturality x)

theorem spectrumToLocusNatIso_hom :
    (spectrumToLocusNatIso (K := K) (A := A)).hom = spectrumToLocusNat K A := by
  apply NatTrans.ext
  funext V
  rfl

/-- Extend any full domain over `U.algebra` to the original base.
The algebra is unchanged and the actual structural maps are composed. -/
def extend (V : Domain K U.algebra) : Domain K A :=
  U.extendOfInjective U.spectrumMap_injective V

@[simp]
theorem extend_algebra (V : Domain K U.algebra) :
    (U.extend V).algebra = V.algebra := rfl

@[simp]
theorem extend_baseMap (V : Domain K U.algebra) :
    (U.extend V).baseMap = V.baseMap.comp U.baseMap := rfl

@[simp]
theorem extend_locus (V : Domain K U.algebra) :
    (U.extend V).locus = U.spectrumMap '' V.locus := rfl

theorem extend_locus_subset (V : Domain K U.algebra) :
    (U.extend V).locus ⊆ U.locus :=
  U.extendOfInjective_locus_subset U.spectrumMap_injective V

theorem extend_spectrumMap (V : Domain K U.algebra) (x : BanachSpectrum V.algebra) :
    (U.extend V).spectrumMap x = U.spectrumMap (V.spectrumMap x) :=
  U.extendOfInjective_spectrumMap U.spectrumMap_injective V x

/-- The extension's actual inclusion into `U` has restriction `V.baseMap`. -/
def extendInclusion (V : Domain K U.algebra) : U.extend V ⟶ U :=
  U.extendOfInjectiveInclusion U.spectrumMap_injective V

@[simp]
theorem extendInclusion_restriction (V : Domain K U.algebra) :
    (U.extendInclusion V).restriction = V.baseMap := rfl

/-- Extension retains every bounded restriction between the inner domains. -/
def extendFunctor : Domain K U.algebra ⥤ Domain K A :=
  U.extendOfInjectiveFunctor U.spectrumMap_injective

@[simp]
theorem extendFunctor_map_restriction {V W : Domain K U.algebra} (f : V ⟶ W) :
    (U.extendFunctor.map f).restriction = f.restriction := rfl

def fullyFaithfulExtend : U.extendFunctor.FullyFaithful :=
  U.fullyFaithfulExtendOfInjective U.spectrumMap_injective

instance : U.extendFunctor.Full := U.fullyFaithfulExtend.full

instance : U.extendFunctor.Faithful := U.fullyFaithfulExtend.faithful

theorem extendFunctor_comp_toAffinoidSpace :
    U.extendFunctor ⋙ toAffinoidSpace K A = toAffinoidSpace K U.algebra := rfl

theorem extendFunctor_comp_toTopologicalSpace :
    U.extendFunctor ⋙ toTopologicalSpace K A = toTopologicalSpace K U.algebra := rfl

/-- The extended domain together with its actual inclusion into `U`. -/
def extendOverFunctor : Domain K U.algebra ⥤ Over U :=
  U.extendOfInjectiveOverFunctor U.spectrumMap_injective

theorem extendOverFunctor_comp_forget :
    U.extendOverFunctor ⋙ Over.forget U = U.extendFunctor := rfl

/-- Full domains over the actual algebra of any full domain are equivalent
to ambient full domains with their actual inclusion into it. -/
def localizationEquivalence : Domain K U.algebra ≌ Over U :=
  U.localizationEquivalenceOfInjective U.spectrumMap_injective

@[simp]
theorem localizationEquivalence_functor :
    U.localizationEquivalence.functor = U.extendOverFunctor := rfl

@[simp]
theorem localizationEquivalence_inverse :
    U.localizationEquivalence.inverse = U.relativeFunctor := rfl

/-- The actual relative representation has the entire inverse-image locus. -/
theorem relative_locus_eq_preimage (V : Domain K A) (f : V ⟶ U) :
    (U.relative V f).locus = U.spectrumMap ⁻¹' V.locus :=
  U.relative_locus_eq_preimage_of_injective U.spectrumMap_injective V f

theorem relative_extend_locus (V : Domain K U.algebra) :
    (U.relative (U.extend V) (U.extendInclusion V)).locus = V.locus :=
  U.relative_extendOfInjective_locus U.spectrumMap_injective V

theorem extend_relative_locus (V : Domain K A) (f : V ⟶ U) :
    (U.extend (U.relative V f)).locus = V.locus :=
  U.extendOfInjective_relative_locus U.spectrumMap_injective V f

/-- Extension gives the actual subspace homeomorphism on each inner locus. -/
def extendLocusHomeomorph (V : Domain K U.algebra) :
    V.locus ≃ₜ (U.extend V).locus :=
  U.extendOfInjectiveLocusHomeomorph U.spectrumMap_injective V

@[simp]
theorem extendLocusHomeomorph_apply_coe (V : Domain K U.algebra) (x : V.locus) :
    (U.extendLocusHomeomorph V x : BanachSpectrum A) = U.spectrumMap x := rfl

/-- Repeated full-domain extension agrees with direct extension through
the composite domain, via bounded identity maps on the unchanged algebra. -/
def extendAssocIso (V : Domain K U.algebra) (W : Domain K V.algebra) :
    U.extend (V.extend W) ≅ (U.extend V).extend W where
  hom := ⟨BoundedAlgHom.id K W.algebra, by
    change W.baseMap.comp (V.baseMap.comp U.baseMap) =
      (W.baseMap.comp V.baseMap).comp U.baseMap
    exact (BoundedAlgHom.comp_assoc W.baseMap V.baseMap U.baseMap).symm⟩
  inv := ⟨BoundedAlgHom.id K W.algebra, by
    change (W.baseMap.comp V.baseMap).comp U.baseMap =
      W.baseMap.comp (V.baseMap.comp U.baseMap)
    exact BoundedAlgHom.comp_assoc W.baseMap V.baseMap U.baseMap⟩
  hom_inv_id := Inclusion.ext rfl
  inv_hom_id := Inclusion.ext rfl

@[simp]
theorem extendAssocIso_hom_restriction (V : Domain K U.algebra)
    (W : Domain K V.algebra) :
    (U.extendAssocIso V W).hom.restriction = BoundedAlgHom.id K W.algebra := rfl

@[simp]
theorem extendAssocIso_inv_restriction (V : Domain K U.algebra)
    (W : Domain K V.algebra) :
    (U.extendAssocIso V W).inv.restriction = BoundedAlgHom.id K W.algebra := rfl

end Domain
end Langlands.Analytic.PresentedAffinoidAlgebra
