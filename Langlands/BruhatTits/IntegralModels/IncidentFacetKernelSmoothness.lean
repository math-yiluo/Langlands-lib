import Langlands.BruhatTits.IntegralModels.RootCentralizerKernelAssembly
import Langlands.BruhatTits.IntegralModels.IncidentCentralizerReductiveQuotient
import Langlands.BruhatTits.IntegralModels.IncidentFacetRootImages
import Langlands.BruhatTits.IntegralModels.IncidentNegativeRootReduction
import Langlands.BruhatTits.IntegralModels.IntegralTorusRootSupport
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.IntegralModel.ConnectedFibreDescent

/-! # Full incident special-fibre kernels from rootwise reduction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

namespace Langlands.BruhatTits.IntegralModels

section Local

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
    {source target : RelativeComponentModelData R K G}
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}

namespace IntegralTorusData

variable (T : IntegralTorusData source S i) (hT : IsSplitTorus T.torus.toGrp)

/-- Integral specialization preserves divisibility within the actual root set. -/
theorem mem_indivisibleRoots_characterSpecialization_iff (a : characterLattice S) :
    T.characterSpecialization hT a ∈ RelativeRoot.indivisibleRoots T.specialFibreInclusion ↔
      a ∈ RelativeRoot.indivisibleRoots i := by
  constructor
  · intro ha
    refine ⟨(T.mem_relativeRoots_characterSpecialization_iff hT a).mp ha.1, ?_⟩
    intro b hb n hn he
    apply ha.2 (T.characterSpecialization hT b)
      ((T.mem_relativeRoots_characterSpecialization_iff hT b).mpr hb) n hn
    simpa only [map_nsmul] using congrArg (T.characterSpecialization hT) he
  · intro ha
    refine ⟨(T.mem_relativeRoots_characterSpecialization_iff hT a).mpr ha.1, ?_⟩
    intro b hb n hn he
    obtain ⟨b₀, rfl⟩ := (T.characterSpecialization hT).surjective b
    apply ha.2 b₀ ((T.mem_relativeRoots_characterSpecialization_iff hT b₀).mp hb) n hn
    apply (T.characterSpecialization hT).injective
    simpa only [map_nsmul] using he

/-- The actual indivisible root sets are canonically identified through the
specified integral split torus. -/
def indivisibleRootsSpecializationEquiv :
    RelativeRoot.indivisibleRoots i ≃
      RelativeRoot.indivisibleRoots T.specialFibreInclusion :=
  (T.characterSpecialization hT).toEquiv.subtypeEquiv
    (fun a => (T.mem_indivisibleRoots_characterSpecialization_iff hT a).symm)

include hT in
/-- Distinct indivisible residue roots have disjoint positive integral rays
when the generic roots have their actual relative-root-system realization. -/
theorem disjoint_cyclicTail_indivisibleRoots_specialFibre
    [Mono i.hom.hom.left] (hroot : HasRelativeRootSystem i)
    (hS : IsSplitTorus S.toGrp)
    {a b : characterLattice T.specialFibre}
    (ha : a ∈ RelativeRoot.indivisibleRoots T.specialFibreInclusion)
    (hb : b ∈ RelativeRoot.indivisibleRoots T.specialFibreInclusion) (hne : a ≠ b) :
    Disjoint (RelativeRoot.cyclicTail a 1 : Set (characterLattice T.specialFibre))
      (RelativeRoot.cyclicTail b 1 : Set (characterLattice T.specialFibre)) := by
  obtain ⟨a₀, rfl⟩ := (T.characterSpecialization hT).surjective a
  obtain ⟨b₀, rfl⟩ := (T.characterSpecialization hT).surjective b
  have hd := RelativeRoot.disjoint_cyclicTail_indivisibleRoots i hroot hS
    ((T.mem_indivisibleRoots_characterSpecialization_iff hT a₀).mp ha)
    ((T.mem_indivisibleRoots_characterSpecialization_iff hT b₀).mp hb)
    (fun h => hne (congrArg (T.characterSpecialization hT) h))
  apply Set.disjoint_left.mpr
  rintro c ⟨m, hm, hm0, hma⟩ ⟨n, hn, hn0, hnb⟩
  apply Set.disjoint_left.mp hd
    (show (T.characterSpecialization hT).symm c ∈ RelativeRoot.cyclicTail a₀ 1 from
      ⟨m, hm, hm0, by
        simpa only [map_nsmul, AddEquiv.symm_apply_apply] using
          congrArg (T.characterSpecialization hT).symm hma⟩)
    (show (T.characterSpecialization hT).symm c ∈ RelativeRoot.cyclicTail b₀ 1 from
      ⟨n, hn, hn0, by
        simpa only [map_nsmul, AddEquiv.symm_apply_apply] using
          congrArg (T.characterSpecialization hT).symm hnb⟩)

end IntegralTorusData

namespace RelativeComponentModelHom

/-- The target reductive-quotient root support lies in the source neutral
special-fibre root support on the very same residue torus. -/
theorem relativeRoots_quotient_subset_source
    (φ : RelativeComponentModelHom source target)
    (T : IntegralTorusData source S i) (hT : IsSplitTorus T.torus.toGrp)
    (Q : SpecialFibreQuotientData target) (hQ : Q.IsReductiveQuotient) :
    relativeRoots (T.specialFibreInclusion ≫ (φ.neutralSpecialFibreMap ≫ Q.projection)) ⊆
      relativeRoots T.specialFibreInclusion := by
  intro a ha
  obtain ⟨a₀, rfl⟩ := (T.characterSpecialization hT).surjective a
  apply (T.mem_relativeRoots_characterSpecialization_iff hT a₀).mpr
  apply ((φ.mapIntegralTorus T).mem_relativeRoots_characterSpecialization_iff hT a₀).mp
  apply Q.relativeRoots_subset_specialFibre hQ (φ.mapIntegralTorus T) hT
  rw [φ.mapIntegralTorus_specialFibreInclusion T,
    φ.mapIntegralTorus_characterSpecialization T hT, Category.assoc]
  change T.characterSpecialization hT a₀ ∈
    relativeRoots (T.specialFibreInclusion ≫ φ.neutralSpecialFibreMap ≫ Q.projection)
  exact ha

end RelativeComponentModelHom
end Local

namespace RelativeComponentModelHom

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    {source target :
      RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G}
    (φ : RelativeComponentModelHom source target)
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (T : IntegralTorusData source C.S C.i) (hT : IsSplitTorus T.torus.toGrp)
    (Q : SpecialFibreQuotientData target) (hQ : Q.IsReductiveQuotient)
    (Ω Ω' : Set C.Apartment)
    (hsource : source.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω'))
    (htarget : target.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))

private instance incidentKernel_neutral_smooth
    (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G) :
    Smooth D.neutral.group.X.hom := D.neutral_smooth

private instance incidentKernel_neutralSpecialFibre_affine
    (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G) :
    IsAffineHom D.neutral.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
    (IntegralModel.residueBaseMap (fixedFieldIntegers F)))
  infer_instance

private instance incidentKernel_neutralSpecialFibre_smooth
    (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G) :
    Smooth D.neutral.specialFibre.X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
    (IntegralModel.residueBaseMap (fixedFieldIntegers F)))
  infer_instance

private instance incidentKernel_neutralSpecialFibre_connected
    (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G) :
    ConnectedSpace D.neutral.specialFibre.X.left :=
  D.neutral.hasConnectedSpecialFibre_of_hasConnectedFibres D.neutral_connectedFibres

include hQ hsource htarget in
/-- Original full generic-root composite kernels and the actual zero-fixer
centralizer comparison imply smoothness of the full original ambient kernel. -/
theorem reductiveComposite_smooth_kernel_of_root_kernels
    (hne : Ω.Nonempty) (hne' : Ω'.Nonempty)
    (hroot : ∀ a : relativeRoots C.i,
      Smooth (kernel (φ.rootTargetReductiveQuotientMap T hT Q a a.2.1)).X.hom) :
    Smooth (kernel (φ.neutralSpecialFibreMap ≫ Q.projection)).X.hom := by
  let : Algebra 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (residueToFixedField F).toAlgebra
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).isAlgClosed
  let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  let : ConnectedSpace Q.quotient.X.left := hQ.2.2.connectedSpace
  let A := T.toIntegralSplitTorusData hT
  let jZ := (A.centralizerModelMap C.centralizer.j C.centralizer.isRepresentedBy).specialFibreMap
  have hjZ : (torusCentralizer T.specialFibreInclusion).IsRepresentedBy jZ :=
    A.centralizerModelMap_specialFibre_isCentralizer C.centralizer.j
      C.centralizer.isRepresentedBy
  apply RootCentralizerKernel.smooth_kernel_of_root_and_centralizer
    (hT.baseChange (IntegralModel.residueBaseMap (fixedFieldIntegers F)))
    T.specialFibreInclusion (φ.neutralSpecialFibreMap ≫ Q.projection) jZ hjZ
  · exact φ.relativeRoots_quotient_subset_source T hT Q hQ
  · intro a ha b hb hneab
    exact T.disjoint_cyclicTail_indivisibleRoots_specialFibre hT
      (relativeRootSystem _ G C.isConnectedReductive C.S C.i C.isMaximalSplitTorus)
      C.isMaximalSplitTorus.isSplitSubtorus.1 ha hb hneab
  · intro a ha U j hj
    obtain ⟨a₀, rfl⟩ := (T.characterSpecialization hT).surjective a
    have ha₀ := (T.mem_relativeRoots_characterSpecialization_iff hT a₀).mp ha
    exact RootCentralizerKernel.smooth_kernel_of_representatives
      (φ.neutralSpecialFibreMap ≫ Q.projection)
      (A.rootModelMap a₀ ha₀.1).specialFibreMap j
      (A.rootModelMap_specialFibre_isRepresentedBy a₀ ha₀.1) hj (hroot ⟨a₀, ha₀⟩)
  · exact φ.centralizerTargetReductiveQuotientMap_smooth_kernel C E T hT Q
      Ω Ω' hsource htarget hne hne' hQ

include T hT hQ hsource htarget in
/-- At incident facet subsets, positive reduction supplies smoothness of the
full kernel of the original neutral-special-fibre-to-quotient composite. -/
theorem reductiveComposite_smooth_kernel_of_incidentFacets
    (hP : UnramifiedRootPositiveReductionStatement.{u})
    (Ωf Ωf' : Set C.Apartment)
    (hface : AffineRootSystem.IsFaceOf C.affineRoots Ωf Ωf')
    (hsub : Ω ⊆ Ωf) (hsub' : Ω' ⊆ Ωf')
    (x : C.Apartment) (hx : x ∈ Ω) (v : RealTorusSpace.V C.S)
    (hv : (Submodule.Quotient.mk v : TranslationSpace C.i) +ᵥ x ∈ Ω') :
    Smooth (kernel (φ.neutralSpecialFibreMap ≫ Q.projection)).X.hom := by
  apply φ.reductiveComposite_smooth_kernel_of_root_kernels C E T hT Q hQ Ω Ω'
    hsource htarget ⟨x, hx⟩ ⟨_, hv⟩
  intro a
  by_cases ha : 0 ≤ RealTorusSpace.eval C.S a v
  · exact φ.rootTargetReductiveQuotientMap_smooth_kernel_of_incidentFacets_of_nonneg
      C E T hT Ωf Ωf' Ω Ω' hface hsub hsub' hsource htarget Q hQ x hx v hv a ha
  · have hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω) :=
      fun f => (C.isBoundedApartmentSubset_of_isFacet
        (MaximalUnramified.exists_order_ne_zero F) hface.1 f).mono (Set.image_mono hsub)
    exact φ.rootTargetReductiveQuotientMap_smooth_kernel_of_eval_neg
      C E T hT Q hQ Ω Ω' hsource htarget hb hP x hx v hv a (lt_of_not_ge ha)

end RelativeComponentModelHom
end Langlands.BruhatTits.IntegralModels
