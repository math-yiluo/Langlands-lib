import Langlands.BruhatTits.IntegralModels.UnramifiedZeroFixerCentralizerIndependence
import Langlands.BruhatTits.IntegralModels.UnramifiedZeroFixerConnected
import Langlands.GroupScheme.Rational.PseudoParabolicAmbientTransport
import Langlands.GroupScheme.Reductive.UnipotentRadicalExistenceProof
import Langlands.GroupScheme.Absolute.TorusCentralizerUnipotentRadicalStatement
import Langlands.GroupScheme.SubgroupFunctor.IntersectionNormalizer
import Langlands.GroupScheme.IntegralModel.HenselianReduction

/-! # Transport of centralizer radical preimages -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.GroupScheme.IntegralModel.Iso

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {N M : IntegralModel R K G}

/-- A generic-identity-compatible model isomorphism preserves the image of the
actual reduction preimage of any represented unipotent radical. -/
theorem radicalPreimage_eq (e : N.Iso M (CategoryTheory.Iso.refl G))
    {U V : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}
    (i : U ⟶ N.specialFibre) (j : V ⟶ M.specialFibre)
    (hi : IsUnipotentRadical i) (hj : IsUnipotentRadical j) :
    ((rationalPoints.map i).range.comap N.reduction).map N.integralPointMap =
      ((rationalPoints.map j).range.comap M.reduction).map M.integralPointMap := by
  let es := (GroupScheme.baseChange (IntegralModel.residueBaseMap R)).mapIso e.iso
  have hr := (hi.comp_iso es).range_eq hj
  rw [SubgroupFunctor.range_comp_iso] at hr
  have hmem (x : N.integralSections) :
      M.reduction (e.integralSectionsEquiv x) ∈ (rationalPoints.map j).range ↔
        N.reduction x ∈ (rationalPoints.map i).range := by
    change M.reduction (rationalPoints.map e.iso.hom x) ∈
      (SubgroupFunctor.range j).carrier _ ↔ _
    have hn := e.toHom.reduction_naturality x
    change M.reduction (rationalPoints.map e.iso.hom x) =
      rationalPoints.map es.hom (N.reduction x) at hn
    rw [← hr, SubgroupFunctor.mem_comap, hn]
    change (N.reduction x ≫ es.hom.hom.hom) ≫ es.inv.hom.hom ∈
      (SubgroupFunctor.range i).carrier _ ↔ _
    rw [Category.assoc, ← Grp.comp_hom_hom, es.hom_inv_id,
      Grp.id_hom_hom, Category.comp_id]
    rfl
  have hp (x : N.integralSections) :
      M.integralPointMap (e.integralSectionsEquiv x) = N.integralPointMap x := by
    simpa only [CategoryTheory.Iso.refl_hom, rationalPoints.map_apply,
      Grp.id_hom_hom, Category.comp_id] using e.integralPointMap_naturality x
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨e.integralSectionsEquiv x, (hmem x).mpr hx, hp x⟩
  · rintro ⟨y, hy, rfl⟩
    let x := e.integralSectionsEquiv.symm y
    have he : e.integralSectionsEquiv x = y := e.integralSectionsEquiv.apply_symm_apply y
    refine ⟨x, (hmem x).mp ?_, ?_⟩
    · rwa [he]
    · exact (hp x).symm.trans (congrArg M.integralPointMap he)

end Langlands.GroupScheme.IntegralModel.Iso

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    {Z G : GroupScheme (Spec (CommRingCat.of K))}
    {P : IntegralModel R K Z} {N : IntegralModel R K G} {f : Z ⟶ G}

/-- A closed compatible integral inclusion transports the exact residue-subgroup
preimage to the inverse image of the ambient radical-preimage subgroup. -/
theorem Hom.radicalPreimage_comap (φ : P.Hom N f) (hφ : IsClosedSubgroup φ.hom)
    {U V : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}
    (i : U ⟶ N.specialFibre) (v : V ⟶ P.specialFibre)
    (hres : SubgroupFunctor.range v =
      (SubgroupFunctor.range i).comap φ.specialFibreMap) :
    ((rationalPoints.map v).range.comap P.reduction).map P.integralPointMap =
      (((rationalPoints.map i).range.comap N.reduction).map N.integralPointMap).comap
        (rationalPoints.map f) := by
  have hrespts : (rationalPoints.map v).range =
      (rationalPoints.map i).range.comap (rationalPoints.map φ.specialFibreMap) :=
    congrArg (fun H => H.carrier (Over.mk (𝟙 _))) hres
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨rationalPoints.map φ.hom x, ?_, φ.integralPointMap_naturality x⟩
    change N.reduction (rationalPoints.map φ.hom x) ∈ (rationalPoints.map i).range
    rw [φ.reduction_naturality]
    change P.reduction x ∈ (rationalPoints.map v).range at hx
    rwa [hrespts] at hx
  · intro hz
    obtain ⟨x, hx, hxz⟩ := hz
    have hzint : z ∈ P.integralPoints := by
      rw [φ.integralPoints_eq_comap hφ]
      exact ⟨x, hxz⟩
    obtain ⟨s, hsz⟩ := hzint
    have hsx : rationalPoints.map φ.hom s = x := by
      apply N.integralPointMap_injective
      rw [φ.integralPointMap_naturality, hsz, hxz]
    refine ⟨s, ?_, hsz⟩
    change P.reduction s ∈ (rationalPoints.map v).range
    rw [hrespts]
    change rationalPoints.map φ.specialFibreMap (P.reduction s) ∈
      (rationalPoints.map i).range
    rw [← φ.reduction_naturality, hsx]
    exact hx

end Langlands.GroupScheme.IntegralModel

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (N M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
    [Smooth N.group.X.hom] [Smooth M.group.X.hom]
    (Ω Ω' : Set C.Apartment)
    (hN : N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))
    (hM : M.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω'))

/-- Intrinsic centralizer radical-preimage images agree across every pair of
characterized models on nonempty apartment subsets. -/
theorem unramifiedZeroFixerCentralizer_radicalPreimage_eq
    (hne : Ω.Nonempty) (hne' : Ω'.Nonempty)
    {U V : GroupScheme
      (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F))))}
    (i : U ⟶ (unramifiedZeroFixerCentralizerModel C E N Ω hN).specialFibre)
    (j : V ⟶ (unramifiedZeroFixerCentralizerModel C E M Ω' hM).specialFibre)
    (hi : IsUnipotentRadical i) (hj : IsUnipotentRadical j) :
    ((rationalPoints.map i).range.comap
        (unramifiedZeroFixerCentralizerModel C E N Ω hN).reduction).map
      (unramifiedZeroFixerCentralizerModel C E N Ω hN).integralPointMap =
    ((rationalPoints.map j).range.comap
        (unramifiedZeroFixerCentralizerModel C E M Ω' hM).reduction).map
      (unramifiedZeroFixerCentralizerModel C E M Ω' hM).integralPointMap :=
  (unramifiedZeroFixerCentralizerIso C E N M Ω Ω' hN hM hne hne').radicalPreimage_eq
    i j hi hj

private instance specialFibre_affine
    {H : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    (P : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) H) : IsAffineHom P.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd P.group.X.hom
    (IntegralModel.residueBaseMap (fixedFieldIntegers F)))
  exact MorphismProperty.pullback_snd _ _ P.affine

private instance specialFibre_smooth
    {H : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    (P : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) H)
    [Smooth P.group.X.hom] : Smooth P.specialFibre.X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd P.group.X.hom
    (IntegralModel.residueBaseMap (fixedFieldIntegers F)))
  infer_instance

/-- The actual residue centralizer admits a represented unipotent radical. -/
theorem unramifiedZeroFixerCentralizer_exists_radical
    (hne : Ω.Nonempty)
    (hfacet : ∃ x : C.Apartment, Ω ⊆ AffineRootSystem.facet C.affineRoots x) :
    ∃ (V : GroupScheme
        (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))))
      (v : V ⟶ (unramifiedZeroFixerCentralizerModel C E N Ω hN).specialFibre),
      IsUnipotentRadical v := by
  let A := unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN
  let P := unramifiedZeroFixerCentralizerModel C E N Ω hN
  let : Smooth P.group.X.hom :=
    A.centralizerModel_isSmooth C.centralizer.j C.centralizer.isRepresentedBy
  let : ConnectedSpace N.specialFibre.X.left :=
    unramifiedZeroFixerConnected F G C E Ω hne hfacet N (inferInstance : Smooth N.group.X.hom) hN
  let : ConnectedSpace P.specialFibre.X.left :=
    A.specialFibreTorus_isSplit.connectedSpace_centralizer A.specialFibreInclusion
      (A.centralizerModelMap_specialFibre_isCentralizer C.centralizer.j
        C.centralizer.isRepresentedBy)
  exact unipotentRadicalExistence _ P.specialFibre

/-- The torus-centralizer radical-intersection statement identifies the intrinsic
centralizer radical preimage with the centralizer inverse image of the ambient one. -/
theorem unramifiedZeroFixerCentralizer_radicalPreimage_comap
    (hinter : TorusCentralizerUnipotentRadicalStatement.{u})
    (hne : Ω.Nonempty)
    (hfacet : ∃ x : C.Apartment, Ω ⊆ AffineRootSystem.facet C.affineRoots x)
    {U V : GroupScheme
      (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F))))}
    (i : U ⟶ N.specialFibre)
    (v : V ⟶ (unramifiedZeroFixerCentralizerModel C E N Ω hN).specialFibre)
    (hi : IsUnipotentRadical i) (hv : IsUnipotentRadical v) :
    ((rationalPoints.map v).range.comap
        (unramifiedZeroFixerCentralizerModel C E N Ω hN).reduction).map
      (unramifiedZeroFixerCentralizerModel C E N Ω hN).integralPointMap =
    (((rationalPoints.map i).range.comap N.reduction).map N.integralPointMap).comap
      (rationalPoints.map C.centralizer.j) := by
  let A := unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN
  let P := unramifiedZeroFixerCentralizerModel C E N Ω hN
  let φ := unramifiedZeroFixerCentralizerModelMap C E N Ω hN
  have hφ : IsClosedSubgroup φ.hom :=
    A.centralizerModelMap_isClosedSubgroup C.centralizer.j C.centralizer.isRepresentedBy
  have hφs : IsClosedSubgroup φ.specialFibreMap :=
    hφ.baseChange (IntegralModel.residueBaseMap (fixedFieldIntegers F))
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).1
  let : ConnectedSpace N.specialFibre.X.left :=
    unramifiedZeroFixerConnected F G C E Ω hne hfacet N (inferInstance : Smooth N.group.X.hom) hN
  have heq := hinter _ N.specialFibre A.specialFibreTorus A.specialFibreInclusion
    A.specialFibreTorus_isSplit.isTorus
    (A.specialInclusion_isClosedSubgroup
      (unramifiedZeroFixerIntegralSplitTorusData_isClosedSubgroup C E N Ω hN))
    P.specialFibre φ.specialFibreMap
    (A.centralizerModelMap_specialFibre_isCentralizer C.centralizer.j
      C.centralizer.isRepresentedBy) hφs U i hi V v hv
  let : IsClosedImmersion φ.specialFibreMap.hom.hom.left := hφs
  let : Mono φ.specialFibreMap.hom.hom := Over.mono_of_mono_left _
  have hswap : SubgroupFunctor.range i ⊓ SubgroupFunctor.range φ.specialFibreMap =
      SubgroupFunctor.range φ.specialFibreMap ⊓ SubgroupFunctor.range i := by
    apply SubgroupFunctor.ext
    intro T
    exact inf_comm _ _
  have hres : SubgroupFunctor.range v =
      (SubgroupFunctor.range i).comap φ.specialFibreMap :=
    SubgroupFunctor.range_eq_comap_of_range_comp_eq_inf v φ.specialFibreMap
      (SubgroupFunctor.range i) (heq.trans hswap)
  exact φ.radicalPreimage_comap hφ i v hres

/-- The intrinsic centralizer radical-preimage subgroup does not depend on the
nonempty apartment subset, ambient model, or represented radical. -/
def UnramifiedZeroFixerCentralizerRadicalIndependenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (N M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
    [Smooth N.group.X.hom] [Smooth M.group.X.hom]
    (Ω Ω' : Set C.Apartment)
    (hN : N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))
    (hM : M.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω')),
    Ω.Nonempty → Ω'.Nonempty →
    ∀ (U V : GroupScheme
      (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))))
      (i : U ⟶ (unramifiedZeroFixerCentralizerModel C E N Ω hN).specialFibre)
      (j : V ⟶ (unramifiedZeroFixerCentralizerModel C E M Ω' hM).specialFibre),
      IsUnipotentRadical i → IsUnipotentRadical j →
      ((rationalPoints.map i).range.comap
          (unramifiedZeroFixerCentralizerModel C E N Ω hN).reduction).map
        (unramifiedZeroFixerCentralizerModel C E N Ω hN).integralPointMap =
      ((rationalPoints.map j).range.comap
          (unramifiedZeroFixerCentralizerModel C E M Ω' hM).reduction).map
        (unramifiedZeroFixerCentralizerModel C E M Ω' hM).integralPointMap

/-- The intrinsic radical-preimage independence statement holds unconditionally. -/
theorem unramifiedZeroFixerCentralizerRadicalIndependence :
    UnramifiedZeroFixerCentralizerRadicalIndependenceStatement.{u} := by
  intro F _ _ _ _ G _ C E N M _ _ Ω Ω' hN hM hne hne' U V i j hi hj
  exact unramifiedZeroFixerCentralizer_radicalPreimage_eq C E N M Ω Ω' hN hM
    hne hne' i j hi hj

end Langlands.BruhatTits.IntegralModels
