import Langlands.BruhatTits.IntegralModels.UnramifiedZeroFixerRootSupport
import Langlands.BruhatTits.IntegralModels.UnramifiedIncidentRootImage
import Langlands.GroupScheme.Rational.DynamicRootProductRayReduction
import Langlands.GroupScheme.Rational.RootRayDecomposition
import Langlands.GroupScheme.Rational.OrderedProductPoints
import Langlands.GroupScheme.Rational.RelativeRootSystemProof

/-! # Dynamic positive subgroups in actual incident special-fibre images -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [Smooth H.X.hom]

/-- Disjoint indivisible positive rays give containment of the complete dynamic
unipotent functor in any subgroup functor containing the positive root groups.
The ambient smooth affine group need not be reductive or connected. -/
theorem dynamicUnipotent_le_of_positive_rootSubgroups_le
    (hS : IsSplitTorus S.toGrp) (j : S.toGrp ⟶ H)
    (nu : cocharacterLattice S)
    (hdisj : ∀ a ∈ indivisiblePositiveRoots j nu,
      ∀ b ∈ indivisiblePositiveRoots j nu, a ≠ b →
        Disjoint (cyclicTail a 1 : Set (characterLattice S))
          (cyclicTail b 1 : Set (characterLattice S)))
    (F : SubgroupFunctor H)
    (hroot : ∀ a ∈ positiveRelativeRoots j nu, subgroup j a ≤ F) :
    Dynamic.unipotent (CommGroupScheme.groupHom nu ≫ j) ≤ F := by
  have hfin : (indivisiblePositiveRoots j nu).Finite :=
    (hS.finite_relativeRoots j).subset (fun _ ha => ha.1.1)
  obtain ⟨n, a, hinj, ha⟩ := hfin.fin_param
  let b := AutomorphicAction.conjugation j
  let A := positiveSemigroup nu
  obtain ⟨⟨U, jU, hjU, hjUc, hUs, hUc⟩, hStable, _, hUnip, _, _⟩ :=
    semigroupRealization k H inferInstance inferInstance S hS b A
  have hzero : (0 : characterLattice S) ∉ A := by
    change ¬ 0 < latticePairing S 0 nu
    simp
  obtain ⟨hUu, _⟩ := hUnip U jU hjU hzero
  let : IsAffineHom U.X.hom := hjUc.isAffineHom
  let : Smooth U.X.hom := hUs
  let : ConnectedSpace U.X.left := hUc
  let c := b.onRepresentedSubgroup jU hjU hStable
  have hequiv : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X)
      (x : T ⟶ U.X), c.act s x ≫ jU.hom.hom = b.act s (x ≫ jU.hom.hom) :=
    fun _ s x => b.onRepresentedSubgroup_act_comp jU hjU hStable s x
  have htop : (⊤ : SubgroupFunctor U).map jU = semigroupSubgroup b A := by
    rw [SubgroupFunctor.map_top, hjU.2]
  have hsupport : actionWeightSupport c ⊤ = positiveRelativeRoots j nu := by
    rw [← actionWeightSupport_map jU hjU.1 c b hequiv, htop]
    exact actionWeightSupport_positiveSemigroup semigroupRealization inferInstance hS j nu
  have hblocks := rootRayBlock_pairwise j nu a hinj ha hdisj
  have hcover : (⋃ r, rootRayBlock j (a r)) = actionWeightSupport c ⊤ :=
    (iUnion_rootRayBlock j nu a ha
      (fun chi hchi => positive_iff_mem_indivisiblePositiveRoot_ray j nu hchi)).trans
        hsupport.symm
  obtain ⟨K, jK, hK, hIso⟩ :=
    hasOrderedSemigroupProducts_of_unipotent c hS hUu n
      (fun r => rootRayBlock j (a r)) hcover hblocks.1 hblocks.2
  have hrootmem (r : Fin n) : a r ∈ indivisiblePositiveRoots j nu :=
    ha ▸ Set.mem_range_self r
  have hsemigroup (r : Fin n) :
      ((semigroupSubgroup c (AddSubsemigroup.closure (rootRayBlock j (a r)))).map jU) =
        semigroupSubgroup b (cyclicTail (a r) 1) := by
    rw [closure_rootRayBlock j (hrootmem r).1.1]
    apply semigroupSubgroup_map_eq jU hjUc c b hequiv
    rw [hjU.2]
    exact semigroupSubgroup_mono b (cyclicTail_one_le_positiveSemigroup (hrootmem r).2)
  have hfactor (r : Fin n) : (subgroup j (a r)).IsRepresentedBy (jK r ≫ jU) := by
    have hrep : (semigroupSubgroup b (cyclicTail (a r) 1)).IsRepresentedBy
        (jK r ≫ jU) := by
      rw [← hsemigroup r]
      exact (hK r).1.comp hjU
    have hcyclic := cyclicRootFunctorComparison k H inferInstance inferInstance
      S hS j (a r) (hrootmem r).1.1.1
    exact hcyclic ▸ hrep
  have hDynamic :
      Dynamic.unipotent (CommGroupScheme.groupHom nu ≫ j) = semigroupSubgroup b A :=
    dynamicUnipotentSemigroupComparison H S hS j nu
  let := hIso
  intro T g hg
  have hgA : g ∈ (semigroupSubgroup b A).carrier T := hDynamic ▸ hg
  let gU : T ⟶ U.X := (hjU.pointsEquiv _).symm ⟨g, hgA⟩
  let x : T ⟶ (∏ᶜ K).X := gU ≫ inv (orderedMultiplication jK)
  have hx : x ≫ orderedMultiplication (fun r => jK r ≫ jU) = g := by
    rw [← orderedMultiplication_comp jK jU]
    simp only [x, Category.assoc, IsIso.inv_hom_id_assoc]
    exact hjU.pointsEquiv_symm_comp _
  rw [← hx, comp_orderedMultiplication]
  unfold orderedPoints
  apply (F.carrier T).list_prod_mem
  intro y hy
  obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hy
  exact hroot (a r) ⟨(hrootmem r).1.1, (hrootmem r).2⟩ T
    (((hfactor r).pointsEquiv _ (finiteProductPointsEquiv K T x r)).property)

end Langlands.GroupScheme.RelativeRoot

namespace Langlands.BruhatTits.IntegralModels

namespace IntegralSplitTorusData

variable {R K : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {S : CommGroupScheme (Spec (CommRingCat.of K))}
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
    {i : S.toGrp ⟶ G} {N : IntegralModel R K G}
    [Smooth N.group.X.hom] (A : IntegralSplitTorusData N i)

private instance dynamicImage_specialFibre_affine : IsAffineHom N.specialFibre.X.hom :=
  MorphismProperty.pullback_snd _ _ (inferInstanceAs (IsAffineHom N.group.X.hom))

open RelativeRoot

/-- Divisibility within the actual root set is preserved by the canonical
character specialization to the full special fibre. -/
theorem mem_indivisibleRoots_characterSpecialization_iff (a : characterLattice S) :
    A.characterSpecialization a ∈ indivisibleRoots A.specialFibreInclusion ↔
      a ∈ indivisibleRoots i := by
  constructor
  · intro ha
    refine ⟨(A.mem_roots_characterSpecialization_iff a).mp ha.1, ?_⟩
    intro b hb m hm h
    apply ha.2 (A.characterSpecialization b)
      ((A.mem_roots_characterSpecialization_iff b).mpr hb) m hm
    simpa only [map_nsmul] using congrArg A.characterSpecialization h
  · intro ha
    refine ⟨(A.mem_roots_characterSpecialization_iff a).mpr ha.1, ?_⟩
    intro b hb m hm h
    have hb' : A.characterSpecialization.symm b ∈ relativeRoots i :=
      (A.mem_roots_characterSpecialization_iff _).mp (by simpa using hb)
    apply ha.2 (A.characterSpecialization.symm b) hb' m hm
    apply A.characterSpecialization.injective
    simpa only [map_nsmul, AddEquiv.apply_symm_apply] using h

/-- Disjoint positive root rays in the full special fibre follow from the
actual generic root system through the same integral split torus. -/
theorem disjoint_cyclicTail_special_indivisiblePositiveRoots
    [Mono i.hom.hom.left]
    (hroot : HasRelativeRootSystem i) (hS : IsSplitTorus S.toGrp)
    (nu : cocharacterLattice A.specialFibreTorus)
    {a b : characterLattice A.specialFibreTorus}
    (ha : a ∈ indivisiblePositiveRoots A.specialFibreInclusion nu)
    (hb : b ∈ indivisiblePositiveRoots A.specialFibreInclusion nu) (hne : a ≠ b) :
    Disjoint (cyclicTail a 1 : Set (characterLattice A.specialFibreTorus))
      (cyclicTail b 1 : Set (characterLattice A.specialFibreTorus)) := by
  have ha' : A.characterSpecialization.symm a ∈ indivisibleRoots i :=
    (A.mem_indivisibleRoots_characterSpecialization_iff _).mp (by simpa using ha.1)
  have hb' : A.characterSpecialization.symm b ∈ indivisibleRoots i :=
    (A.mem_indivisibleRoots_characterSpecialization_iff _).mp (by simpa using hb.1)
  have hne' : A.characterSpecialization.symm a ≠ A.characterSpecialization.symm b :=
    fun h => hne (A.characterSpecialization.symm.injective h)
  have hd := disjoint_cyclicTail_indivisibleRoots i hroot hS ha' hb' hne'
  apply Set.disjoint_left.mpr
  rintro chi ⟨m, hm, hm0, hma⟩ ⟨n, hn, hn0, hnb⟩
  apply Set.disjoint_left.mp hd
  · exact ⟨m, hm, hm0, by
      simpa only [map_nsmul] using congrArg A.characterSpecialization.symm hma⟩
  · exact ⟨n, hn, hn0, by
      simpa only [map_nsmul] using congrArg A.characterSpecialization.symm hnb⟩

end IntegralSplitTorusData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (N N' : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
    [Smooth N.group.X.hom] (Omega Omega' : Set C.Apartment)
    (hN : N.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Omega))
    (hN' : N'.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Omega'))
    (psi : N'.Hom N (𝟙 G))
    {Fa Ca : Set C.Apartment}
    (hCa : AffineRootSystem.IsFacet C.affineRoots Ca)
    (hFaCa : AffineRootSystem.IsFaceOf C.affineRoots Fa Ca)
    (hOmega : Omega.Nonempty) (hOmega' : Omega'.Nonempty)
    (hsub : Omega ⊆ Fa) (hsub' : Omega' ⊆ Ca)

local notation "A" => unramifiedZeroFixerIntegralSplitTorusData C E N Omega hN
local notation "nuS" =>
  IntegralSplitTorusData.cocharacterSpecialization
    (unramifiedZeroFixerIntegralSplitTorusData C E N Omega hN)
    (C.incidentFacetCocharacter hCa hFaCa)
local notation "chiS" => CommGroupScheme.groupHom nuS ≫
  IntegralSplitTorusData.specialFibreInclusion
    (unramifiedZeroFixerIntegralSplitTorusData C E N Omega hN)

local instance dynamic_model_specialFibre_affine
    (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G) :
    IsAffineHom M.specialFibre.X.hom :=
  MorphismProperty.pullback_snd _ _ (inferInstanceAs (IsAffineHom M.group.X.hom))

local instance target_specialFibre_smooth : Smooth N.specialFibre.X.hom :=
  MorphismProperty.pullback_snd _ _ (inferInstanceAs (Smooth N.group.X.hom))

include hN' hOmega hOmega' hsub hsub' in
/-- The actual dynamic positive subgroup selected by incident facets lies
in the actual comparison image on every residue-scheme test. -/
theorem unramifiedIncidentDynamicUnipotent_le_image :
    Dynamic.unipotent chiS ≤
      SubgroupFunctor.range (SchematicImage.inclusion psi.specialFibreMap) := by
  apply RelativeRoot.dynamicUnipotent_le_of_positive_rootSubgroups_le
    (A).specialFibreTorus_isSplit (A).specialFibreInclusion nuS
  · intro a ha b hb hne
    exact (A).disjoint_cyclicTail_special_indivisiblePositiveRoots
      (relativeRootSystem (inertiaFixedField F) G C.isConnectedReductive
        C.S C.i C.isMaximalSplitTorus)
      C.isMaximalSplitTorus.isSplitSubtorus.1 nuS ha hb hne
  · intro b hb
    let a := (A).characterSpecialization.symm b
    have he : (A).characterSpecialization a = b :=
      (A).characterSpecialization.apply_symm_apply b
    have har : a ∈ relativeRoots C.i :=
      ((A).mem_roots_characterSpecialization_iff a).mp (he.symm ▸ hb.1)
    have hpos : 0 < latticePairing C.S a (C.incidentFacetCocharacter hCa hFaCa) := by
      have hpair := (A).latticePairing_specialization a
        (C.incidentFacetCocharacter hCa hFaCa)
      rw [he] at hpair
      exact hpair ▸ hb.2
    have hrep := (A).rootModelMap_specialFibre_isRepresentedBy a har.1
    rw [← he, ← hrep.2]
    exact unramifiedIncidentPositiveRoot_range_le_image
      C E N N' Omega Omega' hN hN' psi hCa hFaCa hOmega hOmega' hsub hsub' ⟨a, har⟩ hpos

/-- The canonical inclusion of dynamic positive points into incident image
points, as a group homomorphism for every residue-scheme test. -/
def unramifiedIncidentDynamicUnipotentImagePoints
    (T : Over (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F))))) :
    (Dynamic.unipotent chiS).carrier T →*
      (SubgroupFunctor.range (SchematicImage.inclusion psi.specialFibreMap)).carrier T :=
  Subgroup.inclusion ((unramifiedIncidentDynamicUnipotent_le_image
    C E N N' Omega Omega' hN hN' psi hCa hFaCa hOmega hOmega' hsub hsub') T)

@[simp]
theorem unramifiedIncidentDynamicUnipotentImagePoints_val
    (T : Over (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))))
    (x : (Dynamic.unipotent chiS).carrier T) :
    (unramifiedIncidentDynamicUnipotentImagePoints
      C E N N' Omega Omega' hN hN' psi hCa hFaCa hOmega hOmega' hsub hsub' T x).val = x.val :=
  rfl

end Langlands.BruhatTits.IntegralModels
