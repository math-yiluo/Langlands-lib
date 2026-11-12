import Langlands.BruhatTits.IntegralModels.FacetAxioms

/-! # Transport of supplied KP models along a generic-group isomorphism

For `f : G ≅ H`, a supplied integral model of `G` is regarded as a model of `H` by keeping
its integral group scheme and composing its generic identification with `f`. All special
fibres, reductions, special-fibre maps and quotient data are then literally unchanged, so
every special-fibre clause of KP Axioms 4.1.20 and 4.1.22 transfers by `Iff.rfl`, while
the generic integral-point images are carried along `rationalPoints.map f.hom`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section RationalPointsIso

variable {k : Type u} [CommRing k] {G H J : GroupScheme (Spec (CommRingCat.of k))}

/-- Rational-point maps are functorial (here over any ring). -/
theorem rationalPoints_map_comp_apply_of_ring (a : G ⟶ H) (b : H ⟶ J)
    (x : rationalPoints G) :
    rationalPoints.map (a ≫ b) x = rationalPoints.map b (rationalPoints.map a x) := by
  simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]

/-- An isomorphism of group schemes induces an injective map of rational points. -/
theorem rationalPoints_map_injective_of_iso (f : G ≅ H) :
    Function.Injective (rationalPoints.map f.hom) := by
  intro x y hxy
  have h := congrArg (rationalPoints.map f.inv) hxy
  change (x ≫ f.hom.hom.hom) ≫ f.inv.hom.hom = (y ≫ f.hom.hom.hom) ≫ f.inv.hom.hom at h
  simpa only [Category.assoc, ← Grp.comp_hom_hom, f.hom_inv_id, Grp.id_hom_hom,
    Category.comp_id] using h

end RationalPointsIso

namespace IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G H : GroupScheme (Spec (CommRingCat.of K))}

/-- The same integral group scheme, with its supplied generic identification
composed with `f : G ≅ H`. -/
def transport (M : IntegralModel R K G) (f : G ≅ H) : IntegralModel R K H where
  group := M.group
  genericIso := M.genericIso ≪≫ f

variable (M : IntegralModel R K G) (f : G ≅ H)

@[simp] theorem transport_group : (M.transport f).group = M.group := rfl

theorem transport_genericIso_hom :
    (M.transport f).genericIso.hom = M.genericIso.hom ≫ f.hom := rfl

/-- Smoothness concerns only the unchanged integral group scheme. -/
theorem isSmooth_transport_iff : (M.transport f).IsSmooth ↔ M.IsSmooth := Iff.rfl

/-- Connectedness of fibres concerns only the unchanged integral group scheme. -/
theorem hasConnectedFibres_transport_iff :
    (M.transport f).HasConnectedFibres ↔ M.HasConnectedFibres := Iff.rfl

/-- Generic points of transported integral sections are the `f`-images of the old ones. -/
theorem transport_integralPointMap (x : M.integralSections) :
    (M.transport f).integralPointMap x = rationalPoints.map f.hom (M.integralPointMap x) := by
  change rationalPoints.map (M.genericIso.hom ≫ f.hom)
      (baseChangeSectionHom (Spec.algebraMap R K) M.group x) =
    rationalPoints.map f.hom (rationalPoints.map M.genericIso.hom
      (baseChangeSectionHom (Spec.algebraMap R K) M.group x))
  exact rationalPoints_map_comp_apply_of_ring _ _ _

/-- The transported integral-point image is the `f`-image of the original one. -/
theorem transport_integralPoints :
    (M.transport f).integralPoints = M.integralPoints.map (rationalPoints.map f.hom) := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨M.integralPointMap x, ⟨x, rfl⟩, (M.transport_integralPointMap f x).symm⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, M.transport_integralPointMap f x⟩

variable {M}

/-- A model morphism over `g` is a morphism of the transported models over any generic
map `g'` making the square with the two generic isomorphisms commute. -/
def Hom.transport {N : IntegralModel R K H} {g : G ⟶ H} (φ : M.Hom N g)
    {G' H' : GroupScheme (Spec (CommRingCat.of K))} (e : G ≅ G') (e' : H ≅ H')
    (g' : G' ⟶ H') (hg : g ≫ e'.hom = e.hom ≫ g') :
    (M.transport e).Hom (N.transport e') g' where
  hom := φ.hom
  generic_comm := by
    change (GroupScheme.baseChange (Spec.algebraMap R K)).map φ.hom ≫
        N.genericIso.hom ≫ e'.hom = (M.genericIso.hom ≫ e.hom) ≫ g'
    rw [← Category.assoc, φ.generic_comm, Category.assoc, hg, Category.assoc]

@[simp] theorem Hom.transport_hom {N : IntegralModel R K H} {g : G ⟶ H} (φ : M.Hom N g)
    {G' H' : GroupScheme (Spec (CommRingCat.of K))} (e : G ≅ G') (e' : H ≅ H')
    (g' : G' ⟶ H') (hg : g ≫ e'.hom = e.hom ≫ g') :
    (φ.transport e e' g' hg).hom = φ.hom := rfl

/-- The identity-generic case: a morphism over `𝟙 G` becomes one over `𝟙 H`. -/
def Hom.transportId {N : IntegralModel R K G} (φ : M.Hom N (𝟙 G)) (f : G ≅ H) :
    (M.transport f).Hom (N.transport f) (𝟙 H) :=
  φ.transport f f (𝟙 H) (by rw [Category.id_comp, Category.comp_id])

@[simp] theorem Hom.transportId_hom {N : IntegralModel R K G} (φ : M.Hom N (𝟙 G))
    (f : G ≅ H) : (φ.transportId f).hom = φ.hom := rfl

end IntegralModel
end Langlands.GroupScheme

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G H : GroupScheme (Spec (CommRingCat.of K))}

/-- A commutative-group-scheme isomorphism regarded on the underlying group schemes. -/
def underlyingTorusIso {X : Scheme.{u}} {S S' : CommGroupScheme X} (σ : S ≅ S') :
    S.toGrp ≅ S'.toGrp where
  hom := CommGroupScheme.groupHom σ.hom
  inv := CommGroupScheme.groupHom σ.inv
  hom_inv_id := congrArg Additive.toMul σ.hom_inv_id
  inv_hom_id := congrArg Additive.toMul σ.inv_hom_id

section LatticeTransport

variable {X : CommRingCat.{u}} {T S S' : CommGroupScheme (Spec X)}

/-- Pulling characters back along `e` followed by `σ` is pulling back along `e`,
then transporting by `σ`. -/
theorem comapIso_trans_symm_apply (e : T.toGrp ≅ S.toGrp) (σ : S ≅ S')
    (χ : characterLattice T) :
    (characterLattice.comapIso (e ≪≫ underlyingTorusIso σ)).symm χ =
      characterLattice.congr σ ((characterLattice.comapIso e).symm χ) :=
  Category.assoc σ.inv (Additive.ofMul e.inv : S ⟶ T) χ

/-- Pushing cocharacters forward along `e` followed by `σ` is pushing forward along
`e`, then transporting by `σ`. -/
theorem cocharacterCongr_isoOfGroupIso_trans (e : T.toGrp ≅ S.toGrp) (σ : S ≅ S')
    (ν : cocharacterLattice T) :
    cocharacterLattice.congr (CommGroupScheme.isoOfGroupIso (e ≪≫ underlyingTorusIso σ)) ν =
      cocharacterLattice.congr σ
        (cocharacterLattice.congr (CommGroupScheme.isoOfGroupIso e) ν) :=
  (Category.assoc ν (Additive.ofMul e.hom : T ⟶ S) σ.hom).symm

end LatticeTransport

namespace RelativeComponentModelData

/-- Both supplied models transported along `f`, with the same inclusion morphism. -/
def transport (D : RelativeComponentModelData R K G) (f : G ≅ H) :
    RelativeComponentModelData R K H where
  full := D.full.transport f
  neutral := D.neutral.transport f
  full_smooth := D.full_smooth
  neutral_smooth := D.neutral_smooth
  neutral_connectedFibres := D.neutral_connectedFibres
  inclusion := D.inclusion.transportId f
  isRelativeComponent := D.isRelativeComponent

variable (D : RelativeComponentModelData R K G) (f : G ≅ H)

@[simp] theorem transport_full : (D.transport f).full = D.full.transport f := rfl

@[simp] theorem transport_neutral : (D.transport f).neutral = D.neutral.transport f := rfl

@[simp] theorem transport_inclusion_hom : (D.transport f).inclusion.hom = D.inclusion.hom :=
  rfl

/-- The full integral points of the transported data are the `f`-image of the old ones. -/
theorem transport_full_integralPoints :
    (D.transport f).full.integralPoints =
      D.full.integralPoints.map (rationalPoints.map f.hom) :=
  D.full.transport_integralPoints f

/-- The neutral integral points of the transported data are the `f`-image of the old ones. -/
theorem transport_neutral_integralPoints :
    (D.transport f).neutral.integralPoints =
      D.neutral.integralPoints.map (rationalPoints.map f.hom) :=
  D.neutral.transport_integralPoints f

/-- KP Axiom 4.1.20(4) transfers, since simple connectedness is isomorphism invariant. -/
theorem hasEqualComponentsForSimplyConnected_transport_iff :
    (D.transport f).HasEqualComponentsForSimplyConnected ↔
      D.HasEqualComponentsForSimplyConnected := by
  change (IsSimplyConnected H → IsIso D.inclusion.hom) ↔
    (IsSimplyConnected G → IsIso D.inclusion.hom)
  rw [isSimplyConnected_iff_of_iso f]

end RelativeComponentModelData

namespace RelativeComponentModelHom

variable {source target : RelativeComponentModelData R K G}

/-- The same integral morphisms between the transported model data. -/
def transport (φ : RelativeComponentModelHom source target) (f : G ≅ H) :
    RelativeComponentModelHom (source.transport f) (target.transport f) where
  full := φ.full.transportId f
  neutral := φ.neutral.transportId f
  component_comm := φ.component_comm

variable (φ : RelativeComponentModelHom source target) (f : G ≅ H)

@[simp] theorem transport_full_hom : (φ.transport f).full.hom = φ.full.hom := rfl

@[simp] theorem transport_neutral_hom : (φ.transport f).neutral.hom = φ.neutral.hom := rfl

section Residue

variable [IsLocalRing R]

theorem transport_neutralSpecialFibreMap :
    (φ.transport f).neutralSpecialFibreMap = φ.neutralSpecialFibreMap := rfl

/-- The preamble and part (1) of KP Axiom 4.1.22 transfer verbatim. -/
theorem satisfiesGeneralSpecialFibreClauses_transport_iff :
    (φ.transport f).SatisfiesGeneralSpecialFibreClauses ↔
      φ.SatisfiesGeneralSpecialFibreClauses := Iff.rfl

/-- KP Axiom 4.1.22(2) transfers verbatim. -/
theorem hasParabolicSpecialFibreImage_transport_iff :
    (φ.transport f).HasParabolicSpecialFibreImage ↔ φ.HasParabolicSpecialFibreImage :=
  Iff.rfl

/-- KP Axiom 4.1.22(4) transfers verbatim. -/
theorem hasParabolicReductionPreimage_transport_iff :
    (φ.transport f).HasParabolicReductionPreimage ↔ φ.HasParabolicReductionPreimage := by
  have e₁ : (φ.transport f).specialFibreImagePoints.comap (target.transport f).neutral.reduction =
      φ.specialFibreImagePoints.comap target.neutral.reduction := by
    unfold IntegralModel.reduction
    rfl
  have e₂ : (rationalPoints.map (φ.transport f).neutral.hom).range =
      (rationalPoints.map φ.neutral.hom).range := rfl
  unfold HasParabolicReductionPreimage
  rw [e₁, e₂]

end Residue
end RelativeComponentModelHom

section Quotient

variable [IsLocalRing R] {D : RelativeComponentModelData R K G}

/-- The same radical and quotient, regarded as data for the transported models. -/
def SpecialFibreQuotientData.transport (Q : SpecialFibreQuotientData D) (f : G ≅ H) :
    SpecialFibreQuotientData (D.transport f) where
  radical := Q.radical
  radicalInclusion := Q.radicalInclusion
  quotient := Q.quotient
  projection := Q.projection

namespace SpecialFibreQuotientData

variable (Q : SpecialFibreQuotientData D) (f : G ≅ H)

theorem isReductiveQuotient_transport_iff :
    (Q.transport f).IsReductiveQuotient ↔ Q.IsReductiveQuotient := Iff.rfl

/-- The positive subgroup of the transported data is the `f`-image of the old one. -/
theorem transport_positivePoints :
    (Q.transport f).positivePoints = Q.positivePoints.map (rationalPoints.map f.hom) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨D.neutral.integralPointMap x, ⟨x, hx, rfl⟩,
      (D.neutral.transport_integralPointMap f x).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, D.neutral.transport_integralPointMap f x⟩

end SpecialFibreQuotientData

/-- KP Axiom 4.1.22(7) transfers, since `rationalPoints.map f.hom` is injective. -/
theorem RelativeComponentModelHom.satisfiesPositiveRadicalClause_transport_iff
    {source target : RelativeComponentModelData R K G}
    (Q : SpecialFibreQuotientData target) (Qsource : SpecialFibreQuotientData source)
    (f : G ≅ H) :
    RelativeComponentModelHom.SatisfiesPositiveRadicalClause (Q.transport f)
        (Qsource.transport f) ↔
      RelativeComponentModelHom.SatisfiesPositiveRadicalClause Q Qsource := by
  change (Function.Surjective target.neutral.reduction ∧
      Function.Surjective source.neutral.reduction ∧
      (Q.transport f).positivePoints ≤ (Qsource.transport f).positivePoints) ↔ _
  rw [Q.transport_positivePoints, Qsource.transport_positivePoints,
    Subgroup.map_le_map_iff_of_injective (rationalPoints_map_injective_of_iso f)]
  rfl

end Quotient

namespace IntegralTorusData

variable {D : RelativeComponentModelData R K G}
  {S S' : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}

/-- The same integral torus and inclusion, for the transported models and the torus
`S'`, using any generic inclusion `j` forming a commuting square with `σ` and `f`. -/
def transport (T : IntegralTorusData D S i) (f : G ≅ H) (σ : S ≅ S')
    {j : S'.toGrp ⟶ H} (h : i ≫ f.hom = CommGroupScheme.groupHom σ.hom ≫ j) :
    IntegralTorusData (D.transport f) S' j where
  torus := T.torus
  genericIso := T.genericIso ≪≫ underlyingTorusIso σ
  inclusion := T.inclusion
  generic_comm := by
    change (GroupScheme.baseChange (Spec.algebraMap R K)).map T.inclusion ≫
        D.neutral.genericIso.hom ≫ f.hom =
      (T.genericIso.hom ≫ CommGroupScheme.groupHom σ.hom) ≫ j
    rw [← Category.assoc, T.generic_comm, Category.assoc, h, Category.assoc]

variable (T : IntegralTorusData D S i) (f : G ≅ H) (σ : S ≅ S')
  {j : S'.toGrp ⟶ H} (h : i ≫ f.hom = CommGroupScheme.groupHom σ.hom ≫ j)

@[simp] theorem transport_torus : (T.transport f σ h).torus = T.torus := rfl

@[simp] theorem transport_inclusion : (T.transport f σ h).inclusion = T.inclusion := rfl

theorem isClosedSplit_transport_iff :
    (T.transport f σ h).IsClosedSplit ↔ T.IsClosedSplit := Iff.rfl

section Residue

variable [IsLocalRing R]

theorem transport_specialFibreInclusion :
    (T.transport f σ h).specialFibreInclusion = T.specialFibreInclusion := rfl

theorem hasMaximalSplitSpecialFibre_transport_iff :
    (T.transport f σ h).HasMaximalSplitSpecialFibre ↔ T.HasMaximalSplitSpecialFibre :=
  Iff.rfl

/-- KP Axiom 4.1.20(3) transfers verbatim. -/
theorem satisfiesTorusClause_transport_iff :
    (T.transport f σ h).SatisfiesTorusClause ↔ T.SatisfiesTorusClause := Iff.rfl

omit [IsLocalRing R] in
/-- The generic character identification changes by `σ`. -/
theorem transport_genericCharacterEquiv (hT : IsSplitTorus T.torus.toGrp)
    (ψ : characterLattice T.torus) :
    (T.transport f σ h).genericCharacterEquiv hT ψ =
      characterLattice.congr σ (T.genericCharacterEquiv hT ψ) := by
  simp only [genericCharacterEquiv, AddEquiv.trans_apply, AddEquiv.ofBijective_apply]
  exact comapIso_trans_symm_apply
    (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T.torus) T.genericIso σ
    (characterLattice.baseChange (Spec.algebraMap R K) T.torus ψ)

/-- Character specialization through the transported torus is precomposed with `σ`. -/
theorem transport_characterSpecialization (hT : IsSplitTorus T.torus.toGrp)
    (χ : characterLattice S) :
    (T.transport f σ h).characterSpecialization hT (characterLattice.congr σ χ) =
      T.characterSpecialization hT χ := by
  obtain ⟨ψ, rfl⟩ := (T.genericCharacterEquiv hT).surjective χ
  rw [← T.transport_genericCharacterEquiv f σ h hT ψ]
  change (T.transport f σ h).specialCharacterEquiv hT
      (((T.transport f σ h).genericCharacterEquiv hT).symm
        ((T.transport f σ h).genericCharacterEquiv hT ψ)) =
    T.specialCharacterEquiv hT ((T.genericCharacterEquiv hT).symm (T.genericCharacterEquiv hT ψ))
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  rfl

/-- The inverse specialization through the transported torus is followed by `σ`. -/
theorem transport_characterSpecialization_symm (hT : IsSplitTorus T.torus.toGrp)
    (χ : characterLattice T.specialFibre) :
    ((T.transport f σ h).characterSpecialization hT).symm χ =
      characterLattice.congr σ ((T.characterSpecialization hT).symm χ) := by
  apply ((T.transport f σ h).characterSpecialization hT).injective
  rw [AddEquiv.apply_symm_apply]
  exact ((T.transport_characterSpecialization f σ h hT _).trans
    (AddEquiv.apply_symm_apply _ _)).symm

omit [IsLocalRing R] in
/-- The generic cocharacter identification changes by `σ`. -/
theorem transport_genericCocharacterEquiv (hT : IsSplitTorus T.torus.toGrp)
    (ν : cocharacterLattice T.torus) :
    (T.transport f σ h).genericCocharacterEquiv hT ν =
      cocharacterLattice.congr σ (T.genericCocharacterEquiv hT ν) := by
  simp only [genericCocharacterEquiv, AddEquiv.trans_apply]
  exact cocharacterCongr_isoOfGroupIso_trans
    (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T.torus) T.genericIso σ
    (cocharacterLattice.baseChangeEquiv (Spec.algebraMap R K) T.torus hT ν)

/-- Cocharacter specialization through the transported torus is precomposed with `σ`. -/
theorem transport_cocharacterSpecialization (hT : IsSplitTorus T.torus.toGrp)
    (ν : cocharacterLattice S) :
    (T.transport f σ h).cocharacterSpecialization hT (cocharacterLattice.congr σ ν) =
      T.cocharacterSpecialization hT ν := by
  obtain ⟨ν₀, rfl⟩ := (T.genericCocharacterEquiv hT).surjective ν
  rw [← T.transport_genericCocharacterEquiv f σ h hT ν₀]
  change (T.transport f σ h).specialCocharacterEquiv hT
      (((T.transport f σ h).genericCocharacterEquiv hT).symm
        ((T.transport f σ h).genericCocharacterEquiv hT ν₀)) =
    T.specialCocharacterEquiv hT
      ((T.genericCocharacterEquiv hT).symm (T.genericCocharacterEquiv hT ν₀))
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  rfl

end Residue
end IntegralTorusData

namespace RelativeComponentModelHom

variable [IsLocalRing R] {source target : RelativeComponentModelData R K G}
  (φ : RelativeComponentModelHom source target) (Q : SpecialFibreQuotientData target)
  {S S' : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
  (T : IntegralTorusData source S i) (f : G ≅ H) (σ : S ≅ S')
  {j : S'.toGrp ⟶ H} (h : i ≫ f.hom = CommGroupScheme.groupHom σ.hom ≫ j)

theorem transport_targetTorusInclusion :
    (φ.transport f).targetTorusInclusion (T.transport f σ h) = φ.targetTorusInclusion T :=
  rfl

theorem transport_quotientTorusInclusion :
    (φ.transport f).quotientTorusInclusion (Q.transport f) (T.transport f σ h) =
      φ.quotientTorusInclusion Q T :=
  rfl

/-- The maximal-split-torus assertions of KP Axiom 4.1.22(3) transfer verbatim. -/
theorem hasMaximalSplitTori_transport_iff :
    (φ.transport f).HasMaximalSplitTori (Q.transport f) (T.transport f σ h) ↔
      φ.HasMaximalSplitTori Q T := Iff.rfl

end RelativeComponentModelHom
end Langlands.BruhatTits.IntegralModels
