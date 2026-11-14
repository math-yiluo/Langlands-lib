import Langlands.BruhatTits.IntegralModels.FacetRootSignRestriction
import Langlands.BruhatTits.IntegralModels.RelativeComponentFunctoriality
import Langlands.GroupScheme.Reductive.PinningScalarCoherence
import Langlands.GroupScheme.SchematicImageComparison
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Torus.RootSupportBaseChange
import Langlands.GroupScheme.Rational.CrossTorusLieTransport
import Langlands.GroupScheme.BaseChangeReflection

/-! # The facet root identity under extension of local coefficients

Let `R → A` be a local homomorphism of local domains, compatible with a
homomorphism `K → L` of their fraction fields. The model pair, the model
morphism, the special-fibre quotient data and the integral torus of the KP
facet sign formula all change base along `R → A`. The special fibres of the
base-changed data are the residue-field base changes of the original special
fibres, and the reductive image is compatible with this base change. Hence the
root form of the sign formula descends from `A` to `R`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

/-- Base change of an affine group scheme is affine. -/
local instance facetRootSignBaseChange_isAffineHom {S S' : Scheme.{u}} (b : S' ⟶ S)
    (M : GroupScheme S) [IsAffineHom M.X.hom] :
    IsAffineHom ((GroupScheme.baseChange b).obj M).X.hom := by
  change IsAffineHom (pullback.snd M.X.hom b)
  exact MorphismProperty.pullback_snd _ _ ‹IsAffineHom M.X.hom›

section ResidueTorusLevel

variable {R A : Type u} [CommRing R] [CommRing A] [IsLocalRing R] [IsLocalRing A]
  [Algebra R A] [IsLocalHom (algebraMap R A)]
  {T : CommGroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}
  {T' : CommGroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField A)))}
  {H Q : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}
  {H' Q' : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField A)))}
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  [IsAffineHom Q.X.hom] [LocallyOfFiniteType Q.X.hom]
  [IsAffineHom H'.X.hom] [IsAffineHom Q'.X.hom]

local notation "resExt" =>
  algebraBaseMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A)

/-- **Descent of a signed root identity along a residue field extension.** Let
`R → A` be a local homomorphism of local rings with residue fields `k → k'`.
Let `T` be a split torus over `k` mapping to `H` and `Q` by `t` and `a`, and
let `t' : T' → H'`, `a' : T' → Q'` over `k'` be identified with the base
changes of `t` and `a` by isomorphisms `e`, `f`, `g`. Let the sign functions
satisfy `s' (e(χ_{k'})) = s χ`. If the roots of `t'` are the roots of `a'`
with `s' ≥ 0`, then the roots of `t` are the roots of `a` with `s ≥ 0`.

The statement uses the ring structure of the residue fields that the special
fibres of integral models use. -/
theorem roots_eq_nonneg_of_residueBaseChange (hT : IsSplitTorus T.toGrp)
    (t : T.toGrp ⟶ H) (a : T.toGrp ⟶ Q) (t' : T'.toGrp ⟶ H') (a' : T'.toGrp ⟶ Q')
    (e : (CommGroupScheme.baseChange resExt).obj T ≅ T')
    (f : (GroupScheme.baseChange resExt).obj H ≅ H')
    (g : (GroupScheme.baseChange resExt).obj Q ≅ Q')
    (ht : (GroupScheme.baseChange resExt).map t ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ t')
    (ha : (GroupScheme.baseChange resExt).map a ≫ g.hom = CommGroupScheme.groupHom e.hom ≫ a')
    (s : characterLattice T → ℝ) (s' : characterLattice T' → ℝ)
    (hs : ∀ χ, s' (characterLattice.congr e (characterLattice.baseChange resExt T χ)) = s χ)
    (h : roots t' = {χ | χ ∈ roots a' ∧ 0 ≤ s' χ}) :
    roots t = {χ | χ ∈ roots a ∧ 0 ≤ s χ} := by
  ext χ
  have h₁ := mem_roots_baseChange_iff (K := IsLocalRing.ResidueField A) H T hT t χ
  have h₂ := mem_roots_baseChange_iff (K := IsLocalRing.ResidueField A) Q T hT a χ
  have h₃ := roots_mem_of_transport_iff e f ht (characterLattice.baseChange resExt T χ)
  have h₄ := roots_mem_of_transport_iff e g ha (characterLattice.baseChange resExt T χ)
  have h₅ : characterLattice.congr e (characterLattice.baseChange resExt T χ) ∈ roots t' ↔
      characterLattice.congr e (characterLattice.baseChange resExt T χ) ∈ roots a' ∧
        0 ≤ s χ := by
    rw [h, ← hs χ]
    exact Iff.rfl
  rw [Set.mem_ofPred_eq, ← h₁, ← h₃, h₅, h₄, h₂]

end ResidueTorusLevel

section Coefficients

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (A L : Type u) [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]

namespace RelativeComponentModelHom

variable {D D' : RelativeComponentModelData R K G}

/-- Change the coefficients of a model morphism along the coefficient square. -/
def baseChange (φ : RelativeComponentModelHom D' D) :
    RelativeComponentModelHom (D'.baseChange A L) (D.baseChange A L) where
  full :=
    { hom := (GroupScheme.baseChange (Spec.algebraMap R A)).map φ.full.hom
      generic_comm := by
        have h := D'.full.baseChangeGenericIso_naturality A L D.full φ.full
        rw [CategoryTheory.Functor.map_id] at h
        exact h }
  neutral :=
    { hom := (GroupScheme.baseChange (Spec.algebraMap R A)).map φ.neutral.hom
      generic_comm := by
        have h := D'.neutral.baseChangeGenericIso_naturality A L D.neutral φ.neutral
        rw [CategoryTheory.Functor.map_id] at h
        exact h }
  component_comm := by
    change (GroupScheme.baseChange (Spec.algebraMap R A)).map φ.neutral.hom ≫
        (GroupScheme.baseChange (Spec.algebraMap R A)).map D.inclusion.hom =
      (GroupScheme.baseChange (Spec.algebraMap R A)).map D'.inclusion.hom ≫
        (GroupScheme.baseChange (Spec.algebraMap R A)).map φ.full.hom
    rw [← Functor.map_comp, ← Functor.map_comp, φ.component_comm]

@[simp] theorem baseChange_full_hom (φ : RelativeComponentModelHom D' D) :
    (φ.baseChange A L).full.hom =
      (GroupScheme.baseChange (Spec.algebraMap R A)).map φ.full.hom := rfl

@[simp] theorem baseChange_neutral_hom (φ : RelativeComponentModelHom D' D) :
    (φ.baseChange A L).neutral.hom =
      (GroupScheme.baseChange (Spec.algebraMap R A)).map φ.neutral.hom := rfl

end RelativeComponentModelHom

namespace IntegralTorusData

/-- The generic fibre of an inclusion of an integral torus into the neutral
model, as a map out of the generic fibre of the commutative torus. -/
def genericInclusionOf (D : RelativeComponentModelData R K G)
    (torus : CommGroupScheme (Spec (CommRingCat.of R)))
    (inclusion : torus.toGrp ⟶ D.neutral.group) :
    ((CommGroupScheme.baseChange (Spec.algebraMap R K)).obj torus).toGrp ⟶ G :=
  (GroupScheme.baseChange (Spec.algebraMap R K)).map inclusion ≫ D.neutral.genericIso.hom

/-- An integral torus in the neutral model, with its own generic fibre as the
generic torus and the generic fibre of the inclusion as the generic inclusion. -/
abbrev ofInclusion (D : RelativeComponentModelData R K G)
    (torus : CommGroupScheme (Spec (CommRingCat.of R)))
    (inclusion : torus.toGrp ⟶ D.neutral.group) :
    IntegralTorusData D ((CommGroupScheme.baseChange (Spec.algebraMap R K)).obj torus)
      (genericInclusionOf D torus inclusion) where
  torus := torus
  genericIso := Iso.refl _
  inclusion := inclusion
  generic_comm := (Category.id_comp _).symm

@[simp] theorem ofInclusion_torus (D : RelativeComponentModelData R K G)
    (torus : CommGroupScheme (Spec (CommRingCat.of R)))
    (inclusion : torus.toGrp ⟶ D.neutral.group) :
    (ofInclusion D torus inclusion).torus = torus := rfl

@[simp] theorem ofInclusion_inclusion (D : RelativeComponentModelData R K G)
    (torus : CommGroupScheme (Spec (CommRingCat.of R)))
    (inclusion : torus.toGrp ⟶ D.neutral.group) :
    (ofInclusion D torus inclusion).inclusion = inclusion := rfl

variable {D' : RelativeComponentModelData R K G}
  {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}

/-- The base change of the inclusion of an integral torus, as a map out of the
base change of the commutative torus. -/
def baseChangeInclusion (T : IntegralTorusData D' S i) :
    ((CommGroupScheme.baseChange (Spec.algebraMap R A)).obj T.torus).toGrp ⟶
      (D'.baseChange A L).neutral.group :=
  (GroupScheme.baseChange (Spec.algebraMap R A)).map T.inclusion

/-- Change the coefficients of an integral torus along the coefficient square.
Its generic torus is the generic fibre of the base-changed integral torus. -/
abbrev baseChange (T : IntegralTorusData D' S i) :
    IntegralTorusData (D'.baseChange A L)
      ((CommGroupScheme.baseChange (Spec.algebraMap A L)).obj
        ((CommGroupScheme.baseChange (Spec.algebraMap R A)).obj T.torus))
      (genericInclusionOf (D'.baseChange A L)
        ((CommGroupScheme.baseChange (Spec.algebraMap R A)).obj T.torus)
        (T.baseChangeInclusion A L)) :=
  ofInclusion (D'.baseChange A L)
    ((CommGroupScheme.baseChange (Spec.algebraMap R A)).obj T.torus)
    (T.baseChangeInclusion A L)

@[simp] theorem baseChange_torus (T : IntegralTorusData D' S i) :
    (T.baseChange A L).torus =
      (CommGroupScheme.baseChange (Spec.algebraMap R A)).obj T.torus := rfl

@[simp] theorem baseChange_inclusion (T : IntegralTorusData D' S i) :
    (T.baseChange A L).inclusion = T.baseChangeInclusion A L := rfl

/-- The base change of a split integral torus is split. -/
theorem isSplitTorus_baseChange (T : IntegralTorusData D' S i) (hT : IsSplitTorus T.torus.toGrp) :
    IsSplitTorus (T.baseChange A L).torus.toGrp :=
  hT.baseChange (Spec.algebraMap R A)

end IntegralTorusData

section Residue

variable [IsLocalRing R] [IsLocalRing A] [IsLocalHom (algebraMap R A)]

local notation "resExt" =>
  algebraBaseMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A)

omit [IsLocalRing A] [IsLocalHom (algebraMap R A)] in
/-- The special character equivalence is the residue-base change of characters. -/
theorem IntegralTorusData.specialCharacterEquiv_apply {D : RelativeComponentModelData R K G}
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
    (T : IntegralTorusData D S i) (hT : IsSplitTorus T.torus.toGrp)
    (m : characterLattice T.torus) :
    T.specialCharacterEquiv hT m =
      characterLattice.baseChange (IntegralModel.residueBaseMap R) T.torus m :=
  rfl

omit [IsDomain R] [IsDomain A] in
/-- The residue maps commute with the coefficient change. -/
theorem residueExtension_comp_residueBaseMap :
    resExt ≫ IntegralModel.residueBaseMap R =
      IntegralModel.residueBaseMap A ≫ Spec.algebraMap R A := by
  simp only [IntegralModel.residueBaseMap, algebraBaseMap, Spec.algebraMap, ← Spec.map_comp]
  congr 1

/-- The residue-field base change of the special fibre of a group scheme over
`R` is the special fibre of its base change to `A`. -/
def specialFibreSquareIso (M : GroupScheme (Spec (CommRingCat.of R))) :
    (GroupScheme.baseChange resExt).obj
        ((GroupScheme.baseChange (IntegralModel.residueBaseMap R)).obj M) ≅
      (GroupScheme.baseChange (IntegralModel.residueBaseMap A)).obj
        ((GroupScheme.baseChange (Spec.algebraMap R A)).obj M) :=
  GroupScheme.Descent.pullbackComparison (IntegralModel.residueBaseMap R) resExt
      (resExt ≫ IntegralModel.residueBaseMap R) rfl M ≪≫
    (GroupScheme.Descent.pullbackComparison (Spec.algebraMap R A)
      (IntegralModel.residueBaseMap A) (resExt ≫ IntegralModel.residueBaseMap R)
      (residueExtension_comp_residueBaseMap A).symm M).symm

omit [IsDomain R] [IsDomain A] in
/-- The special-fibre square isomorphism is natural. -/
@[reassoc]
theorem specialFibreSquareIso_naturality {M N : GroupScheme (Spec (CommRingCat.of R))}
    (f : M ⟶ N) :
    (GroupScheme.baseChange resExt).map
        ((GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map f) ≫
        (specialFibreSquareIso A N).hom =
      (specialFibreSquareIso A M).hom ≫
        (GroupScheme.baseChange (IntegralModel.residueBaseMap A)).map
          ((GroupScheme.baseChange (Spec.algebraMap R A)).map f) := by
  simp only [specialFibreSquareIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [GroupScheme.Descent.pullbackComparison_naturality_assoc]
  congr 1
  rw [Iso.comp_inv_eq, Category.assoc, GroupScheme.Descent.pullbackComparison_naturality,
    Iso.inv_hom_id_assoc]

/-- The special-fibre square isomorphism for commutative group schemes. -/
def specialFibreCommSquareIso (C : CommGroupScheme (Spec (CommRingCat.of R))) :
    (CommGroupScheme.baseChange resExt).obj
        ((CommGroupScheme.baseChange (IntegralModel.residueBaseMap R)).obj C) ≅
      (CommGroupScheme.baseChange (IntegralModel.residueBaseMap A)).obj
        ((CommGroupScheme.baseChange (Spec.algebraMap R A)).obj C) :=
  GroupScheme.Descent.commPullbackComparison (IntegralModel.residueBaseMap R) resExt
      (resExt ≫ IntegralModel.residueBaseMap R) rfl C ≪≫
    (GroupScheme.Descent.commPullbackComparison (Spec.algebraMap R A)
      (IntegralModel.residueBaseMap A) (resExt ≫ IntegralModel.residueBaseMap R)
      (residueExtension_comp_residueBaseMap A).symm C).symm

omit [IsDomain R] [IsDomain A] in
theorem groupHom_specialFibreCommSquareIso_hom
    (C : CommGroupScheme (Spec (CommRingCat.of R))) :
    CommGroupScheme.groupHom (specialFibreCommSquareIso A C).hom =
      (specialFibreSquareIso A C.toGrp).hom :=
  rfl

omit [IsDomain R] [IsDomain A] in
/-- **Characters around the residue square.** The square isomorphism carries
the residue-field base change of the special character of `m` to the special
character of the base change of `m`. -/
theorem congr_specialFibreCommSquareIso_baseChange
    (C : CommGroupScheme (Spec (CommRingCat.of R))) (m : characterLattice C) :
    characterLattice.congr (specialFibreCommSquareIso A C)
        (characterLattice.baseChange resExt _
          (characterLattice.baseChange (IntegralModel.residueBaseMap R) C m)) =
      characterLattice.baseChange (IntegralModel.residueBaseMap A) _
        (characterLattice.baseChange (Spec.algebraMap R A) C m) := by
  rw [characterLattice.congr_apply,
    GroupScheme.Descent.characterBaseChange_tower (IntegralModel.residueBaseMap R) resExt
      (resExt ≫ IntegralModel.residueBaseMap R) rfl,
    GroupScheme.Descent.characterBaseChange_tower (Spec.algebraMap R A)
      (IntegralModel.residueBaseMap A) (resExt ≫ IntegralModel.residueBaseMap R)
      (residueExtension_comp_residueBaseMap A).symm]
  simp only [specialFibreCommSquareIso, Iso.trans_inv, Iso.symm_inv, Category.assoc,
    Iso.inv_hom_id_assoc]

/-- The special character of the base change of an integral character is the
residue-field base change of its special character, transported by the
special-fibre square isomorphism. -/
theorem IntegralTorusData.baseChange_specialCharacterEquiv_apply
    {D' : RelativeComponentModelData R K G}
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
    (T : IntegralTorusData D' S i) (hT : IsSplitTorus T.torus.toGrp)
    (m : characterLattice T.torus) :
    (T.baseChange A L).specialCharacterEquiv (T.isSplitTorus_baseChange A L hT)
        (characterLattice.baseChange (Spec.algebraMap R A) T.torus m) =
      characterLattice.congr (specialFibreCommSquareIso A T.torus)
        (characterLattice.baseChange resExt _ (T.specialCharacterEquiv hT m)) :=
  (congr_specialFibreCommSquareIso_baseChange A T.torus m).symm

/-- The inverse form of `IntegralTorusData.baseChange_specialCharacterEquiv_apply`. -/
theorem IntegralTorusData.baseChange_specialCharacterEquiv_symm_apply
    {D' : RelativeComponentModelData R K G}
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
    (T : IntegralTorusData D' S i) (hT : IsSplitTorus T.torus.toGrp)
    (m : characterLattice T.torus) :
    ((T.baseChange A L).specialCharacterEquiv (T.isSplitTorus_baseChange A L hT)).symm
        (characterLattice.congr (specialFibreCommSquareIso A T.torus)
          (characterLattice.baseChange resExt _ (T.specialCharacterEquiv hT m))) =
      characterLattice.baseChange (Spec.algebraMap R A) T.torus m := by
  rw [← T.baseChange_specialCharacterEquiv_apply A L hT m, AddEquiv.symm_apply_apply]

namespace SpecialFibreQuotientData

variable {D : RelativeComponentModelData R K G}

/-- Change the coefficients of the special-fibre quotient data: the radical
and the quotient change base along the residue field extension. -/
def baseChange (Q : SpecialFibreQuotientData D) :
    SpecialFibreQuotientData (D.baseChange A L) where
  radical := (GroupScheme.baseChange resExt).obj Q.radical
  radicalInclusion := (GroupScheme.baseChange resExt).map Q.radicalInclusion ≫
    (specialFibreSquareIso A D.neutral.group).hom
  quotient := (GroupScheme.baseChange resExt).obj Q.quotient
  projection := (specialFibreSquareIso A D.neutral.group).inv ≫
    (GroupScheme.baseChange resExt).map Q.projection

@[simp] theorem baseChange_quotient (Q : SpecialFibreQuotientData D) :
    (Q.baseChange A L).quotient = (GroupScheme.baseChange resExt).obj Q.quotient := rfl

@[simp] theorem baseChange_projection (Q : SpecialFibreQuotientData D) :
    (Q.baseChange A L).projection = (specialFibreSquareIso A D.neutral.group).inv ≫
      (GroupScheme.baseChange resExt).map Q.projection := rfl

end SpecialFibreQuotientData

namespace RelativeComponentModelHom

variable {D D' : RelativeComponentModelData R K G} (φ : RelativeComponentModelHom D' D)
  (Q : SpecialFibreQuotientData D)
  {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
  (T : IntegralTorusData D' S i)

attribute [local instance] neutralSpecialFibre_affine neutralSpecialFibre_isAffine
  quotient_isAffine

/-- The base-changed map to the reductive quotient is the residue-field base
change of the original map, up to the special-fibre square isomorphism. -/
theorem specialFibreSquareIso_hom_comp_baseChange_quotientMap :
    (specialFibreSquareIso A D'.neutral.group).hom ≫
        ((φ.baseChange A L).neutralSpecialFibreMap ≫ (Q.baseChange A L).projection) =
      (GroupScheme.baseChange resExt).map (φ.neutralSpecialFibreMap ≫ Q.projection) := by
  change (specialFibreSquareIso A D'.neutral.group).hom ≫
      ((GroupScheme.baseChange (IntegralModel.residueBaseMap A)).map
          ((GroupScheme.baseChange (Spec.algebraMap R A)).map φ.neutral.hom) ≫
        (specialFibreSquareIso A D.neutral.group).inv ≫
          (GroupScheme.baseChange resExt).map Q.projection) =
    (GroupScheme.baseChange resExt).map
      ((GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map φ.neutral.hom ≫
        Q.projection)
  rw [← specialFibreSquareIso_naturality_assoc, Iso.hom_inv_id_assoc, Functor.map_comp]

/-- The base-changed torus in the quotient is the residue-field base change of
the original torus in the quotient. -/
theorem groupHom_comp_baseChange_quotientTorusInclusion :
    CommGroupScheme.groupHom (specialFibreCommSquareIso A T.torus).hom ≫
        (φ.baseChange A L).quotientTorusInclusion (Q.baseChange A L) (T.baseChange A L) =
      (GroupScheme.baseChange resExt).map (φ.quotientTorusInclusion Q T) := by
  simp only [quotientTorusInclusion, targetTorusInclusion, Category.assoc]
  rw [Functor.map_comp, ← specialFibreSquareIso_hom_comp_baseChange_quotientMap A L φ Q]
  exact (specialFibreSquareIso_naturality_assoc A T.inclusion _).symm

omit [IsDomain A] in
/-- The residue-field base change of the projection onto the reductive image is
schematically dominant, since a field extension is flat. -/
theorem isSchemeTheoreticallyDominant_baseChange_reductiveImageProjection :
    IsSchemeTheoreticallyDominant ((GroupScheme.baseChange resExt).map
      (SchematicImage.projection (φ.neutralSpecialFibreMap ≫ Q.projection))).hom.hom.left := by
  have : Flat resExt := (fieldExtension_fpqc (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField A)).2.1
  exact isSchemeTheoreticallyDominant_baseChange resExt _

/-- The projection of the base-changed data onto its reductive image, precomposed
with the special-fibre square isomorphism, is schematically dominant. -/
theorem isSchemeTheoreticallyDominant_squareIso_reductiveImageProjection :
    IsSchemeTheoreticallyDominant ((specialFibreSquareIso A D'.neutral.group).hom ≫
      SchematicImage.projection ((φ.baseChange A L).neutralSpecialFibreMap ≫
        (Q.baseChange A L).projection)).hom.hom.left := by
  rw [Grp.comp_hom_hom, Over.comp_left]
  infer_instance

attribute [local instance] isSchemeTheoreticallyDominant_baseChange_reductiveImageProjection
  isSchemeTheoreticallyDominant_squareIso_reductiveImageProjection

/-- The residue-field base change of the reductive image `℘_F(F')` is the
reductive image of the base-changed data. Both are closed subgroups of the
base-changed quotient through which the base-changed quotient map factors
schematically dominantly. -/
def reductiveImageBaseChangeIso :
    (GroupScheme.baseChange resExt).obj (φ.reductiveImage Q) ≅
      (φ.baseChange A L).reductiveImage (Q.baseChange A L) :=
  SchematicImage.isoOfDominantFactorizations
    ((GroupScheme.baseChange resExt).map
      (SchematicImage.projection (φ.neutralSpecialFibreMap ≫ Q.projection)))
    ((specialFibreSquareIso A D'.neutral.group).hom ≫
      SchematicImage.projection ((φ.baseChange A L).neutralSpecialFibreMap ≫
        (Q.baseChange A L).projection))
    ((GroupScheme.baseChange resExt).map
      (SchematicImage.inclusion (φ.neutralSpecialFibreMap ≫ Q.projection)))
    (SchematicImage.inclusion ((φ.baseChange A L).neutralSpecialFibreMap ≫
      (Q.baseChange A L).projection))
    (IsClosedSubgroup.baseChange resExt
      (show IsClosedImmersion
        (SchematicImage.inclusion (φ.neutralSpecialFibreMap ≫ Q.projection)).hom.hom.left
        from inferInstance))
    (show IsClosedImmersion (SchematicImage.inclusion
        ((φ.baseChange A L).neutralSpecialFibreMap ≫
          (Q.baseChange A L).projection)).hom.hom.left from inferInstance)
    (by
      rw [← Functor.map_comp, SchematicImage.projection_inclusion, Category.assoc,
        SchematicImage.projection_inclusion,
        specialFibreSquareIso_hom_comp_baseChange_quotientMap])

/-- The comparison of reductive images preserves the inclusions into the
base-changed quotient. -/
theorem reductiveImageBaseChangeIso_hom_comp :
    (φ.reductiveImageBaseChangeIso A L Q).hom ≫
        (φ.baseChange A L).reductiveImageInclusion (Q.baseChange A L) =
      (GroupScheme.baseChange resExt).map (φ.reductiveImageInclusion Q) := by
  unfold reductiveImageBaseChangeIso
  exact SchematicImage.isoOfDominantFactorizations_hom_comp _ _ _ _ _ _ _

/-- The comparison of reductive images carries the base change of the torus
map to the torus map of the base-changed data. -/
theorem baseChange_reductiveImageTorusMap :
    (GroupScheme.baseChange resExt).map (φ.reductiveImageTorusMap Q T) ≫
        (φ.reductiveImageBaseChangeIso A L Q).hom =
      CommGroupScheme.groupHom (specialFibreCommSquareIso A T.torus).hom ≫
        (φ.baseChange A L).reductiveImageTorusMap (Q.baseChange A L) (T.baseChange A L) := by
  have : Mono ((φ.baseChange A L).reductiveImageInclusion (Q.baseChange A L)).hom.hom :=
    inferInstanceAs (Mono (SchematicImage.inclusionOver _))
  apply Grp.hom_ext
  apply (cancel_mono
    ((φ.baseChange A L).reductiveImageInclusion (Q.baseChange A L)).hom.hom).mp
  rw [← Grp.comp_hom_hom, ← Grp.comp_hom_hom, Category.assoc, Category.assoc,
    reductiveImageBaseChangeIso_hom_comp, ← Functor.map_comp,
    reductiveImageTorusMap_comp_inclusion, reductiveImageTorusMap_comp_inclusion,
    groupHom_comp_baseChange_quotientTorusInclusion]

/-- **Descent of the root-form sign formula along a local coefficient
extension.** If the roots of the base-changed special-fibre torus in the
base-changed reductive image are the base-changed quotient roots with
`σ ≥ 0`, then the roots of the original special-fibre torus in the reductive
image are the quotient roots `χ` whose integral character, base changed to
`A`, has `σ ≥ 0`. -/
theorem roots_reductiveImageTorusMap_of_baseChange [LocallyOfFiniteType Q.quotient.X.hom]
    (hT : IsSplitTorus T.torus.toGrp)
    (σ : characterLattice ((CommGroupScheme.baseChange (Spec.algebraMap R A)).obj T.torus) → ℝ)
    (h : roots ((φ.baseChange A L).reductiveImageTorusMap (Q.baseChange A L)
          (T.baseChange A L)) =
      {χ | χ ∈ roots ((φ.baseChange A L).quotientTorusInclusion (Q.baseChange A L)
          (T.baseChange A L)) ∧
        0 ≤ σ (((T.baseChange A L).specialCharacterEquiv
          (T.isSplitTorus_baseChange A L hT)).symm χ)}) :
    roots (φ.reductiveImageTorusMap Q T) =
      {χ | χ ∈ roots (φ.quotientTorusInclusion Q T) ∧
        0 ≤ σ (characterLattice.baseChange (Spec.algebraMap R A) T.torus
          ((T.specialCharacterEquiv hT).symm χ))} := by
  refine roots_eq_nonneg_of_residueBaseChange (A := A)
    (hT.baseChange (IntegralModel.residueBaseMap R)) _ _ _ _
    (specialFibreCommSquareIso A T.torus) (φ.reductiveImageBaseChangeIso A L Q) (Iso.refl _)
    (φ.baseChange_reductiveImageTorusMap A L Q T) ?_
    (fun χ => σ (characterLattice.baseChange (Spec.algebraMap R A) T.torus
      ((T.specialCharacterEquiv hT).symm χ)))
    (fun χ => σ (((T.baseChange A L).specialCharacterEquiv
      (T.isSplitTorus_baseChange A L hT)).symm χ)) ?_ h
  · rw [Iso.refl_hom, Category.comp_id]
    exact (φ.groupHom_comp_baseChange_quotientTorusInclusion A L Q T).symm
  · intro χ
    obtain ⟨m, rfl⟩ := (T.specialCharacterEquiv hT).surjective χ
    rw [AddEquiv.symm_apply_apply]
    rw [T.baseChange_specialCharacterEquiv_symm_apply A L hT m]

end RelativeComponentModelHom

end Residue

end Coefficients

end Langlands.BruhatTits.IntegralModels
