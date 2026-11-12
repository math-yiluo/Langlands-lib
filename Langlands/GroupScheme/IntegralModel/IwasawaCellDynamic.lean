import Langlands.GroupScheme.IntegralModel.IwasawaCellReduction
import Langlands.GroupScheme.IntegralModel.DynamicParabolic
import Langlands.GroupScheme.IntegralModel.LocalReductivity
import Langlands.Global.IntegralIwasawaFamilyReduction
import Langlands.GroupScheme.Dynamic.OppositeBaseChange
import Langlands.GroupScheme.Dynamic.SchemeDecomposition
import Langlands.GroupScheme.Reductive.SteinbergBigCellGeometry

/-! # Opposite Iwasawa cell data from a cocharacter of the integral model -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped ValuativeRel CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme.IntegralModel

open Langlands.AlgebraicGeometry.PointTopology

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  (M : IntegralModel ↥𝒪[F] F G)

/-- The generic cocharacter of a cocharacter of the integral model, through the supplied
generic isomorphism. -/
def genericCocharacter (χ : (Gm (Spec (CommRingCat.of ↥𝒪[F]))).toGrp ⟶ M.group) :
    (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G :=
  Dynamic.baseChangeCocharacter (Spec.algebraMap ↥𝒪[F] F) χ ≫ M.genericIso.hom

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The generic cocharacter of the opposite cocharacter is the opposite generic cocharacter. -/
theorem genericCocharacter_opposite
    (χ : (Gm (Spec (CommRingCat.of ↥𝒪[F]))).toGrp ⟶ M.group) :
    M.genericCocharacter (Dynamic.oppositeCocharacter χ) =
      Dynamic.oppositeCocharacter (M.genericCocharacter χ) := by
  unfold genericCocharacter Dynamic.oppositeCocharacter
  rw [Dynamic.baseChangeCocharacter_powerHom, Category.assoc]

/-- The rational points of `G` in a subgroup functor. -/
abbrev subgroupFunctorPoints (P : SubgroupFunctor G) : Subgroup (rationalPoints G) :=
  P.carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))

section Iwasawa

variable (hG : IsConnectedReductive G)
  (hspecial : IsConnectedReductive
    ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group))

include hG hspecial in
/-- Every field-valued pullback of the model is connected reductive. -/
theorem fieldReductive_localField (k : Type u) [Field k] [Algebra ↥𝒪[F] k] :
    IsConnectedReductive ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] k)).obj M.group) :=
  fieldReductive_of_residueReductive M.group Set.univ
    (fun t _ => (M.isReductive_of_reductive_localField hG hspecial).isConnectedReductive_residueFiber t)
    (Spec.algebraMap ↥𝒪[F] k) (Set.mem_univ _)

include hG hspecial in
/-- The Iwasawa covering for a closed subgroup presented as the generic dynamic parabolic of
a cocharacter of the integral model. -/
theorem range_mul_integralPoints_eq_univ_of_cocharacter
    (χ : (Gm (Spec (CommRingCat.of ↥𝒪[F]))).toGrp ⟶ M.group)
    {P : GroupScheme (Spec (CommRingCat.of F))} (p : P ⟶ G) (hp : IsClosedSubgroup p)
    (hχ : SubgroupFunctor.range (p ≫ M.genericIso.inv) =
      Dynamic.parabolic (Dynamic.baseChangeCocharacter (Spec.algebraMap ↥𝒪[F] F) χ)) :
    Set.range (rationalPoints.map p) * (M.integralPoints : Set (rationalPoints G)) =
      Set.univ := by
  have : Smooth M.group.X.hom := M.isSmooth_of_reductive_localField hG hspecial
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  exact (DynamicParabolic.modelData M χ p hp hχ parabolicDynamic
    (M.isReductive_of_reductive_localField hG hspecial)
    (fun k _ _ => M.fieldReductive_localField hG hspecial k)).range_mul_integralPoints_eq_univ
    Langlands.Global.IntegralIwasawaFamily.relativeParabolicQuotient

end Iwasawa

section Construction

variable [IsAffine G.X.left]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The chosen generic dynamic parabolic of an integral cocharacter is presented by the
base-changed cocharacter. -/
theorem range_parabolicHom_genericCocharacter
    (χ : (Gm (Spec (CommRingCat.of ↥𝒪[F]))).toGrp ⟶ M.group) :
    SubgroupFunctor.range
        (Dynamic.Affine.parabolicHom (M.genericCocharacter χ) ≫ M.genericIso.inv) =
      Dynamic.parabolic (Dynamic.baseChangeCocharacter (Spec.algebraMap ↥𝒪[F] F) χ) :=
  ((Dynamic.Affine.isRepresentedBy_parabolicHom (M.genericCocharacter χ)).comp_iso
    M.genericIso.symm).2.trans (Dynamic.parabolic_eq_comap_of_iso _ M.genericIso).symm

private instance cellAffineHom : IsAffineHom G.X.hom := isAffineHom_of_isAffine _

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem isAffineHom_of_closed {H : GroupScheme (Spec (CommRingCat.of F))}
    (i : H ⟶ G) (hi : IsClosedSubgroup i) : IsAffineHom H.X.hom := by
  have : IsClosedImmersion i.hom.hom.left := hi
  rw [← i.hom.hom.w]
  infer_instance

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The chosen centralizer also represents the centralizer of the opposite cocharacter. -/
theorem isRepresentedBy_centralizerHom_opposite
    (χ : (Gm (Spec (CommRingCat.of ↥𝒪[F]))).toGrp ⟶ M.group) :
    (Dynamic.centralizer (Dynamic.oppositeCocharacter (M.genericCocharacter χ))).IsRepresentedBy
      (Dynamic.Affine.centralizerHom (M.genericCocharacter χ)) := by
  rw [Dynamic.centralizer_oppositeCocharacter]
  exact Dynamic.Affine.isRepresentedBy_centralizerHom _

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A rational point of a represented dynamic parabolic with trivial limit lies in the dynamic
unipotent subgroup. -/
private theorem mem_unipotent_of_limitGroupHom_eq_one
    {χF : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
    {P Z : GroupScheme (Spec (CommRingCat.of F))} {iP : P ⟶ G} {iZ : Z ⟶ G}
    (hP : (Dynamic.parabolic χF).IsRepresentedBy iP)
    (hZ : (Dynamic.centralizer χF).IsRepresentedBy iZ) (w : rationalPoints P)
    (hw : rationalPoints.map (Dynamic.limitGroupHom hP hZ) w = 1) :
    rationalPoints.map iP w ∈ subgroupFunctorPoints (Dynamic.unipotent χF) := by
  have h := Dynamic.limitGroupHom_comp hP hZ w
  have h1 : (w ≫ (Dynamic.limitGroupHom hP hZ).hom.hom) ≫ iZ.hom.hom = 1 := by
    change rationalPoints.map (Dynamic.limitGroupHom hP hZ) w ≫ iZ.hom.hom = 1
    rw [hw]
    exact MonObj.one_comp _
  rw [h1] at h
  have h2 := (Dynamic.limit_eq_one_iff χF (hP.pointsEquiv _ w)).mp h.symm
  rwa [SubgroupFunctor.IsRepresentedBy.pointsEquiv_apply_coe] at h2

variable (χ : (Gm (Spec (CommRingCat.of ↥𝒪[F]))).toGrp ⟶ M.group)

/-- The chosen generic dynamic parabolic `P_G(λ)` of the generic cocharacter `λ` of `χ`. -/
def cellParabolic : GroupScheme (Spec (CommRingCat.of F)) :=
  Dynamic.Affine.parabolicScheme (M.genericCocharacter χ)

/-- The chosen generic dynamic parabolic `P_G(λ⁻¹)` of the opposite cocharacter. -/
def cellOppositeParabolic : GroupScheme (Spec (CommRingCat.of F)) :=
  Dynamic.Affine.parabolicScheme (Dynamic.oppositeCocharacter (M.genericCocharacter χ))

/-- The chosen generic dynamic centralizer `Z_G(λ)`. -/
def cellLevi : GroupScheme (Spec (CommRingCat.of F)) :=
  Dynamic.Affine.centralizerScheme (M.genericCocharacter χ)

/-- The inclusion of `P_G(λ)`. -/
def cellParabolicHom : M.cellParabolic χ ⟶ G :=
  Dynamic.Affine.parabolicHom (M.genericCocharacter χ)

/-- The inclusion of `P_G(λ⁻¹)`. -/
def cellOppositeParabolicHom : M.cellOppositeParabolic χ ⟶ G :=
  Dynamic.Affine.parabolicHom (Dynamic.oppositeCocharacter (M.genericCocharacter χ))

/-- The inclusion of `Z_G(λ)`. -/
def cellLeviHom : M.cellLevi χ ⟶ G :=
  Dynamic.Affine.centralizerHom (M.genericCocharacter χ)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- `P_G(λ)` is represented by its chosen inclusion. -/
theorem isRepresentedBy_cellParabolicHom :
    (Dynamic.parabolic (M.genericCocharacter χ)).IsRepresentedBy (M.cellParabolicHom χ) :=
  Dynamic.Affine.isRepresentedBy_parabolicHom _

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- `P_G(λ⁻¹)` is represented by its chosen inclusion. -/
theorem isRepresentedBy_cellOppositeParabolicHom :
    (Dynamic.parabolic (Dynamic.oppositeCocharacter (M.genericCocharacter χ))).IsRepresentedBy
      (M.cellOppositeParabolicHom χ) :=
  Dynamic.Affine.isRepresentedBy_parabolicHom _

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- `Z_G(λ)` is represented by its chosen inclusion. -/
theorem isRepresentedBy_cellLeviHom :
    (Dynamic.centralizer (M.genericCocharacter χ)).IsRepresentedBy (M.cellLeviHom χ) :=
  Dynamic.Affine.isRepresentedBy_centralizerHom _

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- `Z_G(λ⁻¹) = Z_G(λ)` is represented by the same inclusion. -/
theorem isRepresentedBy_cellLeviHom_opposite :
    (Dynamic.centralizer (Dynamic.oppositeCocharacter (M.genericCocharacter χ))).IsRepresentedBy
      (M.cellLeviHom χ) :=
  M.isRepresentedBy_centralizerHom_opposite χ

/-- The inclusion `Z_G(λ) ⟶ P_G(λ)`. -/
def cellLeviSection : M.cellLevi χ ⟶ M.cellParabolic χ :=
  Dynamic.centralizerToParabolic (M.isRepresentedBy_cellParabolicHom χ)
    (M.isRepresentedBy_cellLeviHom χ)

/-- The inclusion `Z_G(λ) ⟶ P_G(λ⁻¹)`. -/
def cellOppositeLeviSection : M.cellLevi χ ⟶ M.cellOppositeParabolic χ :=
  Dynamic.centralizerToParabolic (M.isRepresentedBy_cellOppositeParabolicHom χ)
    (M.isRepresentedBy_cellLeviHom_opposite χ)

/-- The limit homomorphism `P_G(λ) ⟶ Z_G(λ)`. -/
def cellLeviProj : M.cellParabolic χ ⟶ M.cellLevi χ :=
  Dynamic.limitGroupHom (M.isRepresentedBy_cellParabolicHom χ) (M.isRepresentedBy_cellLeviHom χ)

/-- The limit homomorphism `P_G(λ⁻¹) ⟶ Z_G(λ)`. -/
def cellOppositeLeviProj : M.cellOppositeParabolic χ ⟶ M.cellLevi χ :=
  Dynamic.limitGroupHom (M.isRepresentedBy_cellOppositeParabolicHom χ)
    (M.isRepresentedBy_cellLeviHom_opposite χ)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Unfolding equation for `cellLeviProj`. -/
theorem cellLeviProj_eq : M.cellLeviProj χ =
    Dynamic.limitGroupHom (M.isRepresentedBy_cellParabolicHom χ)
      (M.isRepresentedBy_cellLeviHom χ) := rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Unfolding equation for `cellOppositeLeviProj`. -/
theorem cellOppositeLeviProj_eq : M.cellOppositeLeviProj χ =
    Dynamic.limitGroupHom (M.isRepresentedBy_cellOppositeParabolicHom χ)
      (M.isRepresentedBy_cellLeviHom_opposite χ) := rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The inclusion of `P_G(λ)` is a closed immersion. -/
theorem cellParabolicHom_closed : IsClosedSubgroup (M.cellParabolicHom χ) :=
  Dynamic.Affine.isClosedSubgroup_parabolicHom _

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The inclusion of `P_G(λ⁻¹)` is a closed immersion. -/
theorem cellOppositeParabolicHom_closed : IsClosedSubgroup (M.cellOppositeParabolicHom χ) :=
  Dynamic.Affine.isClosedSubgroup_parabolicHom _

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The inclusion of `Z_G(λ)` is a closed immersion. -/
theorem cellLeviHom_closed : IsClosedSubgroup (M.cellLeviHom χ) :=
  Dynamic.Affine.isClosedSubgroup_centralizerHom _

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The section of `P_G(λ) ⟶ Z_G(λ)` is compatible with the inclusions into `G`. -/
theorem cellLeviSection_comp : M.cellLeviSection χ ≫ M.cellParabolicHom χ = M.cellLeviHom χ :=
  Dynamic.centralizerToParabolic_comp _ _

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The section of `P_G(λ⁻¹) ⟶ Z_G(λ)` is compatible with the inclusions into `G`. -/
theorem cellOppositeLeviSection_comp :
    M.cellOppositeLeviSection χ ≫ M.cellOppositeParabolicHom χ = M.cellLeviHom χ :=
  Dynamic.centralizerToParabolic_comp _ _

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The inclusion `Z_G(λ) ⟶ P_G(λ)` is a section of the limit homomorphism. -/
theorem cellLeviSection_proj : M.cellLeviSection χ ≫ M.cellLeviProj χ = 𝟙 (M.cellLevi χ) :=
  Dynamic.centralizerToParabolic_comp_limitGroupHom _ _

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The inclusion `Z_G(λ) ⟶ P_G(λ⁻¹)` is a section of the limit homomorphism. -/
theorem cellOppositeLeviSection_proj :
    M.cellOppositeLeviSection χ ≫ M.cellOppositeLeviProj χ = 𝟙 (M.cellLevi χ) :=
  Dynamic.centralizerToParabolic_comp_limitGroupHom _ _

variable (hG : IsConnectedReductive G)
  (hspecial : IsConnectedReductive
    ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group))

include hG hspecial in
/-- The Iwasawa covering for `P_G(λ)`. -/
theorem cellIwasawa :
    Set.range (rationalPoints.map (M.cellParabolicHom χ)) *
      (M.integralPoints : Set (rationalPoints G)) = Set.univ :=
  M.range_mul_integralPoints_eq_univ_of_cocharacter hG hspecial χ _
    (Dynamic.Affine.isClosedSubgroup_parabolicHom _) (M.range_parabolicHom_genericCocharacter χ)

include hG hspecial in
/-- The Iwasawa covering for `P_G(λ⁻¹)`. -/
theorem cellOppositeIwasawa :
    Set.range (rationalPoints.map (M.cellOppositeParabolicHom χ)) *
      (M.integralPoints : Set (rationalPoints G)) = Set.univ := by
  have h := M.range_parabolicHom_genericCocharacter (Dynamic.oppositeCocharacter χ)
  rw [genericCocharacter_opposite] at h
  exact M.range_mul_integralPoints_eq_univ_of_cocharacter hG hspecial
    (Dynamic.oppositeCocharacter χ) _ (Dynamic.Affine.isClosedSubgroup_parabolicHom _) h

omit [IsNonarchimedeanLocalField F] in
/-- Maximality on the generic centralizer, transported to the rational points of `Z_G(λ)`. -/
theorem cellLeviMaximal
    (hlevi :
      letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      ∀ C : Subgroup (rationalPoints G), IsCompact (C : Set (rationalPoints G)) →
        C ≤ subgroupFunctorPoints (Dynamic.centralizer (M.genericCocharacter χ)) →
        M.integralPoints ⊓ subgroupFunctorPoints (Dynamic.centralizer (M.genericCocharacter χ)) ≤
          C →
        C ≤ M.integralPoints)
    [IsAffine (M.cellLevi χ).X.left] :
    letI : TopologicalSpace (rationalPoints (M.cellLevi χ)) :=
      rationalPointTopology F (M.cellLevi χ).X
    ∀ C : Subgroup (rationalPoints (M.cellLevi χ)),
      IsCompact (C : Set (rationalPoints (M.cellLevi χ))) →
      M.integralPoints.comap (rationalPoints.map (M.cellLeviHom χ)) ≤ C →
      C ≤ M.integralPoints.comap (rationalPoints.map (M.cellLeviHom χ)) := by
  intro C hC hle
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : TopologicalSpace (rationalPoints (M.cellLevi χ)) :=
    rationalPointTopology F (M.cellLevi χ).X
  have hZ := M.isRepresentedBy_cellLeviHom χ
  have hcont : Continuous (rationalPoints.map (M.cellLeviHom χ)) :=
    continuous_rationalPointMap F (M.cellLeviHom χ).hom.hom
  have hmap := hlevi (C.map (rationalPoints.map (M.cellLeviHom χ)))
    (by simpa only [Subgroup.coe_map] using hC.image hcont)
    (by
      rintro _ ⟨z, -, rfl⟩
      have := (hZ.pointsEquiv _ z).2
      rwa [SubgroupFunctor.IsRepresentedBy.pointsEquiv_apply_coe] at this)
    (by
      rintro g ⟨hgK, hgZ⟩
      let z := (hZ.pointsEquiv _).symm ⟨g, hgZ⟩
      have hz : rationalPoints.map (M.cellLeviHom χ) z = g := by
        have := congrArg Subtype.val ((hZ.pointsEquiv _).apply_symm_apply ⟨g, hgZ⟩)
        rwa [SubgroupFunctor.IsRepresentedBy.pointsEquiv_apply_coe] at this
      refine ⟨z, hle ?_, hz⟩
      show rationalPoints.map (M.cellLeviHom χ) z ∈ M.integralPoints
      rw [hz]
      exact hgK)
  intro z hz
  exact hmap ⟨z, hz, rfl⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Cell integrality for the generic dynamic unipotent subgroups, read on the kernels of the
two limit homomorphisms. -/
theorem cellIntegral
    (hcell : ∀ v w : rationalPoints G,
      v ∈ subgroupFunctorPoints
        (Dynamic.unipotent (Dynamic.oppositeCocharacter (M.genericCocharacter χ))) →
      w ∈ subgroupFunctorPoints (Dynamic.unipotent (M.genericCocharacter χ)) →
      v * w ∈ M.integralPoints → w ∈ M.integralPoints)
    (v : rationalPoints (M.cellOppositeParabolic χ)) (w : rationalPoints (M.cellParabolic χ))
    (hv : rationalPoints.map (M.cellOppositeLeviProj χ) v = 1)
    (hw : rationalPoints.map (M.cellLeviProj χ) w = 1)
    (hvw : rationalPoints.map (M.cellOppositeParabolicHom χ) v *
      rationalPoints.map (M.cellParabolicHom χ) w ∈ M.integralPoints) :
    rationalPoints.map (M.cellParabolicHom χ) w ∈ M.integralPoints := by
  rw [cellOppositeLeviProj_eq] at hv
  rw [cellLeviProj_eq] at hw
  exact hcell _ _
    (mem_unipotent_of_limitGroupHom_eq_one (M.isRepresentedBy_cellOppositeParabolicHom χ)
      (M.isRepresentedBy_cellLeviHom_opposite χ) v hv)
    (mem_unipotent_of_limitGroupHom_eq_one (M.isRepresentedBy_cellParabolicHom χ)
      (M.isRepresentedBy_cellLeviHom χ) w hw) hvw

/-- Opposite Iwasawa cell data from an integral cocharacter, its generic dynamic parabolics
and centralizer, given maximality on the centralizer and cell integrality. -/
def IwasawaCellData.ofCocharacter
    (hlevi :
      letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      ∀ C : Subgroup (rationalPoints G), IsCompact (C : Set (rationalPoints G)) →
        C ≤ subgroupFunctorPoints (Dynamic.centralizer (M.genericCocharacter χ)) →
        M.integralPoints ⊓ subgroupFunctorPoints (Dynamic.centralizer (M.genericCocharacter χ)) ≤
          C →
        C ≤ M.integralPoints)
    (hcell : ∀ v w : rationalPoints G,
      v ∈ subgroupFunctorPoints
        (Dynamic.unipotent (Dynamic.oppositeCocharacter (M.genericCocharacter χ))) →
      w ∈ subgroupFunctorPoints (Dynamic.unipotent (M.genericCocharacter χ)) →
      v * w ∈ M.integralPoints → w ∈ M.integralPoints) :
    IwasawaCellData M where
  parabolic := M.cellParabolic χ
  oppositeParabolic := M.cellOppositeParabolic χ
  levi := M.cellLevi χ
  parabolic_affine := isAffineHom_of_closed _ (M.cellParabolicHom_closed χ)
  oppositeParabolic_affine := isAffineHom_of_closed _ (M.cellOppositeParabolicHom_closed χ)
  levi_affine := isAffineHom_of_closed _ (M.cellLeviHom_closed χ)
  parabolicHom := M.cellParabolicHom χ
  oppositeParabolicHom := M.cellOppositeParabolicHom χ
  parabolicHom_closed := M.cellParabolicHom_closed χ
  oppositeParabolicHom_closed := M.cellOppositeParabolicHom_closed χ
  leviHom := M.cellLeviHom χ
  leviSection := M.cellLeviSection χ
  oppositeLeviSection := M.cellOppositeLeviSection χ
  leviProj := M.cellLeviProj χ
  oppositeLeviProj := M.cellOppositeLeviProj χ
  leviSection_comp := M.cellLeviSection_comp χ
  oppositeLeviSection_comp := M.cellOppositeLeviSection_comp χ
  leviSection_proj := M.cellLeviSection_proj χ
  oppositeLeviSection_proj := M.cellOppositeLeviSection_proj χ
  iwasawa := M.cellIwasawa χ hG hspecial
  oppositeIwasawa := M.cellOppositeIwasawa χ hG hspecial
  levi_maximal := by
    have : IsAffineHom (M.cellLevi χ).X.hom := isAffineHom_of_closed _ (M.cellLeviHom_closed χ)
    have : IsAffine (M.cellLevi χ).X.left := isAffine_of_isAffineHom (M.cellLevi χ).X.hom
    exact M.cellLeviMaximal χ hlevi
  cell_integral := M.cellIntegral χ hcell

end Construction

/-- An internal construction target: opposite-cell integrality for every cocharacter of every
supplied model with connected reductive full special fibre. If `v` lies in the generic
dynamic unipotent subgroup of the opposite cocharacter, `w` in that of the cocharacter, and
`v * w` is integral, then `w` is integral. -/
def DynamicCellIntegralityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (_hG : IsConnectedReductive G)
    (M : IntegralModel ↥𝒪[F] F G),
    IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group) →
    ∀ (χ : (Gm (Spec (CommRingCat.of ↥𝒪[F]))).toGrp ⟶ M.group) (v w : rationalPoints G),
      v ∈ subgroupFunctorPoints
        (Dynamic.unipotent (Dynamic.oppositeCocharacter (M.genericCocharacter χ))) →
      w ∈ subgroupFunctorPoints (Dynamic.unipotent (M.genericCocharacter χ)) →
      v * w ∈ M.integralPoints → w ∈ M.integralPoints

/-- An internal construction target: every supplied model with connected reductive full
special fibre has a cocharacter whose generic centralizer satisfies maximality: a compact
subgroup of `G(F)` inside the centralizer's rational points and containing its integral
points consists of integral points. -/
def LeviMaximalCocharacterStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (M : IntegralModel ↥𝒪[F] F G),
    IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group) →
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∃ χ : (Gm (Spec (CommRingCat.of ↥𝒪[F]))).toGrp ⟶ M.group,
      ∀ C : Subgroup (rationalPoints G), IsCompact (C : Set (rationalPoints G)) →
        C ≤ subgroupFunctorPoints (Dynamic.centralizer (M.genericCocharacter χ)) →
        M.integralPoints ⊓ subgroupFunctorPoints (Dynamic.centralizer (M.genericCocharacter χ)) ≤
          C →
        C ≤ M.integralPoints

/-- The two dynamic targets construct opposite Iwasawa cell data for every supplied model. -/
theorem iwasawaCellDataStatement_of_dynamic
    (hcell : DynamicCellIntegralityStatement.{u})
    (hlevi : LeviMaximalCocharacterStatement.{u}) :
    IwasawaCellDataStatement.{u} := by
  intro F _ _ _ _ G hG M hspecial
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨χ, hχ⟩ := hlevi F G hG M hspecial
  exact ⟨IwasawaCellData.ofCocharacter M χ hG hspecial hχ (hcell F G hG M hspecial χ)⟩

/-- The two dynamic targets prove the exact published maximal-compactness statement. -/
theorem maximalCompactStatement_of_dynamic
    (hcell : DynamicCellIntegralityStatement.{u})
    (hlevi : LeviMaximalCocharacterStatement.{u}) :
    MaximalCompactStatement.{u} :=
  maximalCompactStatement_of_iwasawaCellData (iwasawaCellDataStatement_of_dynamic hcell hlevi)

end Langlands.GroupScheme.IntegralModel
