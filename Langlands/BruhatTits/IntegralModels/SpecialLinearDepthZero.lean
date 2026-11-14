import Langlands.BruhatTits.IntegralModels.GeneralLinearDepthZero
import Langlands.GroupScheme.Reductive.SpecialLinear
import Langlands.GroupScheme.SpecialLinearRootGroups

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Depth-zero data for `SL_n` over a local field

The special linear group scheme `SL_n` is defined over every commutative ring,
is smooth for nonempty `n`, and commutes with base change. Over a domain `R`
with fraction field `K` it is therefore an integral model of `SL_{n,K}`, the
standard model.

For a nonarchimedean local field `F`, both fibres of the standard model over
`𝒪[F]` are connected reductive, so it gives actual relative-component model
data with full and neutral model equal, and the identity quotient of its
special fibre is a reductive quotient. This is the hyperspecial `SL_n`
regression example for the depth-zero layer: `G^0(𝒪) = SL_n(𝒪[F])`,
`G(F)^{0+}` is the kernel of reduction `SL_n(𝒪[F]) → SL_n(𝓀[F])`, and the
index is `|SL_n(𝓀[F])|`, which times `q - 1` is `|GL_n(𝓀[F])|`. Both subgroups
are cut out of `SL_n(F)` by the corresponding subgroups of `GL_n`; in rank
`n + 1` these are the Library's concrete `Conductor.integralSubgroup 𝒪[F] n` and
`Conductor.principalLevelSubgroup F n 1`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel Matrix

namespace Langlands.GroupScheme.SpecialLinear

section Matrices

variable {n : Type} [Fintype n] [DecidableEq n]

/-- An invertible matrix whose image under an injective ring homomorphism has
determinant one has determinant one. -/
theorem det_eq_one_of_map {A B : Type*} [CommRing A] [CommRing B] {f : A →+* B}
    (hf : Function.Injective f) {M : Matrix n n A} (hM : (M.map f).det = 1) : M.det = 1 := by
  apply hf
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hM, map_one]

/-- Over a finite field, `|SL_n| · (q - 1) = |GL_n|` for nonempty `n`. -/
theorem card_specialLinearGroup_mul {k : Type*} [Field k] [Finite k] [Nonempty n] :
    Nat.card (Matrix.SpecialLinearGroup n k) * (Nat.card k - 1) = Nat.card (GL n k) := by
  have h1 : Nat.card (Matrix.SpecialLinearGroup n k) =
      Nat.card (Matrix.GeneralLinearGroup.det : GL n k →* kˣ).ker :=
    Nat.card_congr Matrix.SpecialLinearGroup.toGLKerEquiv.toEquiv
  have h2 : (Matrix.GeneralLinearGroup.det : GL n k →* kˣ).ker.index = Nat.card k - 1 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr Matrix.GeneralLinearGroup.det_surjective,
      Subgroup.card_top, Nat.card_units]
  rw [h1, ← h2, Subgroup.card_mul_index]

end Matrices

section BaseChange

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Changing the base of a section of `SL_n` along `Spec φ` and reading the
matrix over `B` applies `φ` to every entry of the matrix over `A`. -/
theorem matrixRingEquiv_pointsEquiv_baseChangeSectionHom {A B : Type u} [CommRing A]
    [CommRing B] (φ : A →+* B)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ (groupScheme n (CommRingCat.of A)).X) :
    Root.matrixRingEquiv (Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv
        (pointsEquiv n (CommRingCat.of A)
          ((Over.map (Spec.map (CommRingCat.ofHom φ))).obj (Over.mk (𝟙 _)))
          (baseChangePointsEquiv (Spec.map (CommRingCat.ofHom φ))
            (groupScheme n (CommRingCat.of A)) (Over.mk (𝟙 _))
            (baseChangeSectionHom (Spec.map (CommRingCat.ofHom φ))
              (groupScheme n (CommRingCat.of A)) x))) =
      Matrix.SpecialLinearGroup.map φ (Root.rationalMatrixEquiv A x) := by
  rw [baseChangePointsEquiv_baseChangeSectionHom, pointsEquiv_naturality]
  ext i j
  change (Scheme.ΓSpecIso (CommRingCat.of B)).hom
      ((Spec.map (CommRingCat.ofHom φ)).appTop
        ((pointsEquiv n (CommRingCat.of A) (Over.mk (𝟙 _)) x) i j)) =
    φ ((Scheme.ΓSpecIso (CommRingCat.of A)).hom
        ((pointsEquiv n (CommRingCat.of A) (Over.mk (𝟙 _)) x) i j))
  change ((Spec.map (CommRingCat.ofHom φ)).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom) _ =
    _
  rw [Scheme.ΓSpecIso_naturality]
  rfl

end BaseChange

section StandardModel

variable (R K : Type u) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (n : Type) [Fintype n] [DecidableEq n] [Nonempty n]

/-- The special linear group over the integral base, with the Library's
base-change identification over the fraction field. Flatness and local finite
type come from the published smoothness of the special linear group scheme. -/
def standardIntegralModel : IntegralModel R K (groupScheme n (CommRingCat.of K)) where
  group := groupScheme n (CommRingCat.of R)
  affine := isAffineHom_groupScheme (n := n) (R := CommRingCat.of R)
  flat :=
    haveI := smooth_groupScheme n (Classical.arbitrary n) (CommRingCat.of R)
    inferInstance
  finiteType :=
    haveI := smooth_groupScheme n (Classical.arbitrary n) (CommRingCat.of R)
    inferInstance
  genericIso := baseChangeModelIso n (Spec.algebraMap R K)

/-- The standard model is smooth. -/
theorem standardIntegralModel_isSmooth : (standardIntegralModel R K n).IsSmooth :=
  smooth_groupScheme n (Classical.arbitrary n) (CommRingCat.of R)

/-- The integral sections of the standard model are the determinant-one
matrices over `R`. -/
def standardSectionsEquiv :
    (standardIntegralModel R K n).integralSections ≃* Matrix.SpecialLinearGroup n R :=
  Root.rationalMatrixEquiv R

/-- The generic identification of the standard model sends an integral
section to the same matrix, with entries mapped into `K`. -/
theorem standardIntegralModel_integralPointMap
    (x : (standardIntegralModel R K n).integralSections) :
    Root.rationalMatrixEquiv K ((standardIntegralModel R K n).integralPointMap x) =
      Matrix.SpecialLinearGroup.map (algebraMap R K) (standardSectionsEquiv R K n x) := by
  change Root.matrixRingEquiv (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
      (pointsEquiv n (CommRingCat.of K) (Over.mk (𝟙 _))
        (baseChangeSectionHom (Spec.algebraMap R K) (groupScheme n (CommRingCat.of R)) x ≫
          (baseChangeModelIso n (Spec.algebraMap R K)).hom.hom.hom)) = _
  rw [pointsEquiv_baseChangeModelIso_hom]
  exact matrixRingEquiv_pointsEquiv_baseChangeSectionHom (algebraMap R K) x

/-- The integral points of the standard model are the points whose matrix
is the image of a determinant-one matrix over `R`. -/
theorem mem_standardIntegralModel_integralPoints
    (g : rationalPoints (groupScheme n (CommRingCat.of K))) :
    g ∈ (standardIntegralModel R K n).integralPoints ↔
      ∃ u : Matrix.SpecialLinearGroup n R, Root.rationalMatrixEquiv K g =
        Matrix.SpecialLinearGroup.map (algebraMap R K) u := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨standardSectionsEquiv R K n x, standardIntegralModel_integralPointMap R K n x⟩
  · rintro ⟨u, hg⟩
    refine ⟨(standardSectionsEquiv R K n).symm u, ?_⟩
    apply (Root.rationalMatrixEquiv (n := n) K).injective
    rw [standardIntegralModel_integralPointMap, MulEquiv.apply_symm_apply, hg]

end StandardModel

end Langlands.GroupScheme.SpecialLinear

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (n : Type) [Fintype n] [DecidableEq n] [Nonempty n]

/-- The special fibre of the standard model of `SL_n` is connected
reductive. -/
theorem isConnectedReductive_specialLinearSpecialFibre :
    IsConnectedReductive
      ((baseChange (Spec.algebraMap 𝒪[F] 𝓀[F])).obj
        (SpecialLinear.standardIntegralModel 𝒪[F] F n).group) :=
  IsConnectedReductive.of_iso (SpecialLinear.baseChangeModelIso n _)
    (SpecialLinear.isConnectedReductive 𝓀[F] n (Classical.arbitrary n))

/-- The standard model `SL_{n,𝒪[F]}`, as relative-component model data whose
full and neutral models are both this model. Smoothness and connected fibres
come from the published reductive-model criterion. -/
def specialLinearModelData :
    RelativeComponentModelData 𝒪[F] F (SpecialLinear.groupScheme n (CommRingCat.of F)) :=
  (SpecialLinear.standardIntegralModel 𝒪[F] F n).relativeComponentData_of_reductive_localField
    (SpecialLinear.isConnectedReductive F n (Classical.arbitrary n))
    (isConnectedReductive_specialLinearSpecialFibre F n)

/-- The neutral model is the standard model. -/
theorem specialLinearModelData_neutral :
    (specialLinearModelData F n).neutral = SpecialLinear.standardIntegralModel 𝒪[F] F n :=
  rfl

/-- The special-fibre quotient data of the standard model: the identity
quotient. -/
def specialLinearQuotientData : SpecialFibreQuotientData (specialLinearModelData F n) :=
  SpecialFibreQuotientData.identityQuotient _

/-- The identity quotient of the standard model is a reductive quotient. -/
theorem specialLinearQuotientData_isReductiveQuotient :
    (specialLinearQuotientData F n).IsReductiveQuotient :=
  SpecialFibreQuotientData.identityQuotient_isReductiveQuotient _
    (isConnectedReductive_specialLinearSpecialFibre F n)

/-- The residue-field points of the special fibre of the standard model are
the determinant-one matrices over the residue field. -/
def specialLinearSpecialFibrePointsEquiv :
    rationalPoints (specialLinearModelData F n).neutral.specialFibre ≃*
      Matrix.SpecialLinearGroup n 𝓀[F] :=
  ((GroupScheme.baseChangePointsEquiv (IntegralModel.residueBaseMap 𝒪[F])
      (SpecialLinear.groupScheme n (CommRingCat.of 𝒪[F])) (Over.mk (𝟙 _))).trans
    (SpecialLinear.pointsEquiv n (CommRingCat.of 𝒪[F]) _)).trans
    (SpecialLinear.Root.matrixRingEquiv
      (Scheme.ΓSpecIso (CommRingCat.of 𝓀[F])).commRingCatIsoToRingEquiv)

/-- Under the matrix identifications, reduction of integral sections is the
residue map on every entry. -/
theorem specialLinearSpecialFibrePointsEquiv_reduction
    (x : (specialLinearModelData F n).neutral.integralSections) :
    specialLinearSpecialFibrePointsEquiv F n ((specialLinearModelData F n).neutral.reduction x) =
      Matrix.SpecialLinearGroup.map (IsLocalRing.residue 𝒪[F])
        (SpecialLinear.standardSectionsEquiv 𝒪[F] F n x) :=
  SpecialLinear.matrixRingEquiv_pointsEquiv_baseChangeSectionHom (IsLocalRing.residue 𝒪[F]) x

/-- The index of `G(F)^{0+}` in `G^0(𝒪) = SL_n(𝒪[F])` is the order of
`SL_n(𝓀[F])`. -/
theorem specialLinear_index_positivePoints_subgroupOf :
    ((specialLinearQuotientData F n).positivePoints.subgroupOf
      (specialLinearModelData F n).neutral.integralPoints).index =
        Nat.card (Matrix.SpecialLinearGroup n 𝓀[F]) := by
  obtain ⟨hrad, hQ, -⟩ := specialLinearQuotientData_isReductiveQuotient F n
  rw [SpecialFibreQuotientData.localField_index_positivePoints_subgroupOf _ hrad hQ]
  change Nat.card (rationalPoints (specialLinearModelData F n).neutral.specialFibre) = _
  exact Nat.card_congr (specialLinearSpecialFibrePointsEquiv F n).toEquiv

/-- For `n = Fin N`, the same index times `q - 1` is `∏_{i < N} (q ^ N - q ^ i)`,
where `q` is the cardinality of the residue field. -/
theorem specialLinear_index_positivePoints_subgroupOf_mul (N : ℕ) [NeZero N] :
    ((specialLinearQuotientData F (Fin N)).positivePoints.subgroupOf
      (specialLinearModelData F (Fin N)).neutral.integralPoints).index *
        (Nat.card 𝓀[F] - 1) =
      ∏ i : Fin N, (Nat.card 𝓀[F] ^ N - Nat.card 𝓀[F] ^ (i : ℕ)) := by
  let : Fintype 𝓀[F] := Fintype.ofFinite _
  rw [specialLinear_index_positivePoints_subgroupOf, SpecialLinear.card_specialLinearGroup_mul,
    Matrix.card_GL_field, Nat.card_eq_fintype_card]

/-- `G(F)^{0+}` consists of the points whose matrix is the image of a
determinant-one matrix `u` over `𝒪[F]` with reduction `1`. -/
theorem mem_specialLinear_positivePoints
    (g : rationalPoints (SpecialLinear.groupScheme n (CommRingCat.of F))) :
    g ∈ (specialLinearQuotientData F n).positivePoints ↔
      ∃ u : Matrix.SpecialLinearGroup n 𝒪[F],
        Matrix.SpecialLinearGroup.map (IsLocalRing.residue 𝒪[F]) u = 1 ∧
          SpecialLinear.Root.rationalMatrixEquiv F g =
            Matrix.SpecialLinearGroup.map (algebraMap 𝒪[F] F) u := by
  rw [specialLinearQuotientData, SpecialFibreQuotientData.mem_identityQuotient_positivePoints]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨SpecialLinear.standardSectionsEquiv 𝒪[F] F n x, ?_,
      SpecialLinear.standardIntegralModel_integralPointMap 𝒪[F] F n x⟩
    have h := congrArg (specialLinearSpecialFibrePointsEquiv F n) hx
    rw [specialLinearSpecialFibrePointsEquiv_reduction] at h
    exact h.trans (specialLinearSpecialFibrePointsEquiv F n).map_one
  · rintro ⟨u, hu, hg⟩
    refine ⟨(SpecialLinear.standardSectionsEquiv 𝒪[F] F n).symm u, ?_, ?_⟩
    · apply (specialLinearSpecialFibrePointsEquiv F n).injective
      rw [specialLinearSpecialFibrePointsEquiv_reduction, MulEquiv.apply_symm_apply, hu]
      exact (specialLinearSpecialFibrePointsEquiv F n).map_one.symm
    · apply (SpecialLinear.Root.rationalMatrixEquiv (n := n) F).injective
      change SpecialLinear.Root.rationalMatrixEquiv F
        ((SpecialLinear.standardIntegralModel 𝒪[F] F n).integralPointMap
          ((SpecialLinear.standardSectionsEquiv 𝒪[F] F n).symm u)) = _
      rw [SpecialLinear.standardIntegralModel_integralPointMap, MulEquiv.apply_symm_apply, hg]

/-- `G^0(𝒪)` consists of the points whose matrix is the image of a
determinant-one matrix over `𝒪[F]`. -/
theorem mem_specialLinear_integralPoints
    (g : rationalPoints (SpecialLinear.groupScheme n (CommRingCat.of F))) :
    g ∈ (specialLinearModelData F n).neutral.integralPoints ↔
      ∃ u : Matrix.SpecialLinearGroup n 𝒪[F],
        SpecialLinear.Root.rationalMatrixEquiv F g =
          Matrix.SpecialLinearGroup.map (algebraMap 𝒪[F] F) u :=
  SpecialLinear.mem_standardIntegralModel_integralPoints 𝒪[F] F n g

section Comparison

/-- `G^0(𝒪)` is cut out of `SL_n(F)` by `GL_n(𝒪[F])`. -/
theorem mem_specialLinear_integralPoints_iff_generalLinear
    (g : rationalPoints (SpecialLinear.groupScheme n (CommRingCat.of F))) :
    g ∈ (specialLinearModelData F n).neutral.integralPoints ↔
      ∃ u : GL n 𝒪[F],
        Matrix.SpecialLinearGroup.toGL (SpecialLinear.Root.rationalMatrixEquiv F g) =
          Matrix.GeneralLinearGroup.map (algebraMap 𝒪[F] F) u := by
  rw [mem_specialLinear_integralPoints]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨Matrix.SpecialLinearGroup.toGL u, ?_⟩
    rw [hu]
    exact Units.ext rfl
  · rintro ⟨u, hu⟩
    have hmap : (u : Matrix n n 𝒪[F]).map (algebraMap 𝒪[F] F) =
        ((SpecialLinear.Root.rationalMatrixEquiv F g : Matrix.SpecialLinearGroup n F) :
          Matrix n n F) :=
      (congrArg Units.val hu).symm
    have hdet : (u : Matrix n n 𝒪[F]).det = 1 :=
      SpecialLinear.det_eq_one_of_map (IsFractionRing.injective 𝒪[F] F)
        (hmap ▸ (SpecialLinear.Root.rationalMatrixEquiv F g).2)
    refine ⟨⟨u, hdet⟩, ?_⟩
    ext i j
    exact (congrFun (congrFun hmap i) j).symm

/-- `G(F)^{0+}` is cut out of `SL_n(F)` by the principal congruence subgroup
of level one of `GL_n(𝒪[F])`. -/
theorem mem_specialLinear_positivePoints_iff_generalLinear
    (g : rationalPoints (SpecialLinear.groupScheme n (CommRingCat.of F))) :
    g ∈ (specialLinearQuotientData F n).positivePoints ↔
      ∃ u : GL n 𝒪[F], Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[F]) u = 1 ∧
        Matrix.SpecialLinearGroup.toGL (SpecialLinear.Root.rationalMatrixEquiv F g) =
          Matrix.GeneralLinearGroup.map (algebraMap 𝒪[F] F) u := by
  rw [mem_specialLinear_positivePoints]
  constructor
  · rintro ⟨u, hu, hg⟩
    refine ⟨Matrix.SpecialLinearGroup.toGL u, ?_, ?_⟩
    · apply Units.ext
      exact congrArg (fun v : Matrix.SpecialLinearGroup n 𝓀[F] => (v : Matrix n n 𝓀[F])) hu
    · rw [hg]
      exact Units.ext rfl
  · rintro ⟨u, hu, hg⟩
    have hmap : (u : Matrix n n 𝒪[F]).map (algebraMap 𝒪[F] F) =
        ((SpecialLinear.Root.rationalMatrixEquiv F g : Matrix.SpecialLinearGroup n F) :
          Matrix n n F) :=
      (congrArg Units.val hg).symm
    have hdet : (u : Matrix n n 𝒪[F]).det = 1 :=
      SpecialLinear.det_eq_one_of_map (IsFractionRing.injective 𝒪[F] F)
        (hmap ▸ (SpecialLinear.Root.rationalMatrixEquiv F g).2)
    refine ⟨⟨u, hdet⟩, ?_, ?_⟩
    · apply Subtype.ext
      exact congrArg Units.val hu
    · ext i j
      exact (congrFun (congrFun hmap i) j).symm

variable (m : ℕ)

/-- In rank `m + 1`, `G^0(𝒪)` is the preimage of the Library's concrete
integral subgroup `GL_{m+1}(𝒪[F])` of `GL_{m+1}(F)`. -/
theorem specialLinear_integralPoints_eq_comap_integralSubgroup :
    (specialLinearModelData F (Fin (m + 1))).neutral.integralPoints =
      (Conductor.integralSubgroup 𝒪[F] m).comap
        (Matrix.SpecialLinearGroup.toGL.comp
          (SpecialLinear.Root.rationalMatrixEquiv (n := Fin (m + 1)) F).toMonoidHom) := by
  ext g
  rw [Subgroup.mem_comap, mem_specialLinear_integralPoints_iff_generalLinear]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, hu.symm⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, hu.symm⟩

/-- In rank `m + 1`, `G(F)^{0+}` is the preimage of the Library's concrete
principal congruence subgroup of level one. -/
theorem specialLinear_positivePoints_eq_comap_principalLevelSubgroup :
    (specialLinearQuotientData F (Fin (m + 1))).positivePoints =
      (Conductor.principalLevelSubgroup F m 1).comap
        (Matrix.SpecialLinearGroup.toGL.comp
          (SpecialLinear.Root.rationalMatrixEquiv (n := Fin (m + 1)) F).toMonoidHom) := by
  ext g
  rw [Subgroup.mem_comap, mem_specialLinear_positivePoints_iff_generalLinear,
    Conductor.principalLevelSubgroup,
    pow_one (IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer),
    Conductor.principalCongruenceSubgroup, Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, hh⟩
    exact ⟨u, hu, hh.symm⟩
  · rintro ⟨u, hu, hh⟩
    exact ⟨u, hu, hh.symm⟩

end Comparison

end Langlands.BruhatTits.IntegralModels
