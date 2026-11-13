import Langlands.BruhatTits.IntegralModels.FiniteReductiveQuotient
import Langlands.GroupScheme.IntegralModel.LocalReductivity
import Langlands.GroupScheme.IntegralModel.GeneralLinearStandardPoints
import Langlands.GroupScheme.IntegralModel.SplitIntegralPoints
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.Reductive.ToPseudoReductive
import Langlands.GroupScheme.Reductive.TrivialUnipotentRadical
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.Representation.Conductor.PrincipalCongruence
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Depth-zero data for `GL_N` over a local field

For model data `D` whose neutral special fibre is connected reductive, the
trivial subgroup with its unit inclusion is the unipotent radical and the
identity of the special fibre is a reductive quotient
(`SpecialFibreQuotientData.identityQuotient`). Its positive subgroup is the
congruence subgroup of the neutral model, the image of the kernel of
reduction.

For a nonarchimedean local field `F`, the standard model `GL_{N,𝒪[F]}` gives
actual relative-component model data with full and neutral model equal. Its
special fibre `GL_{N,𝓀[F]}` is connected reductive, so the identity quotient
applies. This is the hyperspecial `GL_N` regression example for the
depth-zero layer: `G^0(𝒪) = GL_N(𝒪[F])`, `G(F)^{0+}` is the kernel of
reduction `GL_N(𝒪[F]) → GL_N(𝓀[F])`, and the index is `|GL_N(𝓀[F])|`. For
`N = n + 1` the two subgroups are identified with the Library's concrete
`Conductor.integralSubgroup 𝒪[F] n` and `Conductor.principalLevelSubgroup F n 1`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

namespace SpecialFibreQuotientData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))}

/-- The neutral special fibre is affine over the residue field. -/
private lemma neutralSpecialFibre_isAffineHom (D : RelativeComponentModelData R K G) :
    IsAffineHom D.neutral.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

/-- The special-fibre quotient data whose radical is the trivial group with
its unit inclusion and whose quotient is the neutral special fibre itself with
the identity projection. -/
def identityQuotient (D : RelativeComponentModelData R K G) : SpecialFibreQuotientData D where
  radical := Grp.trivial _
  radicalInclusion := kernelUnit _
  quotient := D.neutral.specialFibre
  quotient_affine := neutralSpecialFibre_isAffineHom D
  projection := 𝟙 _

/-- If the neutral special fibre is connected reductive, the identity quotient
is a reductive quotient: the trivial subgroup is the unipotent radical, the
identity is the fppf quotient by it, and the quotient is connected reductive. -/
theorem identityQuotient_isReductiveQuotient (D : RelativeComponentModelData R K G)
    (h : IsConnectedReductive D.neutral.specialFibre) :
    (identityQuotient D).IsReductiveQuotient := by
  have : IsAffineHom D.neutral.specialFibre.X.hom := neutralSpecialFibre_isAffineHom D
  refine ⟨?_, ?_, h⟩
  · exact isUnipotentRadical_kernelUnit _ h.hasTrivialUnipotentRadical
  · refine ⟨?_, ?_, ?_, ?_⟩
    · change Flat (𝟙 _)
      infer_instance
    · change Surjective (𝟙 _)
      infer_instance
    · change LocallyOfFinitePresentation (𝟙 _)
      infer_instance
    change SubgroupFunctor.range (kernelι (𝟙 _)) = SubgroupFunctor.range (kernelUnit _)
    rw [range_kernelUnit]
    ext T x
    rw [mem_range_kernelι_iff]
    change x ≫ 𝟙 _ = 1 ↔ x = 1
    rw [Category.comp_id]

/-- The trivial radical has only the identity residue-field point. -/
theorem identityQuotient_radicalPoints (D : RelativeComponentModelData R K G) :
    (identityQuotient D).radicalPoints = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨y, rfl⟩
  have hy : y ≫ (kernelUnit D.neutral.specialFibre).hom.hom ∈
      (SubgroupFunctor.range (kernelUnit D.neutral.specialFibre)).carrier
        (Over.mk (𝟙 _)) := ⟨y, rfl⟩
  rw [range_kernelUnit] at hy
  simp only [SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hy
  exact Subgroup.mem_bot.mpr hy

/-- The positive subgroup of the identity quotient is the congruence subgroup
of the neutral model: the image of the kernel of reduction. -/
theorem identityQuotient_positivePoints (D : RelativeComponentModelData R K G) :
    (identityQuotient D).positivePoints = D.neutral.congruenceSubgroup := by
  ext g
  rw [mem_positivePoints, identityQuotient_radicalPoints, IntegralModel.mem_congruenceSubgroup]
  simp only [Subgroup.mem_bot]

/-- A point is positive for the identity quotient exactly when it is the
image of an integral section with trivial reduction. -/
theorem mem_identityQuotient_positivePoints (D : RelativeComponentModelData R K G)
    (g : rationalPoints G) :
    g ∈ (identityQuotient D).positivePoints ↔
      ∃ x : D.neutral.integralSections,
        D.neutral.reduction x = 1 ∧ D.neutral.integralPointMap x = g := by
  rw [identityQuotient_positivePoints, IntegralModel.mem_congruenceSubgroup]

end SpecialFibreQuotientData

end Langlands.BruhatTits.IntegralModels

namespace Langlands.GroupScheme.GeneralLinear

/-- Changing the base of a section of `GL_N` along `Spec φ` and reading the
matrix over `B` applies `φ` to every entry of the matrix over `A`. -/
theorem glRingEquiv_pointsEquiv_baseChangeSectionHom {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (N : ℕ)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ (groupScheme (Fin N) (CommRingCat.of A)).X) :
    glRingEquiv (globalSectionsEquiv (CommRingCat.of B))
        (pointsEquiv (Fin N) (CommRingCat.of A)
          ((Over.map (Spec.map (CommRingCat.ofHom φ))).obj (Over.mk (𝟙 _)))
          (baseChangePointsEquiv (Spec.map (CommRingCat.ofHom φ))
            (groupScheme (Fin N) (CommRingCat.of A)) (Over.mk (𝟙 _))
            (baseChangeSectionHom (Spec.map (CommRingCat.ofHom φ))
              (groupScheme (Fin N) (CommRingCat.of A)) x))) =
      Matrix.GeneralLinearGroup.map φ (rationalPointsEquiv N (CommRingCat.of A) x) := by
  rw [baseChangePointsEquiv_baseChangeSectionHom, pointsEquiv_naturality]
  apply Units.ext
  ext i j
  change (Scheme.ΓSpecIso (CommRingCat.of B)).hom
      ((Spec.map (CommRingCat.ofHom φ)).appTop
        (pointsEquiv (Fin N) (CommRingCat.of A) (Over.mk (𝟙 _)) x i j)) =
    φ ((Scheme.ΓSpecIso (CommRingCat.of A)).hom
        (pointsEquiv (Fin N) (CommRingCat.of A) (Over.mk (𝟙 _)) x i j))
  change ((Spec.map (CommRingCat.ofHom φ)).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom) _ =
    _
  rw [Scheme.ΓSpecIso_naturality]
  rfl

variable (R K : Type u) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (N : ℕ)

/-- The integral sections of the standard model are the invertible matrices
over `R`. -/
def standardSectionsEquiv :
    (standardIntegralModel R K (Fin N)).integralSections ≃* GL (Fin N) R :=
  rationalPointsEquiv N (CommRingCat.of R)

/-- The integral points of the standard model are the points whose matrix
is the image of an invertible matrix over `R`. -/
theorem mem_standardIntegralModel_integralPoints
    (g : rationalPoints (groupScheme (Fin N) (CommRingCat.of K))) :
    g ∈ (standardIntegralModel R K (Fin N)).integralPoints ↔
      ∃ u : GL (Fin N) R, rationalPointsEquiv N (CommRingCat.of K) g =
        Matrix.GeneralLinearGroup.map (algebraMap R K) u := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨standardSectionsEquiv R K N x, standardIntegralModel_integralPointMap R K x⟩
  · rintro ⟨u, hg⟩
    refine ⟨(standardSectionsEquiv R K N).symm u, ?_⟩
    apply (rationalPointsEquiv N (CommRingCat.of K)).injective
    rw [standardIntegralModel_integralPointMap]
    change Matrix.GeneralLinearGroup.map (algebraMap R K)
      (standardSectionsEquiv R K N ((standardSectionsEquiv R K N).symm u)) = _
    rw [MulEquiv.apply_symm_apply, hg]

end Langlands.GroupScheme.GeneralLinear

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (N : ℕ)

/-- The standard model `GL_{N,𝒪[F]}`, as relative-component model data whose
full and neutral models are both this model. Smoothness and connected fibres
come from the published reductive-model criterion. -/
def generalLinearModelData :
    RelativeComponentModelData 𝒪[F] F (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)) :=
  (GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N)).relativeComponentData_of_reductive_localField
    (isConnectedReductive_generalLinear F (Fin N))
    (IsConnectedReductive.of_iso (GeneralLinear.baseChangeIso (Fin N) _)
      (isConnectedReductive_generalLinear 𝓀[F] (Fin N)))

/-- The neutral model is the standard model. -/
theorem generalLinearModelData_neutral :
    (generalLinearModelData F N).neutral = GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N) :=
  rfl

/-- The special fibre of the standard model is connected reductive. -/
theorem isConnectedReductive_generalLinearSpecialFibre :
    IsConnectedReductive (generalLinearModelData F N).neutral.specialFibre :=
  IsConnectedReductive.of_iso (GeneralLinear.baseChangeIso (Fin N) _)
    (isConnectedReductive_generalLinear 𝓀[F] (Fin N))

/-- The special-fibre quotient data of the standard model: the identity
quotient. -/
def generalLinearQuotientData : SpecialFibreQuotientData (generalLinearModelData F N) :=
  SpecialFibreQuotientData.identityQuotient _

/-- The identity quotient of the standard model is a reductive quotient. -/
theorem generalLinearQuotientData_isReductiveQuotient :
    (generalLinearQuotientData F N).IsReductiveQuotient :=
  SpecialFibreQuotientData.identityQuotient_isReductiveQuotient _
    (isConnectedReductive_generalLinearSpecialFibre F N)

/-- The residue-field points of the special fibre of the standard model are
the invertible matrices over the residue field. -/
def generalLinearSpecialFibrePointsEquiv :
    rationalPoints (generalLinearModelData F N).neutral.specialFibre ≃* GL (Fin N) 𝓀[F] :=
  ((GroupScheme.baseChangePointsEquiv (IntegralModel.residueBaseMap 𝒪[F])
      (GeneralLinear.groupScheme (Fin N) (CommRingCat.of 𝒪[F])) (Over.mk (𝟙 _))).trans
    (GeneralLinear.pointsEquiv (Fin N) (CommRingCat.of 𝒪[F]) _)).trans
    (GeneralLinear.glRingEquiv (GeneralLinear.globalSectionsEquiv (CommRingCat.of 𝓀[F])))

/-- Under the matrix identifications, reduction of integral sections is the
residue map on every entry. -/
theorem generalLinearSpecialFibrePointsEquiv_reduction
    (x : (generalLinearModelData F N).neutral.integralSections) :
    generalLinearSpecialFibrePointsEquiv F N ((generalLinearModelData F N).neutral.reduction x) =
      Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[F])
        (GeneralLinear.standardSectionsEquiv 𝒪[F] F N x) :=
  GeneralLinear.glRingEquiv_pointsEquiv_baseChangeSectionHom (IsLocalRing.residue 𝒪[F]) N x

/-- The index of `G(F)^{0+}` in `G^0(𝒪) = GL_N(𝒪[F])` is the order of
`GL_N(𝓀[F])`. -/
theorem generalLinear_index_positivePoints_subgroupOf :
    ((generalLinearQuotientData F N).positivePoints.subgroupOf
      (generalLinearModelData F N).neutral.integralPoints).index =
        Nat.card (GL (Fin N) 𝓀[F]) := by
  obtain ⟨hrad, hQ, -⟩ := generalLinearQuotientData_isReductiveQuotient F N
  rw [SpecialFibreQuotientData.localField_index_positivePoints_subgroupOf _ hrad hQ]
  change Nat.card (rationalPoints (generalLinearModelData F N).neutral.specialFibre) = _
  exact Nat.card_congr (generalLinearSpecialFibrePointsEquiv F N).toEquiv

/-- The same index is `∏_{i < N} (q ^ N - q ^ i)`, where `q` is the
cardinality of the residue field. -/
theorem generalLinear_index_positivePoints_subgroupOf_eq_prod :
    ((generalLinearQuotientData F N).positivePoints.subgroupOf
      (generalLinearModelData F N).neutral.integralPoints).index =
        ∏ i : Fin N, (Nat.card 𝓀[F] ^ N - Nat.card 𝓀[F] ^ (i : ℕ)) := by
  let : Fintype 𝓀[F] := Fintype.ofFinite _
  rw [generalLinear_index_positivePoints_subgroupOf, Matrix.card_GL_field, Nat.card_eq_fintype_card]

/-- `G(F)^{0+}` consists of the points whose matrix is the image of an
invertible matrix `u` over `𝒪[F]` with reduction `1`. -/
theorem mem_generalLinear_positivePoints
    (g : rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F))) :
    g ∈ (generalLinearQuotientData F N).positivePoints ↔
      ∃ u : GL (Fin N) 𝒪[F], Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[F]) u = 1 ∧
        GeneralLinear.rationalPointsEquiv N (CommRingCat.of F) g =
          Matrix.GeneralLinearGroup.map (algebraMap 𝒪[F] F) u := by
  rw [generalLinearQuotientData, SpecialFibreQuotientData.mem_identityQuotient_positivePoints]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨GeneralLinear.standardSectionsEquiv 𝒪[F] F N x, ?_,
      GeneralLinear.standardIntegralModel_integralPointMap 𝒪[F] F x⟩
    have h := congrArg (generalLinearSpecialFibrePointsEquiv F N) hx
    rw [generalLinearSpecialFibrePointsEquiv_reduction] at h
    exact h.trans (generalLinearSpecialFibrePointsEquiv F N).map_one
  · rintro ⟨u, hu, hg⟩
    refine ⟨(GeneralLinear.standardSectionsEquiv 𝒪[F] F N).symm u, ?_, ?_⟩
    · apply (generalLinearSpecialFibrePointsEquiv F N).injective
      rw [generalLinearSpecialFibrePointsEquiv_reduction, MulEquiv.apply_symm_apply, hu]
      exact (generalLinearSpecialFibrePointsEquiv F N).map_one.symm
    · apply (GeneralLinear.rationalPointsEquiv N (CommRingCat.of F)).injective
      change GeneralLinear.rationalPointsEquiv N (CommRingCat.of F)
        ((GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N)).integralPointMap
          ((GeneralLinear.standardSectionsEquiv 𝒪[F] F N).symm u)) = _
      rw [GeneralLinear.standardIntegralModel_integralPointMap]
      change Matrix.GeneralLinearGroup.map (algebraMap 𝒪[F] F)
        (GeneralLinear.standardSectionsEquiv 𝒪[F] F N
          ((GeneralLinear.standardSectionsEquiv 𝒪[F] F N).symm u)) = _
      rw [MulEquiv.apply_symm_apply, hg]

/-- `G^0(𝒪)` consists of the points whose matrix is the image of an
invertible matrix over `𝒪[F]`. -/
theorem mem_generalLinear_integralPoints
    (g : rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F))) :
    g ∈ (generalLinearModelData F N).neutral.integralPoints ↔
      ∃ u : GL (Fin N) 𝒪[F], GeneralLinear.rationalPointsEquiv N (CommRingCat.of F) g =
        Matrix.GeneralLinearGroup.map (algebraMap 𝒪[F] F) u :=
  GeneralLinear.mem_standardIntegralModel_integralPoints 𝒪[F] F N g

section Comparison

variable (n : ℕ)

/-- In rank `n + 1`, the matrix image of `G^0(𝒪)` is the Library's concrete
integral subgroup `GL_{n+1}(𝒪[F])` of `GL_{n+1}(F)`. -/
theorem generalLinear_integralPoints_map_eq_integralSubgroup :
    (generalLinearModelData F (n + 1)).neutral.integralPoints.map
        (GeneralLinear.rationalPointsEquiv (n + 1) (CommRingCat.of F)).toMonoidHom =
      Conductor.integralSubgroup 𝒪[F] n := by
  ext h
  rw [Subgroup.mem_map_equiv, mem_generalLinear_integralPoints, MulEquiv.apply_symm_apply]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, hu.symm⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, hu.symm⟩

/-- In rank `n + 1`, the matrix image of `G(F)^{0+}` is the Library's
concrete principal congruence subgroup of level one. -/
theorem generalLinear_positivePoints_map_eq_principalLevelSubgroup :
    (generalLinearQuotientData F (n + 1)).positivePoints.map
        (GeneralLinear.rationalPointsEquiv (n + 1) (CommRingCat.of F)).toMonoidHom =
      Conductor.principalLevelSubgroup F n 1 := by
  ext h
  rw [Subgroup.mem_map_equiv, mem_generalLinear_positivePoints, MulEquiv.apply_symm_apply,
    Conductor.principalLevelSubgroup, pow_one, Conductor.principalCongruenceSubgroup,
    Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, hh⟩
    exact ⟨u, hu, hh.symm⟩
  · rintro ⟨u, hu, hh⟩
    exact ⟨u, hu, hh.symm⟩

/-- Consequently the concrete principal congruence subgroup of level one has
index `|GL_{n+1}(𝓀[F])|` in the concrete integral subgroup. -/
theorem generalLinear_principalLevelSubgroup_relIndex :
    (Conductor.principalLevelSubgroup F n 1).relIndex (Conductor.integralSubgroup 𝒪[F] n) =
      Nat.card (GL (Fin (n + 1)) 𝓀[F]) := by
  rw [← generalLinear_integralPoints_map_eq_integralSubgroup,
    ← generalLinear_positivePoints_map_eq_principalLevelSubgroup,
    Subgroup.relIndex_map_map_of_injective _ _ (MulEquiv.injective _)]
  exact generalLinear_index_positivePoints_subgroupOf F (n + 1)

end Comparison

end Langlands.BruhatTits.IntegralModels
