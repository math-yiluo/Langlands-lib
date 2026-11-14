import Langlands.BruhatTits.IntegralModels.GeneralLinearDepthZero
import Langlands.GroupScheme.SymplecticMatrix.Reductive

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Depth-zero data for split `Sp_{2l}` over a local field

The split symplectic group scheme `Sp_{2l}` is defined over every commutative
ring, is smooth, and commutes with base change. Over a domain `R` with
fraction field `K` it is therefore an integral model of `Sp_{2l,K}`, the
standard model.

For a nonarchimedean local field `F`, both fibres of the standard model over
`𝒪[F]` are connected reductive, so it gives actual relative-component model
data with full and neutral model equal, and the identity quotient of its
special fibre is a reductive quotient. This is the hyperspecial `Sp_{2l}`
regression example for the depth-zero layer:
`G^0(𝒪) = Sp_{2l}(𝒪[F])`, `G(F)^{0+}` is the kernel of reduction
`Sp_{2l}(𝒪[F]) → Sp_{2l}(𝓀[F])`, and the index is `|Sp_{2l}(𝓀[F])|`. Both
subgroups are cut out of `Sp_{2l}(F)` by the corresponding subgroups of
`GL_{l ⊕ l}`: a symplectic matrix lies in `G^0(𝒪)` exactly when its entries are
integral, and in `G(F)^{0+}` exactly when it is moreover congruent to `1`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel Matrix

namespace Langlands.GroupScheme.SymplecticMatrix

section RingEquiv

variable {l : Type} [Fintype l] [DecidableEq l]

/-- Symplectic matrices transported along a ring isomorphism of their entries. -/
def mapEquiv {A B : Type*} [CommRing A] [CommRing B] (φ : A ≃+* B) :
    Matrix.symplecticGroup l A ≃* Matrix.symplecticGroup l B where
  toFun := map l φ.toRingHom
  invFun := map l φ.symm.toRingHom
  left_inv _ := ext fun _ _ => φ.symm_apply_apply _
  right_inv _ := ext fun _ _ => φ.apply_symm_apply _
  map_mul' := (map l φ.toRingHom).map_mul

theorem mapEquiv_apply {A B : Type*} [CommRing A] [CommRing B] (φ : A ≃+* B)
    (g : Matrix.symplecticGroup l A) (i j : l ⊕ l) :
    (mapEquiv φ g : Matrix (l ⊕ l) (l ⊕ l) B) i j = φ ((g : Matrix (l ⊕ l) (l ⊕ l) A) i j) :=
  rfl

/-- A matrix whose image under an injective ring homomorphism is symplectic
is itself symplectic. -/
theorem mem_symplecticGroup_of_map_mem {A B : Type*} [CommRing A] [CommRing B]
    {f : A →+* B} (hf : Function.Injective f) {M : Matrix (l ⊕ l) (l ⊕ l) A}
    (hM : M.map f ∈ Matrix.symplecticGroup l B) : M ∈ Matrix.symplecticGroup l A := by
  rw [SymplecticGroup.mem_iff] at hM ⊢
  refine Matrix.map_injective hf ?_
  change (M * Matrix.J l A * Mᵀ).map f = (Matrix.J l A).map f
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.map_J, hM]

end RingEquiv

section RationalPoints

variable (l : Type) [Fintype l] [DecidableEq l] (R : CommRingCat.{u})

/-- The rational points of `Sp_{2l}` over `Spec R` are the symplectic matrices
over `R`: the matrix of a point, with entries moved from `Γ(Spec R, ⊤)` to `R`. -/
def rationalPointsEquiv :
    (Over.mk (𝟙 (Spec R)) ⟶ (groupScheme l R).X) ≃* Matrix.symplecticGroup l R :=
  (pointsEquiv l R (Over.mk (𝟙 (Spec R)))).trans
    (mapEquiv (GeneralLinear.globalSectionsEquiv R))

end RationalPoints

section BaseChange

variable {l : Type} [Fintype l] [DecidableEq l]

/-- Changing the base of a section of `Sp_{2l}` along `Spec φ` and reading the
matrix over `B` applies `φ` to every entry of the matrix over `A`. -/
theorem mapEquiv_pointsEquiv_baseChangeSectionHom {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ (groupScheme l (CommRingCat.of A)).X) :
    mapEquiv (GeneralLinear.globalSectionsEquiv (CommRingCat.of B))
        (pointsEquiv l (CommRingCat.of A)
          ((Over.map (Spec.map (CommRingCat.ofHom φ))).obj (Over.mk (𝟙 _)))
          (baseChangePointsEquiv (Spec.map (CommRingCat.ofHom φ))
            (groupScheme l (CommRingCat.of A)) (Over.mk (𝟙 _))
            (baseChangeSectionHom (Spec.map (CommRingCat.ofHom φ))
              (groupScheme l (CommRingCat.of A)) x))) =
      map l φ (rationalPointsEquiv l (CommRingCat.of A) x) := by
  rw [baseChangePointsEquiv_baseChangeSectionHom, pointsEquiv_naturality]
  apply ext
  intro i j
  change (Scheme.ΓSpecIso (CommRingCat.of B)).hom
      ((Spec.map (CommRingCat.ofHom φ)).appTop
        ((pointsEquiv l (CommRingCat.of A) (Over.mk (𝟙 _)) x).1 i j)) =
    φ ((Scheme.ΓSpecIso (CommRingCat.of A)).hom
        ((pointsEquiv l (CommRingCat.of A) (Over.mk (𝟙 _)) x).1 i j))
  change ((Spec.map (CommRingCat.ofHom φ)).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom) _ =
    _
  rw [Scheme.ΓSpecIso_naturality]
  rfl

end BaseChange

section StandardModel

variable (R K : Type u) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (l : Type) [Fintype l] [DecidableEq l]

/-- The split symplectic group over the integral base, with the Library's
base-change identification over the fraction field. Flatness and local finite
type come from the published smoothness of the symplectic group scheme. -/
def standardIntegralModel : IntegralModel R K (groupScheme l (CommRingCat.of K)) where
  group := groupScheme l (CommRingCat.of R)
  affine := isAffineHom_groupScheme l (CommRingCat.of R)
  flat :=
    haveI := smooth_groupScheme l (CommRingCat.of R)
    inferInstance
  finiteType :=
    haveI := smooth_groupScheme l (CommRingCat.of R)
    inferInstance
  genericIso := baseChangeModelIso l (Spec.algebraMap R K)

/-- The standard model is smooth. -/
theorem standardIntegralModel_isSmooth : (standardIntegralModel R K l).IsSmooth :=
  smooth_groupScheme l (CommRingCat.of R)

/-- The integral sections of the standard model are the symplectic matrices
over `R`. -/
def standardSectionsEquiv :
    (standardIntegralModel R K l).integralSections ≃* Matrix.symplecticGroup l R :=
  rationalPointsEquiv l (CommRingCat.of R)

/-- The generic identification of the standard model sends an integral
section to the same matrix, with entries mapped into `K`. -/
theorem standardIntegralModel_integralPointMap
    (x : (standardIntegralModel R K l).integralSections) :
    rationalPointsEquiv l (CommRingCat.of K) ((standardIntegralModel R K l).integralPointMap x) =
      map l (algebraMap R K) (standardSectionsEquiv R K l x) := by
  change mapEquiv (GeneralLinear.globalSectionsEquiv (CommRingCat.of K))
      (pointsEquiv l (CommRingCat.of K) (Over.mk (𝟙 _))
        (baseChangeSectionHom (Spec.algebraMap R K) (groupScheme l (CommRingCat.of R)) x ≫
          (baseChangeModelIso l (Spec.algebraMap R K)).hom.hom.hom)) = _
  rw [pointsEquiv_baseChangeModelIso_hom]
  exact mapEquiv_pointsEquiv_baseChangeSectionHom (algebraMap R K) x

/-- The integral points of the standard model are the points whose matrix
is the image of a symplectic matrix over `R`. -/
theorem mem_standardIntegralModel_integralPoints
    (g : rationalPoints (groupScheme l (CommRingCat.of K))) :
    g ∈ (standardIntegralModel R K l).integralPoints ↔
      ∃ u : Matrix.symplecticGroup l R, rationalPointsEquiv l (CommRingCat.of K) g =
        map l (algebraMap R K) u := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨standardSectionsEquiv R K l x, standardIntegralModel_integralPointMap R K l x⟩
  · rintro ⟨u, hg⟩
    refine ⟨(standardSectionsEquiv R K l).symm u, ?_⟩
    apply (rationalPointsEquiv l (CommRingCat.of K)).injective
    rw [standardIntegralModel_integralPointMap, MulEquiv.apply_symm_apply, hg]

/-- Equivalently, a point is integral exactly when every entry of its matrix
lies in `R`. -/
theorem mem_standardIntegralModel_integralPoints_iff_entries
    (g : rationalPoints (groupScheme l (CommRingCat.of K))) :
    g ∈ (standardIntegralModel R K l).integralPoints ↔
      ∀ i j, ((rationalPointsEquiv l (CommRingCat.of K) g : Matrix.symplecticGroup l K) :
        Matrix (l ⊕ l) (l ⊕ l) K) i j ∈ (algebraMap R K).range := by
  rw [mem_standardIntegralModel_integralPoints]
  constructor
  · rintro ⟨u, hu⟩ i j
    rw [hu]
    exact ⟨_, rfl⟩
  · intro h
    choose a ha using h
    have hmap : (Matrix.of a).map (algebraMap R K) =
        ((rationalPointsEquiv l (CommRingCat.of K) g : Matrix.symplecticGroup l K) :
          Matrix (l ⊕ l) (l ⊕ l) K) := by
      ext i j
      exact ha i j
    have hmem : Matrix.of a ∈ Matrix.symplecticGroup l R :=
      mem_symplecticGroup_of_map_mem (IsFractionRing.injective R K)
        (hmap ▸ (rationalPointsEquiv l (CommRingCat.of K) g).2)
    exact ⟨⟨Matrix.of a, hmem⟩, Subtype.ext hmap.symm⟩

end StandardModel

end Langlands.GroupScheme.SymplecticMatrix

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (l : Type) [Fintype l] [DecidableEq l]

/-- The special fibre of the standard model of `Sp_{2l}` is connected
reductive. -/
theorem isConnectedReductive_symplecticSpecialFibre :
    IsConnectedReductive
      ((baseChange (Spec.algebraMap 𝒪[F] 𝓀[F])).obj
        (SymplecticMatrix.standardIntegralModel 𝒪[F] F l).group) :=
  IsConnectedReductive.of_iso (SymplecticMatrix.baseChangeModelIso l _)
    (SymplecticMatrix.isConnectedReductive l 𝓀[F])

/-- The standard model `Sp_{2l,𝒪[F]}`, as relative-component model data whose
full and neutral models are both this model. Smoothness and connected fibres
come from the published reductive-model criterion. -/
def symplecticModelData :
    RelativeComponentModelData 𝒪[F] F
      (SymplecticMatrix.groupScheme l (CommRingCat.of F)) :=
  (SymplecticMatrix.standardIntegralModel 𝒪[F] F l).relativeComponentData_of_reductive_localField
    (SymplecticMatrix.isConnectedReductive l F)
    (isConnectedReductive_symplecticSpecialFibre F l)

/-- The neutral model is the standard model. -/
theorem symplecticModelData_neutral :
    (symplecticModelData F l).neutral = SymplecticMatrix.standardIntegralModel 𝒪[F] F l :=
  rfl

/-- The special-fibre quotient data of the standard model: the identity
quotient. -/
def symplecticQuotientData : SpecialFibreQuotientData (symplecticModelData F l) :=
  SpecialFibreQuotientData.identityQuotient _

/-- The identity quotient of the standard model is a reductive quotient. -/
theorem symplecticQuotientData_isReductiveQuotient :
    (symplecticQuotientData F l).IsReductiveQuotient :=
  SpecialFibreQuotientData.identityQuotient_isReductiveQuotient _
    (isConnectedReductive_symplecticSpecialFibre F l)

/-- The residue-field points of the special fibre of the standard model are
the symplectic matrices over the residue field. -/
def symplecticSpecialFibrePointsEquiv :
    rationalPoints (symplecticModelData F l).neutral.specialFibre ≃*
      Matrix.symplecticGroup l 𝓀[F] :=
  ((GroupScheme.baseChangePointsEquiv (IntegralModel.residueBaseMap 𝒪[F])
      (SymplecticMatrix.groupScheme l (CommRingCat.of 𝒪[F])) (Over.mk (𝟙 _))).trans
    (SymplecticMatrix.pointsEquiv l (CommRingCat.of 𝒪[F]) _)).trans
    (SymplecticMatrix.mapEquiv (GeneralLinear.globalSectionsEquiv (CommRingCat.of 𝓀[F])))

/-- Under the matrix identifications, reduction of integral sections is the
residue map on every entry. -/
theorem symplecticSpecialFibrePointsEquiv_reduction
    (x : (symplecticModelData F l).neutral.integralSections) :
    symplecticSpecialFibrePointsEquiv F l ((symplecticModelData F l).neutral.reduction x) =
      SymplecticMatrix.map l (IsLocalRing.residue 𝒪[F])
        (SymplecticMatrix.standardSectionsEquiv 𝒪[F] F l x) :=
  SymplecticMatrix.mapEquiv_pointsEquiv_baseChangeSectionHom (IsLocalRing.residue 𝒪[F]) x

/-- The index of `G(F)^{0+}` in `G^0(𝒪) = Sp_{2l}(𝒪[F])` is the order of
`Sp_{2l}(𝓀[F])`. -/
theorem symplectic_index_positivePoints_subgroupOf :
    ((symplecticQuotientData F l).positivePoints.subgroupOf
      (symplecticModelData F l).neutral.integralPoints).index =
        Nat.card (Matrix.symplecticGroup l 𝓀[F]) := by
  obtain ⟨hrad, hQ, -⟩ := symplecticQuotientData_isReductiveQuotient F l
  rw [SpecialFibreQuotientData.localField_index_positivePoints_subgroupOf _ hrad hQ]
  change Nat.card (rationalPoints (symplecticModelData F l).neutral.specialFibre) = _
  exact Nat.card_congr (symplecticSpecialFibrePointsEquiv F l).toEquiv

/-- `G(F)^{0+}` consists of the points whose matrix is the image of a
symplectic matrix `u` over `𝒪[F]` with reduction `1`. -/
theorem mem_symplectic_positivePoints
    (g : rationalPoints (SymplecticMatrix.groupScheme l (CommRingCat.of F))) :
    g ∈ (symplecticQuotientData F l).positivePoints ↔
      ∃ u : Matrix.symplecticGroup l 𝒪[F],
        SymplecticMatrix.map l (IsLocalRing.residue 𝒪[F]) u = 1 ∧
          SymplecticMatrix.rationalPointsEquiv l (CommRingCat.of F) g =
            SymplecticMatrix.map l (algebraMap 𝒪[F] F) u := by
  rw [symplecticQuotientData, SpecialFibreQuotientData.mem_identityQuotient_positivePoints]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨SymplecticMatrix.standardSectionsEquiv 𝒪[F] F l x, ?_,
      SymplecticMatrix.standardIntegralModel_integralPointMap 𝒪[F] F l x⟩
    have h := congrArg (symplecticSpecialFibrePointsEquiv F l) hx
    rw [symplecticSpecialFibrePointsEquiv_reduction] at h
    exact h.trans (symplecticSpecialFibrePointsEquiv F l).map_one
  · rintro ⟨u, hu, hg⟩
    refine ⟨(SymplecticMatrix.standardSectionsEquiv 𝒪[F] F l).symm u, ?_, ?_⟩
    · apply (symplecticSpecialFibrePointsEquiv F l).injective
      rw [symplecticSpecialFibrePointsEquiv_reduction, MulEquiv.apply_symm_apply, hu]
      exact (symplecticSpecialFibrePointsEquiv F l).map_one.symm
    · apply (SymplecticMatrix.rationalPointsEquiv l (CommRingCat.of F)).injective
      change SymplecticMatrix.rationalPointsEquiv l (CommRingCat.of F)
        ((SymplecticMatrix.standardIntegralModel 𝒪[F] F l).integralPointMap
          ((SymplecticMatrix.standardSectionsEquiv 𝒪[F] F l).symm u)) = _
      rw [SymplecticMatrix.standardIntegralModel_integralPointMap, MulEquiv.apply_symm_apply, hg]

/-- `G^0(𝒪)` consists of the points whose matrix is the image of a
symplectic matrix over `𝒪[F]`. -/
theorem mem_symplectic_integralPoints
    (g : rationalPoints (SymplecticMatrix.groupScheme l (CommRingCat.of F))) :
    g ∈ (symplecticModelData F l).neutral.integralPoints ↔
      ∃ u : Matrix.symplecticGroup l 𝒪[F],
        SymplecticMatrix.rationalPointsEquiv l (CommRingCat.of F) g =
          SymplecticMatrix.map l (algebraMap 𝒪[F] F) u :=
  SymplecticMatrix.mem_standardIntegralModel_integralPoints 𝒪[F] F l g

section Comparison

/-- `G^0(𝒪)` is cut out of `Sp_{2l}(F)` by `GL_{l ⊕ l}(𝒪[F])`: a point is
integral exactly when its matrix, as an invertible matrix, is the image of an
invertible matrix over `𝒪[F]`. -/
theorem mem_symplectic_integralPoints_iff_generalLinear
    (g : rationalPoints (SymplecticMatrix.groupScheme l (CommRingCat.of F))) :
    g ∈ (symplecticModelData F l).neutral.integralPoints ↔
      ∃ u : GL (l ⊕ l) 𝒪[F],
        SymplecticMatrix.toGL (SymplecticMatrix.rationalPointsEquiv l (CommRingCat.of F) g) =
          Matrix.GeneralLinearGroup.map (algebraMap 𝒪[F] F) u := by
  rw [mem_symplectic_integralPoints]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨SymplecticMatrix.toGL u, ?_⟩
    rw [hu]
    exact Units.ext rfl
  · rintro ⟨u, hu⟩
    have hmap : (u : Matrix (l ⊕ l) (l ⊕ l) 𝒪[F]).map (algebraMap 𝒪[F] F) =
        ((SymplecticMatrix.rationalPointsEquiv l (CommRingCat.of F) g :
          Matrix.symplecticGroup l F) : Matrix (l ⊕ l) (l ⊕ l) F) :=
      (congrArg Units.val hu).symm
    have hmem : (u : Matrix (l ⊕ l) (l ⊕ l) 𝒪[F]) ∈ Matrix.symplecticGroup l 𝒪[F] :=
      SymplecticMatrix.mem_symplecticGroup_of_map_mem (IsFractionRing.injective 𝒪[F] F)
        (hmap ▸ (SymplecticMatrix.rationalPointsEquiv l (CommRingCat.of F) g).2)
    exact ⟨⟨u, hmem⟩, Subtype.ext hmap.symm⟩

/-- `G(F)^{0+}` is cut out of `Sp_{2l}(F)` by the principal congruence
subgroup of level one of `GL_{l ⊕ l}(𝒪[F])`. -/
theorem mem_symplectic_positivePoints_iff_generalLinear
    (g : rationalPoints (SymplecticMatrix.groupScheme l (CommRingCat.of F))) :
    g ∈ (symplecticQuotientData F l).positivePoints ↔
      ∃ u : GL (l ⊕ l) 𝒪[F], Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[F]) u = 1 ∧
        SymplecticMatrix.toGL (SymplecticMatrix.rationalPointsEquiv l (CommRingCat.of F) g) =
          Matrix.GeneralLinearGroup.map (algebraMap 𝒪[F] F) u := by
  rw [mem_symplectic_positivePoints]
  constructor
  · rintro ⟨u, hu, hg⟩
    refine ⟨SymplecticMatrix.toGL u, ?_, ?_⟩
    · apply Units.ext
      exact congrArg Subtype.val hu
    · rw [hg]
      exact Units.ext rfl
  · rintro ⟨u, hu, hg⟩
    have hmap : (u : Matrix (l ⊕ l) (l ⊕ l) 𝒪[F]).map (algebraMap 𝒪[F] F) =
        ((SymplecticMatrix.rationalPointsEquiv l (CommRingCat.of F) g :
          Matrix.symplecticGroup l F) : Matrix (l ⊕ l) (l ⊕ l) F) :=
      (congrArg Units.val hg).symm
    have hmem : (u : Matrix (l ⊕ l) (l ⊕ l) 𝒪[F]) ∈ Matrix.symplecticGroup l 𝒪[F] :=
      SymplecticMatrix.mem_symplecticGroup_of_map_mem (IsFractionRing.injective 𝒪[F] F)
        (hmap ▸ (SymplecticMatrix.rationalPointsEquiv l (CommRingCat.of F) g).2)
    refine ⟨⟨u, hmem⟩, ?_, Subtype.ext hmap.symm⟩
    apply Subtype.ext
    exact congrArg Units.val hu

end Comparison

end Langlands.BruhatTits.IntegralModels
