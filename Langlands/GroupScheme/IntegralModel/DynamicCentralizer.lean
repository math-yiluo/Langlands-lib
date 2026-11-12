import Langlands.GroupScheme.IntegralModel.TorusModelPowerIntegrality
import Langlands.GroupScheme.IntegralModel.IwasawaCellDynamic
import Langlands.GroupScheme.Dynamic.RelativeCentralizerComparison
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups

/-! # An integral centralizer model from a cocharacter, and Levi maximality -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

section Reflection

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G P : GroupScheme (Spec (CommRingCat.of K))}
  {M : IntegralModel R K G} {Z : IntegralModel R K P} {p : P ⟶ G}

/-- **Integral points through a closed model morphism.** If a model morphism over `p` is a
closed subgroup of the target model and the image of a rational point under `p` is integral,
the point is integral. -/
theorem Hom.mem_integralPoints_of_map_mem (φ : Z.Hom M p) (hφ : IsClosedSubgroup φ.hom)
    {ℓ : rationalPoints P} (h : rationalPoints.map p ℓ ∈ M.integralPoints) :
    ℓ ∈ Z.integralPoints := by
  obtain ⟨x, hx⟩ := h
  let y : rationalPoints Z.genericFibre := ℓ ≫ Z.genericIso.inv.hom.hom
  have hy : rationalPoints.map (M.genericHom φ.hom) y = rationalPoints.map p ℓ := by
    rw [rationalPoints.map_apply, rationalPoints.map_apply, genericHom, φ.generic_comm]
    change (ℓ ≫ Z.genericIso.inv.hom.hom) ≫ (Z.genericIso.hom ≫ p).hom.hom = ℓ ≫ p.hom.hom
    rw [Grp.comp_hom_hom, Category.assoc, ← Category.assoc Z.genericIso.inv.hom.hom,
      ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom, Category.id_comp]
  obtain ⟨h, -, hh⟩ := M.exists_eq_of_integralPointMap_eq φ.hom hφ x y (hx.trans hy.symm)
  refine ⟨h, ?_⟩
  change baseChangeSectionHom (Spec.algebraMap R K) Z.group h ≫ Z.genericIso.hom.hom.hom = ℓ
  rw [hh, Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom,
    Category.comp_id]

end Reflection

namespace DynamicCentralizer

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G P : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)

local instance : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom

variable (χ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ M.group)
  (p : P ⟶ G) (hp : IsClosedSubgroup p)
  (hχ : SubgroupFunctor.range (p ≫ M.genericIso.inv) =
    Dynamic.centralizer (Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ))

include hp hχ in
/-- The supplied subgroup and the generic dynamic centralizer represent the same functor. -/
theorem isRepresentedBy_generic :
    (Dynamic.centralizer (Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ)).IsRepresentedBy
      (p ≫ M.genericIso.inv) := by
  have : IsClosedImmersion (p ≫ M.genericIso.inv).hom.hom.left :=
    hp.comp_iso M.genericIso.symm
  exact ⟨Over.mono_of_mono_left _, hχ⟩

/-- The generic-fibre identification of the integral centralizer, determined by the supplied
inclusion. -/
def genericIso :
    (GroupScheme.baseChange (Spec.algebraMap R K)).obj (Dynamic.Affine.centralizerScheme χ) ≅ P :=
  (Dynamic.isRepresentedBy_centralizer_baseChange (Spec.algebraMap R K) χ
    (Dynamic.Affine.isRepresentedBy_centralizerHom χ)).isoOfIsRepresentedBy
      (isRepresentedBy_generic M χ p hp hχ)

/-- The generic identification preserves the original subgroup homomorphism. -/
theorem genericIso_hom_comp :
    (genericIso M χ p hp hχ).hom ≫ p =
      (GroupScheme.baseChange (Spec.algebraMap R K)).map (Dynamic.Affine.centralizerHom χ) ≫
        M.genericIso.hom := by
  have h := SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp
    (Dynamic.isRepresentedBy_centralizer_baseChange (Spec.algebraMap R K) χ
      (Dynamic.Affine.isRepresentedBy_centralizerHom χ))
    (isRepresentedBy_generic M χ p hp hχ)
  have h' := congrArg (fun f => f ≫ M.genericIso.hom) h
  simpa only [genericIso, Category.assoc, Iso.inv_hom_id, Category.comp_id] using h'

variable [Smooth M.group.X.hom]

/-- A smooth affine integral model of the supplied subgroup: the dynamic centralizer of the
integral cocharacter. -/
def model : IntegralModel R K P where
  group := Dynamic.Affine.centralizerScheme χ
  affine := by
    have : IsClosedImmersion (Dynamic.Affine.centralizerHom χ).hom.hom.left :=
      Dynamic.Affine.isClosedSubgroup_centralizerHom χ
    rw [← (Dynamic.Affine.centralizerHom χ).hom.hom.w]
    infer_instance
  flat := by
    have := Dynamic.smooth_affineCentralizer_overRing χ (inferInstance : Smooth M.group.X.hom)
    infer_instance
  finiteType := by
    have := Dynamic.smooth_affineCentralizer_overRing χ (inferInstance : Smooth M.group.X.hom)
    infer_instance
  genericIso := genericIso M χ p hp hχ

/-- The dynamic inclusion extends the supplied generic arrow. -/
def inclusion : (model M χ p hp hχ).Hom M p where
  hom := Dynamic.Affine.centralizerHom χ
  generic_comm := (genericIso_hom_comp M χ p hp hχ).symm

theorem isClosedSubgroup_inclusion : IsClosedSubgroup (inclusion M χ p hp hχ).hom :=
  Dynamic.Affine.isClosedSubgroup_centralizerHom χ

end DynamicCentralizer

section LocalField

open Langlands.AlgebraicGeometry.PointTopology

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  (M : IntegralModel ↥𝒪[F] F G)

local instance dynamicCentralizerModelAffine : IsAffine M.group.X.left :=
  isAffine_of_isAffineHom M.group.X.hom

variable [IsAffine G.X.left] (χ : (Gm (Spec (CommRingCat.of ↥𝒪[F]))).toGrp ⟶ M.group)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The chosen generic centralizer of an integral cocharacter is presented by the base-changed
cocharacter. -/
theorem range_centralizerHom_genericCocharacter :
    SubgroupFunctor.range
        (Dynamic.Affine.centralizerHom (M.genericCocharacter χ) ≫ M.genericIso.inv) =
      Dynamic.centralizer (Dynamic.baseChangeCocharacter (Spec.algebraMap ↥𝒪[F] F) χ) :=
  ((Dynamic.Affine.isRepresentedBy_centralizerHom (M.genericCocharacter χ)).comp_iso
    M.genericIso.symm).2.trans (Dynamic.centralizer_eq_comap_of_iso _ M.genericIso).symm

/-- **Levi maximality from a torus special centralizer.** Let `G` be connected reductive with
connected reductive special fibre of the model, and let `χ` be an integral cocharacter whose
integral centralizer has a torus as special fibre. If the integral points of the model are open, every
compact subgroup of `G(F)` inside the centralizer of the generic cocharacter consists of integral
points. -/
theorem leviMaximal_of_isTorus_specialCentralizer (hG : IsConnectedReductive G)
    (hspecial : IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group))
    (hT : IsTorus ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj
      (Dynamic.Affine.centralizerScheme χ)))
    (hopen : letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsOpen (M.integralPoints : Set (rationalPoints G))) :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∀ C : Subgroup (rationalPoints G), IsCompact (C : Set (rationalPoints G)) →
      C ≤ subgroupFunctorPoints (Dynamic.centralizer (M.genericCocharacter χ)) →
      C ≤ M.integralPoints := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  have : Smooth M.group.X.hom := M.isSmooth_of_reductive_localField hG hspecial
  have : Smooth G.X.hom := hG.smooth
  have : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  intro C hC hCZ g hg
  obtain ⟨n, hn, hgn⟩ := exists_pow_mem_of_isCompact_of_isOpen hC hopen hg
  have hgZ := hCZ hg
  rw [← (Dynamic.Affine.isRepresentedBy_centralizerHom (M.genericCocharacter χ)).2] at hgZ
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : rationalPoints (Dynamic.Affine.centralizerScheme
      (M.genericCocharacter χ)),
      rationalPoints.map (Dynamic.Affine.centralizerHom (M.genericCocharacter χ)) ℓ = g := hgZ
  subst hℓ
  let hp := Dynamic.Affine.isClosedSubgroup_centralizerHom (M.genericCocharacter χ)
  let hχ := M.range_centralizerHom_genericCocharacter χ
  let Z := DynamicCentralizer.model M χ _ hp hχ
  let φ := DynamicCentralizer.inclusion M χ _ hp hχ
  have hL : IsConnectedReductive (Dynamic.Affine.centralizerScheme (M.genericCocharacter χ)) :=
    dynamicCentralizerReductive F G hG _ _ _ hp
      (Dynamic.Affine.isRepresentedBy_centralizerHom _)
  have hZspecial : IsTorus ((GroupScheme.baseChange
      (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj Z.group) := hT
  have hℓn : ℓ ^ n ∈ Z.integralPoints := by
    refine φ.mem_integralPoints_of_map_mem
      (DynamicCentralizer.isClosedSubgroup_inclusion M χ _ hp hχ) ?_
    rw [map_pow]
    exact hgn
  exact φ.map_mem_integralPoints
    (Z.mem_integralPoints_of_pow_mem_of_isTorus_special hL hZspecial hn.ne' hℓn)

end LocalField

end Langlands.GroupScheme.IntegralModel
