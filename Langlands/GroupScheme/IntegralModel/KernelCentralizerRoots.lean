import Langlands.GroupScheme.IntegralModel.KernelCentralizerTorus
import Langlands.GroupScheme.IntegralModel.DynamicTripleCell
import Langlands.GroupScheme.IntegralModel.ClosedSubgroupIntegralPoints
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.BaseSmoothConnectedProof
import Langlands.GroupScheme.Dynamic.OppositeBaseChange
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.GroupScheme.Rational.RootFactorPairExistenceReduction
import Langlands.GroupScheme.Rational.CrossTorusRootTransport
import Langlands.GroupScheme.Rational.NormalRadicalConjugacy

/-! # Dynamic integral models in character-kernel centralizer components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.IntegralModel

private theorem map_comap_iso {B : Scheme.{u}} {H J : GroupScheme B}
    (e : H ≅ J) (F : SubgroupFunctor J) :
    (F.comap e.hom).map e.hom = F := by
  rw [SubgroupFunctor.map_comap]
  ext U x
  constructor
  · exact And.right
  · intro hx
    refine ⟨⟨x ≫ e.inv.hom.hom, ?_⟩, hx⟩
    change (x ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = x
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom,
      Category.comp_id]

namespace DynamicModels

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    (M : IntegralModel R K G) [Smooth M.group.X.hom]
    (χ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ M.group)

local instance : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom

instance unipotent_affine : IsAffineHom (Dynamic.Affine.unipotentScheme χ).X.hom := by
  have : IsClosedImmersion (Dynamic.Affine.unipotentHom χ).hom.hom.left :=
    Dynamic.Affine.isClosedSubgroup_unipotentHom χ
  rw [← (Dynamic.Affine.unipotentHom χ).hom.hom.w]
  infer_instance

instance centralizer_affine : IsAffineHom (Dynamic.Affine.centralizerScheme χ).X.hom := by
  have : IsClosedImmersion (Dynamic.Affine.centralizerHom χ).hom.hom.left :=
    Dynamic.Affine.isClosedSubgroup_centralizerHom χ
  rw [← (Dynamic.Affine.centralizerHom χ).hom.hom.w]
  infer_instance

instance unipotent_smooth : Smooth (Dynamic.Affine.unipotentScheme χ).X.hom :=
  ((dynamicBaseSmoothConnected _ M.group χ _ _).1
    (Dynamic.Affine.isRepresentedBy_unipotentHom χ)).1

instance centralizer_smooth : Smooth (Dynamic.Affine.centralizerScheme χ).X.hom :=
  ((dynamicBaseSmoothConnected _ M.group χ _ _).2.2
    (Dynamic.Affine.isRepresentedBy_centralizerHom χ)).1

instance unipotent_geometricallyConnected :
    GeometricallyConnected (Dynamic.Affine.unipotentScheme χ).X.hom :=
  ((dynamicBaseSmoothConnected _ M.group χ _ _).1
    (Dynamic.Affine.isRepresentedBy_unipotentHom χ)).2

instance centralizer_geometricallyConnected [GeometricallyConnected M.group.X.hom] :
    GeometricallyConnected (Dynamic.Affine.centralizerScheme χ).X.hom :=
  ((dynamicBaseSmoothConnected _ M.group χ _ _).2.2
    (Dynamic.Affine.isRepresentedBy_centralizerHom χ)).2 inferInstance

/-- The actual generic fibre of the canonical integral dynamic unipotent. -/
abbrev unipotentGeneric : GroupScheme (Spec (CommRingCat.of K)) :=
  (baseChange (Spec.algebraMap R K)).obj (Dynamic.Affine.unipotentScheme χ)

/-- The actual generic fibre of the canonical integral dynamic centralizer. -/
abbrev centralizerGeneric : GroupScheme (Spec (CommRingCat.of K)) :=
  (baseChange (Spec.algebraMap R K)).obj (Dynamic.Affine.centralizerScheme χ)

/-- The smooth affine integral dynamic unipotent, with its actual generic fibre. -/
def unipotentModel : IntegralModel R K (unipotentGeneric M χ) where
  group := Dynamic.Affine.unipotentScheme χ
  genericIso := Iso.refl _

/-- The smooth affine integral dynamic centralizer, with its actual generic fibre. -/
def centralizerModel : IntegralModel R K (centralizerGeneric M χ) where
  group := Dynamic.Affine.centralizerScheme χ
  genericIso := Iso.refl _

/-- The closed unipotent inclusion extends its actual generic inclusion. -/
def unipotentInclusion :
    (unipotentModel M χ).Hom M (M.genericHom (Dynamic.Affine.unipotentHom χ)) where
  hom := Dynamic.Affine.unipotentHom χ
  generic_comm := (Category.id_comp _).symm

/-- The closed centralizer inclusion extends its actual generic inclusion. -/
def centralizerInclusion :
    (centralizerModel M χ).Hom M (M.genericHom (Dynamic.Affine.centralizerHom χ)) where
  hom := Dynamic.Affine.centralizerHom χ
  generic_comm := (Category.id_comp _).symm

omit [Smooth M.group.X.hom] in
/-- The generic inclusion represents the dynamic unipotent in the specified
generic ambient group, retaining its chosen generic-fibre identification. -/
theorem unipotent_isRepresentedBy_genericHom :
    ((Dynamic.unipotent (Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ)).comap
      M.genericIso.inv).IsRepresentedBy
        (M.genericHom (Dynamic.Affine.unipotentHom χ)) := by
  have h := (Dynamic.Affine.isRepresentedBy_unipotentHom χ).baseChange
    (Spec.algebraMap R K)
  rw [← Dynamic.unipotent_baseChange] at h
  exact h.comp_iso M.genericIso

/-- The integral unipotent points have exactly the expected intersection
inside the specified generic ambient group. -/
theorem unipotent_map_integralPoints_eq :
    (unipotentModel M χ).integralPoints.map
        (rationalPoints.map (M.genericHom (Dynamic.Affine.unipotentHom χ))) =
      M.integralPoints ⊓
        ((Dynamic.unipotent (Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ)).comap
          M.genericIso.inv).carrier (Over.mk (𝟙 (Spec (CommRingCat.of K)))) := by
  have hrange := congrArg
    (fun F => F.carrier (Over.mk (𝟙 (Spec (CommRingCat.of K)))))
    (unipotent_isRepresentedBy_genericHom M χ).2
  change (rationalPoints.map (M.genericHom (Dynamic.Affine.unipotentHom χ))).range = _
    at hrange
  rw [← hrange]
  refine Eq.trans ?_ (M.integralPoints_inf_range_genericHom
    (Dynamic.Affine.unipotentHom χ) (Dynamic.Affine.isClosedSubgroup_unipotentHom χ)).symm
  change ((unipotentModel M χ).integralPointMap.range).map
    (rationalPoints.map (M.genericHom (Dynamic.Affine.unipotentHom χ))) = _
  rw [MonoidHom.map_range]
  congr 1
  apply MonoidHom.ext
  intro x
  exact ((unipotentInclusion M χ).integralPointMap_naturality x).symm

/-- The two opposite dynamic models and the centralizer have an actual
open ordered multiplication cell over the integral base. -/
def tripleCell [IsLocalRing R] :
    IntegralTripleCellData M
      (unipotentGeneric M (CommGroupScheme.groupHom
        (Gm.powerHom (Spec (CommRingCat.of R)) (-1)) ≫ χ))
      (centralizerGeneric M χ) (unipotentGeneric M χ)
      (M.genericHom (Dynamic.Affine.unipotentHom (CommGroupScheme.groupHom
        (Gm.powerHom (Spec (CommRingCat.of R)) (-1)) ≫ χ)))
      (M.genericHom (Dynamic.Affine.centralizerHom χ))
      (M.genericHom (Dynamic.Affine.unipotentHom χ)) :=
  IntegralTripleCellData.ofDynamic M χ
    (unipotentModel M _) (centralizerModel M χ) (unipotentModel M χ)
    (unipotentInclusion M _) (centralizerInclusion M χ) (unipotentInclusion M χ)
    (Dynamic.Affine.isRepresentedBy_unipotentHom _)
    (Dynamic.Affine.isRepresentedBy_centralizerHom χ)
    (Dynamic.Affine.isRepresentedBy_unipotentHom χ)

end DynamicModels

namespace KernelCentralizerData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {M : IntegralModel R K G}
    {T : CommGroupScheme (Spec (CommRingCat.of R))}
    {i : T.toGrp ⟶ M.group} {a : characterLattice T}
    (D : KernelCentralizerData M i a) (hT : IsSplitTorus T.toGrp)

variable {k : Type u} [Field k]
    (b : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))

local instance : Smooth ((baseChange b).obj D.fullGroup).X.hom :=
  inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd D.fullGroup.X.hom b))

local instance : IsAffineHom ((baseChange b).obj D.fullGroup).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd D.fullGroup.X.hom b))

/-- The integral cocharacter is identified with the cocharacter of the
canonical torus in every field fibre of the centralizer component. -/
theorem cocharacter_fibreIso (ν : cocharacterLattice T) :
    Dynamic.baseChangeCocharacter b (CommGroupScheme.groupHom ν ≫ D.torus hT) ≫
        (D.fibreIso b).hom =
      CommGroupScheme.groupHom (cocharacterLattice.baseChange b T ν) ≫
        RelativeRoot.kernelCentralizerIdentityTorus
          (T := (CommGroupScheme.baseChange b).obj T)
          (G := (baseChange b).obj M.group) (C := (baseChange b).obj D.fullGroup)
          ((baseChange b).map i) (hT.baseChange b) (characterLattice.baseChange b T a)
          ((baseChange b).map D.fullHom) (D.fullFibreRepresents b) := by
  rw [Dynamic.baseChangeCocharacter, Functor.map_comp, Category.assoc, Category.assoc,
    D.torus_fibreIso]
  rfl

/-- A positive pairing remains positive, so the character of every field
fibre is nonzero. -/
theorem character_fibre_ne_zero (ν : cocharacterLattice T)
    (hpos : 0 < latticePairing T a ν) :
    characterLattice.baseChange b T a ≠ 0 := by
  intro hz
  have hp := latticePairing_baseChange b T a ν
  rw [hz, map_zero] at hp
  exact (ne_of_gt hpos) hp.symm

/-- The actual dynamic unipotent in a field fibre is the intrinsic root
functor, transported through the canonical component isomorphism. -/
theorem dynamicUnipotent_fibre_eq (ν : cocharacterLattice T)
    (hpos : 0 < latticePairing T a ν) :
    Dynamic.unipotent
        (Dynamic.baseChangeCocharacter b (CommGroupScheme.groupHom ν ≫ D.torus hT)) =
      (RelativeRoot.subgroup
        (RelativeRoot.kernelCentralizerIdentityTorus
          (T := (CommGroupScheme.baseChange b).obj T)
          (G := (baseChange b).obj M.group) (C := (baseChange b).obj D.fullGroup)
          ((baseChange b).map i) (hT.baseChange b) (characterLattice.baseChange b T a)
          ((baseChange b).map D.fullHom) (D.fullFibreRepresents b))
        (characterLattice.baseChange b T a)).comap (D.fibreIso b).hom := by
  rw [Dynamic.unipotent_eq_comap_of_iso _ (D.fibreIso b), D.cocharacter_fibreIso]
  congr 1
  exact RelativeRoot.kernelCentralizerIdentity_dynamicUnipotent_eq_subgroup
    (T := (CommGroupScheme.baseChange b).obj T)
    (G := (baseChange b).obj M.group) (C := (baseChange b).obj D.fullGroup)
    ((baseChange b).map i) (hT.baseChange b) (characterLattice.baseChange b T a)
    (character_fibre_ne_zero b ν hpos) ((baseChange b).map D.fullHom)
    (D.fullFibreRepresents b) (cocharacterLattice.baseChange b T ν)
    (by rwa [latticePairing_baseChange])

/-- The analogous field-fibre centralizer is the whole-torus centralizer
inside the same actual component. -/
theorem dynamicCentralizer_fibre_eq (ν : cocharacterLattice T)
    (hpos : 0 < latticePairing T a ν) :
    Dynamic.centralizer
        (Dynamic.baseChangeCocharacter b (CommGroupScheme.groupHom ν ≫ D.torus hT)) =
      (torusCentralizer
        (RelativeRoot.kernelCentralizerIdentityTorus
          (T := (CommGroupScheme.baseChange b).obj T)
          (G := (baseChange b).obj M.group) (C := (baseChange b).obj D.fullGroup)
          ((baseChange b).map i) (hT.baseChange b) (characterLattice.baseChange b T a)
          ((baseChange b).map D.fullHom) (D.fullFibreRepresents b))).comap
        (D.fibreIso b).hom := by
  rw [Dynamic.centralizer_eq_comap_of_iso _ (D.fibreIso b), D.cocharacter_fibreIso]
  congr 1
  exact RelativeRoot.kernelCentralizerIdentity_dynamicCentralizer_eq_torusCentralizer
    (T := (CommGroupScheme.baseChange b).obj T)
    (G := (baseChange b).obj M.group) (C := (baseChange b).obj D.fullGroup)
    ((baseChange b).map i) (hT.baseChange b) (characterLattice.baseChange b T a)
    (character_fibre_ne_zero b ν hpos) ((baseChange b).map D.fullHom)
    (D.fullFibreRepresents b) (cocharacterLattice.baseChange b T ν)
    (by rw [latticePairing_baseChange]; exact ne_of_gt hpos)

/-- In the actual component fibre, the positive dynamic subgroup is the
root functor for its original base-changed torus map. -/
theorem dynamicUnipotent_fibre_eq_subgroup (ν : cocharacterLattice T)
    (hpos : 0 < latticePairing T a ν) :
    Dynamic.unipotent
        (Dynamic.baseChangeCocharacter b (CommGroupScheme.groupHom ν ≫ D.torus hT)) =
      RelativeRoot.subgroup ((baseChange b).map (D.torus hT))
        (characterLattice.baseChange b T a) := by
  rw [D.dynamicUnipotent_fibre_eq hT b ν hpos]
  simpa only [characterLattice.congr_apply, Iso.refl_inv, Category.id_comp] using
    RelativeRoot.subgroup_comap_of_transport
      (Iso.refl ((CommGroupScheme.baseChange b).obj T)) (D.fibreIso b)
      (i := (baseChange b).map (D.torus hT))
      (by
        change _ = 𝟙 _ ≫ _
        rw [Category.id_comp]
        exact D.torus_fibreIso b hT)
      (characterLattice.baseChange b T a)

/-- The dynamic centralizer on the actual component fibre is its
whole-torus centralizer. -/
theorem dynamicCentralizer_fibre_eq_torusCentralizer (ν : cocharacterLattice T)
    (hpos : 0 < latticePairing T a ν) :
    Dynamic.centralizer
        (Dynamic.baseChangeCocharacter b (CommGroupScheme.groupHom ν ≫ D.torus hT)) =
      torusCentralizer (T := (CommGroupScheme.baseChange b).obj T)
        ((baseChange b).map (D.torus hT)) := by
  rw [D.dynamicCentralizer_fibre_eq hT b ν hpos]
  have hc := torusCentralizer_eq_comap_of_iso
    (B := (CommGroupScheme.baseChange b).obj T)
    ((baseChange b).map (D.torus hT)) (D.fibreIso b)
  rw [D.torus_fibreIso] at hc
  exact hc.symm

/-- The positive dynamic subgroup maps onto the original ambient root
functor on every field fibre, on all scheme tests. -/
theorem dynamicUnipotent_fibre_map (ν : cocharacterLattice T)
    (hpos : 0 < latticePairing T a ν) :
    (Dynamic.unipotent
      (Dynamic.baseChangeCocharacter b (CommGroupScheme.groupHom ν ≫ D.torus hT))).map
        ((baseChange b).map (D.componentHom ≫ D.fullHom)) =
      RelativeRoot.subgroup ((baseChange b).map i) (characterLattice.baseChange b T a) := by
  obtain ⟨hqc, hflat, hsurj⟩ := RelativeRoot.characterFpqc k
    ((CommGroupScheme.baseChange b).obj T) (hT.baseChange b)
    (characterLattice.baseChange b T a) (character_fibre_ne_zero b ν hpos)
  rw [D.dynamicUnipotent_fibre_eq hT b ν hpos, Functor.map_comp,
    ← D.fibreIso_hom_comp b, Category.assoc, ← SubgroupFunctor.map_comp, map_comap_iso]
  exact RelativeRoot.kernelCentralizerIdentity_subgroup_map
    (T := (CommGroupScheme.baseChange b).obj T)
    (G := (baseChange b).obj M.group) (C := (baseChange b).obj D.fullGroup)
    ((baseChange b).map i) (hT.baseChange b) (characterLattice.baseChange b T a)
    ((baseChange b).map D.fullHom) (D.fullFibreRepresents b) (D.fullClosed.baseChange b)

/-- Negating a torus cocharacter is precomposition by inversion on the
integral multiplicative group. This holds over the integral base itself. -/
theorem opposite_torusCocharacter (ν : cocharacterLattice T) :
    CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of R)) (-1)) ≫
        (CommGroupScheme.groupHom ν ≫ D.torus hT) =
      CommGroupScheme.groupHom (-ν) ≫ D.torus hT := by
  have hν : Gm.powerHom (Spec (CommRingCat.of R)) (-1) ≫ ν = -ν := by
    simp only [Gm.powerHom_apply, neg_one_zsmul, Preadditive.neg_comp, Category.id_comp]
  rw [← Category.assoc]
  change CommGroupScheme.groupHom (Gm.powerHom _ (-1) ≫ ν) ≫ D.torus hT = _
  rw [hν]

/-- The opposite integral cocharacter gives precisely the opposite root
functor on every actual component field fibre. The full character kernel
and the component torus are unchanged when the character is negated. -/
theorem dynamicOppositeUnipotent_fibre_eq_subgroup (ν : cocharacterLattice T)
    (hpos : 0 < latticePairing T a ν) :
    Dynamic.unipotent
        (Dynamic.baseChangeCocharacter b
          (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of R)) (-1)) ≫
            (CommGroupScheme.groupHom ν ≫ D.torus hT))) =
      RelativeRoot.subgroup ((baseChange b).map (D.torus hT))
        (-characterLattice.baseChange b T a) := by
  rw [D.opposite_torusCocharacter, Dynamic.unipotent_eq_comap_of_iso _ (D.fibreIso b),
    D.cocharacter_fibreIso]
  have hp : 0 < latticePairing ((CommGroupScheme.baseChange b).obj T)
      (-characterLattice.baseChange b T a) (-cocharacterLattice.baseChange b T ν) := by
    simpa only [map_neg, LinearMap.neg_apply, neg_neg, latticePairing_baseChange] using hpos
  have hu := RelativeRoot.kernelCentralizerIdentity_dynamicUnipotent_eq_subgroup
    (T := (CommGroupScheme.baseChange b).obj T)
    (G := (baseChange b).obj M.group) (C := (baseChange b).obj D.fullGroup)
    ((baseChange b).map i) (hT.baseChange b) (-characterLattice.baseChange b T a)
    (neg_ne_zero.mpr (character_fibre_ne_zero b ν hpos)) ((baseChange b).map D.fullHom)
    (by simpa only [RelativeRoot.kernelCentralizer_neg] using D.fullFibreRepresents b)
    (-cocharacterLattice.baseChange b T ν) hp
  rw [RelativeRoot.kernelCentralizerIdentityTorus_neg] at hu
  rw [map_neg, hu]
  simpa only [characterLattice.congr_apply, Iso.refl_inv, Category.id_comp] using
    RelativeRoot.subgroup_comap_of_transport
      (Iso.refl ((CommGroupScheme.baseChange b).obj T)) (D.fibreIso b)
      (i := (baseChange b).map (D.torus hT))
      (by
        change _ = 𝟙 _ ≫ _
        rw [Category.id_comp]
        exact D.torus_fibreIso b hT)
      (-characterLattice.baseChange b T a)

/-- The opposite dynamic subgroup maps onto the negative ambient root
functor through the same actual component and full-centralizer inclusions. -/
theorem dynamicOppositeUnipotent_fibre_map (ν : cocharacterLattice T)
    (hpos : 0 < latticePairing T a ν) :
    (Dynamic.unipotent
      (Dynamic.baseChangeCocharacter b
        (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of R)) (-1)) ≫
          (CommGroupScheme.groupHom ν ≫ D.torus hT)))).map
        ((baseChange b).map (D.componentHom ≫ D.fullHom)) =
      RelativeRoot.subgroup ((baseChange b).map i) (-characterLattice.baseChange b T a) := by
  obtain ⟨hqc, hflat, hsurj⟩ := RelativeRoot.characterFpqc k
    ((CommGroupScheme.baseChange b).obj T) (hT.baseChange b)
    (-characterLattice.baseChange b T a) (neg_ne_zero.mpr (character_fibre_ne_zero b ν hpos))
  have hrep : (RelativeRoot.kernelCentralizer ((baseChange b).map i)
      (-characterLattice.baseChange b T a)).IsRepresentedBy
        ((baseChange b).map D.fullHom) := by
    simpa only [RelativeRoot.kernelCentralizer_neg] using D.fullFibreRepresents b
  have hm := RelativeRoot.kernelCentralizerIdentity_subgroup_map
    (T := (CommGroupScheme.baseChange b).obj T)
    (G := (baseChange b).obj M.group) (C := (baseChange b).obj D.fullGroup)
    ((baseChange b).map i) (hT.baseChange b) (-characterLattice.baseChange b T a)
    ((baseChange b).map D.fullHom) hrep (D.fullClosed.baseChange b)
  rw [RelativeRoot.kernelCentralizerIdentityTorus_neg] at hm
  rw [D.dynamicOppositeUnipotent_fibre_eq_subgroup hT b ν hpos]
  have ht := RelativeRoot.subgroup_comap_of_transport
    (Iso.refl ((CommGroupScheme.baseChange b).obj T)) (D.fibreIso b)
    (i := (baseChange b).map (D.torus hT))
    (j := RelativeRoot.kernelCentralizerIdentityTorus
      (T := (CommGroupScheme.baseChange b).obj T)
      (G := (baseChange b).obj M.group) (C := (baseChange b).obj D.fullGroup)
      ((baseChange b).map i) (hT.baseChange b) (characterLattice.baseChange b T a)
      ((baseChange b).map D.fullHom) (D.fullFibreRepresents b))
    (by
      change _ = 𝟙 _ ≫ _
      rw [Category.id_comp]
      exact D.torus_fibreIso b hT)
    (-characterLattice.baseChange b T a)
  simp only [characterLattice.congr_apply, Iso.refl_inv, Category.id_comp] at ht
  rw [← ht, Functor.map_comp, ← D.fibreIso_hom_comp b, Category.assoc,
    ← SubgroupFunctor.map_comp, map_comap_iso]
  exact hm

omit b in
include hT in
/-- A nonzero integral character admits a positively pairing integral
cocharacter whose generic fibre is generic for the supplied ambient torus.
No extra cocharacter-spreading premise is needed. -/
theorem exists_integralCocharacter_pairing_pos (ha : a ≠ 0) :
    ∃ ν : cocharacterLattice T, 0 < latticePairing T a ν ∧
      IsGenericCocharacter ((baseChange (Spec.algebraMap R K)).map i)
        (cocharacterLattice.baseChange (Spec.algebraMap R K) T ν) := by
  let b := Spec.algebraMap R K
  have : IsAffineHom M.genericFibre.X.hom :=
    inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd M.group.X.hom b))
  have : LocallyOfFiniteType M.genericFibre.X.hom :=
    inferInstanceAs (LocallyOfFiniteType
      (CategoryTheory.Limits.pullback.snd M.group.X.hom b))
  have haK : characterLattice.baseChange b T a ≠ 0 := by
    intro hz
    apply ha
    apply (hT.characterLattice_baseChange_bijective b T).injective
    exact hz.trans (map_zero _).symm
  obtain ⟨νK, hgen, hpos⟩ := RelativeRoot.exists_genericCocharacter_pairing_pos
    (T := (CommGroupScheme.baseChange b).obj T) (H := M.genericFibre)
    ((baseChange b).map i) (hT.baseChange b) haK
  obtain ⟨ν, hν⟩ := (hT.cocharacterLattice_baseChange_bijective b T).surjective νK
  refine ⟨ν, ?_, ?_⟩
  · rw [← latticePairing_baseChange b T a ν, hν]
    exact hpos
  · rwa [hν]

end KernelCentralizerData

end Langlands.GroupScheme.IntegralModel
