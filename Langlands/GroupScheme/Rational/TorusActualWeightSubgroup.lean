import Langlands.GroupScheme.Rational.TorusCoordinateWeights
import Langlands.GroupScheme.Rational.WeightSemigroup
import Langlands.GroupScheme.Lie.TorusCentralizer
import Langlands.GroupScheme.Torus.SplitReductiveProof

/-! # Actual coordinate weight subgroups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace Corepresented

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
    {B : CommAlgCat.{u} R}
    (c : (F ⋙ forget GrpCat).CorepresentableBy B)
    {I : Type u} [Fintype I] [DecidableEq I] (σ : TorusAction F I)

/-- Membership can be tested on homogeneous functions rather than arbitrary components. -/
theorem mem_weightSubgroup_iff_homogeneous (P : AddSubsemigroup (I → ℤ))
    {A : CommAlgCat.{u} R} (x : F.obj A) :
    x ∈ weightSubgroup c σ P A ↔
      ∀ m, m ∉ P → ∀ f, IsHomogeneous c σ m f →
        coord c x f = algebraMap R A (AffineLinearEmbedding.counit c f) := by
  rw [mem_weightSubgroup]
  constructor
  · intro hx m hm f hf
    simpa only [hf.comp_self] using hx f m hm
  · intro hx f m hm
    exact hx m hm (comp c σ m f) (isHomogeneous_comp c σ m f)

variable {c σ} in
/-- Subtracting the augmentation preserves the weight of a homogeneous coordinate. -/
theorem IsHomogeneous.sub_counit {m : I → ℤ} {f : B} (hf : IsHomogeneous c σ m f) :
    IsHomogeneous c σ m (f - algebraMap R B (AffineLinearEmbedding.counit c f)) := by
  by_cases hm : m = 0
  · subst m
    exact (homogeneousSubmodule c σ 0).sub_mem hf (isHomogeneous_algebraMap c σ _)
  · simpa only [hf.counit_eq_zero hm, map_zero, sub_zero] using hf

/-- Only homogeneous functions in the augmentation ideal are needed to test membership. -/
theorem mem_weightSubgroup_iff_augmentation (P : AddSubsemigroup (I → ℤ))
    {A : CommAlgCat.{u} R} (x : F.obj A) :
    x ∈ weightSubgroup c σ P A ↔
      ∀ m, m ∉ P → ∀ f, IsHomogeneous c σ m f →
        AffineLinearEmbedding.counit c f = 0 → coord c x f = 0 := by
  rw [mem_weightSubgroup_iff_homogeneous]
  constructor
  · intro hx m hm f hf hε
    simpa only [hε, map_zero] using hx m hm f hf
  · intro hx m hm f hf
    have hε : AffineLinearEmbedding.counit c
        (f - algebraMap R B (AffineLinearEmbedding.counit c f)) = 0 := by
      rw [map_sub, AlgHom.commutes]
      exact sub_self _
    have h := hx m hm _ hf.sub_counit hε
    rwa [map_sub, AlgHom.commutes, sub_eq_zero] at h

end Corepresented

namespace TorusActionCoordinates

section Affinization

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]

/-- The recovered group isomorphism has the original coordinate identification underneath. -/
theorem groupSchemeIso_hom :
    (groupSchemeIso G).hom.hom.hom = (Lie.coordinateIso G).hom := by
  change (yonedaGrp.map (groupSchemeIso G).hom).app
    (op (Corepresented.groupScheme G.affinePointFunctor (corepresentation G)).X) (𝟙 _) = _
  dsimp only [groupSchemeIso, AffineLinearEmbedding.modelIso,
    Functor.FullyFaithful.preimageIso]
  rw [yonedaGrpFullyFaithful.map_preimage]
  exact Category.id_comp (Lie.coordinateIso G).hom

theorem groupSchemeIso_inv :
    (groupSchemeIso G).inv.hom.hom = (Lie.coordinateIso G).inv := by
  apply (cancel_mono (Lie.coordinateIso G).hom).1
  calc
    _ = 𝟙 G.X := by
      rw [← groupSchemeIso_hom, ← Grp.comp_hom_hom, Iso.inv_hom_id]
      rfl
    _ = _ := (Lie.coordinateIso G).inv_hom_id.symm

/-- On every test scheme, the corepresented point is the actual affinization factor. -/
theorem pointsEquiv_eq_affinizationFactor {T : Over (Spec R)} (x : T ⟶ G.X) :
    Corepresented.pointsEquiv G.affinePointFunctor (corepresentation G) T
        (x ≫ (groupSchemeIso G).inv.hom.hom) = Lie.affinizationFactor G x := by
  rw [groupSchemeIso_inv]
  rfl

/-- Maps to an affine group are determined after precomposition by the affinization unit. -/
theorem unit_comp_injective (T : Over (Spec R)) :
    Function.Injective (fun y : (algSpec R).obj ((algΓ R).obj T) ⟶ G.X =>
      (algΓAlgSpecAdjunction R).unit.app T ≫ y) := by
  intro y z hyz
  have hpre :
      algSpec.fullyFaithful.preimage (y ≫ (Lie.coordinateIso G).inv) =
        algSpec.fullyFaithful.preimage (z ≫ (Lie.coordinateIso G).inv) := by
    apply ((algΓAlgSpecAdjunction R).homEquiv T (op (Lie.coordinateAlgebra G))).injective
    simpa only [Adjunction.homEquiv_unit, algSpec.fullyFaithful.map_preimage,
      ← Category.assoc] using congrArg (fun q => q ≫ (Lie.coordinateIso G).inv) hyz
  apply (cancel_mono (Lie.coordinateIso G).inv).1
  simpa only [algSpec.fullyFaithful.map_preimage] using congrArg (algSpec R).map hpre

/-- Affinization respects any actual action between affine group schemes. -/
theorem affinizationFactor_act {H : GroupScheme (Spec R)} [IsAffineHom H.X.hom]
    (a : AutomorphicAction H G) {T : Over (Spec R)} (h : T ⟶ H.X) (x : T ⟶ G.X) :
    Lie.affinizationFactor G (a.act h x) =
      a.act (Lie.affinizationFactor H h) (Lie.affinizationFactor G x) := by
  apply unit_comp_injective G T
  dsimp only
  rw [Lie.unit_affinizationFactor, a.naturality,
    Lie.unit_affinizationFactor, Lie.unit_affinizationFactor]

end Affinization

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {I : Type u} [Fintype I] [DecidableEq I]
    (b : AutomorphicAction S.toGrp G)
    (e : S.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I)

/-- Pull back an actual character semigroup to the exponent lattice of the chosen splitting. -/
def exponentSemigroup (A : AddSubsemigroup (characterLattice S)) :
    AddSubsemigroup (I → ℤ) where
  carrier := {m | PointedCoordinateWeights.characterEquiv e m ∈ A}
  add_mem' {m n} hm hn := by
    change PointedCoordinateWeights.characterEquiv e (m + n) ∈ A
    rw [map_add]
    exact A.add_mem hm hn

omit [DecidableEq I] in
@[simp] theorem mem_exponentSemigroup (A : AddSubsemigroup (characterLattice S)) (m : I → ℤ) :
    m ∈ exponentSemigroup e A ↔ PointedCoordinateWeights.characterEquiv e m ∈ A := Iff.rfl

/-- The coordinate weight subgroup, indexed by the original actual character lattice. -/
abbrev weightSubgroup (A : AddSubsemigroup (characterLattice S))
    (R' : CommAlgCat.{u} (CommRingCat.of k)) : Subgroup (G.affinePoints R') :=
  Corepresented.weightSubgroup (corepresentation G) (b.toCorepresentedTorusAction e)
    (exponentSemigroup e A) R'

/-- Membership uses the original actual eigenfunctions and original augmentation. -/
theorem mem_weightSubgroup_iff_eigenfunction (A : AddSubsemigroup (characterLattice S))
    {R' : CommAlgCat.{u} (CommRingCat.of k)} (x : G.affinePoints R') :
    x ∈ weightSubgroup b e A R' ↔
      ∀ χ, χ ∉ A → ∀ f, CoordinateWeights.IsEigenfunction b χ f →
        Lie.pointCoordinates G x f = algebraMap k R' (Lie.coordinateOrigin G f) := by
  rw [Corepresented.mem_weightSubgroup_iff_homogeneous]
  constructor
  · intro hx χ hχ f hf
    obtain ⟨m, rfl⟩ := (PointedCoordinateWeights.characterEquiv e).surjective χ
    exact hx m hχ f ((isHomogeneous_iff_isEigenfunction b e m f).2 hf)
  · intro hx m hm f hf
    exact hx _ hm f ((isHomogeneous_iff_isEigenfunction b e m f).1 hf)

/-- Membership is vanishing of the actual augmentation eigenfunctions outside the semigroup. -/
theorem mem_weightSubgroup_iff_augmentation (A : AddSubsemigroup (characterLattice S))
    {R' : CommAlgCat.{u} (CommRingCat.of k)} (x : G.affinePoints R') :
    x ∈ weightSubgroup b e A R' ↔
      ∀ χ, χ ∉ A → ∀ f : CoordinateWeights.augmentation G,
        f ∈ CoordinateWeights.augmentationWeightSpace b χ → Lie.pointCoordinates G x f.val = 0 := by
  rw [Corepresented.mem_weightSubgroup_iff_augmentation]
  constructor
  · intro hx χ hχ f hf
    obtain ⟨m, rfl⟩ := (PointedCoordinateWeights.characterEquiv e).surjective χ
    exact hx m hχ f.val ((isHomogeneous_iff_isEigenfunction b e m f.val).2 hf) f.property
  · intro hx m hm f hf hε
    exact hx _ hm ⟨f, hε⟩ ((isHomogeneous_iff_isEigenfunction b e m f).1 hf)

/-- All actual acting points preserve the coordinate weight subgroup over each algebra. -/
theorem act_mem_weightSubgroup (A : AddSubsemigroup (characterLattice S))
    {R' : CommAlgCat.{u} (CommRingCat.of k)} (s : Lie.AffinePoints S.toGrp R')
    {x : G.affinePoints R'} (hx : x ∈ weightSubgroup b e A R') :
    b.act s x ∈ weightSubgroup b e A R' := by
  rw [← b.toCorepresentedTorusAction_act_point e s x]
  exact Corepresented.act_mem_weightSubgroup _ _ _ _ hx

/-- The quotient coordinate group representing the algebra weight subgroups. -/
abbrev weightGroupScheme (A : AddSubsemigroup (characterLattice S)) :
    GroupScheme (Spec (CommRingCat.of k)) :=
  Corepresented.cutGroupScheme
    (Corepresented.isCutOutBy_weightIdeal (corepresentation G)
      (b.toCorepresentedTorusAction e) (exponentSemigroup e A))

/-- The quotient-coordinate inclusion into the original actual group. -/
abbrev weightHom (A : AddSubsemigroup (characterLattice S)) :
    weightGroupScheme b e A ⟶ G :=
  Corepresented.cutHom
    (Corepresented.isCutOutBy_weightIdeal (corepresentation G)
      (b.toCorepresentedTorusAction e) (exponentSemigroup e A)) ≫ (groupSchemeIso G).hom

theorem isClosedSubgroup_weightHom (A : AddSubsemigroup (characterLattice S)) :
    IsClosedSubgroup (weightHom b e A) := by
  change IsClosedImmersion
    ((Corepresented.cutHom _).hom.hom.left ≫ (groupSchemeIso G).hom.hom.hom.left)
  infer_instance

/-- All-test range membership is exactly the original algebra-point criterion on global sections. -/
theorem mem_range_weightHom_iff (A : AddSubsemigroup (characterLattice S))
    {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ G.X) :
    x ∈ (SubgroupFunctor.range (weightHom b e A)).carrier T ↔
      Lie.affinizationFactor G x ∈ weightSubgroup b e A
        ((algΓ (CommRingCat.of k)).obj T).unop := by
  have hmem :
      x ∈ (SubgroupFunctor.range (weightHom b e A)).carrier T ↔
        x ≫ (groupSchemeIso G).inv.hom.hom ∈
          (SubgroupFunctor.range (Corepresented.cutHom
            (Corepresented.isCutOutBy_weightIdeal (corepresentation G)
              (b.toCorepresentedTorusAction e) (exponentSemigroup e A)))).carrier T := by
    rw [SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨y, ?_⟩
      simp only [weightHom, Category.assoc,
        ← Grp.comp_hom_hom, Iso.hom_inv_id, Category.comp_id]
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      rw [weightHom, Grp.comp_hom_hom, ← Category.assoc, hy, Category.assoc,
        ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  rw [hmem, Corepresented.range_cutHom, Corepresented.mem_cutSubgroupFunctor,
    pointsEquiv_eq_affinizationFactor]

/-- The quotient inclusion is stable under the original action on every scheme test. -/
theorem isStable_range_weightHom (A : AddSubsemigroup (characterLattice S)) :
    b.IsStable (SubgroupFunctor.range (weightHom b e A)) := by
  let : IsAffineHom S.toGrp.X.hom := IsSplitTorus.isAffineHom ⟨I, inferInstance, ⟨e⟩⟩
  intro T s x hx
  have hx' := (mem_range_weightHom_iff b e A x).1 hx
  apply (mem_range_weightHom_iff b e A (b.act s x)).2
  rw [affinizationFactor_act G b s x]
  exact act_mem_weightSubgroup b e A
    (R' := ((algΓ (CommRingCat.of k)).obj T).unop)
    (x := Lie.affinizationFactor G x) (Lie.affinizationFactor S.toGrp s) hx'

end TorusActionCoordinates

end Langlands.GroupScheme
