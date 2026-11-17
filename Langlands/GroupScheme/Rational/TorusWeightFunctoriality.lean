import Langlands.GroupScheme.Rational.CyclicWeightConjugation

/-! # Intrinsic weight subgroups and equivariant natural homomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Corepresented

variable {R : CommRingCat.{u}} {F F' : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B B' : CommAlgCat.{u} R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  (e' : (F' ⋙ forget GrpCat).CorepresentableBy B')
  {I : Type u} [Fintype I] [DecidableEq I]
  (σ : TorusAction F I) (σ' : TorusAction F' I)

/-- Equivariance of an actual natural group homomorphism for split-torus actions,
required over every algebra of the original base ring. -/
def TorusAction.IsEquivariant (α : F ⟶ F') : Prop :=
  ∀ {A : CommAlgCat.{u} R} (s : I → Aˣ) (x : F.obj A),
    α.app A (σ.act s x) = σ'.act s (α.app A x)

/-- The classifying algebra homomorphism of the image of the universal point. -/
def transformationPullback (α : F ⟶ F') : B' →ₐ[R] B :=
  coord e' (α.app B (univ e))

/-- Naturality identifies every coordinate pullback with the universal one. -/
theorem coord_transformation (α : F ⟶ F') {A : CommAlgCat.{u} R} (x : F.obj A) :
    coord e' (α.app A x) = (coord e x).comp (transformationPullback e e' α) := by
  have h := ConcreteCategory.congr_hom (α.naturality (e.homEquiv.symm x)) (univ e)
  change α.app A (F.map (e.homEquiv.symm x) (univ e)) =
    F'.map (e.homEquiv.symm x) (α.app B (univ e)) at h
  rw [← eq_map_univ e x] at h
  rw [h, coord_map]
  rfl

/-- An equivariant natural group map pulls a homogeneous function back to the
same character, even when the two corepresenting algebras differ. -/
theorem isHomogeneous_transformationPullback (α : F ⟶ F')
    (hα : TorusAction.IsEquivariant σ σ' α)
    {m : I → ℤ} {g : B'} (hg : IsHomogeneous e' σ' m g) :
    IsHomogeneous e σ m (transformationPullback e e' α g) := by
  have hhat : α.app (laurent I B) (hat σ (univ e)) =
      hat σ' (α.app B (univ e)) := by
    change α.app _ (σ.act (universalUnits I B) (F.map (constHom I B) (univ e))) = _
    rw [hα]
    have hn := ConcreteCategory.congr_hom (α.naturality (constHom I B)) (univ e)
    exact congrArg (σ'.act (universalUnits I B)) hn
  change rho e σ (transformationPullback e e' α g) =
    AddMonoidAlgebra.single m (transformationPullback e e' α g)
  rw [rho, ← AlgHom.comp_apply, ← coord_transformation e e' α (hat σ (univ e)),
    hhat, coord_hat, AlgHom.comp_apply, hg, AddMonoidAlgebra.mapAlgHom_single]
  rfl

/-- Pullback through a natural group map preserves the identity augmentation. -/
theorem counit_transformationPullback (α : F ⟶ F') (g : B') :
    AffineLinearEmbedding.counit e (transformationPullback e e' α g) =
      AffineLinearEmbedding.counit e' g := by
  have h := congrArg (fun f : B' →ₐ[R] R => f g)
    (coord_transformation e e' α (1 : F.obj (CommAlgCat.of R R)))
  simpa [coord_one, AlgHom.comp_apply] using h.symm

/-- Every intrinsic weight subgroup is functorial for equivariant natural group
maps over arbitrary commutative coefficient rings. -/
theorem map_mem_weightSubgroup_of_equivariant (α : F ⟶ F')
    (hα : TorusAction.IsEquivariant σ σ' α) (P : AddSubsemigroup (I → ℤ))
    {A : CommAlgCat.{u} R} {x : F.obj A} (hx : x ∈ weightSubgroup e σ P A) :
    α.app A x ∈ weightSubgroup e' σ' P A := by
  intro f m hm
  have hg := isHomogeneous_transformationPullback e e' σ σ' α hα
    (isHomogeneous_comp e' σ' m f)
  have hs := (mem_weightSubgroup e σ P x).1 hx
    (transformationPullback e e' α (comp e' σ' m f)) m hm
  rw [hg.comp_self, counit_transformationPullback] at hs
  rw [coord_transformation e e' α, AlgHom.comp_apply, hs]

/-- Forward equivariance of a natural group isomorphism also gives inverse
 equivariance; no separate inverse compatibility is required. -/
theorem TorusAction.IsEquivariant.inverse (η : F ≅ F')
    (hη : TorusAction.IsEquivariant σ σ' η.hom) :
    TorusAction.IsEquivariant σ' σ η.inv := by
  intro A s x
  apply (ConcreteCategory.bijective_of_isIso (η.hom.app A)).1
  have hi (y : F'.obj A) : η.hom.app A (η.inv.app A y) = y :=
    ConcreteCategory.congr_hom (η.app A).inv_hom_id y
  rw [hi, hη, hi]

/-- A natural equivariant group isomorphism identifies the intrinsic weight
subgroups, independently of the chosen corepresenting algebra. -/
theorem mem_weightSubgroup_iso_iff (η : F ≅ F')
    (hη : TorusAction.IsEquivariant σ σ' η.hom) (P : AddSubsemigroup (I → ℤ))
    {A : CommAlgCat.{u} R} (x : F.obj A) :
    η.hom.app A x ∈ weightSubgroup e' σ' P A ↔ x ∈ weightSubgroup e σ P A := by
  constructor
  · intro hx
    have h := map_mem_weightSubgroup_of_equivariant e' e σ' σ η.inv
      (TorusAction.IsEquivariant.inverse σ σ' η hη) P hx
    have hi : η.inv.app A (η.hom.app A x) = x :=
      ConcreteCategory.congr_hom (η.app A).hom_inv_id x
    rwa [hi] at h
  · exact map_mem_weightSubgroup_of_equivariant e e' σ σ' η.hom hη P

/-- The induced actual scheme homomorphism preserves intrinsic weight subgroup
functors on every scheme test, with no affineness hypothesis on the test. -/
theorem groupSchemeMap_mem_weightSubgroup (α : F ⟶ F')
    (hα : TorusAction.IsEquivariant σ σ' α) (P : AddSubsemigroup (I → ℤ))
    {T : Over (Spec R)} {x : T ⟶ (groupScheme F e).X}
    (hx : x ∈ (cutSubgroupFunctor (isCutOutBy_weightIdeal e σ P)).carrier T) :
    x ≫ (groupSchemeMap e e' α).hom.hom ∈
      (cutSubgroupFunctor (isCutOutBy_weightIdeal e' σ' P)).carrier T := by
  rw [mem_cutSubgroupFunctor] at hx ⊢
  rw [groupSchemeMap_points]
  exact map_mem_weightSubgroup_of_equivariant e e' σ σ' α hα P hx

/-- On arbitrary scheme tests, the induced isomorphism identifies the actual
intrinsic subgroup functors. -/
theorem groupSchemeMap_mem_weightSubgroup_iso_iff (η : F ≅ F')
    (hη : TorusAction.IsEquivariant σ σ' η.hom) (P : AddSubsemigroup (I → ℤ))
    {T : Over (Spec R)} (x : T ⟶ (groupScheme F e).X) :
    x ≫ (groupSchemeMap e e' η.hom).hom.hom ∈
      (cutSubgroupFunctor (isCutOutBy_weightIdeal e' σ' P)).carrier T ↔
    x ∈ (cutSubgroupFunctor (isCutOutBy_weightIdeal e σ P)).carrier T := by
  rw [mem_cutSubgroupFunctor, mem_cutSubgroupFunctor, groupSchemeMap_points]
  exact mem_weightSubgroup_iso_iff e e' σ σ' η hη P _

end Langlands.GroupScheme.Corepresented
