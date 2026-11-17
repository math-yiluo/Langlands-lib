import Langlands.GroupScheme.Rational.AffineIntrinsicWeight

/-! # Reflection of intrinsic weights along closed equivariant inclusions -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Corepresented

variable {R : CommRingCat.{u}} {F F' : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B B' : CommAlgCat.{u} R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  (e' : (F' ⋙ forget GrpCat).CorepresentableBy B')
  {I : Type u} [Fintype I] [DecidableEq I]
  (σ : TorusAction F I) (σ' : TorusAction F' I)
  (α : F ⟶ F') (hα : TorusAction.IsEquivariant σ σ' α)

include hα in
/-- Every weight component commutes with the actual equivariant pullback. -/
theorem comp_transformationPullback (m : I → ℤ) (g : B') :
    comp e σ m (transformationPullback e e' α g) =
      transformationPullback e e' α (comp e' σ' m g) := by
  have hhat : α.app (laurent I B) (hat σ (univ e)) =
      hat σ' (α.app B (univ e)) := by
    change α.app _ (σ.act (universalUnits I B) (F.map (constHom I B) (univ e))) = _
    rw [hα]
    have hn := ConcreteCategory.congr_hom (α.naturality (constHom I B)) (univ e)
    exact congrArg (σ'.act (universalUnits I B)) hn
  have hr : rho e σ (transformationPullback e e' α g) =
      AddMonoidAlgebra.mapAlgHom (I → ℤ) (transformationPullback e e' α) (rho e' σ' g) := by
    rw [rho, ← AlgHom.comp_apply, ← coord_transformation e e' α (hat σ (univ e)),
      hhat, coord_hat, AlgHom.comp_apply]
    rfl
  rw [comp_apply, hr, AddMonoidAlgebra.coeff_mapAlgHom, comp_apply]

include hα in
/-- An equivariant algebra-surjective closed inclusion reflects every intrinsic
weight condition, over arbitrary coefficient rings. -/
theorem mem_weightSubgroup_iff_of_pullback_surjective
    (hsurj : Function.Surjective (transformationPullback e e' α))
    (P : AddSubsemigroup (I → ℤ)) {A : CommAlgCat.{u} R} (x : F.obj A) :
    α.app A x ∈ weightSubgroup e' σ' P A ↔ x ∈ weightSubgroup e σ P A := by
  constructor
  · intro hx g m hm
    obtain ⟨g', rfl⟩ := hsurj g
    have h := hx g' m hm
    rw [coord_transformation e e' α, AlgHom.comp_apply] at h
    rw [comp_transformationPullback e e' σ σ' α hα,
      counit_transformationPullback]
    exact h
  · exact map_mem_weightSubgroup_of_equivariant e e' σ σ' α hα P

include hα in
/-- The same reflection holds on every scheme test of the actual models. -/
theorem groupSchemeMap_mem_weightSubgroup_iff_of_pullback_surjective
    (hsurj : Function.Surjective (transformationPullback e e' α))
    (P : AddSubsemigroup (I → ℤ)) {T : Over (Spec R)}
    (x : T ⟶ (groupScheme F e).X) :
    x ≫ (groupSchemeMap e e' α).hom.hom ∈
        (cutSubgroupFunctor (isCutOutBy_weightIdeal e' σ' P)).carrier T ↔
      x ∈ (cutSubgroupFunctor (isCutOutBy_weightIdeal e σ P)).carrier T := by
  rw [mem_cutSubgroupFunctor, mem_cutSubgroupFunctor, groupSchemeMap_points]
  exact mem_weightSubgroup_iff_of_pullback_surjective e e' σ σ' α hα hsurj P _

end Langlands.GroupScheme.Corepresented

namespace Langlands.GroupScheme.AffineCorepresentation

open Corepresented

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
  {B B' : CommAlgCat.{u} R}
  (ψ : (algSpec R).obj (op B) ≅ G.X)
  (ψ' : (algSpec R).obj (op B') ≅ H.X)
  (f : G ⟶ H)

/-- The actual coordinate pullback of a closed immersion is surjective. -/
theorem transformationPullback_surjective_of_isClosedSubgroup
    (hf : IsClosedSubgroup f) :
    Function.Surjective (transformationPullback (corep G ψ) (corep H ψ')
      (affinePointsTransformation f)) := by
  let α := affinePointsTransformation f
  let φ := transformationPullback (corep G ψ) (corep H ψ') α
  have he : (groupSchemeMap (corep G ψ) (corep H ψ') α).hom.hom.left =
      ψ.hom.left ≫ f.hom.hom.left ≫ ψ'.inv.left := by
    have h := congrArg (fun a => a.hom.hom.left) (toModel_map ψ ψ' f)
    change ψ.inv.left ≫ (groupSchemeMap (corep G ψ) (corep H ψ') α).hom.hom.left =
      f.hom.hom.left ≫ ψ'.inv.left at h
    have h' := congrArg (fun a => ψ.hom.left ≫ a) h
    simpa only [← Category.assoc, ← Over.comp_left, Iso.hom_inv_id,
      Over.id_left, Category.id_comp] using h'
  let : IsClosedImmersion f.hom.hom.left := hf
  let : IsIso ψ.hom.left := inferInstanceAs (IsIso ((Over.forget _).map ψ.hom))
  let : IsIso ψ'.inv.left := inferInstanceAs (IsIso ((Over.forget _).map ψ'.inv))
  have hm : IsClosedImmersion (groupSchemeMap (corep G ψ) (corep H ψ') α).hom.hom.left := by
    rw [he]
    infer_instance
  have hs : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) := hm
  let := hs
  have hsurj := (IsClosedImmersion.isAffine_surjective_of_isAffine
    (Spec.map (CommRingCat.ofHom φ.toRingHom))).2
  intro b
  obtain ⟨s, hs⟩ := hsurj ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of B')).hom s, ?_⟩
  have hn := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ.toRingHom)) s
  change (Scheme.ΓSpecIso (CommRingCat.of B)).hom
    ((Spec.map (CommRingCat.ofHom φ.toRingHom)).appTop s) =
      φ ((Scheme.ΓSpecIso (CommRingCat.of B')).hom s) at hn
  change φ ((Scheme.ΓSpecIso (CommRingCat.of B')).hom s) = b
  rw [← hn, hs]
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of B)).inv_hom_id b

variable {I : Type u} [Fintype I] [DecidableEq I]

/-- The intrinsic weight subgroup pulled back along an actual group map. -/
def intrinsicWeightPreimage (σ' : TorusAction H.affinePointFunctor I)
    (P : AddSubsemigroup (I → ℤ)) : SubgroupFunctor G :=
  (intrinsicWeightSubgroup ψ' σ' P).comap f

/-- An actual closed equivariant inclusion reflects all intrinsic weight
conditions on every scheme test, in any supplied affine presentations. -/
theorem intrinsicWeightPreimage_eq_of_isClosedSubgroup
    (hf : IsClosedSubgroup f)
    (σ : TorusAction G.affinePointFunctor I) (σ' : TorusAction H.affinePointFunctor I)
    (heq : TorusAction.IsEquivariant σ σ' (affinePointsTransformation f))
    (P : AddSubsemigroup (I → ℤ)) :
    intrinsicWeightPreimage ψ' f σ' P = intrinsicWeightSubgroup ψ σ P := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  have h := groupSchemeMap_mem_weightSubgroup_iff_of_pullback_surjective
    (corep G ψ) (corep H ψ') σ σ' (affinePointsTransformation f) heq
    (transformationPullback_surjective_of_isClosedSubgroup ψ ψ' f hf) P
    (x ≫ (toModel G ψ).hom.hom)
  change ((x ≫ (toModel G ψ).hom.hom) ≫
    (groupSchemeMap (corep G ψ) (corep H ψ') (affinePointsTransformation f)).hom.hom ∈ _) ↔ _ at h
  rw [Category.assoc, ← Grp.comp_hom_hom, toModel_map ψ ψ' f,
    Grp.comp_hom_hom, ← Category.assoc] at h
  exact h

end Langlands.GroupScheme.AffineCorepresentation
