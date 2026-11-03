import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.Dynamic.BaseChange
import Langlands.GroupScheme.Reductive.Basic

/-! # Base change of represented subgroup functors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S S' : Scheme.{u}} (b : S' ⟶ S)
variable {G H : GroupScheme S}

namespace SubgroupFunctor

/-- The pullback point equivalence restricts to the base-changed subgroup. -/
def baseChangeCarrierEquiv (F : SubgroupFunctor G) (T : Over S') :
    (F.baseChange b).carrier T ≃* F.carrier ((Over.map b).obj T) where
  toFun x := ⟨baseChangePointsEquiv b G T x, x.property⟩
  invFun x := ⟨(baseChangePointsEquiv b G T).symm x, by
    change baseChangePointsEquiv b G T ((baseChangePointsEquiv b G T).symm x) ∈
      F.carrier ((Over.map b).obj T)
    simpa only [MulEquiv.apply_symm_apply] using x.property⟩
  left_inv x := Subtype.ext ((baseChangePointsEquiv b G T).left_inv x)
  right_inv x := Subtype.ext ((baseChangePointsEquiv b G T).right_inv x)
  map_mul' x y := Subtype.ext ((baseChangePointsEquiv b G T).map_mul x y)

@[simp]
theorem baseChangeCarrierEquiv_coe (F : SubgroupFunctor G) (T : Over S')
    (x : (F.baseChange b).carrier T) :
    (baseChangeCarrierEquiv b F T x).val = baseChangePointsEquiv b G T x :=
  rfl

/-- The pointwise range of a group homomorphism commutes with arbitrary base change. -/
theorem range_baseChangeHom (f : H ⟶ G) :
    range ((GroupScheme.baseChange b).map f) = (range f).baseChange b := by
  ext T x
  rw [mem_baseChange, mem_range, mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨baseChangePointsEquiv b H T y, (baseChangePointsEquiv_comp b f T y).symm⟩
  · rintro ⟨y, hy⟩
    refine ⟨(baseChangePointsEquiv b H T).symm y, ?_⟩
    apply (baseChangePointsEquiv b G T).injective
    rw [baseChangePointsEquiv_comp, MulEquiv.apply_symm_apply, hy]

@[simp]
theorem top_baseChange :
    (⊤ : SubgroupFunctor G).baseChange b = ⊤ := by
  ext T x
  exact Iff.rfl

@[simp]
theorem bot_baseChange :
    (⊥ : SubgroupFunctor G).baseChange b = ⊥ := by
  ext T x
  change baseChangePointsEquiv b G T x = 1 ↔ x = 1
  exact (baseChangePointsEquiv b G T).map_eq_one_iff

theorem inf_baseChange (F F' : SubgroupFunctor G) :
    (F ⊓ F').baseChange b = F.baseChange b ⊓ F'.baseChange b := by
  ext T x
  exact Iff.rfl

/-- Normalization is preserved on every test scheme by base change. -/
theorem IsNormalizedBy.baseChange {F F' : SubgroupFunctor G}
    (h : F.IsNormalizedBy F') : (F.baseChange b).IsNormalizedBy (F'.baseChange b) := by
  intro T g x hg hx
  change baseChangePointsEquiv b G T (g * x * g⁻¹) ∈ F.carrier _
  rw [map_mul, map_mul, map_inv]
  exact h _ _ _ hg hx

/-- A normal subgroup functor remains normal after arbitrary base change. -/
theorem IsNormal.baseChange {F : SubgroupFunctor G} (h : F.IsNormal) :
    (F.baseChange b).IsNormal := by
  simpa only [IsNormal, top_baseChange] using (IsNormalizedBy.baseChange b h)

/-- The base-changed inclusion represents the base-changed subgroup functor. -/
theorem IsRepresentedBy.baseChange {F : SubgroupFunctor G} {f : H ⟶ G}
    (hf : F.IsRepresentedBy f) :
    (F.baseChange b).IsRepresentedBy ((GroupScheme.baseChange b).map f) := by
  refine ⟨?_, ?_⟩
  · let : Mono f.hom.hom := hf.1
    change Mono ((Over.pullback b).map f.hom.hom)
    infer_instance
  · rw [range_baseChangeHom, hf.2]

end SubgroupFunctor

/-- Closed subgroup inclusions remain closed after arbitrary base change. -/
theorem IsClosedSubgroup.baseChange {f : H ⟶ G} (hf : IsClosedSubgroup f) :
    IsClosedSubgroup ((GroupScheme.baseChange b).map f) := by
  have houter : IsPullback
      (((GroupScheme.baseChange b).map f).hom.hom.left ≫ pullback.snd G.X.hom b)
      (pullback.fst H.X.hom b) b (f.hom.hom.left ≫ G.X.hom) := by
    change IsPullback (((Over.pullback b).map f.hom.hom).left ≫ _) _ _ _
    simpa only [Over.w f.hom.hom, Over.pullback_map_left, pullback.lift_snd] using
      (IsPullback.of_hasPullback H.X.hom b).flip
  have hp := houter.of_right
    (show ((GroupScheme.baseChange b).map f).hom.hom.left ≫ pullback.fst G.X.hom b =
        pullback.fst H.X.hom b ≫ f.hom.hom.left by
      change ((Over.pullback b).map f.hom.hom).left ≫ _ = _
      simp only [Over.pullback_map_left, pullback.lift_fst])
    (IsPullback.of_hasPullback G.X.hom b).flip
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) hp.flip hf

namespace Dynamic

/-- A representative of a dynamic centralizer remains a representative after base change. -/
theorem isRepresentedBy_centralizer_baseChange
    (χ : (Gm S).toGrp ⟶ G) {f : H ⟶ G}
    (hf : (centralizer χ).IsRepresentedBy f) :
    (centralizer (baseChangeCocharacter b χ)).IsRepresentedBy
      ((GroupScheme.baseChange b).map f) := by
  rw [centralizer_baseChange]
  exact hf.baseChange b

end Dynamic
end Langlands.GroupScheme
