import Langlands.GroupScheme.Descent.SquareSemilinear
import Langlands.GroupScheme.IntegralModel.GenericRigidity

/-! # Actual coefficient twists of integral models -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

/-- Pullback along a base isomorphism gives every section of the pullback. -/
theorem baseChangeSectionHom_surjective {S : Scheme.{u}} (a : S ⟶ S) [IsIso a]
    (H : GroupScheme S) : Function.Surjective (baseChangeSectionHom a H) := by
  intro x
  let y := baseChangeBasePointsEquiv a H x
  let z : Over.mk (𝟙 S) ⟶ H.X := Over.homMk (inv a ≫ y.left) (by
    rw [Category.assoc, y.w]
    exact IsIso.inv_hom_id a)
  refine ⟨z, ?_⟩
  apply (baseChangeBasePointsEquiv a H).injective
  apply Over.OverMorphism.ext
  change (baseChangeSectionHom a H z).left ≫ pullback.fst H.X.hom a = y.left
  rw [baseChangeSectionHom_fst]
  change a ≫ inv a ≫ y.left = y.left
  simp

namespace IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (N : IntegralModel R K G)
  (a : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R))
  (v : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K))
  (hvc : v ≫ Spec.algebraMap R K = Spec.algebraMap R K ≫ a)

/-- The actual integral and generic coefficient twist, using their commuting
square to identify the prescribed generic fibre. -/
def twist : IntegralModel R K ((GroupScheme.baseChange v).obj G) where
  group := (GroupScheme.baseChange a).obj N.group
  affine := MorphismProperty.pullback_snd _ _ N.affine
  flat := MorphismProperty.pullback_snd _ _ N.flat
  finiteType := MorphismProperty.pullback_snd _ _ N.finiteType
  genericIso :=
    (Descent.squareComparison (Spec.algebraMap R K) v a (Spec.algebraMap R K)
      hvc N.group).symm ≪≫ (GroupScheme.baseChange v).mapIso N.genericIso

/-- Smoothness is preserved by coefficient twisting. -/
theorem isSmooth_twist (hN : N.IsSmooth) : (N.twist a v hvc).IsSmooth := by
  let : Smooth N.group.X.hom := hN
  exact inferInstanceAs (Smooth (pullback.snd N.group.X.hom a))

/-- A compatible homomorphism out of the actual twist is exactly the generic
semilinear law used in descent comparisons. -/
theorem Hom.twist_generic_comm {H : GroupScheme (Spec (CommRingCat.of K))}
    {M : IntegralModel R K H} {f : (GroupScheme.baseChange v).obj G ⟶ H}
    (φ : (N.twist a v hvc).Hom M f) :
    (GroupScheme.baseChange v).map N.genericIso.hom ≫ f =
      (Descent.squareComparison (Spec.algebraMap R K) v a (Spec.algebraMap R K)
        hvc N.group).hom ≫
          (GroupScheme.baseChange (Spec.algebraMap R K)).map φ.hom ≫ M.genericIso.hom := by
  have h := congrArg
    (fun g => (Descent.squareComparison (Spec.algebraMap R K) v a
      (Spec.algebraMap R K) hvc N.group).hom ≫ g) φ.generic_comm
  simpa only [twist, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc] using h.symm

/-- Opposite generic extensions produce an actual isomorphism from the twist,
with its exact generic semilinear law. -/
def twistIso {H : GroupScheme (Spec (CommRingCat.of K))}
    {M : IntegralModel R K H} (f : (GroupScheme.baseChange v).obj G ≅ H)
    (φ : (N.twist a v hvc).Hom M f.hom)
    (ψ : M.Hom (N.twist a v hvc) f.inv) :
    (N.twist a v hvc).Iso M f :=
  Iso.ofHoms φ ψ

theorem twistIso_generic_comm {H : GroupScheme (Spec (CommRingCat.of K))}
    {M : IntegralModel R K H} (f : (GroupScheme.baseChange v).obj G ≅ H)
    (φ : (N.twist a v hvc).Hom M f.hom)
    (ψ : M.Hom (N.twist a v hvc) f.inv) :
    (GroupScheme.baseChange v).map N.genericIso.hom ≫ f.hom =
      (Descent.squareComparison (Spec.algebraMap R K) v a (Spec.algebraMap R K)
        hvc N.group).hom ≫
          (GroupScheme.baseChange (Spec.algebraMap R K)).map
            (N.twistIso a v hvc f φ ψ).iso.hom ≫ M.genericIso.hom :=
  Hom.twist_generic_comm N a v hvc φ

end IntegralModel
end Langlands.GroupScheme
