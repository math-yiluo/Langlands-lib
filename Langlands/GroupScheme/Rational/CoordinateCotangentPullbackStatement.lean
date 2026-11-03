import Langlands.GroupScheme.Rational.CoordinateCotangent

/-! # Actual augmentation-cotangent pullback and equivariant weight target -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CoordinateWeights

section Construction

variable {k : Type u} [Field k]
    {G H K : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [IsAffineHom K.X.hom]

/-- The actual coordinate pullback preserves the original augmentation ideals. -/
theorem pullback_augmentationIdeal (f : G ⟶ H) :
    augmentationIdeal H ≤ (augmentationIdeal G).comap (pullback f.hom.hom) := by
  intro z hz
  change Lie.coordinateOrigin G (pullback f.hom.hom z) = 0
  rw [← AlgHom.comp_apply, pullback_origin]
  exact hz

/-- The induced pullback on the actual augmentation quotients. -/
def cotangentPullback (f : G ⟶ H) : Cotangent H →ₗ[k] Cotangent G :=
  Ideal.mapCotangent (augmentationIdeal H) (augmentationIdeal G)
    (pullback f.hom.hom) (pullback_augmentationIdeal f)

/-- The cotangent pullback is the quotient of the actual augmentation pullback. -/
@[simp] theorem cotangentPullback_mk (f : G ⟶ H) (z : augmentation H) :
    cotangentPullback f (cotangentMk H z) = cotangentMk G (augmentationPullback f z) := rfl

@[simp] theorem cotangentPullback_id :
    cotangentPullback (𝟙 G) = LinearMap.id (R := k) (M := Cotangent G) := by
  ext q
  obtain ⟨z, rfl⟩ := (augmentationIdeal G).toCotangent_surjective q
  change cotangentMk G (augmentationPullback (𝟙 G) z) = cotangentMk G z
  congr 1
  apply Subtype.ext
  change pullback (𝟙 G.X) z.val = z.val
  rw [pullback_id, AlgHom.id_apply]

/-- Cotangent pullback reverses the composition of actual group homomorphisms. -/
@[simp] theorem cotangentPullback_comp (f : G ⟶ H) (g : H ⟶ K) :
    cotangentPullback (f ≫ g) = (cotangentPullback f).comp (cotangentPullback g) := by
  ext q
  obtain ⟨z, rfl⟩ := (augmentationIdeal K).toCotangent_surjective q
  change cotangentMk G (augmentationPullback (f ≫ g) z) =
    cotangentMk G (augmentationPullback f (augmentationPullback g z))
  congr 1
  apply Subtype.ext
  change pullback (f.hom.hom ≫ g.hom.hom) z.val =
    pullback f.hom.hom (pullback g.hom.hom z.val)
  rw [pullback_comp, AlgHom.comp_apply]

/-- Actual group-scheme isomorphisms induce equivalences of actual cotangents. -/
def cotangentPullbackEquiv (e : G ≅ H) : Cotangent H ≃ₗ[k] Cotangent G :=
  LinearEquiv.ofLinearMap (cotangentPullback e.hom) (cotangentPullback e.inv)
    (by rw [← cotangentPullback_comp, e.hom_inv_id, cotangentPullback_id])
    (by rw [← cotangentPullback_comp, e.inv_hom_id, cotangentPullback_id])

end Construction

/-- Exact remaining equivariant functoriality target for the actual cotangent
weights, including support invariance under actual equivariant group isomorphisms. -/
def CotangentPullbackStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G H : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsAffineHom G.X.hom) (hH : IsAffineHom H.X.hom)
    (S : CommGroupScheme (Spec (CommRingCat.of k)))
    (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp H),
    letI := hG
    letI := hH
    (∀ (f : G ⟶ H), IsEquivariant b c f.hom.hom →
      ∀ χ : characterLattice S,
        (cotangentWeightSpace c χ).map (cotangentPullback f) ≤ cotangentWeightSpace b χ) ∧
    (∀ (e : G ≅ H), IsEquivariant b c e.hom.hom.hom →
      cotangentSupport b = cotangentSupport c)

end Langlands.GroupScheme.CoordinateWeights
