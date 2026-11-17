import Langlands.GroupScheme.Reductive.AffinePinnedModel
import Langlands.GroupScheme.Rational.CrossTorusLieTransport

/-! # Actual exponent-weight transport for affine pinned comparisons -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.splitTorus

variable {R : CommRingCat.{u}}
    {I I' : Type u} [Fintype I] [Fintype I']
    {G H : GroupScheme (Spec R)} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    {i : splitTorus (Spec R) I ⟶ G} {i' : splitTorus (Spec R) I' ⟶ H}

/-- A monomial identity on every scheme test gives its affine algebra-point identity. -/
theorem exponentValue_transport_of_points
    (tau : splitTorus (Spec R) I ≅ splitTorus (Spec R) I')
    (n : I → ℤ) (m : I' → ℤ)
    (h : ∀ (U : Over (Spec R)) (x : U ⟶ (splitTorus (Spec R) I).X),
      (∏ j', pointsEquiv I' U (x ≫ tau.hom.hom.hom) j' ^ m j') =
        ∏ j, pointsEquiv I U x j ^ n j)
    (A : Type u) [CommRing A] [Algebra R A]
    (x : Lie.AffinePoints (splitTorus (Spec R) I) A) :
    exponentValue I' (algebraPointsEquiv I' A (x ≫ tau.hom.hom.hom))
        (Multiplicative.ofAdd m) =
      exponentValue I (algebraPointsEquiv I A x) (Multiplicative.ofAdd n) := by
  let F := Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom
  change (∏ j', F (pointsEquiv I' _ (x ≫ tau.hom.hom.hom) j') ^ m j') =
    ∏ j, F (pointsEquiv I _ x j) ^ n j
  simpa only [map_prod, map_zpow] using congrArg F (h _ x)

/-- A compatible group map carries an actual exponent weight to the matching target weight. -/
theorem mem_exponentWeightSpace_of_transport
    (phi : G ⟶ H) (tau : splitTorus (Spec R) I ≅ splitTorus (Spec R) I')
    (hsquare : i ≫ phi = tau.hom ≫ i') (n : I → ℤ) (m : I' → ℤ)
    (hchar : ∀ (A : Type u) [CommRing A] [Algebra R A]
      (x : Lie.AffinePoints (splitTorus (Spec R) I) A),
      exponentValue I' (algebraPointsEquiv I' A (x ≫ tau.hom.hom.hom))
          (Multiplicative.ofAdd m) =
        exponentValue I (algebraPointsEquiv I A x) (Multiplicative.ofAdd n))
    {X : Additive (lieKernel G R)} (hX : X ∈ exponentWeightSpace I G i n) :
    Lie.targetMapLinear phi R X ∈ exponentWeightSpace I' H i' m := by
  intro A _ _ t'
  let y := (algebraPointsEquiv (R := R) I' A).symm t'
  let x := y ≫ tau.inv.hom.hom
  have hxy : x ≫ tau.hom.hom.hom = y := by
    dsimp only [x]
    rw [Category.assoc, ← Grp.comp_hom_hom, tau.inv_hom_id,
      Grp.id_hom_hom, Category.comp_id]
  have hx := hX A (algebraPointsEquiv I A x)
  rw [MulEquiv.symm_apply_apply] at hx
  have hs : (x ≫ i.hom.hom) ≫ phi.hom.hom = y ≫ i'.hom.hom := by
    rw [Category.assoc, ← Grp.comp_hom_hom, hsquare, Grp.comp_hom_hom,
      ← Category.assoc, hxy]
  have he := hchar A x
  rw [hxy] at he
  change exponentValue I' (algebraPointsEquiv I' A ((algebraPointsEquiv I' A).symm t'))
    (Multiplicative.ofAdd m) = _ at he
  rw [MulEquiv.apply_symm_apply] at he
  rw [← lieKernelHomLinear_map]
  change adjoint H A (y ≫ i'.hom.hom) _ = _
  rw [← hs, ← lieKernelHomLinear_adjoint, hx, LinearMap.map_smul, ← he]

omit [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] in
/-- The inverse square follows from the original square of actual group isomorphisms. -/
theorem inverse_torus_square
    (phi : G ≅ H) (tau : splitTorus (Spec R) I ≅ splitTorus (Spec R) I')
    (hsquare : i ≫ phi.hom = tau.hom ≫ i') :
    i' ≫ phi.inv = tau.inv ≫ i := by
  rw [Iso.comp_inv_eq, Category.assoc, hsquare, ← Category.assoc,
    tau.inv_hom_id, Category.id_comp]

/-- The full actual exponent weight spaces are linearly equivalent under a compatible
ambient group isomorphism and the given monomial identity. -/
def exponentWeightSpaceTransportEquiv
    (phi : G ≅ H) (tau : splitTorus (Spec R) I ≅ splitTorus (Spec R) I')
    (hsquare : i ≫ phi.hom = tau.hom ≫ i') (n : I → ℤ) (m : I' → ℤ)
    (hchar : ∀ (A : Type u) [CommRing A] [Algebra R A]
      (x : Lie.AffinePoints (splitTorus (Spec R) I) A),
      exponentValue I' (algebraPointsEquiv I' A (x ≫ tau.hom.hom.hom))
          (Multiplicative.ofAdd m) =
        exponentValue I (algebraPointsEquiv I A x) (Multiplicative.ofAdd n)) :
    exponentWeightSpace I G i n ≃ₗ[R] exponentWeightSpace I' H i' m where
  toFun X := ⟨Lie.targetMapLinear phi.hom R X.val,
    mem_exponentWeightSpace_of_transport phi.hom tau hsquare n m hchar X.property⟩
  invFun Y := ⟨Lie.targetMapLinear phi.inv R Y.val, by
    apply mem_exponentWeightSpace_of_transport phi.inv tau.symm
      (inverse_torus_square phi tau hsquare) m n _ Y.property
    intro A _ _ y
    have h := hchar A (y ≫ tau.inv.hom.hom)
    rw [Category.assoc, ← Grp.comp_hom_hom, tau.inv_hom_id,
      Grp.id_hom_hom, Category.comp_id] at h
    exact h.symm⟩
  left_inv X := Subtype.ext (Lie.targetMapLinear_hom_inv phi R X.val)
  right_inv Y := Subtype.ext (Lie.targetMapLinear_inv_hom phi R Y.val)
  map_add' X Y := Subtype.ext (map_add _ X.val Y.val)
  map_smul' c X := Subtype.ext (map_smul _ c X.val)

@[simp] theorem exponentWeightSpaceTransportEquiv_apply
    (phi : G ≅ H) (tau : splitTorus (Spec R) I ≅ splitTorus (Spec R) I')
    (hsquare : i ≫ phi.hom = tau.hom ≫ i') (n : I → ℤ) (m : I' → ℤ)
    (hchar : ∀ (A : Type u) [CommRing A] [Algebra R A]
      (x : Lie.AffinePoints (splitTorus (Spec R) I) A),
      exponentValue I' (algebraPointsEquiv I' A (x ≫ tau.hom.hom.hom))
          (Multiplicative.ofAdd m) =
        exponentValue I (algebraPointsEquiv I A x) (Multiplicative.ofAdd n))
    (X : exponentWeightSpace I G i n) :
    (exponentWeightSpaceTransportEquiv phi tau hsquare n m hchar X).val =
      Lie.targetMapLinear phi.hom R X.val := rfl

end Langlands.GroupScheme.splitTorus
