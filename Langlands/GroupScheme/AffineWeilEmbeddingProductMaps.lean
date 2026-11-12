import Langlands.GroupScheme.AffinePoints
import Langlands.GroupScheme.ProductProperties
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Actual products of base changes along embeddings, on homomorphisms -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

section PiMap

variable {S : Scheme.{u}} {I : Type u} [Finite I] {G G' : I → GroupScheme S}

/-- Each projection of the product of a family of homomorphisms is the corresponding factor
homomorphism, on the underlying morphisms over the base. -/
@[reassoc (attr := simp)]
theorem pi_map_hom_π (f : ∀ i, G i ⟶ G' i) (i : I) :
    (Limits.Pi.map f : pi G ⟶ pi G').hom.hom ≫ (Pi.π G' i).hom.hom =
      (Pi.π G i).hom.hom ≫ (f i).hom.hom := by
  have h := congrArg (fun g => g.hom.hom) (Limits.Pi.map_π f i)
  change (Limits.Pi.map f : pi G ⟶ pi G').hom.hom ≫ (Pi.π G' i).hom.hom =
    (Pi.π G i).hom.hom ≫ (f i).hom.hom at h
  exact h

/-- The product homomorphism applies the factor homomorphisms to the coordinates of a point. -/
theorem piPointsEquiv_pi_map (f : ∀ i, G i ⟶ G' i) (T : Over S) (x : T ⟶ (pi G).X) :
    piPointsEquiv G' T (x ≫ (Limits.Pi.map f : pi G ⟶ pi G').hom.hom) =
      fun i => piPointsEquiv G T x i ≫ (f i).hom.hom := by
  funext i
  simp only [piPointsEquiv_apply, Category.assoc, pi_map_hom_π]

/-- Reassembling a family of points and then applying the product homomorphism is reassembling
the family of images. -/
theorem piPointsEquiv_symm_pi_map (f : ∀ i, G i ⟶ G' i) (T : Over S)
    (x : ∀ i, T ⟶ (G i).X) :
    (piPointsEquiv G T).symm x ≫ (Limits.Pi.map f : pi G ⟶ pi G').hom.hom =
      (piPointsEquiv G' T).symm (fun i => x i ≫ (f i).hom.hom) := by
  apply (piPointsEquiv G' T).injective
  rw [piPointsEquiv_pi_map, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

end PiMap

section AffinePiMap

variable {R : CommRingCat.{u}} {I : Type u} [Finite I] {G G' : I → GroupScheme (Spec R)}

/-- On points with coefficients in an algebra, the product homomorphism acts coordinatewise. -/
theorem piPointsEquiv_affinePointsTarget_pi_map (f : ∀ i, G i ⟶ G' i)
    (A : CommAlgCat.{u} R) (x : (pi G).affinePoints A) :
    piPointsEquiv G' ((algSpec R).obj (op A))
        ((pi G).affinePointsTarget (Limits.Pi.map f : pi G ⟶ pi G') A x) =
      fun i => (G i).affinePointsTarget (f i) A (piPointsEquiv G ((algSpec R).obj (op A)) x i) :=
  piPointsEquiv_pi_map f ((algSpec R).obj (op A)) x

end AffinePiMap

/-- The actual base change of an affine group scheme along a map of affine bases is affine. -/
instance baseChange_spec_isAffine {C D : CommRingCat.{u}} (b : Spec D ⟶ Spec C)
    (G : GroupScheme (Spec C)) [IsAffine G.X.left] :
    IsAffine ((GroupScheme.baseChange b).obj G).X.left := by
  change IsAffine (pullback G.X.hom b)
  infer_instance

namespace AffineWeil

variable (k K Ω : Type u) [CommRing k] [CommRing K] [CommRing Ω]
  [Algebra k K] [Algebra k Ω] [Finite (K →ₐ[k] Ω)]

/-- The finite product over the `k`-embeddings `τ : K → Ω` of an affine group scheme over `K`
is affine. -/
instance embeddingProduct_isAffine (H : GroupScheme (Spec (CommRingCat.of K)))
    [IsAffine H.X.left] :
    IsAffine (GroupScheme.pi (fun τ : K →ₐ[k] Ω =>
      (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).obj H)).X.left := by
  have : IsAffineHom (GroupScheme.pi (fun τ : K →ₐ[k] Ω =>
      (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).obj H)).X.hom :=
    prop_pi_hom @IsAffineHom (fun τ : K →ₐ[k] Ω =>
      (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).obj H)
      (fun _ => inferInstance)
  exact isAffine_of_isAffineHom (GroupScheme.pi (fun τ : K →ₐ[k] Ω =>
    (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).obj H)).X.hom

variable {K Ω} {H H' H'' : GroupScheme (Spec (CommRingCat.of K))}

/-- The actual homomorphism of finite products of the base changes along all `k`-embeddings
`τ : K → Ω`, whose `τ`-factor is the base change of `f` along `τ`. -/
def embeddingProductMap (f : H ⟶ H') :
    GroupScheme.pi (fun τ : K →ₐ[k] Ω =>
        (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).obj H) ⟶
      GroupScheme.pi (fun τ : K →ₐ[k] Ω =>
        (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).obj H') :=
  Limits.Pi.map fun τ => (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).map f

/-- The `τ`-projection of the product homomorphism is the base change of `f` along `τ`. -/
@[reassoc (attr := simp)]
theorem embeddingProductMap_π (f : H ⟶ H') (τ : K →ₐ[k] Ω) :
    embeddingProductMap k f ≫ Pi.π (fun τ : K →ₐ[k] Ω =>
        (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).obj H') τ =
      Pi.π (fun τ : K →ₐ[k] Ω =>
        (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).obj H) τ ≫
        (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).map f :=
  Limits.Pi.map_π _ τ

/-- The `τ`-projection formula on the underlying morphisms over the base. -/
@[reassoc (attr := simp)]
theorem embeddingProductMap_hom_π (f : H ⟶ H') (τ : K →ₐ[k] Ω) :
    (embeddingProductMap k f).hom.hom ≫ (Pi.π (fun τ : K →ₐ[k] Ω =>
        (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).obj H') τ).hom.hom =
      (Pi.π (fun τ : K →ₐ[k] Ω =>
        (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).obj H) τ).hom.hom ≫
        ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).map f).hom.hom :=
  pi_map_hom_π _ τ

@[simp] theorem embeddingProductMap_id (H : GroupScheme (Spec (CommRingCat.of K))) :
    embeddingProductMap (Ω := Ω) k (𝟙 H) = 𝟙 _ := by
  apply Limits.Pi.hom_ext
  intro τ
  rw [embeddingProductMap_π, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

theorem embeddingProductMap_comp (f : H ⟶ H') (g : H' ⟶ H'') :
    embeddingProductMap (Ω := Ω) k (f ≫ g) =
      embeddingProductMap k f ≫ embeddingProductMap k g := by
  apply Limits.Pi.hom_ext
  intro τ
  simp only [Category.assoc, embeddingProductMap_π, embeddingProductMap_π_assoc,
    CategoryTheory.Functor.map_comp]

/-- On points over an arbitrary test scheme, the product homomorphism applies the base change of
`f` along `τ` to the `τ`-coordinate. -/
theorem piPointsEquiv_embeddingProductMap (f : H ⟶ H') (T : Over (Spec (CommRingCat.of Ω)))
    (x : T ⟶ (GroupScheme.pi (fun τ : K →ₐ[k] Ω =>
      (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).obj H)).X)
    (τ : K →ₐ[k] Ω) :
    piPointsEquiv _ T (x ≫ (embeddingProductMap k f).hom.hom) τ =
      piPointsEquiv _ T x τ ≫
        ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).map f).hom.hom :=
  congrFun (piPointsEquiv_pi_map _ T x) τ

/-- On points with coefficients in an `Ω`-algebra, the product homomorphism applies the base
change of `f` along `τ` to the `τ`-coordinate. -/
theorem piPointsEquiv_affinePointsTarget_embeddingProductMap (f : H ⟶ H')
    (R : CommAlgCat.{u} (CommRingCat.of Ω))
    (x : (GroupScheme.pi (fun τ : K →ₐ[k] Ω =>
      (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).obj H)).affinePoints R)
    (τ : K →ₐ[k] Ω) :
    piPointsEquiv _ ((algSpec (CommRingCat.of Ω)).obj (op R))
        ((GroupScheme.pi (fun τ : K →ₐ[k] Ω =>
          (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).obj H)).affinePointsTarget
          (embeddingProductMap k f) R x) τ =
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).obj H).affinePointsTarget
        ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).map f) R
        (piPointsEquiv _ ((algSpec (CommRingCat.of Ω)).obj (op R)) x τ) :=
  piPointsEquiv_embeddingProductMap k f _ x τ

end AffineWeil

end Langlands.GroupScheme
