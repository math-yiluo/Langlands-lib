import Langlands.GroupScheme.Torus.CocharacterDatum
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.CentralSurjectionImage.GroupAlgebraCoeff

/-! # Coordinate bialgebras and weight functionals of points over group algebras

For an affine group scheme `G` over a field `k`, points of `G` over a `k`-algebra `S` are
algebra maps out of the coordinate algebra. Products of points are convolutions along the
comultiplication. For a point over the group algebra `S[Λ]`, its `γ`-weight is the
`γ`-coefficient of its coordinate map. A multiplicative point has orthogonal weights.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.CentralSurjectionImage

open CocharacterDatum

set_option backward.isDefEq.respectTransparency false

section Coordinates

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]

/-- The chosen coordinate algebra corepresents the algebra points of `G`. -/
abbrev corep : (G.affinePointFunctor ⋙ forget GrpCat).CorepresentableBy (coordAlgebra G) :=
  AffineLinearEmbedding.corepresentableBy G (coordIso G)

/-- The comultiplication of the coordinate algebra. -/
abbrev comul : coordAlgebra G →ₐ[CommRingCat.of k]
    coordAlgebra G ⊗[CommRingCat.of k] coordAlgebra G :=
  AffineLinearEmbedding.comul (corep G)

/-- The counit of the coordinate algebra. -/
abbrev counit : coordAlgebra G →ₐ[CommRingCat.of k] CommRingCat.of k :=
  AffineLinearEmbedding.counit (corep G)

variable {G}
variable {S : Type u} [CommRing S] [Algebra k S]

/-- Products of points are convolutions of their coordinate maps. -/
theorem coord_mul (x y : Lie.AffinePoints G S) :
    (coord (x * y)).hom =
      (Algebra.TensorProduct.productMap (coord x).hom (coord y).hom).comp (comul G) :=
  AffineLinearEmbedding.homEquiv_symm_mul (corep G) (A := CommAlgCat.of (CommRingCat.of k) S) x y

/-- The identity point has the counit as coordinate map. -/
theorem coord_one :
    (coord (1 : Lie.AffinePoints G S)).hom = (Algebra.ofId (CommRingCat.of k) S).comp (counit G) :=
  AffineLinearEmbedding.homEquiv_symm_one (corep G) (CommAlgCat.of (CommRingCat.of k) S)

end Coordinates

/-! ### Multiplicative points and their weights -/

section Weights

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]
variable {S : Type u} [CommRing S] [Algebra k S] {Λ : Type u} [AddCommGroup Λ]

/-- Exponent change along an additive map, on points of an arbitrary group scheme with
coefficients in a group algebra. -/
abbrev expMapG {Λ' : Type u} [AddCommGroup Λ'] (g : Λ →+ Λ') :
    Lie.AffinePoints G (AddMonoidAlgebra S Λ) →* Lie.AffinePoints G (AddMonoidAlgebra S Λ') :=
  Lie.affineMap G (AddMonoidAlgebra.mapDomainAlgHom k S g)

/-- A point over `S[Λ]` is multiplicative when it is a homomorphism from the diagonalizable
group of `Λ`. For a commutative group scheme this is `CocharacterDatum.IsMult`. -/
def IsMultG (p : Lie.AffinePoints G (AddMonoidAlgebra S Λ)) : Prop :=
  expMapG (diagHom Λ) p = expMapG (AddMonoidHom.inl Λ Λ) p * expMapG (AddMonoidHom.inr Λ Λ) p

omit [IsAffine G.X.left] in
theorem expMapG_expMapG {Λ' Λ'' : Type u} [AddCommGroup Λ'] [AddCommGroup Λ'']
    (g : Λ →+ Λ') (h : Λ' →+ Λ'') (p : Lie.AffinePoints G (AddMonoidAlgebra S Λ)) :
    expMapG h (expMapG g p) = expMapG (h.comp g) p := by
  rw [expMapG, expMapG, expMapG, ← Lie.affineMap_comp, AddMonoidAlgebra.mapDomainAlgHom_comp]

omit [IsAffine G.X.left] in
/-- A multiplicative point is trivial after collapsing all exponents to zero. -/
theorem IsMultG.expMapG_zero {p : Lie.AffinePoints G (AddMonoidAlgebra S Λ)} (hp : IsMultG p) :
    expMapG (0 : Λ →+ Λ) p = 1 := by
  have h := congrArg (expMapG (0 : Λ × Λ →+ Λ)) hp
  rw [map_mul, expMapG_expMapG, expMapG_expMapG, expMapG_expMapG] at h
  simp only [AddMonoidHom.zero_comp] at h
  exact left_eq_mul.mp h

/-- The `γ`-weight of a point over `S[Λ]`: the `γ`-coefficient of its coordinate map. -/
def weight (p : Lie.AffinePoints G (AddMonoidAlgebra S Λ)) (γ : Λ) :
    coordAlgebra G →ₗ[CommRingCat.of k] S where
  toFun b := ((coord p).hom b).coeff γ
  map_add' a b := by simp
  map_smul' c a := by simp

theorem weight_apply (p : Lie.AffinePoints G (AddMonoidAlgebra S Λ)) (γ : Λ) (b : coordAlgebra G) :
    weight p γ b = ((coord p).hom b).coeff γ :=
  rfl

/-- Points over `S[Λ]` are determined by their weights. -/
theorem eq_of_weight_eq {p q : Lie.AffinePoints G (AddMonoidAlgebra S Λ)}
    (h : ∀ γ b, weight p γ b = weight q γ b) : p = q := by
  apply coord_injective
  apply CommAlgCat.hom_ext
  ext b γ
  exact h γ b

/-- Weights of a coefficient change. -/
theorem weight_coeffMap {S' : Type u} [CommRing S'] [Algebra k S'] (f : S →ₐ[k] S')
    (p : Lie.AffinePoints G (AddMonoidAlgebra S Λ)) (γ : Λ) (b : coordAlgebra G) :
    weight (Lie.affineMap G (AddMonoidAlgebra.mapAlgHom Λ f) p) γ b = f (weight p γ b) := by
  rw [weight_apply, weight_apply, coord_affineMap]
  simp [AddMonoidAlgebra.coeff_mapAlgHom]

/-- Weights of the identity point. -/
theorem weight_one [DecidableEq Λ] (γ : Λ) (b : coordAlgebra G) :
    weight (1 : Lie.AffinePoints G (AddMonoidAlgebra S Λ)) γ b =
      if γ = 0 then algebraMap k S (counit G b) else 0 := by
  rw [weight_apply, coord_one]
  simp [AddMonoidAlgebra.coe_algebraMap, Finsupp.single_apply, eq_comm]

/-- Convolution of two `k`-linear functionals on the coordinate algebra. -/
def conv (f g : coordAlgebra G →ₗ[CommRingCat.of k] S) : coordAlgebra G →ₗ[CommRingCat.of k] S :=
  LinearMap.mul' (CommRingCat.of k) S ∘ₗ TensorProduct.map f g ∘ₗ (comul G).toLinearMap

/-- The `(γ, δ)`-coefficient of the convolution of two points pushed into the two factors of
`S[Λ × Λ]` is the convolution of their weights. -/
theorem coeff_productMap_inl_inr (p : Lie.AffinePoints G (AddMonoidAlgebra S Λ)) (γ δ : Λ)
    (t : coordAlgebra G ⊗[CommRingCat.of k] coordAlgebra G) :
    ((Algebra.TensorProduct.productMap
        ((AddMonoidAlgebra.mapDomainAlgHom k S (AddMonoidHom.inl Λ Λ)).comp (coord p).hom)
        ((AddMonoidAlgebra.mapDomainAlgHom k S (AddMonoidHom.inr Λ Λ)).comp (coord p).hom))
          t).coeff (γ, δ) =
      LinearMap.mul' (CommRingCat.of k) S (TensorProduct.map (weight p γ) (weight p δ) t) :=
  coeff_productMap_inl_inr' (k := k) (coord p).hom γ δ t

/-- The weights of a multiplicative point are orthogonal idempotents for convolution. -/
theorem IsMultG.conv_weight [DecidableEq Λ] {p : Lie.AffinePoints G (AddMonoidAlgebra S Λ)}
    (hp : IsMultG p) (γ δ : Λ) :
    conv (weight p γ) (weight p δ) = if γ = δ then weight p γ else 0 := by
  ext b
  have h := congrArg (fun q => ((coord q).hom b).coeff (γ, δ)) hp
  simp only at h
  rw [coord_mul, coord_affineMap, coord_affineMap, coord_affineMap] at h
  have hl : ((CommAlgCat.Hom.hom (coord p ≫ CommAlgCat.ofHom
      (AddMonoidAlgebra.mapDomainAlgHom k S (diagHom Λ)))) b).coeff (γ, δ) =
      if γ = δ then weight p γ b else 0 :=
    coeff_mapDomain_diag _ γ δ
  rw [hl] at h
  rw [show (if γ = δ then weight p γ else 0) b = if γ = δ then weight p γ b else 0 by
    split_ifs <;> rfl, h]
  exact (coeff_productMap_inl_inr p γ δ (comul G b)).symm

/-- The weights of a multiplicative point sum to the counit. -/
theorem IsMultG.sum_weight {p : Lie.AffinePoints G (AddMonoidAlgebra S Λ)} (hp : IsMultG p)
    (b : coordAlgebra G) :
    ((coord p).hom b).coeff.sum (fun _ c => c) = algebraMap k S (counit G b) := by
  classical
  have h := congrArg (fun q => ((coord q).hom b).coeff 0) hp.expMapG_zero
  simp only at h
  rw [coord_affineMap, coord_one] at h
  change (Finsupp.mapDomain (0 : Λ →+ Λ) ((coord p).hom b).coeff) 0 = _ at h
  rw [Finsupp.mapDomain, Finsupp.sum_apply] at h
  simp only [AddMonoidHom.zero_apply, Finsupp.single_eq_same] at h
  rw [h]
  simp [AddMonoidAlgebra.coe_algebraMap]

/-- A multiplicative point whose nonzero weights vanish is the identity point. -/
theorem IsMultG.eq_one_of_weight_eq_zero {p : Lie.AffinePoints G (AddMonoidAlgebra S Λ)}
    (hp : IsMultG p) (h : ∀ γ : Λ, γ ≠ 0 → weight p γ = 0) : p = 1 := by
  classical
  apply eq_of_weight_eq
  intro γ b
  rw [weight_one]
  split_ifs with hγ
  · subst hγ
    rw [← hp.sum_weight b, Finsupp.sum_eq_single 0]
    · rfl
    · intro δ _ hδ
      exact LinearMap.congr_fun (h δ hδ) b
    · intro _
      rfl
  · exact LinearMap.congr_fun (h γ hγ) b

end Weights

end Langlands.GroupScheme.CentralSurjectionImage
