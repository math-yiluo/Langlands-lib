import Langlands.GroupScheme.CentralSurjectionImage.PointWeights
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Langlands.GroupScheme.Torus.Diagonalizable

/-! # Rigidity of bimultiplicative maps out of split tori

A multiplicative point of an affine group scheme over `R[Λ]`, with `R` a domain, which becomes
trivial after one specialization `R → k` is trivial: on each finite matrix-coefficient
subcoalgebra its weights form orthogonal idempotent matrices over `R`, and the determinant of the
weight-zero matrix is an idempotent of `R` specializing to `1`. Consequently every map
`D(Λ) × D(Λ) → G` which is multiplicative in the first variable and trivial on `D(Λ) × 1` is
trivial.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.CentralSurjectionImage

open CocharacterDatum

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]

/-- **Rigidity over a domain.** A multiplicative point over `R[Λ]`, `R` a domain, whose
specialization along some `k`-algebra map `R → k` is trivial, is trivial. -/
theorem IsMultG.eq_one_of_isDomain {R : Type u} [CommRing R] [IsDomain R] [Algebra k R]
    {Λ : Type u} [AddCommGroup Λ] {p : Lie.AffinePoints G (AddMonoidAlgebra R Λ)}
    (hp : IsMultG p) (ev : R →ₐ[k] k)
    (h1 : Lie.affineMap G (AddMonoidAlgebra.mapAlgHom Λ ev) p = 1) : p = 1 := by
  classical
  apply hp.eq_one_of_weight_eq_zero
  intro γ hγ
  let : Bialgebra (CommRingCat.of k) (coordAlgebra G) :=
    AffineLinearEmbedding.bialgebra (corep G)
  apply LinearMap.ext
  intro b
  obtain ⟨N, Mx, hcomul, hcounit, hspan⟩ :=
    AffineLinearEmbedding.exists_matrix_coefficients (K := CommRingCat.of k)
      (B := coordAlgebra G) {b}
  let P : Λ → Matrix (Fin N) (Fin N) R := fun δ => Matrix.of fun i j => weight p δ (Mx i j)
  have hPmul : ∀ δ ε, P δ * P ε = if δ = ε then P δ else 0 := by
    intro δ ε
    ext i j
    have h := LinearMap.congr_fun (hp.conv_weight δ ε) (Mx i j)
    have hc : (comul G) (Mx i j) = ∑ l, Mx i l ⊗ₜ[CommRingCat.of k] Mx l j := hcomul i j
    simp only [conv, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, hc,
      map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply] at h
    rw [Matrix.mul_apply]
    simp only [P, Matrix.of_apply]
    rw [h]
    split_ifs <;> simp
  have hP0 : (P 0).map ev = 1 := by
    ext i j
    simp only [Matrix.map_apply, P, Matrix.of_apply]
    rw [← weight_coeffMap, h1, weight_one]
    simp only [↓reduceIte]
    have := hcounit i j
    change (counit G) (Mx i j) = _ at this
    rw [this]
    simp [Matrix.one_apply]
  have hP00 : P 0 * P 0 = P 0 := by simpa using hPmul 0 0
  have hidem : IsIdempotentElem (P 0).det := by
    rw [IsIdempotentElem, ← Matrix.det_mul, hP00]
  have hdet : (P 0).det = 1 := by
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp hidem with h | h
    · exfalso
      have h' := congrArg ev h
      have key : ev (P 0).det = ((P 0).map ev).det := RingHom.map_det ev.toRingHom (P 0)
      rw [map_zero, key, hP0, Matrix.det_one] at h'
      exact one_ne_zero h'
    · exact h
  have hunit : IsUnit (P 0) := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [hdet]; exact isUnit_one)
  have hP01 : P 0 = 1 :=
    hunit.mul_left_cancel (hP00.trans (mul_one _).symm)
  have hPγ : P γ = 0 := by
    have h := hPmul γ 0
    simp only [hγ, ↓reduceIte, hP01, mul_one] at h
    exact h
  have hle : Submodule.span (CommRingCat.of k)
      (Set.range fun q : Fin N × Fin N => Mx q.1 q.2) ≤ LinearMap.ker (weight p γ) := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact congrFun (congrFun (congrArg Matrix.of.symm hPγ) i) j
  exact hle (hspan (Finset.mem_coe.mpr (Finset.mem_singleton_self b)))

/-! ### Bimultiplicative maps out of a diagonalizable group -/

section Diagonalizable

open CategoryTheory.MonoidalCategory

variable (Λ : Type u) [AddCommGroup Λ]

/-- The diagonalizable group scheme `D(Λ)` over `k`. -/
abbrev Dg : GroupScheme (Spec (CommRingCat.of k)) :=
  (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp

variable {Λ}

/-- Points of `D(Λ)` over a `k`-algebra are characters of `Λ`. -/
def chi {A : Type u} [CommRing A] [Algebra k A] :
    Lie.AffinePoints (Dg (k := k) Λ) A ≃* (Multiplicative Λ →* Aˣ) :=
  Corepresented.affinePointsEquiv (Diagonalizable.functor (CommRingCat.of k) Λ)
    (Diagonalizable.grpCorepresentation (CommRingCat.of k) Λ)
    (CommAlgCat.of (CommRingCat.of k) A)

theorem chi_affineMap {A A' : Type u} [CommRing A] [Algebra k A] [CommRing A'] [Algebra k A']
    (f : A →ₐ[k] A') (x : Lie.AffinePoints (Dg (k := k) Λ) A) :
    chi (Lie.affineMap _ f x) = (Units.map f.toMonoidHom).comp (chi x) := by
  have h := Corepresented.affinePointsEquiv_naturality
    (Diagonalizable.functor (CommRingCat.of k) Λ)
    (Diagonalizable.grpCorepresentation (CommRingCat.of k) Λ) (CommAlgCat.ofHom f) x
  ext m
  exact congrArg (fun χ : Multiplicative Λ →* A'ˣ => (χ m : A')) h

variable {Λ' : Type u} [AddCommGroup Λ']

omit [IsAffine G.X.left] in
theorem affineMap_lift_comp {T : GroupScheme (Spec (CommRingCat.of k))} {A A' : Type u}
    [CommRing A] [Algebra k A] [CommRing A'] [Algebra k A'] (f : A →ₐ[k] A')
    (x y : Lie.AffinePoints T A) (β : T.X ⊗ T.X ⟶ G.X) :
    Lie.affineMap G f (lift x y ≫ β) =
      lift (Lie.affineMap T f x) (Lie.affineMap T f y) ≫ β := by
  rw [Lie.affineMap_apply, Lie.affineMap_apply, Lie.affineMap_apply, ← Category.assoc, comp_lift]

theorem chi_symm_affineMap {A A' : Type u} [CommRing A] [Algebra k A] [CommRing A'] [Algebra k A']
    (f : A →ₐ[k] A') (c : Multiplicative Λ →* Aˣ) :
    Lie.affineMap (Dg (k := k) Λ) f (chi.symm c) = chi.symm ((Units.map f.toMonoidHom).comp c) := by
  apply chi.injective
  rw [chi_affineMap, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

omit [IsAffine G.X.left] in
/-- Points of `D(Λ)` over any test scheme factor through the affine test scheme of global
sections. -/
theorem exists_affine_factor {U : Over (Spec (CommRingCat.of k))}
    (x y : U ⟶ (Dg (k := k) Λ).X) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra k A)
      (e₀ : U ⟶ (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) A)))
      (x' y' : Lie.AffinePoints (Dg (k := k) Λ) A), x = e₀ ≫ x' ∧ y = e₀ ≫ y' := by
  let adj := algΓAlgSpecAdjunction (CommRingCat.of k)
  refine ⟨((algΓ (CommRingCat.of k)).obj U).unop, inferInstance, inferInstance,
    adj.unit.app U, (algSpec _).map ((adj.homEquiv _ _).symm x),
    (algSpec _).map ((adj.homEquiv _ _).symm y), ?_, ?_⟩
  · rw [← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]
  · rw [← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]

/-- **Bimultiplicative rigidity, affine form.** Let `R` be a domain with a character
`ιc : Λ → Rˣ` that is universal for characters of `Λ` and is killed by a specialization
`ev : R → k`. A map `β : D(Λ) × D(Λ) → G` multiplicative in the first variable and trivial on
`D(Λ) × 1` is trivial on affine points. -/
theorem lift_comp_eq_one_of_bimul_aux (R : Type u) [CommRing R] [IsDomain R] [Algebra k R]
    (ιc : Multiplicative Λ →* Rˣ) (ev : R →ₐ[k] k) (hev : ∀ m, ev (ιc m) = 1)
    (hfac : ∀ (A₀ : Type u) [CommRing A₀] [Algebra k A₀] (d : Multiplicative Λ →* A₀ˣ),
      ∃ ψ : R →ₐ[k] A₀, ∀ m, ψ (ιc m) = d m)
    (β : (Dg (k := k) Λ).X ⊗ (Dg (k := k) Λ).X ⟶ G.X)
    (hmul : ∀ (A : Type u) [CommRing A] [Algebra k A] (x x' y : Lie.AffinePoints (Dg (k := k) Λ) A),
      lift (x * x') y ≫ β = (lift x y ≫ β) * (lift x' y ≫ β))
    (hone : ∀ (A : Type u) [CommRing A] [Algebra k A] (x : Lie.AffinePoints (Dg (k := k) Λ) A),
      lift x 1 ≫ β = 1)
    (A₀ : Type u) [CommRing A₀] [Algebra k A₀] (x₀ y₀ : Lie.AffinePoints (Dg (k := k) Λ) A₀) :
    lift x₀ y₀ ≫ β = 1 := by
  classical
  let outer : Multiplicative Λ →* (AddMonoidAlgebra R Λ)ˣ := (AddMonoidAlgebra.of R Λ).toHomUnits
  let inner : ∀ (Λ' : Type u) [AddCommGroup Λ'], Multiplicative Λ →* (AddMonoidAlgebra R Λ')ˣ :=
    fun Λ' _ => (Units.map (algebraMap R (AddMonoidAlgebra R Λ')).toMonoidHom).comp ιc
  let xA : Lie.AffinePoints (Dg (k := k) Λ) (AddMonoidAlgebra R Λ) := chi.symm outer
  let yA : Lie.AffinePoints (Dg (k := k) Λ) (AddMonoidAlgebra R Λ) := chi.symm (inner Λ)
  let v := lift xA yA ≫ β
  have hinner : ∀ {Λ' : Type u} [AddCommGroup Λ'] (g : Λ →+ Λ'),
      Lie.affineMap (Dg (k := k) Λ) (AddMonoidAlgebra.mapDomainAlgHom k R g) yA =
        chi.symm (inner Λ') := by
    intro Λ' _ g
    rw [chi_symm_affineMap]
    congr 1
    ext m
    simp [inner, AddMonoidAlgebra.coe_algebraMap, AddMonoidAlgebra.mapDomain_single]
  have hv : IsMultG v := by
    change expMapG (diagHom Λ) v = expMapG _ v * expMapG _ v
    simp only [expMapG, v, affineMap_lift_comp, hinner]
    rw [← hmul]
    congr 1
    rw [chi_symm_affineMap, chi_symm_affineMap, chi_symm_affineMap, ← map_mul]
    have e1 : (Units.map (AddMonoidAlgebra.mapDomainAlgHom k R (diagHom Λ)).toMonoidHom).comp
        outer = (Units.map (AddMonoidAlgebra.mapDomainAlgHom k R
          (AddMonoidHom.inl Λ Λ)).toMonoidHom).comp outer *
        (Units.map (AddMonoidAlgebra.mapDomainAlgHom k R
          (AddMonoidHom.inr Λ Λ)).toMonoidHom).comp outer := by
      ext m
      simp [outer, AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.single_mul_single]
    rw [e1]
  have hev' : Lie.affineMap G (AddMonoidAlgebra.mapAlgHom Λ ev) v = 1 := by
    rw [affineMap_lift_comp]
    have h1 : Lie.affineMap (Dg (k := k) Λ) (AddMonoidAlgebra.mapAlgHom Λ ev) yA = 1 := by
      rw [chi_symm_affineMap,
        ← map_one (chi (k := k) (Λ := Λ) (A := AddMonoidAlgebra k Λ)).symm]
      congr 1
      ext m
      simp [inner, AddMonoidAlgebra.coe_algebraMap, hev, AddMonoidAlgebra.one_def]
    rw [h1]
    exact hone _ _
  have hv1 : v = 1 := hv.eq_one_of_isDomain ev hev'
  obtain ⟨ψd, hψd⟩ := hfac A₀ (chi y₀)
  let φr : AddMonoidAlgebra R Λ →+* A₀ := AddMonoidAlgebra.liftNCRingHom ψd.toRingHom
    ((Units.coeHom A₀).comp (chi x₀)) (fun _ _ => Commute.all _ _)
  let φ : AddMonoidAlgebra R Λ →ₐ[k] A₀ :=
    { φr with
      commutes' := fun r => by
        change φr (AddMonoidAlgebra.single 0 (algebraMap k R r)) = algebraMap k A₀ r
        simp [φr, AddMonoidAlgebra.liftNCRingHom] }
  have hx : Lie.affineMap (Dg (k := k) Λ) φ xA = x₀ := by
    apply chi.injective
    rw [chi_symm_affineMap, MulEquiv.apply_symm_apply]
    ext m
    simp [outer, φ, φr, AddMonoidAlgebra.liftNCRingHom]
  have hy : Lie.affineMap (Dg (k := k) Λ) φ yA = y₀ := by
    apply chi.injective
    rw [chi_symm_affineMap, MulEquiv.apply_symm_apply]
    ext m
    simp [inner, φ, φr, AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.coe_algebraMap, hψd]
  rw [← hx, ← hy, ← affineMap_lift_comp]
  change Lie.affineMap G φ v = 1
  rw [hv1, map_one]

/-- **Bimultiplicative rigidity.** Let `β : D(Λ) × D(Λ) → G`, with `k[Λ]` a domain, be
multiplicative in the first variable and trivial on `D(Λ) × 1`, on points over every `k`-algebra.
Then `β` is trivial on points over every test scheme. -/
theorem lift_comp_eq_one_of_bimul [IsDomain (AddMonoidAlgebra k Λ)]
    (β : (Dg (k := k) Λ).X ⊗ (Dg (k := k) Λ).X ⟶ G.X)
    (hmul : ∀ (A : Type u) [CommRing A] [Algebra k A] (x x' y : Lie.AffinePoints (Dg (k := k) Λ) A),
      lift (x * x') y ≫ β = (lift x y ≫ β) * (lift x' y ≫ β))
    (hone : ∀ (A : Type u) [CommRing A] [Algebra k A] (x : Lie.AffinePoints (Dg (k := k) Λ) A),
      lift x 1 ≫ β = 1)
    {U : Over (Spec (CommRingCat.of k))} (x y : U ⟶ (Dg (k := k) Λ).X) : lift x y ≫ β = 1 := by
  obtain ⟨A₀, _, _, e₀, x', y', rfl, rfl⟩ := exists_affine_factor x y
  rw [← comp_lift, Category.assoc,
    lift_comp_eq_one_of_bimul_aux (AddMonoidAlgebra k Λ) (AddMonoidAlgebra.of k Λ).toHomUnits
      (AddMonoidAlgebra.lift k k Λ 1) (fun m => by simp)
      (fun A₀ _ _ d => ⟨AddMonoidAlgebra.lift k A₀ Λ ((Units.coeHom A₀).comp d),
        fun m => by simp⟩) β hmul hone A₀ x' y']
  exact MonObj.comp_one _

end Diagonalizable

end Langlands.GroupScheme.CentralSurjectionImage
