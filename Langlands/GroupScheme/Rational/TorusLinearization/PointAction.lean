import Langlands.GroupScheme.Rational.TorusLinearization.Euclid

/-! # Abstract torus actions on affine space by additive maps -/

noncomputable section

universe u

open MvPolynomial

namespace Langlands.GroupScheme.TorusLinearization

/-- The functor-of-points data of a torus acting on `n`-space over `k` by additive maps,
together with a splitting over the field `K`: over `K`-algebras the points are the families
`I → Cˣ`. No group law on the points is required. -/
structure PointAction (k K : Type u) [Field k] [Field K] [Algebra k K] (I : Type u) (n : ℕ) where
  /-- The points of the torus with values in a `k`-algebra. -/
  Pt : ∀ (B : Type u) [CommRing B] [Algebra k B], Type u
  /-- Transport of points along algebra maps. -/
  map : ∀ {B C : Type u} [CommRing B] [Algebra k B] [CommRing C] [Algebra k C],
    (B →ₐ[k] C) → Pt B → Pt C
  map_id : ∀ {B : Type u} [CommRing B] [Algebra k B] (t : Pt B), map (AlgHom.id k B) t = t
  map_comp : ∀ {B C D : Type u} [CommRing B] [Algebra k B] [CommRing C] [Algebra k C]
    [CommRing D] [Algebra k D] (g : B →ₐ[k] C) (h : C →ₐ[k] D) (t : Pt B),
    map (h.comp g) t = map h (map g t)
  /-- The action of a point on the `B`-points of `n`-space. -/
  act : ∀ {B : Type u} [CommRing B] [Algebra k B], Pt B → (Fin n → B) → (Fin n → B)
  act_add : ∀ {B : Type u} [CommRing B] [Algebra k B] (t : Pt B) (x y : Fin n → B),
    act t (x + y) = act t x + act t y
  act_map : ∀ {B C : Type u} [CommRing B] [Algebra k B] [CommRing C] [Algebra k C]
    (g : B →ₐ[k] C) (t : Pt B) (x : Fin n → B), act (map g t) (g ∘ x) = g ∘ act t x
  /-- The splitting: families of units over `K`-algebras give points. -/
  σ : ∀ {C : Type u} [CommRing C] [Algebra k C] [Algebra K C] [IsScalarTower k K C],
    (I → Cˣ) → Pt C
  σ_surj : ∀ {C : Type u} [CommRing C] [Algebra k C] [Algebra K C] [IsScalarTower k K C]
    (t : Pt C), ∃ τ, σ τ = t
  map_σ : ∀ {C D : Type u} [CommRing C] [Algebra k C] [Algebra K C] [IsScalarTower k K C]
    [CommRing D] [Algebra k D] [Algebra K D] [IsScalarTower k K D] (f : C →ₐ[K] D)
    (τ : I → Cˣ), map (f.restrictScalars k) (σ τ) =
      σ (fun i => Units.map f.toRingHom.toMonoidHom (τ i))
  act_σ_one : ∀ {C : Type u} [CommRing C] [Algebra k C] [Algebra K C] [IsScalarTower k K C]
    (x : Fin n → C), act (σ (1 : I → Cˣ)) x = x
  act_σ_mul : ∀ {C : Type u} [CommRing C] [Algebra k C] [Algebra K C] [IsScalarTower k K C]
    (τ τ' : I → Cˣ) (x : Fin n → C), act (σ (τ * τ')) x = act (σ τ) (act (σ τ') x)

namespace PointAction

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {I : Type u} {n : ℕ}
  (a : PointAction k K I n)

/-- The universal polynomials of a point: its action on the generic point of `n`-space. -/
def poly {B : Type u} [CommRing B] [Algebra k B] (t : a.Pt B) : Fin n → MvPolynomial (Fin n) B :=
  a.act (a.map (IsScalarTower.toAlgHom k B (MvPolynomial (Fin n) B)) t) X

/-- The action of a point is evaluation of its universal polynomials. -/
theorem act_eq_aeval {B : Type u} [CommRing B] [Algebra k B] (t : a.Pt B) (x : Fin n → B) :
    a.act t x = fun i => aeval x (a.poly t i) := by
  have h := a.act_map ((aeval x).restrictScalars k)
    (a.map (IsScalarTower.toAlgHom k B (MvPolynomial (Fin n) B)) t) X
  rw [← a.map_comp] at h
  have hc : ((aeval x).restrictScalars k).comp
      (IsScalarTower.toAlgHom k B (MvPolynomial (Fin n) B)) = AlgHom.id k B := by
    ext b
    simp
  have hx : (((aeval x).restrictScalars k : MvPolynomial (Fin n) B →ₐ[k] B) ∘ X) = x := by
    funext i
    simp
  rw [hc, a.map_id, hx] at h
  rw [h]
  rfl

/-- Pulling back a polynomial over `k` along the action of a point. -/
def pull {B : Type u} [CommRing B] [Algebra k B] (t : a.Pt B) :
    MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) B :=
  aeval (a.poly t)

theorem aeval_pull {B : Type u} [CommRing B] [Algebra k B] (t : a.Pt B)
    (f : MvPolynomial (Fin n) k) (x : Fin n → B) :
    aeval x (a.pull t f) = aeval (a.act t x) f := by
  rw [a.act_eq_aeval, pull, ← AlgHom.restrictScalars_apply k (aeval x), ← AlgHom.comp_apply,
    comp_aeval]
  rfl

/-- The universal polynomials are natural in the coefficient algebra. -/
theorem poly_map {B D : Type u} [CommRing B] [Algebra k B] [CommRing D] [Algebra k D]
    (g : B →ₐ[k] D) (t : a.Pt B) (i : Fin n) :
    a.poly (a.map g t) i = MvPolynomial.map (g : B →+* D) (a.poly t i) := by
  have h := a.act_map (MvPolynomial.mapAlgHom (σ := Fin n) g)
    (a.map (IsScalarTower.toAlgHom k B (MvPolynomial (Fin n) B)) t) X
  rw [← a.map_comp] at h
  have hc : (MvPolynomial.mapAlgHom (σ := Fin n) g).comp
      (IsScalarTower.toAlgHom k B (MvPolynomial (Fin n) B)) =
      (IsScalarTower.toAlgHom k D (MvPolynomial (Fin n) D)).comp g := by
    ext b
    simp
  have hx : ((MvPolynomial.mapAlgHom (σ := Fin n) g : _ →ₐ[k] _) ∘ X) = X := by
    funext j
    simp
  rw [hc, a.map_comp, hx] at h
  exact (congrFun h i).trans (MvPolynomial.mapAlgHom_apply _ _)

/-- The universal polynomials of a point are additive. -/
theorem isAddPoly_poly {B : Type u} [CommRing B] [Algebra k B] (t : a.Pt B) (i : Fin n) :
    IsAddPoly (a.poly t i) := by
  intro D _ _ x y
  let : Algebra k D := ((algebraMap B D).comp (algebraMap k B)).toAlgebra
  have : IsScalarTower k B D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h := a.act_add (a.map (IsScalarTower.toAlgHom k B D) t) x y
  rw [a.act_eq_aeval, a.act_eq_aeval, a.act_eq_aeval] at h
  have hp : ∀ i, a.poly (a.map (IsScalarTower.toAlgHom k B D) t) i =
      MvPolynomial.map (algebraMap B D) (a.poly t i) := fun i => a.poly_map _ t i
  have := congrFun h i
  simp only [hp] at this
  simpa [aeval_def] using this

end PointAction

end Langlands.GroupScheme.TorusLinearization
