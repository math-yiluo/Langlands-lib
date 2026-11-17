import Langlands.GroupScheme.Torus.ConnectedCoefficientRigidity

/-! # Pointed families of homomorphisms from diagonalizable groups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.CentralSurjectionImage

open CocharacterDatum

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffine G.X.left] [IsAffine H.X.left] [ConnectedSpace H.X.left]
  {Λ : Type u} [AddCommGroup Λ]

/-- A natural family of homomorphisms from a diagonalizable group, parametrized
by a connected affine group scheme and trivial at its identity, is trivial. -/
theorem eq_one_of_connected_pointed_family
    (F : ∀ (A : Type u) [CommRing A] [Algebra k A],
      Lie.AffinePoints H A → (Multiplicative Λ →* Aˣ) → Lie.AffinePoints G A)
    (hnat : ∀ (A B : Type u) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
      (f : A →ₐ[k] B) (y : Lie.AffinePoints H A) (x : Multiplicative Λ →* Aˣ),
      Lie.affineMap G f (F A y x) =
        F B (Lie.affineMap H f y) ((Units.map f.toMonoidHom).comp x))
    (hmul : ∀ (A : Type u) [CommRing A] [Algebra k A]
      (y : Lie.AffinePoints H A) (x x' : Multiplicative Λ →* Aˣ),
      F A y (x * x') = F A y x * F A y x')
    (hone : ∀ (A : Type u) [CommRing A] [Algebra k A]
      (x : Multiplicative Λ →* Aˣ), F A 1 x = 1)
    (A₀ : Type u) [CommRing A₀] [Algebra k A₀]
    (y₀ : Lie.AffinePoints H A₀) (x₀ : Multiplicative Λ →* A₀ˣ) :
    F A₀ y₀ x₀ = 1 := by
  classical
  let R := coordAlgebra H
  have : ConnectedSpace (PrimeSpectrum R) := by
    exact (Scheme.homeoOfIso ((Over.forget _).mapIso (coordIso H))).connectedSpace_iff.mpr
      (inferInstanceAs (ConnectedSpace H.X.left))
  let yR : Lie.AffinePoints H R := (coordIso H).hom
  let ev : R →ₐ[k] k := (coord (1 : Lie.AffinePoints H k)).hom
  have hev : Lie.affineMap H ev yR = 1 := map_coord _
  let outer : Multiplicative Λ →* (AddMonoidAlgebra R Λ)ˣ :=
    (AddMonoidAlgebra.of R Λ).toHomUnits
  let inner : ∀ (Λ' : Type u) [AddCommGroup Λ'], Lie.AffinePoints H (AddMonoidAlgebra R Λ') :=
    fun Λ' _ => Lie.affineMap H (IsScalarTower.toAlgHom k R (AddMonoidAlgebra R Λ')) yR
  let v := F (AddMonoidAlgebra R Λ) (inner Λ) outer
  have hinner : ∀ {Λ' : Type u} [AddCommGroup Λ'] (g : Λ →+ Λ'),
      Lie.affineMap H (AddMonoidAlgebra.mapDomainAlgHom k R g) (inner Λ) = inner Λ' := by
    intro Λ' _ g
    dsimp only [inner]
    rw [← Lie.affineMap_comp]
    have hc : (AddMonoidAlgebra.mapDomainAlgHom k R g).comp
        (IsScalarTower.toAlgHom k R (AddMonoidAlgebra R Λ)) =
        IsScalarTower.toAlgHom k R (AddMonoidAlgebra R Λ') := by
      ext
      simp [AddMonoidAlgebra.coe_algebraMap, AddMonoidAlgebra.mapDomain_single]
    rw [hc]
  have hv : IsMultG v := by
    change expMapG (diagHom Λ) v = expMapG _ v * expMapG _ v
    simp only [expMapG, v, hnat, hinner]
    rw [← hmul]
    congr 1
    ext m
    simp [outer, AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.single_mul_single]
  have hev' : Lie.affineMap G (AddMonoidAlgebra.mapAlgHom Λ ev) v = 1 := by
    dsimp only [v]
    rw [hnat]
    have hy : Lie.affineMap H (AddMonoidAlgebra.mapAlgHom Λ ev) (inner Λ) = 1 := by
      dsimp only [inner]
      rw [← Lie.affineMap_comp]
      have hc : (AddMonoidAlgebra.mapAlgHom Λ ev).comp
          (IsScalarTower.toAlgHom k R (AddMonoidAlgebra R Λ)) =
          (IsScalarTower.toAlgHom k k (AddMonoidAlgebra k Λ)).comp ev := by
        ext
        simp
      rw [hc, Lie.affineMap_comp, hev, map_one]
    rw [hy, hone]
  have hv1 : v = 1 := hv.eq_one_of_connectedSpectrum ev hev'
  let ψ : R →ₐ[k] A₀ := (coord y₀).hom
  let φr : AddMonoidAlgebra R Λ →+* A₀ := AddMonoidAlgebra.liftNCRingHom ψ.toRingHom
    ((Units.coeHom A₀).comp x₀) (fun _ _ => Commute.all _ _)
  let φ : AddMonoidAlgebra R Λ →ₐ[k] A₀ :=
    { φr with
      commutes' := fun r => by
        change φr (AddMonoidAlgebra.single 0 (algebraMap k R r)) = algebraMap k A₀ r
        simp [φr, AddMonoidAlgebra.liftNCRingHom] }
  have hx : (Units.map φ.toMonoidHom).comp outer = x₀ := by
    ext m
    simp [outer, φ, φr, AddMonoidAlgebra.liftNCRingHom]
  have hy : Lie.affineMap H φ (inner Λ) = y₀ := by
    dsimp only [inner]
    rw [← Lie.affineMap_comp]
    have hc : φ.comp (IsScalarTower.toAlgHom k R (AddMonoidAlgebra R Λ)) = ψ := by
      ext
      simp [φ, φr, AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.coe_algebraMap]
    rw [hc]
    exact map_coord y₀
  have h := congrArg (Lie.affineMap G φ) hv1
  dsimp only [v] at h
  rw [hnat, hy, hx, map_one] at h
  exact h

end Langlands.GroupScheme.CentralSurjectionImage
