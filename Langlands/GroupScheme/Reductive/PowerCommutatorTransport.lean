import Langlands.GroupScheme.Reductive.LocalSplitWeylCommutatorReduction

/-! # Common-power transport of actual commutator formulas -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R]
    (F : Ga R ⟶ Ga R) (q : ℕ)
    (hF : ∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
      rootPoint F Z x = VectorGroup.scalarPoint (CommRingCat.of R) Z (x ^ q))

/-- A supplied additive-line power homomorphism induces the power ring
endomorphism on the global sections of every scheme test. -/
def sectionPowerRingHom (Z : Over (Spec (CommRingCat.of R))) :
    Γ(Z.left, ⊤) →+* Γ(Z.left, ⊤) where
  toFun x := x ^ q
  map_one' := one_pow q
  map_mul' x y := mul_pow x y q
  map_zero' := by
    have h := congrArg gaCoord (rootPoint_zero F Z)
    simpa only [hF, gaCoord, VectorGroup.coordinates_scalarPoint,
      map_one, toAdd_one, Pi.zero_apply] using h
  map_add' x y := by
    have h := congrArg gaCoord (rootPoint_add F Z x y)
    simpa only [hF, gaCoord, VectorGroup.coordinates_scalarPoint,
      VectorGroup.coordinates_mul, Pi.add_apply] using h

variable {F q}

include hF

/-- Precomposing an actual root map by the supplied power homomorphism
raises its argument to that power on every test. -/
theorem rootPoint_precompose_power
    {G : GroupScheme (Spec (CommRingCat.of R))} (w : Ga R ⟶ G)
    (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)) :
    rootPoint (F ≫ w) Z x = rootPoint w Z (x ^ q) := by
  change (VectorGroup.scalarPoint (CommRingCat.of R) Z x ≫
    F.hom.hom ≫ w.hom.hom) = _
  rw [← Category.assoc]
  change rootPoint F Z x ≫ w.hom.hom = _
  rw [hF]
  rfl

variable (F) {G : GroupScheme (Spec (CommRingCat.of R))}

omit hF in
/-- Precompose the map in each actual commutator term by the same
additive-line endomorphism, retaining its scalar and its two exponents. -/
def powerCommTerms (L : List (CommTerm R G)) : List (CommTerm R G) :=
  L.map fun t => (F ≫ t.1, t.2.1, t.2.2.1, t.2.2.2)

variable {F}

/-- Each precomposed term has the value of the original term on the
powered arguments, provided its coefficient is fixed by the same power. -/
theorem termPoint_precompose_power (t : CommTerm R G)
    (Z : Over (Spec (CommRingCat.of R))) (x y : Γ(Z.left, ⊤))
    (hc : (baseScalar Z t.2.1) ^ q = baseScalar Z t.2.1) :
    termPoint Z x y (F ≫ t.1, t.2.1, t.2.2.1, t.2.2.2) =
      termPoint Z (x ^ q) (y ^ q) t := by
  unfold termPoint
  rw [rootPoint_precompose_power hF]
  congr 1
  simp only [mul_pow, hc, ← pow_mul, Nat.mul_comm]

/-- Transport a literal all-affine-test commutator formula through a
common power, assuming that every coefficient is fixed on each test. -/
theorem CommRel.precompose_power
    {w₁ w₂ : Ga R ⟶ G} {L : List (CommTerm R G)} (h : CommRel w₁ w₂ L)
    (hc : ∀ t ∈ L, ∀ Z : Over (Spec (CommRingCat.of R)),
      (baseScalar Z t.2.1) ^ q = baseScalar Z t.2.1) :
    CommRel (F ≫ w₁) (F ≫ w₂) (powerCommTerms F L) := by
  intro B _ s x y
  rw [rootPoint_precompose_power hF, rootPoint_precompose_power hF,
    h B s (x ^ q) (y ^ q)]
  simp only [powerCommTerms, List.map_map]
  congr 1
  exact List.map_congr_left fun t ht =>
    (termPoint_precompose_power hF t (Over.mk s) x y (hc t ht _)).symm

/-- Integer coefficients of universal commutator formulas are fixed
automatically by any supplied additive-line power homomorphism. -/
theorem CommRel.precompose_power_of_int_coeff
    {w₁ w₂ : Ga R ⟶ G} {L : List (CommTerm R G)} (h : CommRel w₁ w₂ L)
    (hc : ∀ t ∈ L, ∃ n : ℤ, t.2.1 = (n : R)) :
    CommRel (F ≫ w₁) (F ≫ w₂) (powerCommTerms F L) := by
  apply h.precompose_power hF
  intro t ht Z
  obtain ⟨n, hn⟩ := hc t ht
  rw [hn, map_intCast]
  exact map_intCast (sectionPowerRingHom F q hF Z) n

end Langlands.GroupScheme.LocalSplitCell
