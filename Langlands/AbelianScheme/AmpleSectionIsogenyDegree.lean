import Langlands.AbelianScheme.AmpleNonvanishingSection
import Langlands.AbelianScheme.FieldAbelianSchemeGeometry
import Langlands.AlgebraicGeometry.FlatQuasiFiniteStalkDimension
import Langlands.AlgebraicGeometry.Picard.AffineMumfordTransport
import Langlands.AlgebraicGeometry.Picard.FiniteFlatEulerPolynomialCoefficientProof
import Langlands.AlgebraicGeometry.Picard.LineBundleEulerPolynomialSquare

/-! # Degree and ample global sections under an isogeny

The dimension of global sections of an ample line bundle on an abelian variety over an
algebraically closed field multiplies by the degree under pullback by an isogeny.
In particular, when the dimension is unchanged the isogeny is an isomorphism. -/

universe u

open CategoryTheory AlgebraicGeometry Order

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.SchemeModule Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Picard
  Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {K : Type u} [Field K]

/-- A finite flat morphism over the base between abelian schemes over a field preserves
relative dimension. -/
lemma eq_dimension_of_finite_flat {A B : AbelianScheme (Spec (CommRingCat.of K))}
    (f : A.X ⟶ B.X) [IsFinite f.left] [Flat f.left] {g d : ℕ}
    (hA : A.HasRelativeDimension g) (hB : B.HasRelativeDimension d) : g = d := by
  have hi : IsClosedImmersion (unitSection A) :=
    isClosedImmersion_of_comp_eq_id A.X.hom (unitSection A) (unitSection_comp A)
  let x := unitSection A (IsLocalRing.closedPoint K)
  have hx : IsClosed ({x} : Set A.X.left) := by
    have h := (unitSection A).isClosedMap ({IsLocalRing.closedPoint K} : Set (Spec (CommRingCat.of K)))
      (isClosed_discrete _)
    rw [show (fun a ↦ unitSection A a) '' ({IsLocalRing.closedPoint K} :
      Set (Spec (CommRingCat.of K))) = {x} from Set.image_singleton] at h
    exact h
  have hy : IsClosed ({f.left x} : Set B.X.left) := by
    simpa only [Set.image_singleton] using f.left.isClosedMap {x} hx
  have hd := Langlands.AlgebraicGeometry.stalk_ringKrullDim_eq_of_flat_locallyQuasiFinite f.left x
  rw [field_closedPoint_stalk_dimension hA x hx, field_closedPoint_stalk_dimension hB _ hy] at hd
  exact_mod_cast hd

variable [IsAlgClosed K]

/-- For an ample line bundle on an abelian variety, higher cohomology vanishing
identifies its Euler characteristic with the dimension of its global sections. -/
lemma eulerCharacteristic_eq_finrank_ample (A : AbelianScheme (Spec (CommRingCat.of K)))
    (L : LineBundle A.X.left) (hL : L.IsAmple) (h : HasFiniteCohomology A.X.hom L.obj) :
    eulerCharacteristic A.X.hom L.obj h =
      (Module.finrank K ((relativeGlobalSections A.X.hom).obj L.obj) : ℤ) := by
  rw [(eulerCharacteristicBasic K _ A.X.hom).2.2.2.2 _ h
    (ampleLineBundleHigherCohomologyVanishing K A L hL)]
  exact congrArg (Nat.cast : ℕ → ℤ)
    (((relativeCohomologyZeroIso A.X.hom).app L.obj).toLinearEquiv.finrank_eq)

/-- The dimension of the global sections of an ample line bundle is the coefficient at
the dimension of the abelian variety of its actual Euler polynomial. -/
lemma coeff_lineBundleEulerPolynomial_eq_finrank_ample
    (A : AbelianScheme (Spec (CommRingCat.of K))) {g : ℕ} (hg : A.HasRelativeDimension g)
    (L : LineBundle A.X.left) (hL : L.IsAmple) :
    (lineBundleEulerPolynomial A.X.hom L g).coeff g =
      (Module.finrank K ((relativeGlobalSections A.X.hom).obj L.obj) : ℚ) := by
  have := field_isNoetherian A
  have := field_isSeparated A
  have h := lineBundle_hasFiniteCohomology A L
  have he := eulerCharacteristic_eq_finrank_ample A L hL h
  refine lineBundleEulerPolynomial_coeff_eq_of_eulerCharacteristic_sq A.X.hom L g
    (field_topologicalKrullDim hg).le _ (fun k hk hk' ↦ ?_) (fun h1 ↦ ?_)
  · rw [eulerCharacteristic_tensorPow_sq A g hg L hL k hk h hk', he, mul_comm]
  · rw [eulerCharacteristic_eq_of_iso A.X.hom h1 h (tensorPowOneIso _), he]
    positivity

/-- Finite flat pullback between abelian varieties multiplies the dimension of sections
of an ample bundle by the rank of the map at any point. -/
theorem finrank_globalSections_pullback_of_finite_flat
    {A B : AbelianScheme (Spec (CommRingCat.of K))} (f : A.X ⟶ B.X)
    [IsFinite f.left] [Flat f.left] (L : LineBundle B.X.left) (hL : L.IsAmple) (y : B.X.left) :
    Module.finrank K ((relativeGlobalSections A.X.hom).obj
        ((LineBundle.pullback f.left).obj L).obj) =
      f.left.finrank y * Module.finrank K ((relativeGlobalSections B.X.hom).obj L.obj) := by
  have := field_isNoetherian A
  have := field_isNoetherian B
  have := field_isSeparated A
  have := field_isSeparated B
  have := field_isIntegral B
  obtain ⟨g, hg⟩ := Tate.exists_hasRelativeDimension A
  obtain ⟨d, hd⟩ := Tate.exists_hasRelativeDimension B
  obtain rfl := eq_dimension_of_finite_flat f hg hd
  let L' := (LineBundle.pullback f.left).obj L
  have hL' : L'.IsAmple := affinePullbackAmple f.left L hL
  have hF : ∀ n, HasFiniteCohomology (f.left ≫ B.X.hom) (tensorPow L'.obj n) := by
    rw [Over.w f]
    exact lineBundleTensorPow_hasFiniteCohomology A.X.hom L'
  have euler_congr {X : Scheme.{u}} {s s' : X ⟶ Spec (CommRingCat.of K)} (e : s = s')
      (M : X.Modules) (h : HasFiniteCohomology s M) (h' : HasFiniteCohomology s' M) :
      eulerCharacteristic s M h = eulerCharacteristic s' M h' := by
    subst e
    rfl
  have key := finiteFlatEulerPolynomialCoefficient K A.X.left B.X.left B.X.hom inferInstance
    inferInstance inferInstance inferInstance f.left inferInstance inferInstance g
    (field_topologicalKrullDim hd).le L (lineBundleTensorPow_hasFiniteCohomology B.X.hom L) hF
    (lineBundleEulerPolynomial B.X.hom L g) (lineBundleEulerPolynomial A.X.hom L' g)
    (fun n ↦ lineBundleEulerPolynomial_eval B.X.hom L g (field_topologicalKrullDim hd).le n _)
    (fun n ↦ by
      rw [lineBundleEulerPolynomial_eval A.X.hom L' g (field_topologicalKrullDim hg).le n
        (lineBundleTensorPow_hasFiniteCohomology A.X.hom L' n)]
      exact congrArg (Int.cast : ℤ → ℚ) (euler_congr (Over.w f).symm _ _ _)) y
  rw [coeff_lineBundleEulerPolynomial_eq_finrank_ample A hg L' hL',
    coeff_lineBundleEulerPolynomial_eq_finrank_ample B hd L hL] at key
  exact_mod_cast key

/-- If the complete space of sections of an ample line bundle does not grow under a
finite flat pullback between abelian varieties, the map is an isomorphism. -/
theorem isIso_of_finrank_globalSections_pullback_eq
    {A B : AbelianScheme (Spec (CommRingCat.of K))} (f : A.X ⟶ B.X)
    [IsFinite f.left] [Flat f.left] (L : LineBundle B.X.left) (hL : L.IsAmple)
    (h : Module.finrank K ((relativeGlobalSections A.X.hom).obj
      ((LineBundle.pullback f.left).obj L).obj) =
      Module.finrank K ((relativeGlobalSections B.X.hom).obj L.obj)) : IsIso f.left := by
  have := field_isNoetherian B
  apply (f.left.isIso_iff_finrank_eq).mpr
  funext y
  have h₀ : Module.finrank K ((relativeGlobalSections B.X.hom).obj L.obj) ≠ 0 := by
    intro hz
    apply eulerCharacteristic_ne_zero_of_isAmple B L hL (lineBundle_hasFiniteCohomology B L)
    rw [eulerCharacteristic_eq_finrank_ample B L hL, hz, Nat.cast_zero]
  have hy := finrank_globalSections_pullback_of_finite_flat f L hL y
  rw [h] at hy
  -- Cancel the positive dimension of the space of sections.
  change f.left.finrank y = 1
  exact (mul_right_cancel₀ h₀ ((one_mul _).trans hy)).symm

end Langlands.AbelianScheme
