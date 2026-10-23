import Langlands.AbelianScheme.Tate.MultiplicativeAffineTestScheme
import Langlands.AbelianScheme.Tate.MultiplicativeRationalAffine
import Langlands.AbelianScheme.Tate.RationalTestScheme

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.Tate
universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X]
variable {R R' : CommRingCat.{u}} (f : Spec R ⟶ S) (r : R ⟶ R') (P : ℕ → Prop)

/-- Rational restriction along the actual affine arrow induced by a ring map. -/
abbrev affineRationalTestRestrict :
    Rational G (Over.mk f) P →ₗ[ℚ] Rational G (Over.mk (Spec.map r ≫ f)) P :=
  rationalTestRestrict G P (affineTestMorphism f r)

end Langlands.GroupScheme.Tate

namespace Langlands.GroupScheme.Gm.TateComparison
universe u
variable {S : Scheme.{u}} {R R' : CommRingCat.{u}}
variable (f : Spec R ⟶ S) (r : R ⟶ R') (P : ℕ → Prop)

/-- Rationalization preserves naturality of the affine comparison. -/
theorem affineRationalEquiv_testRestrict
    (x : Tate.Rational (Gm S).toGrp (Over.mk f) P) :
    affineRationalEquiv (Spec.map r ≫ f) P
        (Tate.affineRationalTestRestrict (Gm S).toGrp f r P x) =
      TateTwist.Divisibility.rationalMap P r.hom (affineRationalEquiv f P x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    change affineRationalEquiv (Spec.map r ≫ f) P
        (Tate.rationalTestRestrict (Gm S).toGrp P (Tate.affineTestMorphism f r) (q ⊗ₜ[ℤ] x)) = _
    simp only [Tate.rationalTestRestrict_tmul, affineRationalEquiv_tmul,
      TateTwist.Divisibility.rationalMap_tmul, affineIntegralEquiv_testRestrict]
  | add x y hx hy => simp_all

/-- Naturality of the inverse affine rational comparison. -/
theorem affineRationalEquiv_symm_testRestrict (x : TateTwist.Divisibility.Rational R P) :
    (affineRationalEquiv (Spec.map r ≫ f) P).symm
        (TateTwist.Divisibility.rationalMap P r.hom x) =
      Tate.affineRationalTestRestrict (Gm S).toGrp f r P ((affineRationalEquiv f P).symm x) := by
  apply (affineRationalEquiv (Spec.map r ≫ f) P).injective
  rw [LinearEquiv.apply_symm_apply, affineRationalEquiv_testRestrict,
    LinearEquiv.apply_symm_apply]

/-- The finite-adelic bundles retain the same naturality. -/
theorem affineFiniteAdeleEquiv_testRestrict (h : Global.RationalProfiniteIntegerAdeleComparison)
    (x : Tate.Rational (Gm S).toGrp (Over.mk f) P) :
    affineFiniteAdeleEquiv (Spec.map r ≫ f) P h
        (Tate.finiteAdeleTestRestrict (Gm S).toGrp P (Tate.affineTestMorphism f r) h x) =
      TateTwist.Divisibility.finiteAdeleMap P h r.hom (affineFiniteAdeleEquiv f P h x) :=
  affineRationalEquiv_testRestrict f r P x

/-- The inverse finite-adelic square uses the same scalar-comparison witness. -/
theorem affineFiniteAdeleEquiv_symm_testRestrict
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    (x : TateTwist.Divisibility.Rational R P) :
    (affineFiniteAdeleEquiv (Spec.map r ≫ f) P h).symm
        (TateTwist.Divisibility.finiteAdeleMap P h r.hom x) =
      Tate.finiteAdeleTestRestrict (Gm S).toGrp P (Tate.affineTestMorphism f r) h
        ((affineFiniteAdeleEquiv f P h).symm x) :=
  affineRationalEquiv_symm_testRestrict f r P x

variable {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
variable (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)

/-- Ring-map naturality retains the coupled away scalar comparison. -/
theorem affinePrimeToFiniteAdeleEquiv_testRestrict
    (x : Tate.RationalAway (Gm S).toGrp (Over.mk f) m) :
    affinePrimeToFiniteAdeleEquiv (Spec.map r ≫ f) hAway
        (Tate.primeToFiniteAdeleTestRestrict (Gm S).toGrp (Tate.affineTestMorphism f r) hAway x) =
      TateTwist.Divisibility.primeToFiniteAdeleMap hAway r.hom
        (affinePrimeToFiniteAdeleEquiv f hAway x) :=
  affineRationalEquiv_testRestrict f r (fun n => Nat.Coprime n m) x

/-- The inverse away finite-adelic square. -/
theorem affinePrimeToFiniteAdeleEquiv_symm_testRestrict
    (x : TateTwist.Divisibility.RationalAway R m) :
    (affinePrimeToFiniteAdeleEquiv (Spec.map r ≫ f) hAway).symm
        (TateTwist.Divisibility.primeToFiniteAdeleMap hAway r.hom x) =
      Tate.primeToFiniteAdeleTestRestrict (Gm S).toGrp (Tate.affineTestMorphism f r) hAway
        ((affinePrimeToFiniteAdeleEquiv f hAway).symm x) :=
  affineRationalEquiv_symm_testRestrict f r (fun n => Nat.Coprime n m) x

variable (p : ℕ) [Fact p.Prime]

/-- Scalar extension of the affine prime-adic comparison square. -/
theorem affinePrimeRationalEquiv_testRestrict
    (x : Tate.PrimeAdic.Rational (Gm S).toGrp (Over.mk f) p) :
    affinePrimeRationalEquiv p (Spec.map r ≫ f)
        (Tate.PrimeAdic.rationalTestRestrict (Gm S).toGrp p (Tate.affineTestMorphism f r) x) =
      TateTwist.rationalMap p r.hom (affinePrimeRationalEquiv p f x) := by
  have hi : (affinePrimeIntegralEquiv p (Spec.map r ≫ f)).toLinearMap.comp
        (Tate.PrimeAdic.testRestrict (Gm S).toGrp p (Tate.affineTestMorphism f r)) =
      (TateTwist.map p r.hom).comp (affinePrimeIntegralEquiv p f).toLinearMap :=
    LinearMap.ext (affinePrimeIntegralEquiv_testRestrict f r p)
  have hq := congrArg (fun k => k.baseChange ℚ_[p]) hi
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at hq
  exact LinearMap.congr_fun hq x

/-- The inverse affine rational prime-adic comparison is natural. -/
theorem affinePrimeRationalEquiv_symm_testRestrict (x : TateTwist.Rational R p) :
    (affinePrimeRationalEquiv p (Spec.map r ≫ f)).symm (TateTwist.rationalMap p r.hom x) =
      Tate.PrimeAdic.rationalTestRestrict (Gm S).toGrp p (Tate.affineTestMorphism f r)
        ((affinePrimeRationalEquiv p f).symm x) := by
  apply (affinePrimeRationalEquiv p (Spec.map r ≫ f)).injective
  rw [LinearEquiv.apply_symm_apply, affinePrimeRationalEquiv_testRestrict,
    LinearEquiv.apply_symm_apply]

end Langlands.GroupScheme.Gm.TateComparison
