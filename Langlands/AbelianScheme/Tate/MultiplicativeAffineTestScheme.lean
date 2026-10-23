import Langlands.AbelianScheme.Tate.MultiplicativeTestScheme
import Langlands.AbelianScheme.Tate.MultiplicativePrimeTestScheme
import Langlands.AbelianScheme.Tate.MultiplicativeDivisibilityAffine

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Tate
universe u
variable {S : Scheme.{u}} {R R' : CommRingCat.{u}}

/-- The actual affine test-scheme arrow induced by a ring morphism. -/
def affineTestMorphism (f : Spec R ⟶ S) (r : R ⟶ R') :
    Over.mk (Spec.map r ≫ f) ⟶ Over.mk f :=
  Over.homMk (Spec.map r) rfl

@[simp] theorem affineTestMorphism_left (f : Spec R ⟶ S) (r : R ⟶ R') :
    (affineTestMorphism f r).left = Spec.map r := rfl

end Langlands.GroupScheme.Tate

namespace Langlands.GroupScheme.Gm.TateComparison
universe u
variable {S : Scheme.{u}} {R R' : CommRingCat.{u}}
variable (f : Spec R ⟶ S) (r : R ⟶ R') (P : ℕ → Prop)

/-- The affine comparison commutes with the actual map of coefficient rings. -/
theorem affineIntegralEquiv_testRestrict
    (x : Tate.Integral (Gm S).toGrp (Over.mk f) P) :
    affineIntegralEquiv (Spec.map r ≫ f) P
        (Tate.testRestrict (Gm S).toGrp P (Tate.affineTestMorphism f r) x) =
      TateTwist.Divisibility.map P r.hom (affineIntegralEquiv f P x) := by
  rw [affineIntegralEquiv_apply, integralEquiv_testRestrict, affineIntegralEquiv_apply]
  change (TateTwist.Divisibility.map P (Scheme.ΓSpecIso R').hom.hom).comp
      (TateTwist.Divisibility.map P (Spec.map r).appTop.hom) _ =
    (TateTwist.Divisibility.map P r.hom).comp
      (TateTwist.Divisibility.map P (Scheme.ΓSpecIso R).hom.hom) _
  rw [← TateTwist.Divisibility.map_comp, ← TateTwist.Divisibility.map_comp]
  have h := congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_naturality r)
  change (Scheme.ΓSpecIso R').hom.hom.comp (Spec.map r).appTop.hom =
    r.hom.comp (Scheme.ΓSpecIso R).hom.hom at h
  rw [h]

/-- Naturality of the inverse affine integral comparison. -/
theorem affineIntegralEquiv_symm_testRestrict (x : TateTwist.Divisibility.Integral R P) :
    (affineIntegralEquiv (Spec.map r ≫ f) P).symm (TateTwist.Divisibility.map P r.hom x) =
      Tate.testRestrict (Gm S).toGrp P (Tate.affineTestMorphism f r)
        ((affineIntegralEquiv f P).symm x) := by
  apply (affineIntegralEquiv (Spec.map r ≫ f) P).injective
  rw [LinearEquiv.apply_symm_apply, affineIntegralEquiv_testRestrict,
    LinearEquiv.apply_symm_apply]

/-- The full continuous bundles have the same ring-map naturality. -/
theorem affineFullContinuousLinearEquiv_testRestrict
    (x : Tate.Full (Gm S).toGrp (Over.mk f)) :
    affineFullContinuousLinearEquiv (Spec.map r ≫ f)
        (Tate.fullTestRestrict (Gm S).toGrp (fun _ => True) (Tate.affineTestMorphism f r) x) =
      TateTwist.Divisibility.fullLinearMap (fun _ => True) r.hom
        (affineFullContinuousLinearEquiv f x) :=
  affineIntegralEquiv_testRestrict f r (fun _ => True) x

/-- The away residue-linear bundles preserve ring-map naturality. -/
theorem affineAwayContinuousLinearEquiv_testRestrict (m : ℕ)
    (x : Tate.Away (Gm S).toGrp (Over.mk f) m) :
    affineAwayContinuousLinearEquiv (Spec.map r ≫ f) m
        (Tate.awayTestRestrict (Gm S).toGrp m (Tate.affineTestMorphism f r) x) =
      TateTwist.Divisibility.awayLinearMap m r.hom (affineAwayContinuousLinearEquiv f m x) :=
  affineIntegralEquiv_testRestrict f r (fun n => Nat.Coprime n m) x

/-- The inverse away comparison satisfies the same square. -/
theorem affineAwayContinuousLinearEquiv_symm_testRestrict (m : ℕ)
    (x : TateTwist.Divisibility.Away R m) :
    (affineAwayContinuousLinearEquiv (Spec.map r ≫ f) m).symm
        (TateTwist.Divisibility.awayLinearMap m r.hom x) =
      Tate.awayTestRestrict (Gm S).toGrp m (Tate.affineTestMorphism f r)
        ((affineAwayContinuousLinearEquiv f m).symm x) :=
  affineIntegralEquiv_symm_testRestrict f r (fun n => Nat.Coprime n m) x

variable (p : ℕ) [Fact p.Prime]

/-- Affine prime-adic comparison is natural for actual ring-induced restriction. -/
theorem affinePrimeIntegralEquiv_testRestrict
    (x : Tate.PrimeAdic.Integral (Gm S).toGrp (Over.mk f) p) :
    affinePrimeIntegralEquiv p (Spec.map r ≫ f)
        (Tate.PrimeAdic.testRestrict (Gm S).toGrp p (Tate.affineTestMorphism f r) x) =
      TateTwist.map p r.hom (affinePrimeIntegralEquiv p f x) := by
  rw [affinePrimeIntegralEquiv_apply, primeIntegralEquiv_testRestrict,
    affinePrimeIntegralEquiv_apply]
  change (TateTwist.map p (Scheme.ΓSpecIso R').hom.hom).comp
      (TateTwist.map p (Spec.map r).appTop.hom) _ =
    (TateTwist.map p r.hom).comp (TateTwist.map p (Scheme.ΓSpecIso R).hom.hom) _
  rw [← TateTwist.map_comp, ← TateTwist.map_comp]
  have h := congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_naturality r)
  change (Scheme.ΓSpecIso R').hom.hom.comp (Spec.map r).appTop.hom =
    r.hom.comp (Scheme.ΓSpecIso R).hom.hom at h
  rw [h]

/-- The inverse affine prime-adic comparison is natural as well. -/
theorem affinePrimeIntegralEquiv_symm_testRestrict (x : TateTwist.Integral R p) :
    (affinePrimeIntegralEquiv p (Spec.map r ≫ f)).symm (TateTwist.map p r.hom x) =
      Tate.PrimeAdic.testRestrict (Gm S).toGrp p (Tate.affineTestMorphism f r)
        ((affinePrimeIntegralEquiv p f).symm x) := by
  apply (affinePrimeIntegralEquiv p (Spec.map r ≫ f)).injective
  rw [LinearEquiv.apply_symm_apply, affinePrimeIntegralEquiv_testRestrict,
    LinearEquiv.apply_symm_apply]

end Langlands.GroupScheme.Gm.TateComparison
