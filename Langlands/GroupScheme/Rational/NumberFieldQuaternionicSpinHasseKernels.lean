import Langlands.GroupScheme.Rational.NumberFieldScalarSpinHasseReduction
import Langlands.GroupScheme.CocycleAffineRefinement
import Langlands.GroupScheme.CocycleKernelTwist
import Langlands.GroupScheme.CentralIsogeny.FiniteGaloisCoefficientLift
import Langlands.GroupScheme.CentralIsogeny.Transport
import Langlands.GroupScheme.Quaternionic.NormOneIsometryConnectedness
import Langlands.GroupScheme.Rational.NumberFieldClassicalTypeDHasseReduction
import Langlands.GroupScheme.SimplyConnected.FactorProjectionUnique
import Langlands.GroupScheme.SimplyConnected.SpinCoverFundamentalWeightTransport
import Langlands.GroupScheme.Derived.SemisimplePerfectProof

/-! # The quaternionic spin Hasse kernel from its norm-one and central parts -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

open Quaternionic GaloisPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The Hasse kernel of the reduced-norm-one isometry group of a nondegenerate quadratic
form over a quaternion division algebra with an orthogonal involution, over a number
field: a cocycle on a finite Galois cover that is trivial after pullback to every
completion is trivial. -/
def NumberFieldQuaternionicNormOneIsometryHasseStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (D : Type u) [DivisionRing D] [Algebra F D] [Algebra.IsCentral F D] [FiniteDimensional F D],
    Module.finrank F D = 4 → ∀ (σ : FirstKindInvolution F D),
    Module.finrank F σ.symmetricSubspace = 3 →
    ∀ (n : ℕ) [NeZero n] (q : σ.QuadraticForms (Fin n)), σ.IsNondegenerateQuadratic q →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ : Cocycle (σ.normOneIsometryGroup q) (GaloisCocycle.cover F L)),
      ξ.LocallyTrivial → ξ.IsTrivial

/-- The central part of the quaternionic spin Hasse kernel: a cocycle with values in the
kernel of a spin cover whose image in the spin group is trivial after pullback to every
completion has trivial image in the spin group. -/
def NumberFieldQuaternionicSpinKernelHasseStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (D : Type u) [DivisionRing D] [Algebra F D] [Algebra.IsCentral F D] [FiniteDimensional F D],
    Module.finrank F D = 4 → ∀ (σ : FirstKindInvolution F D),
    Module.finrank F σ.symmetricSubspace = 3 →
    ∀ (n : ℕ), 4 ≤ n → ∀ (q : σ.QuadraticForms (Fin n)), σ.IsNondegenerateQuadratic q →
    ∀ (G : GroupScheme (Spec (CommRingCat.of F))) (π : G ⟶ σ.isometryGroup q),
    σ.IsSpinCover q π →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (α : Cocycle (kernel π) (GaloisCocycle.cover F L)),
      (α.map (kernelι π)).LocallyTrivial → (α.map (kernelι π)).IsTrivial

section KernelTwist

variable {F : Type u} [Field F] [NumberField F] {G H : GroupScheme (Spec (CommRingCat.of F))}
  {p : G ⟶ H}

end KernelTwist

section ConnectedIsometry

variable {F : Type u} [Field F] {D : Type u} [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D] (σ : FirstKindInvolution F D)
  {n : ℕ} [NeZero n] (q : σ.QuadraticForms (Fin n))

set_option maxHeartbeats 800000 in
/-- If a semisimple group maps onto the identity component `O(q)⁰` by a central isogeny and
the reduced-norm-one isometry group is connected, then `O(q)⁰` is the reduced-norm-one
isometry group. -/
def Quaternionic.FirstKindInvolution.connectedIsometryIsoNormOne [Smooth (σ.isometryGroup q).X.hom]
    {G : GroupScheme (Spec (CommRingCat.of F))} (p : G ⟶ σ.connectedIsometryGroup q)
    (hp : IsCentralIsogeny p) (hG : IsSemisimple G)
    (hconn : ConnectedSpace (σ.normOneIsometryGroup q).X.left) :
    σ.connectedIsometryGroup q ≅ σ.normOneIsometryGroup q := by
  let S := Spec (CommRingCat.of F)
  let i := identityComponentι (σ.isometryGroup q)
  let r := σ.isometryGroupι q ≫ CentralSimpleUnits.reducedNormHom F (Matrix (Fin n) (Fin n) D)
  let j := σ.normOneIsometryGroupι q
  let : IsSeparated (Gm S).X.hom := by
    have : IsSeparated Gm.overSpecZ.{u}.hom := by
      change IsSeparated (Spec.map _)
      infer_instance
    change IsSeparated (Limits.pullback.snd _ (Gm.toSpecZ _))
    infer_instance
  have hGr : (p ≫ i ≫ r).hom.hom = 1 := by
    apply hom_eq_one_of_commute_image (semisimplePerfect F _ hG)
    intro U x y
    apply (Gm.pointsEquiv S U).injective
    rw [_root_.map_mul, _root_.map_mul]
    exact mul_comm _ _
  have := hp.flat
  have := hp.surjective
  have : Epi p.hom.hom.left := Flat.epi_of_flat_of_surjective _
  have : Epi p.hom.hom := Over.epi_of_epi_left _
  have hzero : (i ≫ r).hom.hom = 1 := by
    apply (cancel_epi p.hom.hom).mp
    rw [MonObj.comp_one, ← Grp.comp_hom_hom]
    exact hGr
  have hle : SubgroupFunctor.range i ≤ SubgroupFunctor.range j := by
    intro U y hy
    obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hy
    apply (mem_range_kernelι_iff r _).mpr
    rw [Category.assoc, ← Grp.comp_hom_hom, hzero, MonObj.comp_one]
  have hi : (SubgroupFunctor.range j).IsRepresentedBy j := ⟨kernelι_mono r, rfl⟩
  let h := hi.factorHom i hle
  let g := IdentityComponent.factor (σ.isometryGroup q) j
  have hh : h ≫ j = i := hi.factorHom_comp i hle
  have hg : g ≫ i = j := IdentityComponent.factor_identityComponentι _ _
  refine ⟨h, g, ?_, ?_⟩
  · apply (cancel_mono i).mp
    rw [Category.assoc, hg, hh, Category.id_comp]
  · apply hi.hom_ext
    rw [Category.assoc, hh, hg, Category.id_comp]

end ConnectedIsometry

private theorem cocycle_eq_of_toFun {S : Scheme.{u}} {G : GroupScheme S} {U : Over S}
    {ξ ζ : Cocycle G U} (h : ∀ {Z : Over S} (a b : Z ⟶ U), ξ.toFun a b = ζ.toFun a b) :
    ξ = ζ := by
  obtain ⟨f, _, _⟩ := ξ
  obtain ⟨g, _, _⟩ := ζ
  have : @f = @g := funext fun Z => funext fun a => funext fun b => h a b
  subst this
  rfl

/-- The norm-one Hasse kernel and the central spin kernel give the quaternionic spin Hasse
kernel. -/
theorem numberFieldQuaternionicSpinHasse_of_kernels
    (hA : NumberFieldQuaternionicNormOneIsometryHasseStatement.{u})
    (hB : NumberFieldQuaternionicSpinKernelHasseStatement.{u}) :
    NumberFieldQuaternionicSpinHasseStatement.{u} := by
  intro F _ _ D _ _ _ _ hD σ hσ n hn q hq G π hπ L _ _ _ _ ξ hξ
  have : NeZero n := ⟨by omega⟩
  have hB' := hB F D hD σ hσ n hn q hq G π hπ
  have := hπ.smooth
  obtain ⟨p, hp, hpπ⟩ := hπ.exists_centralIsogeny
  rw [← hpπ] at hB'
  let e := σ.connectedIsometryIsoNormOne q p hp hπ.isSimplyConnected.isSemisimple
    (quaternionicNormOneIsometryConnectedness F D hD σ hσ n q hq)
  have hp' : IsCentralIsogeny (p ≫ e.hom) := hp.comp_iso e
  have : Mono e.hom.hom.hom := by
    have : IsIso e.hom.hom.hom := (Grp.forget (Over (Spec (CommRingCat.of F)))).map_isIso e.hom
    infer_instance
  refine Cocycle.isTrivial_of_kernelHasse hp' ?_ ξ hξ
    (hA F D hD σ hσ n q hq L (ξ.map (p ≫ e.hom)) (hξ.map _))
  intro L' _ _ _ _ α hα
  let incl := identityComponentι (σ.isometryGroup q)
  let k : kernel (p ≫ e.hom) ⟶ kernel (p ≫ incl) :=
    (kernelPostcompIso p e.hom).hom ≫ (kernelPostcompIso p incl).inv
  have hk : k ≫ kernelι (p ≫ incl) = kernelι (p ≫ e.hom) := by
    rw [Category.assoc, (Iso.inv_comp_eq _).mpr (kernelPostcompIso_hom_ι p incl).symm,
      kernelPostcompIso_hom_ι]
  have heq : (α.map k).map (kernelι (p ≫ incl)) = α.map (kernelι (p ≫ e.hom)) := by
    apply cocycle_eq_of_toFun
    intro Z a b
    change (α.toFun a b ≫ k.hom.hom) ≫ (kernelι (p ≫ incl)).hom.hom =
      α.toFun a b ≫ (kernelι (p ≫ e.hom)).hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, hk]
  rw [← heq] at hα ⊢
  exact hB' L' (α.map k) hα

end Langlands.GroupScheme
