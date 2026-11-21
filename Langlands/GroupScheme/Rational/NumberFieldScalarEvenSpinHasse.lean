import Langlands.GroupScheme.CliffordSpin.ScalarNormOneConnectedness
import Langlands.GroupScheme.Quaternionic.ScalarSpinKernelDegree
import Langlands.GroupScheme.Rational.NumberFieldScalarSpinCoverHasse
import Langlands.GroupScheme.SimplyConnected.FactorProjectionUnique
import Langlands.GroupScheme.SimplyConnected.SpinCoverFundamentalWeightTransport
import Langlands.GroupScheme.Derived.SemisimplePerfectProof
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # The Hasse kernel for scalar even spin groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Quaternionic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

section ScalarConnectedIsometry

variable {F : Type u} [Field F] [CharZero F] [Invertible (2 : F)] {n : ℕ} [NeZero n]
  (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin n))

local notation "τ" => FirstKindInvolution.scalar F
local notation "O" => FirstKindInvolution.isometryGroup τ q
local notation "SO" => FirstKindInvolution.normOneIsometryGroup τ q
local notation "normInclusion" => FirstKindInvolution.normOneIsometryGroupι τ q
local notation "S" => Spec (CommRingCat.of F)

/-- If the regular scalar isometry group's identity component is semisimple, it is its
actual norm-one subgroup. -/
def scalarConnectedIsometryIso_normOne [Smooth ((FirstKindInvolution.scalar F).isometryGroup q).X.hom]
    (hq : (τ).IsNondegenerateQuadratic q)
    (hsem : IsSemisimple ((τ).connectedIsometryGroup q)) : (τ).connectedIsometryGroup q ≅ SO := by
  let i := identityComponentι (O)
  let r := (τ).isometryGroupι q ≫ CentralSimpleUnits.reducedNormHom F (Matrix (Fin n) (Fin n) F)
  have hzero : (i ≫ r).hom.hom = 1 := by
    let : IsSeparated (Gm S).X.hom := by
      have : IsSeparated Gm.overSpecZ.{u}.hom := by
        change IsSeparated (Spec.map _)
        infer_instance
      change IsSeparated (Limits.pullback.snd _ (Gm.toSpecZ _))
      infer_instance
    apply hom_eq_one_of_commute_image (semisimplePerfect F _ hsem)
    intro U x y
    apply (Gm.pointsEquiv S U).injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  have hle : SubgroupFunctor.range i ≤ SubgroupFunctor.range (normInclusion) := by
    intro U y hy
    obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hy
    apply (mem_range_kernelι_iff r _).mpr
    rw [Category.assoc, ← Grp.comp_hom_hom, hzero, MonObj.comp_one]
  have hi : (SubgroupFunctor.range (normInclusion)).IsRepresentedBy (normInclusion) :=
    ⟨kernelι_mono r, rfl⟩
  haveI : ConnectedSpace (SO).X.left := CliffordSpin.connectedSpace_scalarNormOne q hq
  let h := hi.factorHom i hle
  let g := IdentityComponent.factor (O) (normInclusion)
  have hh : h ≫ (normInclusion) = i := hi.factorHom_comp i hle
  have hg : g ≫ i = normInclusion := IdentityComponent.factor_identityComponentι _ _
  refine ⟨h, g, ?_, ?_⟩
  · apply (cancel_mono i).mp
    rw [Category.assoc, hg, hh, Category.id_comp]
  · apply hi.hom_ext
    rw [Category.assoc, hh, hg, Category.id_comp]

end ScalarConnectedIsometry

/-- Over a number field, any spin cover of a regular scalar quadratic form of dimension
`2 * n` with `3 ≤ n` has trivial Hasse kernel on its given finite Galois cover. -/
def NumberFieldScalarEvenSpinHasseStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (n : ℕ), 3 ≤ n →
    ∀ (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin (2 * n))),
      (FirstKindInvolution.scalar F).IsNondegenerateQuadratic q →
      ∀ (G : GroupScheme (Spec (CommRingCat.of F)))
        (π : G ⟶ (FirstKindInvolution.scalar F).isometryGroup q),
        (FirstKindInvolution.scalar F).IsSpinCover q π →
        ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
          (ξ : Cocycle G (GaloisCocycle.cover F L)), ξ.LocallyTrivial → ξ.IsTrivial

/-- The scalar spin Hasse kernel follows by identifying the actual even orthogonal
identity component with the norm-one group and transporting the kernel degree. -/
theorem numberFieldScalarEvenSpinHasse : NumberFieldScalarEvenSpinHasseStatement.{u} := by
  intro F _ _ n hn q hq G π hπ L _ _ _ _ ξ hξ
  let : Invertible (2 : F) := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
  let : NeZero (2 * n) := ⟨by omega⟩
  have := hπ.smooth
  obtain ⟨p, hp, _⟩ := hπ.exists_centralIsogeny
  obtain ⟨hs, habs⟩ := ordinaryOrthogonalGeometry F n hn q hq
  let e := scalarConnectedIsometryIso_normOne q hq habs.1.isSemisimple
  let S := Spec (CommRingCat.of F)
  let K := AlgebraicClosure F
  let A := CommAlgCat.of F K
  have hm : Mono e.hom.hom.hom := by
    have : IsIso e.hom.hom.hom := (Grp.forget (Over S)).map_isIso e.hom
    infer_instance
  let j := (Grp.forget (Over S)).mapIso (kernelPostcompIso p e.hom)
  have hker : Nat.card (affinePoints (kernel (p ≫ e.hom)) A) = 2 :=
    (Nat.card_congr j.homToEquiv).trans
      (FirstKindInvolution.natCard_scalarEvenSpinKernel q hn hq p hπ.isSimplyConnected hp)
  exact numberFieldScalarSpinCoverHasse F K (2 * n) q hq (by omega)
    (IsSemisimple.of_iso e.symm habs.1.isSemisimple) G _ hπ.isSimplyConnected (hp.comp_iso e) hker L ξ hξ

end Langlands.GroupScheme
