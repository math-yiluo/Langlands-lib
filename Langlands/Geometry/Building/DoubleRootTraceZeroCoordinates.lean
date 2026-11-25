import Langlands.Geometry.Building.RootQuotientFieldCoordinates
import Langlands.GroupScheme.Rational.RootHeisenbergCocycleLie
import Langlands.GroupScheme.Examples.SU3RootUnitaryCoordinates
import Langlands.GroupScheme.HomConjugacy

/-! # Trace-zero coordinates for the actual doubled root group -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

universe u v w

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SU3Root

variable (F : Type v) (E : Type w) [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
  (eta0 : Parameters.traceZero (fieldInvolution F E)) (heta0 : (eta0 : E) ≠ 0)

/-- Multiplication by a nonzero trace-zero scalar identifies the base field with
its quadratic extension's trace-zero additive subgroup. -/
def traceZeroScalarEquiv : F ≃+ Parameters.traceZero (fieldInvolution F E) :=
  AddEquiv.ofBijective
    ({
      toFun := fun c => ⟨algebraMap F E c * (eta0 : E), by
        change _ + conjugation F E _ = 0
        rw [map_mul, AlgEquiv.commutes, ← mul_add, show (eta0 : E) + conjugation F E (eta0 : E) = 0 from eta0.property, mul_zero]⟩
      map_zero' := by apply Subtype.ext; simp
      map_add' := by intro c d; apply Subtype.ext; simp [add_mul] } :
        F →+ Parameters.traceZero (fieldInvolution F E))
    ⟨by
      intro c d h
      exact (algebraMap F E).injective ((mul_left_inj' heta0).mp (congrArg Subtype.val h)), by
      intro z
      obtain ⟨c, hc⟩ := exists_algebraMap_mul_eq_of_traceZero F E heta0 eta0.property z.property
      exact ⟨c, Subtype.ext hc⟩⟩

@[simp]
theorem traceZeroScalarEquiv_coe (c : F) :
    (traceZeroScalarEquiv F E eta0 heta0 c : E) = algebraMap F E c * (eta0 : E) := rfl

@[simp]
theorem traceZeroScalarEquiv_symm_mul (z : Parameters.traceZero (fieldInvolution F E)) :
    algebraMap F E ((traceZeroScalarEquiv F E eta0 heta0).symm z) * (eta0 : E) = z :=
  congrArg Subtype.val ((traceZeroScalarEquiv F E eta0 heta0).apply_symm_apply z)

/-- The inverse trace-zero coordinate respects multiplication by base scalars. -/
theorem traceZeroScalarEquiv_symm_mul_of_eq (c : F)
    (z z' : Parameters.traceZero (fieldInvolution F E))
    (hz : (z' : E) = algebraMap F E c * (z : E)) :
    (traceZeroScalarEquiv F E eta0 heta0).symm z' =
      c * (traceZeroScalarEquiv F E eta0 heta0).symm z := by
  apply (algebraMap F E).injective
  apply (mul_left_inj' heta0).mp
  rw [map_mul, mul_assoc, traceZeroScalarEquiv_symm_mul, traceZeroScalarEquiv_symm_mul, hz]

variable (k : Type u) [Field k] [Algebra k F] [Algebra k E] [IsScalarTower k F E]

/-- In a compatible field tower, inverse trace-zero coordinates respect base-field
scalars, without installing a module instance on the trace-zero subgroup. -/
theorem traceZeroScalarEquiv_symm_smul_of_eq (c : k)
    (z z' : Parameters.traceZero (fieldInvolution F E)) (hz : (z' : E) = c • (z : E)) :
    (traceZeroScalarEquiv F E eta0 heta0).symm z' =
      c • (traceZeroScalarEquiv F E eta0 heta0).symm z := by
  simpa only [Algebra.smul_def] using
    traceZeroScalarEquiv_symm_mul_of_eq F E eta0 heta0 (algebraMap k F c) z z' (by
      simpa only [IsScalarTower.algebraMap_apply k F E, Algebra.smul_def] using hz)

end Langlands.GroupScheme.SU3Root

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G H U₂ : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [IsAffineHom U₂.X.hom]
    {i : S.toGrp ⟶ G} {a : characterLattice S} {j₂ : U₂ ⟶ G}

/-- The represented doubled-root comparison intertwines a torus-fixing action
with its differential. -/
theorem doubleRootPointLieEquiv_act
    (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i)
    (hj₂ : (subgroup i (2 • a)).IsRepresentedBy j₂)
    (b : AutomorphicAction H G)
    (hfix : ∀ (X : Over (Spec (CommRingCat.of k))) (z : X ⟶ H.X) (t : X ⟶ S.X),
      b.act z (t ≫ i.hom.hom) = t ≫ i.hom.hom)
    (z : rationalPoints H) (x : rationalPoints U₂) :
    (doubleRootPointLieEquiv hS ha hhigh hj₂
        (Additive.ofMul ((rootActionOfFixesTorus b i hfix (2 • a) j₂ hj₂).act z x)) :
          Additive (lieKernel G k)) =
      b.differential (GaloisPointComparison.rationalCoeffEquiv k H z)
        (doubleRootPointLieEquiv hS ha hhigh hj₂ (Additive.ofMul x)) := by
  have hp : hj₂.pointsEquiv _
      ((rootActionOfFixesTorus b i hfix (2 • a) j₂ hj₂).act z x) =
      rootPointsAutOfFixesTorus i (2 • a) (b.basePointIso z)
        (basePointIso_fixes_torus i b hfix z) _ (hj₂.pointsEquiv _ x) := by
    apply Subtype.ext
    change ((rootActionOfFixesTorus b i hfix (2 • a) j₂ hj₂).act z x) ≫ j₂.hom.hom =
      (x ≫ j₂.hom.hom) ≫ (b.basePointIso z).hom.hom.hom
    rw [rootActionOfFixesTorus_act_comp, b.comp_basePointIso_hom,
      GroupScheme.constantPoint_self]
  have hnat := representedRootPointLieEquiv_aut_apply hS i
    (two_nsmul_ne_zero_of_isSplitTorus hS ha) (hasNoHigherRoots_two_nsmul hhigh)
    (b.basePointIso z) (basePointIso_fixes_torus i b hfix z) hj₂ x
  rw [← hp, b.targetMapLinear_basePointIso,
    DoubleRootCommutatorPairing.constantPoint_eq_rationalCoeffEquiv] at hnat
  exact hnat

end Langlands.GroupScheme.RelativeRoot

namespace Langlands.Geometry.Building

open Langlands.GroupScheme Langlands.GroupScheme.RelativeRoot

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (f : S ⟶ T) (j : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k L
local notation "G_L" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "T_L" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "j_L" => CategoryTheory.Functor.map (GroupScheme.baseChange b) j

private local instance : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

attribute [local instance] rootsGaloisAction

variable [FiniteDimensional k L] [IsGalois k L] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
  {a : characterLattice S} {U₂ : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom U₂.X.hom]
  {j₂ : U₂ ⟶ G}

/-- Coordinates on the doubled root group obtained through its represented
point-to-Lie comparison. -/
def doubleRootFieldEquiv
    (hj₂ : (subgroup (CommGroupScheme.groupHom f ≫ j) (2 • a)).IsRepresentedBy j₂)
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus (T_L).toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (mu0 : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) mu0 = rootRestrictionFiber k L j f (2 • a)) :
    Multiplicative (rootOrbitField k L j mu0) ≃* rationalPoints U₂ :=
  AddEquiv.toMultiplicativeLeft
    ((rootOrbitFieldWeightSpaceLinearEquiv k L j f (2 • a) hG hj hS hT
      (two_nsmul_ne_zero_of_isSplitTorus hS ha) mu0 horbit).toAddEquiv.trans
      (doubleRootPointLieEquiv hS ha hhigh hj₂).symm)

@[simp]
theorem doubleRootPointLieEquiv_doubleRootFieldEquiv
    (hj₂ : (subgroup (CommGroupScheme.groupHom f ≫ j) (2 • a)).IsRepresentedBy j₂)
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus (T_L).toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (mu0 : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) mu0 = rootRestrictionFiber k L j f (2 • a))
    (x : rootOrbitField k L j mu0) :
    doubleRootPointLieEquiv hS ha hhigh hj₂
      (Additive.ofMul (doubleRootFieldEquiv k L f j hj₂ hG hj hS hT ha hhigh mu0 horbit
        (Multiplicative.ofAdd x))) =
    rootOrbitFieldWeightSpaceLinearEquiv k L j f (2 • a) hG hj hS hT
      (two_nsmul_ne_zero_of_isSplitTorus hS ha) mu0 horbit x := by
  change (doubleRootPointLieEquiv hS ha hhigh hj₂)
    ((doubleRootPointLieEquiv hS ha hhigh hj₂).symm
      (rootOrbitFieldWeightSpaceLinearEquiv k L j f (2 • a) hG hj hS hT
        (two_nsmul_ne_zero_of_isSplitTorus hS ha) mu0 horbit x)) = _
  exact AddEquiv.apply_symm_apply _ _

/-- The doubled-root field coordinates are linear through the represented
point-to-Lie comparison. -/
theorem doubleRootFieldEquiv_smul
    (hj₂ : (subgroup (CommGroupScheme.groupHom f ≫ j) (2 • a)).IsRepresentedBy j₂)
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus (T_L).toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (mu0 : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) mu0 = rootRestrictionFiber k L j f (2 • a))
    (c : k) (x : rootOrbitField k L j mu0) :
    (doubleRootPointLieEquiv hS ha hhigh hj₂
      (Additive.ofMul (doubleRootFieldEquiv k L f j hj₂ hG hj hS hT ha hhigh mu0 horbit
        (Multiplicative.ofAdd (c • x)))) : Additive (lieKernel G k)) =
    c • (doubleRootPointLieEquiv hS ha hhigh hj₂
      (Additive.ofMul (doubleRootFieldEquiv k L f j hj₂ hG hj hS hT ha hhigh mu0 horbit
        (Multiplicative.ofAdd x))) : Additive (lieKernel G k)) := by
  rw [doubleRootPointLieEquiv_doubleRootFieldEquiv, doubleRootPointLieEquiv_doubleRootFieldEquiv,
    LinearEquiv.map_smul, Submodule.coe_smul]

/-- Rational torus conjugation scales doubled-root field coordinates by the
value of the doubled absolute root. -/
theorem doubleRootFieldEquiv_act
    [IsAffineHom T.toGrp.X.hom]
    (hj₂ : (subgroup (CommGroupScheme.groupHom f ≫ j) (2 • a)).IsRepresentedBy j₂)
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus (T_L).toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (mu0 : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) mu0 = rootRestrictionFiber k L j f (2 • a))
    (hfix : ∀ (X : Over (Spec (CommRingCat.of k))) (z : X ⟶ T.toGrp.X) (t : X ⟶ S.X),
      (AutomorphicAction.conjugation j).act z (t ≫ (CommGroupScheme.groupHom f ≫ j).hom.hom) =
        t ≫ (CommGroupScheme.groupHom f ≫ j).hom.hom)
    (z : rationalPoints T.toGrp) (x : rootOrbitField k L j mu0) :
    (rootActionOfFixesTorus (AutomorphicAction.conjugation j) (CommGroupScheme.groupHom f ≫ j)
      hfix (2 • a) j₂ hj₂).act z
        (doubleRootFieldEquiv k L f j hj₂ hG hj hS hT ha hhigh mu0 horbit
          (Multiplicative.ofAdd x)) =
      doubleRootFieldEquiv k L f j hj₂ hG hj hS hT ha hhigh mu0 horbit
        (Multiplicative.ofAdd (rootOrbitCharacterValue k L j mu0
          (GaloisPointComparison.rationalCoeffEquiv k T.toGrp z) * x)) := by
  set R := doubleRootPointLieEquiv hS ha hhigh hj₂
  set W := rootOrbitFieldWeightSpaceLinearEquiv k L j f (2 • a) hG hj hS hT
    (two_nsmul_ne_zero_of_isSplitTorus hS ha) mu0 horbit
  set e := doubleRootFieldEquiv k L f j hj₂ hG hj hS hT ha hhigh mu0 horbit
  have key := doubleRootPointLieEquiv_act hS ha hhigh hj₂
    (AutomorphicAction.conjugation j) hfix z (e (Multiplicative.ofAdd x))
  rw [doubleRootPointLieEquiv_doubleRootFieldEquiv] at key
  have hW := conjugation_differential_rootOrbitFieldWeightSpaceEquiv k L j f (2 • a)
    hG hj hS hT (two_nsmul_ne_zero_of_isSplitTorus hS ha) mu0 horbit z x
  have key2 : R (Additive.ofMul
      ((rootActionOfFixesTorus (AutomorphicAction.conjugation j) (CommGroupScheme.groupHom f ≫ j)
        hfix (2 • a) j₂ hj₂).act z (e (Multiplicative.ofAdd x)))) =
      W (rootOrbitCharacterValue k L j mu0 (GaloisPointComparison.rationalCoeffEquiv k T.toGrp z) *
        x) :=
    Subtype.ext (key.trans hW)
  rw [← doubleRootPointLieEquiv_doubleRootFieldEquiv k L f j hj₂ hG hj hS hT ha hhigh mu0 horbit]
    at key2
  exact Additive.ofMul.injective (R.injective key2)

/-- The same action formula written using the descended actual character. -/
theorem doubleRootFieldEquiv_act_character
    [IsAffineHom T.toGrp.X.hom] [IsAffine T.toGrp.X.left]
    (hj₂ : (subgroup (CommGroupScheme.groupHom f ≫ j) (2 • a)).IsRepresentedBy j₂)
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus (T_L).toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (mu0 : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) mu0 = rootRestrictionFiber k L j f (2 • a))
    (hfix : ∀ (X : Over (Spec (CommRingCat.of k))) (z : X ⟶ T.toGrp.X) (t : X ⟶ S.X),
      (AutomorphicAction.conjugation j).act z (t ≫ (CommGroupScheme.groupHom f ≫ j).hom.hom) =
        t ≫ (CommGroupScheme.groupHom f ≫ j).hom.hom)
    (z : rationalPoints T.toGrp) (x : rootOrbitField k L j mu0) :
    (rootActionOfFixesTorus (AutomorphicAction.conjugation j) (CommGroupScheme.groupHom f ≫ j)
      hfix (2 • a) j₂ hj₂).act z
        (doubleRootFieldEquiv k L f j hj₂ hG hj hS hT ha hhigh mu0 horbit
          (Multiplicative.ofAdd x)) =
      doubleRootFieldEquiv k L f j hj₂ hG hj hS hT ha hhigh mu0 horbit
        (Multiplicative.ofAdd ((rationalCharacterEval (rootOrbitCharacter k L j mu0)
          (GaloisPointComparison.rationalExtend k (rootOrbitField k L j mu0) T.toGrp z) :
            rootOrbitField k L j mu0) * x)) := by
  rw [rationalCharacterEval_rootOrbitCharacter]
  exact doubleRootFieldEquiv_act k L f j hj₂ hG hj hS hT ha hhigh mu0 horbit hfix z x

section TraceZero

/-- Trace-zero coordinates for the represented doubled root group. -/
def doubleRootTraceZeroEquiv
    (mu0 : roots (T := T_L) (G := G_L) j_L)
    (E : Type v) [Field E] [Algebra (rootOrbitField k L j mu0) E]
    [Algebra.IsQuadraticExtension (rootOrbitField k L j mu0) E]
    [Algebra.IsSeparable (rootOrbitField k L j mu0) E]
    (hj₂ : (subgroup (CommGroupScheme.groupHom f ≫ j) (2 • a)).IsRepresentedBy j₂)
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus (T_L).toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (horbit : MulAction.orbit (L ≃ₐ[k] L) mu0 = rootRestrictionFiber k L j f (2 • a))
    (eta0 : (SU3Root.Parameters.traceZero (SU3Root.fieldInvolution (rootOrbitField k L j mu0) E))) (heta0 : (eta0 : E) ≠ 0) :
    Multiplicative (SU3Root.Parameters.traceZero (SU3Root.fieldInvolution (rootOrbitField k L j mu0) E)) ≃* rationalPoints U₂ :=
  (AddEquiv.toMultiplicative (SU3Root.traceZeroScalarEquiv (rootOrbitField k L j mu0) E eta0 heta0).symm).trans
    (doubleRootFieldEquiv k L f j hj₂ hG hj hS hT ha hhigh mu0 horbit)

/-- A scalar relation between trace-zero parameters is carried to the same
scalar relation under the doubled-root Lie comparison. -/
theorem doubleRootTraceZeroEquiv_smul
    (mu0 : roots (T := T_L) (G := G_L) j_L)
    (E : Type v) [Field E] [Algebra (rootOrbitField k L j mu0) E]
    [Algebra.IsQuadraticExtension (rootOrbitField k L j mu0) E]
    [Algebra.IsSeparable (rootOrbitField k L j mu0) E]
    [Algebra k E] [IsScalarTower k (rootOrbitField k L j mu0) E]
    (hj₂ : (subgroup (CommGroupScheme.groupHom f ≫ j) (2 • a)).IsRepresentedBy j₂)
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus (T_L).toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (horbit : MulAction.orbit (L ≃ₐ[k] L) mu0 = rootRestrictionFiber k L j f (2 • a))
    (eta0 : (SU3Root.Parameters.traceZero (SU3Root.fieldInvolution (rootOrbitField k L j mu0) E))) (heta0 : (eta0 : E) ≠ 0)
    (c : k) (w w' : (SU3Root.Parameters.traceZero (SU3Root.fieldInvolution (rootOrbitField k L j mu0) E))) (hw : (w' : E) = c • (w : E)) :
    (doubleRootPointLieEquiv hS ha hhigh hj₂
      (Additive.ofMul (doubleRootTraceZeroEquiv k L f j mu0 E hj₂ hG hj hS hT ha hhigh horbit
        eta0 heta0 (Multiplicative.ofAdd w'))) : Additive (lieKernel G k)) =
      c • (doubleRootPointLieEquiv hS ha hhigh hj₂
        (Additive.ofMul (doubleRootTraceZeroEquiv k L f j mu0 E hj₂ hG hj hS hT ha hhigh horbit
          eta0 heta0 (Multiplicative.ofAdd w))) : Additive (lieKernel G k)) := by
  change (doubleRootPointLieEquiv hS ha hhigh hj₂
      (Additive.ofMul (doubleRootFieldEquiv k L f j hj₂ hG hj hS hT ha hhigh mu0 horbit
        (Multiplicative.ofAdd ((SU3Root.traceZeroScalarEquiv (rootOrbitField k L j mu0) E eta0 heta0).symm w')))) :
        Additive (lieKernel G k)) = _
  rw [SU3Root.traceZeroScalarEquiv_symm_smul_of_eq (rootOrbitField k L j mu0) E eta0 heta0 k c w w' hw]
  exact doubleRootFieldEquiv_smul k L f j hj₂ hG hj hS hT ha hhigh mu0 horbit c _

/-- If the doubled-root character value is a prescribed quadratic norm, the
trace-zero coordinates intertwine the actual action with that norm. -/
theorem doubleRootTraceZeroEquiv_act
    (mu0 : roots (T := T_L) (G := G_L) j_L)
    (E : Type v) [Field E] [Algebra (rootOrbitField k L j mu0) E]
    [Algebra.IsQuadraticExtension (rootOrbitField k L j mu0) E]
    [Algebra.IsSeparable (rootOrbitField k L j mu0) E]
    [IsAffineHom T.toGrp.X.hom] [IsAffine T.toGrp.X.left]
    (hj₂ : (subgroup (CommGroupScheme.groupHom f ≫ j) (2 • a)).IsRepresentedBy j₂)
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus (T_L).toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (horbit : MulAction.orbit (L ≃ₐ[k] L) mu0 = rootRestrictionFiber k L j f (2 • a))
    (hfix : ∀ (X : Over (Spec (CommRingCat.of k))) (z : X ⟶ T.toGrp.X) (t : X ⟶ S.X),
      (AutomorphicAction.conjugation j).act z (t ≫ (CommGroupScheme.groupHom f ≫ j).hom.hom) =
        t ≫ (CommGroupScheme.groupHom f ≫ j).hom.hom)
    (eta0 : (SU3Root.Parameters.traceZero (SU3Root.fieldInvolution (rootOrbitField k L j mu0) E))) (heta0 : (eta0 : E) ≠ 0)
    (z : rationalPoints T.toGrp) (value : E)
    (hnorm : algebraMap (rootOrbitField k L j mu0) E (rationalCharacterEval (rootOrbitCharacter k L j mu0)
        (GaloisPointComparison.rationalExtend k (rootOrbitField k L j mu0) T.toGrp z) : (rootOrbitField k L j mu0)) =
      value * SU3Root.conjugation (rootOrbitField k L j mu0) E value)
    (w w' : (SU3Root.Parameters.traceZero (SU3Root.fieldInvolution (rootOrbitField k L j mu0) E))) (hw : (w' : E) = value * SU3Root.conjugation (rootOrbitField k L j mu0) E value * (w : E)) :
    (rootActionOfFixesTorus (AutomorphicAction.conjugation j) (CommGroupScheme.groupHom f ≫ j)
      hfix (2 • a) j₂ hj₂).act z
        (doubleRootTraceZeroEquiv k L f j mu0 E hj₂ hG hj hS hT ha hhigh horbit eta0 heta0
          (Multiplicative.ofAdd w)) =
      doubleRootTraceZeroEquiv k L f j mu0 E hj₂ hG hj hS hT ha hhigh horbit eta0 heta0
        (Multiplicative.ofAdd w') := by
  change (rootActionOfFixesTorus (AutomorphicAction.conjugation j) (CommGroupScheme.groupHom f ≫ j)
      hfix (2 • a) j₂ hj₂).act z
        (doubleRootFieldEquiv k L f j hj₂ hG hj hS hT ha hhigh mu0 horbit
          (Multiplicative.ofAdd ((SU3Root.traceZeroScalarEquiv (rootOrbitField k L j mu0) E eta0 heta0).symm w))) = _
  rw [doubleRootFieldEquiv_act_character]
  apply congrArg (fun x : (rootOrbitField k L j mu0) =>
    doubleRootFieldEquiv k L f j hj₂ hG hj hS hT ha hhigh mu0 horbit (Multiplicative.ofAdd x))
  exact (SU3Root.traceZeroScalarEquiv_symm_mul_of_eq (rootOrbitField k L j mu0) E eta0 heta0 _ w w'
    (by rw [hnorm]; exact hw)).symm

/-- Existence of doubled-root trace-zero coordinates with the linearity and
norm-action laws used by the Heisenberg field-data construction. -/
def HasDoubleRootTraceZeroCoordinates
    (mu0 : roots (T := T_L) (G := G_L) j_L)
    (E : Type v) [Field E] [Algebra (rootOrbitField k L j mu0) E]
    [Algebra.IsQuadraticExtension (rootOrbitField k L j mu0) E]
    [Algebra.IsSeparable (rootOrbitField k L j mu0) E]
    [Algebra k E] [IsScalarTower k (rootOrbitField k L j mu0) E]
    (hj₂ : (subgroup (CommGroupScheme.groupHom f ≫ j) (2 • a)).IsRepresentedBy j₂)
    (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (hfix : ∀ (X : Over (Spec (CommRingCat.of k))) (z : X ⟶ T.toGrp.X) (t : X ⟶ S.X),
      (AutomorphicAction.conjugation j).act z (t ≫ (CommGroupScheme.groupHom f ≫ j).hom.hom) =
        t ≫ (CommGroupScheme.groupHom f ≫ j).hom.hom)
    (value : rationalPoints T.toGrp → E) : Prop :=
  ∃ second : Multiplicative (SU3Root.Parameters.traceZero
      (SU3Root.fieldInvolution (rootOrbitField k L j mu0) E)) ≃* rationalPoints U₂,
    (∀ (c : k) (w w' : SU3Root.Parameters.traceZero
        (SU3Root.fieldInvolution (rootOrbitField k L j mu0) E)),
      (w' : E) = c • (w : E) →
      (doubleRootPointLieEquiv hS ha hhigh hj₂ (Additive.ofMul (second (Multiplicative.ofAdd w'))) :
          Additive (lieKernel G k)) =
        c • (doubleRootPointLieEquiv hS ha hhigh hj₂
          (Additive.ofMul (second (Multiplicative.ofAdd w))) : Additive (lieKernel G k))) ∧
    ∀ (z : rationalPoints T.toGrp) (w w' : SU3Root.Parameters.traceZero
        (SU3Root.fieldInvolution (rootOrbitField k L j mu0) E)),
      (w' : E) = value z * SU3Root.conjugation (rootOrbitField k L j mu0) E (value z) * (w : E) →
      (rootActionOfFixesTorus (AutomorphicAction.conjugation j) (CommGroupScheme.groupHom f ≫ j)
        hfix (2 • a) j₂ hj₂).act z (second (Multiplicative.ofAdd w)) =
        second (Multiplicative.ofAdd w')

/-- A doubled absolute-root orbit and a norm identity provide the trace-zero
coordinates; the nonzero trace-zero scalar need not be supplied. -/
theorem hasDoubleRootTraceZeroCoordinates
    (mu0 : roots (T := T_L) (G := G_L) j_L)
    (E : Type v) [Field E] [Algebra (rootOrbitField k L j mu0) E]
    [Algebra.IsQuadraticExtension (rootOrbitField k L j mu0) E]
    [Algebra.IsSeparable (rootOrbitField k L j mu0) E]
    [Algebra k E] [IsScalarTower k (rootOrbitField k L j mu0) E]
    [IsAffineHom T.toGrp.X.hom] [IsAffine T.toGrp.X.left]
    (hj₂ : (subgroup (CommGroupScheme.groupHom f ≫ j) (2 • a)).IsRepresentedBy j₂)
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus (T_L).toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (horbit : MulAction.orbit (L ≃ₐ[k] L) mu0 = rootRestrictionFiber k L j f (2 • a))
    (hfix : ∀ (X : Over (Spec (CommRingCat.of k))) (z : X ⟶ T.toGrp.X) (t : X ⟶ S.X),
      (AutomorphicAction.conjugation j).act z (t ≫ (CommGroupScheme.groupHom f ≫ j).hom.hom) =
        t ≫ (CommGroupScheme.groupHom f ≫ j).hom.hom)
    (value : rationalPoints T.toGrp → E)
    (hnorm : ∀ z : rationalPoints T.toGrp,
      algebraMap (rootOrbitField k L j mu0) E
        (rationalCharacterEval (rootOrbitCharacter k L j mu0)
          (GaloisPointComparison.rationalExtend k (rootOrbitField k L j mu0) T.toGrp z) :
            rootOrbitField k L j mu0) =
        value z * SU3Root.conjugation (rootOrbitField k L j mu0) E (value z)) :
    HasDoubleRootTraceZeroCoordinates k L f j mu0 E hj₂ hS ha hhigh hfix value := by
  obtain ⟨eta0, heta0, heq⟩ :=
    SU3Root.exists_ne_zero_add_conjugation_eq_zero (rootOrbitField k L j mu0) E
  let eta : SU3Root.Parameters.traceZero
      (SU3Root.fieldInvolution (rootOrbitField k L j mu0) E) := ⟨eta0, heq⟩
  refine ⟨doubleRootTraceZeroEquiv k L f j mu0 E hj₂ hG hj hS hT ha hhigh horbit eta heta0,
    ?_, ?_⟩
  · exact doubleRootTraceZeroEquiv_smul k L f j mu0 E hj₂ hG hj hS hT ha hhigh horbit eta heta0
  · intro z w w' hw
    exact doubleRootTraceZeroEquiv_act k L f j mu0 E hj₂ hG hj hS hT ha hhigh horbit hfix
      eta heta0 z (value z) (hnorm z) w w' hw

end TraceZero

end Langlands.Geometry.Building
