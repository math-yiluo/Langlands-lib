import Langlands.GroupScheme.Rational.RootQuotientLieEquiv
import Langlands.Geometry.Building.RootFieldCoordinatesOfTorus

/-! # Field coordinates on the quotient of a multipliable root group

Let `f ≫ j : S → T → G` be a split torus inside a torus `T` of a connected reductive group, with
`T` split by a finite Galois extension `L/k`. For a nonzero character `a` of `S` with no relative
root `n • a`, `n ≥ 3`, and an absolute root `β` whose Galois orbit is the restriction fiber of
`a`, the rational points of the quotient `V = U_a / U_{2a}` are identified with the field
`E_β = rootOrbitField k L j β`. The identification is the composite of the Library's
comparisons `E_β ≃ₗ[k] 𝔤_a` and `V(k) ≃+ 𝔤_a`. It is `k`-linear through the second comparison,
and conjugation by a rational point `z` of `T` acts on it as multiplication by the root value
`β(z)`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

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

local instance : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

attribute [local instance] rootsGaloisAction

variable [FiniteDimensional k L] [IsGalois k L] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
  {a : characterLattice S} {U U₂ : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom U.X.hom]
  {jU : U ⟶ G} {hjU : (subgroup (CommGroupScheme.groupHom f ≫ j) a).IsRepresentedBy jU}
  {j₂ : U₂ ⟶ G} {hj₂ : (subgroup (CommGroupScheme.groupHom f ≫ j) (2 • a)).IsRepresentedBy j₂}

/-- **Field coordinates on the quotient.** The rational points of `V = U_a / U_{2a}` are
identified with the field `E_β` of an absolute root `β` whose Galois orbit is the restriction
fiber of `a`: `E_β ≃ₗ[k] 𝔤_a` followed by the inverse of `V(k) ≃+ 𝔤_a`. -/
def quotientFieldEquiv (C : DoubleRootCommutatorPairing (CommGroupScheme.groupHom f ≫ j) a hjU hj₂)
    [IsAffineHom C.V.X.hom]
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus (T_L).toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (β : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a) :
    Multiplicative (rootOrbitField k L j β) ≃* rationalPoints C.V :=
  AddEquiv.toMultiplicativeLeft
    ((rootOrbitFieldWeightSpaceLinearEquiv k L j f a hG hj hS hT ha β horbit).toAddEquiv.trans
      (C.rootQuotientPointLieEquiv hS ha hhigh).symm)

/-- The comparison `V(k) ≃+ 𝔤_a` sends the point with field coordinate `x` to the weight vector
of `x`. -/
theorem rootQuotientPointLieEquiv_quotientFieldEquiv
    (C : DoubleRootCommutatorPairing (CommGroupScheme.groupHom f ≫ j) a hjU hj₂)
    [IsAffineHom C.V.X.hom]
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus (T_L).toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (β : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a)
    (x : rootOrbitField k L j β) :
    C.rootQuotientPointLieEquiv hS ha hhigh
        (Additive.ofMul (quotientFieldEquiv k L f j C hG hj hS hT ha hhigh β horbit
          (Multiplicative.ofAdd x))) =
      rootOrbitFieldWeightSpaceLinearEquiv k L j f a hG hj hS hT ha β horbit x := by
  change C.rootQuotientPointLieEquiv hS ha hhigh
      ((C.rootQuotientPointLieEquiv hS ha hhigh).symm
        (rootOrbitFieldWeightSpaceLinearEquiv k L j f a hG hj hS hT ha β horbit x)) = _
  exact AddEquiv.apply_symm_apply _ _

/-- **Linearity.** Through the comparison `V(k) ≃+ 𝔤_a`, the field coordinates are
`k`-linear. -/
theorem quotientFieldEquiv_smul
    (C : DoubleRootCommutatorPairing (CommGroupScheme.groupHom f ≫ j) a hjU hj₂)
    [IsAffineHom C.V.X.hom]
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus (T_L).toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (β : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a)
    (c : k) (x : rootOrbitField k L j β) :
    (C.rootQuotientPointLieEquiv hS ha hhigh
        (Additive.ofMul (quotientFieldEquiv k L f j C hG hj hS hT ha hhigh β horbit
          (Multiplicative.ofAdd (c • x)))) : Additive (lieKernel G k)) =
      c • (C.rootQuotientPointLieEquiv hS ha hhigh
        (Additive.ofMul (quotientFieldEquiv k L f j C hG hj hS hT ha hhigh β horbit
          (Multiplicative.ofAdd x))) : Additive (lieKernel G k)) := by
  rw [rootQuotientPointLieEquiv_quotientFieldEquiv, rootQuotientPointLieEquiv_quotientFieldEquiv,
    LinearEquiv.map_smul, Submodule.coe_smul]

/-- **Equivariance.** Conjugation by a rational point `z` of the torus `T` acts on the field
coordinates of the quotient as multiplication by the root value `β(z)`. -/
theorem quotientFieldEquiv_act
    (C : DoubleRootCommutatorPairing (CommGroupScheme.groupHom f ≫ j) a hjU hj₂)
    [IsAffineHom C.V.X.hom] [IsAffineHom T.toGrp.X.hom]
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus (T_L).toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (β : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a)
    (hfix : ∀ (X : Over (Spec (CommRingCat.of k))) (h : X ⟶ T.toGrp.X) (t : X ⟶ S.X),
      (AutomorphicAction.conjugation j).act h (t ≫ (CommGroupScheme.groupHom f ≫ j).hom.hom) =
        t ≫ (CommGroupScheme.groupHom f ≫ j).hom.hom)
    (z : rationalPoints T.toGrp) (x : rootOrbitField k L j β) :
    (C.torusQuotientAction (AutomorphicAction.conjugation j) hfix).act z
        (quotientFieldEquiv k L f j C hG hj hS hT ha hhigh β horbit (Multiplicative.ofAdd x)) =
      quotientFieldEquiv k L f j C hG hj hS hT ha hhigh β horbit
        (Multiplicative.ofAdd (rootOrbitCharacterValue k L j β
          (GaloisPointComparison.rationalCoeffEquiv k T.toGrp z) * x)) := by
  set R := C.rootQuotientPointLieEquiv hS ha hhigh
  set W := rootOrbitFieldWeightSpaceLinearEquiv k L j f a hG hj hS hT ha β horbit
  set e := quotientFieldEquiv k L f j C hG hj hS hT ha hhigh β horbit
  have key := C.rootQuotientPointLieEquiv_act hS ha hhigh (AutomorphicAction.conjugation j) hfix z
    (e (Multiplicative.ofAdd x))
  rw [rootQuotientPointLieEquiv_quotientFieldEquiv] at key
  have hW := conjugation_differential_rootOrbitFieldWeightSpaceEquiv k L j f a hG hj hS hT ha β
    horbit z x
  have key2 : R (Additive.ofMul ((C.torusQuotientAction (AutomorphicAction.conjugation j) hfix).act
      z (e (Multiplicative.ofAdd x)))) =
      W (rootOrbitCharacterValue k L j β (GaloisPointComparison.rationalCoeffEquiv k T.toGrp z) *
        x) :=
    Subtype.ext (key.trans hW)
  rw [← rootQuotientPointLieEquiv_quotientFieldEquiv k L f j C hG hj hS hT ha hhigh β horbit]
    at key2
  exact Additive.ofMul.injective (R.injective key2)

/-- **Equivariance through the root character.** The same, with the root value written as the
value of the descended root character `rootOrbitCharacter k L j β` at the base change of `z`, in
the form of the field `first_act` of `HeisenbergUnitaryData`. -/
theorem quotientFieldEquiv_act_character
    (C : DoubleRootCommutatorPairing (CommGroupScheme.groupHom f ≫ j) a hjU hj₂)
    [IsAffineHom C.V.X.hom] [IsAffineHom T.toGrp.X.hom] [IsAffine T.toGrp.X.left]
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus (T_L).toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (β : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a)
    (hfix : ∀ (X : Over (Spec (CommRingCat.of k))) (h : X ⟶ T.toGrp.X) (t : X ⟶ S.X),
      (AutomorphicAction.conjugation j).act h (t ≫ (CommGroupScheme.groupHom f ≫ j).hom.hom) =
        t ≫ (CommGroupScheme.groupHom f ≫ j).hom.hom)
    (z : rationalPoints T.toGrp) (x : rootOrbitField k L j β) :
    (C.torusQuotientAction (AutomorphicAction.conjugation j) hfix).act z
        (quotientFieldEquiv k L f j C hG hj hS hT ha hhigh β horbit (Multiplicative.ofAdd x)) =
      quotientFieldEquiv k L f j C hG hj hS hT ha hhigh β horbit
        (Multiplicative.ofAdd ((rationalCharacterEval (rootOrbitCharacter k L j β)
          (GaloisPointComparison.rationalExtend k (rootOrbitField k L j β) T.toGrp z) :
            rootOrbitField k L j β) * x)) := by
  rw [rationalCharacterEval_rootOrbitCharacter]
  exact quotientFieldEquiv_act k L f j C hG hj hS hT ha hhigh β horbit hfix z x

end Langlands.Geometry.Building
