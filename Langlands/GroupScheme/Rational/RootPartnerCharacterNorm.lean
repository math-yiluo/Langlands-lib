import Langlands.GroupScheme.Rational.RootPartnerFields
import Langlands.GroupScheme.Lie.RootOrbitCharacterDescent
import Langlands.GroupScheme.Rational.IndependentWeightProductProof

/-! # Character values of a root and its orbit partner -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RootPartnerFields

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (j : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k L
local notation "T_L" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_L" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "j_L" => CategoryTheory.Functor.map (GroupScheme.baseChange b) j

attribute [local instance] rootsGaloisAction

/-- The value of an orbit root is the corresponding Galois conjugate of the
original root value, at every original-field affine point of the torus. -/
theorem characterValue_partner
    {β β' : roots (T := T_L) (G := G_L) j_L}
    {σ : L ≃ₐ[k] L} (hσ : σ • β = β')
    (z : Lie.AffinePoints T.toGrp k) :
    (rootOrbitCharacterValue k L j β' z : L) =
      σ (rootOrbitCharacterValue k L j β z : L) := by
  rw [rootOrbitCharacterValue_coe, rootOrbitCharacterValue_coe,
    ← characterValue_galoisRepresentation_rationalBaseChangePoint]
  congr 2
  exact (congrArg Subtype.val hσ).symm

/-- Addition of the two root characters multiplies their values. -/
theorem characterValue_sum
    {β β' μ : roots (T := T_L) (G := G_L) j_L}
    (hμ : μ.val = β.val + β'.val)
    (z : Lie.AffinePoints T.toGrp k) :
    (rootOrbitCharacterValue k L j μ z : L) =
      (rootOrbitCharacterValue k L j β z : L) *
        (rootOrbitCharacterValue k L j β' z : L) := by
  simp only [rootOrbitCharacterValue_coe, hμ,
    IndependentWeightProduct.characterValue_add, Units.val_mul]

section Quadratic

variable [FiniteDimensional k L] [IsGalois k L]
  {β μ : roots
    (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
    (G := (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
    ((GroupScheme.baseChange (algebraBaseMap k L)).map j)}
  [Algebra (rootOrbitField k L j μ) (rootOrbitField k L j β)]
  [IsScalarTower (rootOrbitField k L j μ) (rootOrbitField k L j β) L]
  [Algebra.IsQuadraticExtension (rootOrbitField k L j μ) (rootOrbitField k L j β)]
  [Algebra.IsSeparable (rootOrbitField k L j μ) (rootOrbitField k L j β)]

/-- At original rational torus points, the sum-root character is the quadratic
norm of the root character, after inclusion of its value field. -/
def HasCharacterNormValues [IsAffine T.toGrp.X.left] : Prop :=
  ∀ z : rationalPoints T.toGrp,
    algebraMap (rootOrbitField k L j μ) (rootOrbitField k L j β)
        (rationalCharacterEval (rootOrbitCharacter k L j μ)
          (GaloisPointComparison.rationalExtend k (rootOrbitField k L j μ) T.toGrp z) :
            rootOrbitField k L j μ) =
      (rationalCharacterEval (rootOrbitCharacter k L j β)
        (GaloisPointComparison.rationalExtend k (rootOrbitField k L j β) T.toGrp z) :
          rootOrbitField k L j β) *
        SU3Root.conjugation (rootOrbitField k L j μ) (rootOrbitField k L j β)
          (rationalCharacterEval (rootOrbitCharacter k L j β)
            (GaloisPointComparison.rationalExtend k (rootOrbitField k L j β) T.toGrp z) :
              rootOrbitField k L j β)

variable [LocallyOfFiniteType G.X.hom]
  (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
  (hj : IsClosedImmersion ((GroupScheme.baseChange (algebraBaseMap k L)).map j).hom.hom.left)
  {J : Type*} [Finite J]
  {P : RootDatum J
    (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T))
    (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T))}
  (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k L)).map j) P)
  (hne : ∀ γ : roots
    (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
    (G := (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
    ((GroupScheme.baseChange (algebraBaseMap k L)).map j),
    CharacterAveraging.galoisOrbitSum k L T γ.val ≠ 0)

include hT hj hP hne in
/-- For an actual root partner, the sum-root value is the root value times
its quadratic conjugate. This uses all-field character functoriality,
without a rational-density assumption. -/
theorem characterValue_norm {β' : roots (T := T_L) (G := G_L) j_L}
    (h : IsRootPartner k L j β β') (hμ : μ.val = β.val + β'.val)
    (z : Lie.AffinePoints T.toGrp k) :
    algebraMap (rootOrbitField k L j μ) (rootOrbitField k L j β)
        (rootOrbitCharacterValue k L j μ z) =
      rootOrbitCharacterValue k L j β z *
        SU3Root.conjugation (rootOrbitField k L j μ) (rootOrbitField k L j β)
          (rootOrbitCharacterValue k L j β z) := by
  obtain ⟨σ, hσ⟩ := h.1
  apply Subtype.ext
  rw [Langlands.Algebra.QuadraticFixedFields.coe_algebraMap, IntermediateField.coe_mul,
    conjugation_apply k L hT hj hP hne h hμ hσ,
    characterValue_sum k L j hμ z, characterValue_partner k L j hσ z]

include hT hj hP hne in
/-- The descended actual characters on the two root-orbit fields satisfy
the quadratic norm formula at every original rational torus point. -/
theorem hasCharacterNormValues [IsAffine T.toGrp.X.left]
    {β' : roots (T := T_L) (G := G_L) j_L}
    (h : IsRootPartner k L j β β') (hμ : μ.val = β.val + β'.val) :
    HasCharacterNormValues k L j (β := β) (μ := μ) := by
  intro z
  simp only [rationalCharacterEval_rootOrbitCharacter]
  exact characterValue_norm k L j hT hj hP hne h hμ _

end Quadratic

end Langlands.GroupScheme.RootPartnerFields
