import Langlands.GroupScheme.CocharacterAffineTransport
import Langlands.GroupScheme.CocharacterTransportNaturality
import Langlands.GroupScheme.Rational.EvenChainPatternProducts
import Langlands.GroupScheme.GaloisPointRational

/-! # Rational evaluation of transported cocharacters and coroots -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k)))

/-- Evaluation of a cocharacter of the base changed group at a field unit,
in the actual rational-point convention. -/
def rationalCocharacterValue
    (ν : (Gm (Spec (CommRingCat.of K))).toGrp ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
    (t : Kˣ) : rationalPoints (GaloisPointComparison.baseChanged k K G) :=
  (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of K)))).symm t ≫ ν.hom.hom

/-- Projection of rational cocharacter evaluation is the published affine evaluation. -/
theorem baseChangeCoeffEquiv_rationalCocharacterValue
    (ν : (Gm (Spec (CommRingCat.of K))).toGrp ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G) (t : Kˣ) :
    GaloisPointComparison.baseChangeCoeffEquiv k K G
        (rationalCocharacterValue k K G ν t) = G.affineCocharacterValue ν t := rfl

/-- Coefficient conjugation transports a cocharacter and its unit coordinate together. -/
theorem rationalCocharacterValue_rationalConjugate
    (σ : K ≃ₐ[k] K)
    (ν : (Gm (Spec (CommRingCat.of K))).toGrp ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G) (t : Kˣ) :
    GaloisPointComparison.rationalConjugate k K G σ
        (rationalCocharacterValue k K G ν t) =
      rationalCocharacterValue k K G
        (transportCocharacter (algebraBaseMap k K) (galoisBaseMap k K σ)
          (galoisBaseMap_over k K σ) G ν) (Units.map σ.toMonoidHom t) := by
  apply (GaloisPointComparison.baseChangeCoeffEquiv k K G).injective
  rw [GaloisPointComparison.baseChangeCoeffEquiv_rationalConjugate,
    baseChangeCoeffEquiv_rationalCocharacterValue,
    baseChangeCoeffEquiv_rationalCocharacterValue]
  change G.affinePointAut σ (G.affineCocharacterValue ν t) = _
  dsimp only [galoisBaseMap, algebraBaseMap]
  rw [affineCocharacterValue_transport G σ ν (galoisBaseMap_over k K σ)]
  congr 2
  apply Units.ext
  exact (σ.symm_apply_apply (t : K)).symm

variable {G} (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)

/-- Evaluation of the ordinary Galois action on the descended torus lattice,
followed by a ground-field inclusion, agrees with rational conjugation. -/
theorem cocharacterLattice.rationalValue_galoisRepresentation
    (σ : K ≃ₐ[k] K)
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (t : Kˣ) :
    GaloisPointComparison.rationalConjugate k K G σ
        (rationalCocharacterValue k K G
          (CommGroupScheme.groupHom ν ≫
            (GroupScheme.baseChange (algebraBaseMap k K)).map i) t) =
      rationalCocharacterValue k K G
        (CommGroupScheme.groupHom (cocharacterLattice.galoisRepresentation k K T σ ν) ≫
          (GroupScheme.baseChange (algebraBaseMap k K)).map i)
        (Units.map σ.toMonoidHom t) := by
  rw [rationalCocharacterValue_rationalConjugate,
    transportCocharacter_naturality]
  rfl

variable [IsAffineHom G.X.hom]

local instance : IsAffineHom
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

namespace SplitPinning

variable (p : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (eT : p.torus ≅ ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (hT : p.inclusion = CommGroupScheme.groupHom eT.hom ≫
      (GroupScheme.baseChange (algebraBaseMap k K)).map i)

include hT in
/-- The coroot followed by the pinned inclusion is its lattice transport
followed by the descended inclusion. -/
theorem corootHom_congr (α : p.rootIndex) :
    p.corootHom α =
      CommGroupScheme.groupHom (cocharacterLattice.congr eT (p.rootDatum.coroot α)) ≫
        (GroupScheme.baseChange (algebraBaseMap k K)).map i := by
  rw [corootHom, hT]
  rfl

include hT in
/-- A coroot lattice transport equality supplies the required transport of
its actual rational value, including conjugation of the unit coordinate. -/
theorem corootRationalPoint_rationalConjugate
    (σ : K ≃ₐ[k] K) (α β : p.rootIndex)
    (hcoroot : cocharacterLattice.congr eT (p.rootDatum.coroot β) =
      cocharacterLattice.galoisRepresentation k K T σ
        (cocharacterLattice.congr eT (p.rootDatum.coroot α))) (t : Kˣ) :
    GaloisPointComparison.rationalConjugate k K G σ (corootRationalPoint p α t) =
      corootRationalPoint p β (Units.map σ.toMonoidHom t) := by
  change GaloisPointComparison.rationalConjugate k K G σ
      (rationalCocharacterValue k K G (p.corootHom α) t) =
    rationalCocharacterValue k K G (p.corootHom β) (Units.map σ.toMonoidHom t)
  rw [p.corootHom_congr k K T i eT hT α, p.corootHom_congr k K T i eT hT β,
    hcoroot]
  exact cocharacterLattice.rationalValue_galoisRepresentation k K T i σ _ t

end SplitPinning

end Langlands.GroupScheme
