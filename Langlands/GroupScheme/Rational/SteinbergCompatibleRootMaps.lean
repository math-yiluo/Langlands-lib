import Langlands.GroupScheme.Rational.SteinbergGaloisDerivatives

/-! # Whole root-map compatibility from compatible root vectors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
set_option autoImplicit false

namespace SplitPinning

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable (p : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))

/-- Compatibility of the actual pinning vectors with canonical semilinear
Lie transport and a supplied action on the simple roots. -/
def RootVectorsGaloisCompatible
    (ρ : (K ≃ₐ[k] K) →* Equiv.Perm p.base.support) : Prop :=
  ∀ (σ : K ≃ₐ[k] K) (a : p.base.support),
    Lie.baseChangeGaloisEquiv k K G σ (p.pinning.rootVector a) =
      p.pinning.rootVector (ρ σ a)

end SplitPinning

namespace SplitPinning.NormalizedRootParametrization

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local instance :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

local instance :
    IsAffineHom (VectorGroup.groupScheme (CommRingCat.of K) 1).X.hom :=
  VectorGroup.isAffineHom_groupScheme (CommRingCat.of K) 1

variable {p : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)}

variable
    {a : p.base.support} (x : p.NormalizedRootParametrization a) (σ : K ≃ₐ[k] K)
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (j : T.toGrp ⟶ G)
    (eT : p.torus ≅ ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (hT : p.inclusion = CommGroupScheme.groupHom eT.hom ≫
      (GroupScheme.baseChange (algebraBaseMap k K)).map j)
    {c : p.base.support}
    (hroot : characterLattice.congr eT (p.rootDatum.root c) =
      characterLattice.galoisRepresentation k K T σ
        (characterLattice.congr eT (p.rootDatum.root a)))
    (hvector : Lie.baseChangeGaloisEquiv k K G σ (p.pinning.rootVector a) =
      p.pinning.rootVector c)

private def normalizedOfScalarDescent
    (f : VectorGroup.groupScheme (CommRingCat.of K) 1 ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
    (hf : ∀ (U : Over (Spec (CommRingCat.of K))) (z : Γ(U.left, ⊤)),
      descentPoint (algebraBaseMap k K) (galoisBaseMap k K σ)
          (galoisBaseMap_over k K σ) G U
          (VectorGroup.scalarPoint (CommRingCat.of K) U z ≫ f.hom.hom) =
        x.point ((Over.map (galoisBaseMap k K σ)).obj U) z)
    (hr : (RelativeRoot.subgroup p.inclusion (p.rootDatum.root c)).IsRepresentedBy f)
    (hc : IsClosedSubgroup f)
    (hd : Lie.targetMapLinear f K (VectorGroup.standardEpsilon K) =
      Lie.baseChangeGaloisEquiv k K G σ (p.pinning.rootVector a)) :
    p.NormalizedRootParametrization c where
  hom := f
  represents := hr
  isClosedSubgroup := hc
  torus_equivariant := VectorGroup.torus_equivariant_of_scalar_descent k K G σ
    x.hom f hf j p.inclusion eT hT (p.rootDatum.root a) (p.rootDatum.root c)
    hroot x.torus_equivariant
  derivative := hd.trans hvector

include hT hroot hvector in
private theorem hom_eq_of_scalar_descent
    (f : VectorGroup.groupScheme (CommRingCat.of K) 1 ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
    (hf : ∀ (U : Over (Spec (CommRingCat.of K))) (z : Γ(U.left, ⊤)),
      descentPoint (algebraBaseMap k K) (galoisBaseMap k K σ)
          (galoisBaseMap_over k K σ) G U
          (VectorGroup.scalarPoint (CommRingCat.of K) U z ≫ f.hom.hom) =
        x.point ((Over.map (galoisBaseMap k K σ)).obj U) z)
    (hr : (RelativeRoot.subgroup p.inclusion (p.rootDatum.root c)).IsRepresentedBy f)
    (hc : IsClosedSubgroup f)
    (hd : Lie.targetMapLinear f K (VectorGroup.standardEpsilon K) =
      Lie.baseChangeGaloisEquiv k K G σ (p.pinning.rootVector a))
    (y : p.NormalizedRootParametrization c) : f = y.hom := by
  exact (normalizedOfScalarDescent k K G x σ j eT hT hroot hvector f hf hr hc hd).hom_eq y

/-- Actual semilinear transport, normalized at the specified simple root
using the supplied character and vector compatibility. -/
def galoisNormalized : p.NormalizedRootParametrization c :=
  normalizedOfScalarDescent k K G x σ j eT hT hroot hvector
    (x.galoisHom k K G σ) (x.galoisHom_point k K G σ)
    (x.galoisHom_represents_root k K G σ j eT hT hroot)
    (x.galoisHom_isClosedSubgroup k K G σ) (x.galoisHom_derivative k K G σ)

include hT hroot hvector in
/-- Fixed-pinning uniqueness identifies the transported whole homomorphism
with every supplied normalized parametrization at the target root. -/
theorem galoisHom_eq (y : p.NormalizedRootParametrization c) :
    x.galoisHom k K G σ = y.hom :=
  hom_eq_of_scalar_descent k K G x σ j eT hT hroot hvector
    (x.galoisHom k K G σ) (x.galoisHom_point k K G σ)
    (x.galoisHom_represents_root k K G σ j eT hT hroot)
    (x.galoisHom_isClosedSubgroup k K G σ) (x.galoisHom_derivative k K G σ) y

include hT hroot hvector in
/-- The resulting descent identity holds on every scheme test and scalar. -/
theorem point_descent_eq (y : p.NormalizedRootParametrization c)
    (U : Over (Spec (CommRingCat.of K))) (z : Γ(U.left, ⊤)) :
    descentPoint (algebraBaseMap k K) (galoisBaseMap k K σ)
        (galoisBaseMap_over k K σ) G U (y.point U z) =
      x.point ((Over.map (galoisBaseMap k K σ)).obj U) z := by
  have h := x.galoisHom_point k K G σ U z
  rw [x.galoisHom_eq k K G σ j eT hT hroot hvector y] at h
  exact h

include hT hroot hvector in
/-- Normalization and compatible pinning vectors force coefficient
conjugation of the entire root homomorphism. -/
theorem coefficientCurve_conjugate (y : p.NormalizedRootParametrization c) :
    Lie.affineMap G (PolynomialGalois.lineConjugate k K σ)
        (x.coefficientCurve k K G) =
      y.coefficientCurve k K G := by
  rw [← x.galoisHom_coefficientCurve k K G σ,
    x.galoisHom_eq k K G σ j eT hT hroot hvector y]
  rfl

end SplitPinning.NormalizedRootParametrization

namespace SplitPinning

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable (p : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (j : T.toGrp ⟶ G)
    (eT : p.torus ≅ ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (hT : p.inclusion = CommGroupScheme.groupHom eT.hom ≫
      (GroupScheme.baseChange (algebraBaseMap k K)).map j)
    (ρ : (K ≃ₐ[k] K) →* Equiv.Perm p.base.support)
    (hroot : ∀ (σ : K ≃ₐ[k] K) (a : p.base.support),
      characterLattice.congr eT (p.rootDatum.root (ρ σ a)) =
        characterLattice.galoisRepresentation k K T σ
          (characterLattice.congr eT (p.rootDatum.root a)))
    (hvector : RootVectorsGaloisCompatible k K p ρ)

include hT hroot hvector in
/-- Every supplied normalized family is compatible as whole root maps when
the actual root characters and pinning vectors are compatible. -/
theorem rootMapsGaloisCompatible_of_rootVectors
    (x : p.NormalizedSimpleRootParametrizations) :
    RootMapsGaloisCompatible k K p x ρ := by
  intro σ a
  exact (x a).coefficientCurve_conjugate k K G σ j eT hT
    (hroot σ a) (hvector σ a) (x (ρ σ a))

end SplitPinning

end Langlands.GroupScheme
