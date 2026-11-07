import Langlands.GroupScheme.Rational.SteinbergCanonicalGaloisTransport
import Langlands.GroupScheme.Rational.SteinbergOrthogonalFactors

/-! # Whole root-map transport and the actual polynomial Steinberg factors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option autoImplicit false

namespace VectorGroup

variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]

/-- On an affine test, a scalar point is the spectrum of polynomial evaluation. -/
theorem scalarPoint_eq_algSpec_aeval (c : A) :
    scalarPoint (CommRingCat.of K)
        ((algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K A)))
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv c) =
      (algSpec (CommRingCat.of K)).map
        (CommAlgCat.ofHom (MvPolynomial.aeval (fun _ : Fin 1 => c))).op := by
  apply points_ext
  intro j
  rw [coordinates_scalarPoint, coordinates_apply]
  change (Scheme.ΓSpecIso (CommRingCat.of A)).inv c =
    (Spec.map (CommRingCat.ofHom
      (MvPolynomial.aeval (fun _ : Fin 1 => c)).toRingHom)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin 1) K))).inv
          (MvPolynomial.X j))
  let ev : MvPolynomial (Fin 1) K →ₐ[K] A :=
    MvPolynomial.aeval (fun _ : Fin 1 => c)
  have h := congrArg (fun f => f (MvPolynomial.X j))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ev.toRingHom))
  change (Scheme.ΓSpecIso (CommRingCat.of A)).inv (ev (MvPolynomial.X j)) =
    (Spec.map (CommRingCat.ofHom ev.toRingHom)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin 1) K))).inv
        (MvPolynomial.X j)) at h
  simpa only [ev, MvPolynomial.aeval_X] using h

end VectorGroup

namespace PolynomialGalois

variable (k K : Type u) [Field k] [Field K] [Algebra k K] (I : Type u)

/-- Coefficient conjugation on the standard one-variable polynomial algebra. -/
def lineConjugate (σ : K ≃ₐ[k] K) :
    MvPolynomial (Fin 1) K →ₐ[k] MvPolynomial (Fin 1) K :=
  MvPolynomial.mapAlgHom σ.toAlgHom

/-- Substitution of one variable commutes with coefficient transport and the
supplied permutation of the target variables. -/
theorem orbitAction_comp_aeval_X
    (ρ : (K ≃ₐ[k] K) →* Equiv.Perm I) (σ : K ≃ₐ[k] K) (i : I) :
    (orbitAction k K I ρ σ).comp
        ((MvPolynomial.aeval (fun _ : Fin 1 => MvPolynomial.X i) :
          MvPolynomial (Fin 1) K →ₐ[K] MvPolynomial I K).restrictScalars k) =
      ((MvPolynomial.aeval (fun _ : Fin 1 => MvPolynomial.X (ρ σ i)) :
        MvPolynomial (Fin 1) K →ₐ[K] MvPolynomial I K).restrictScalars k).comp
          (lineConjugate k K σ) := by
  apply AlgHom.coe_ringHom_injective
  apply MvPolynomial.ringHom_ext <;> intro c <;>
    simp [AlgHom.comp_apply, lineConjugate]

/-- Evaluation at coordinate one retains coefficient conjugation. -/
theorem aeval_one_comp_conjugate (σ : K ≃ₐ[k] K) :
    ((MvPolynomial.aeval (fun _ : Fin 1 => (1 : K))).restrictScalars k).comp
        (lineConjugate k K σ) =
      σ.toAlgHom.comp
        ((MvPolynomial.aeval (fun _ : Fin 1 => (1 : K))).restrictScalars k) := by
  apply AlgHom.coe_ringHom_injective
  apply MvPolynomial.ringHom_ext <;> intro c <;>
    simp [AlgHom.comp_apply, lineConjugate]

/-- Constants in the polynomial test transform by the same field automorphism. -/
theorem orbitAction_comp_coefficients
    (ρ : (K ≃ₐ[k] K) →* Equiv.Perm I) (σ : K ≃ₐ[k] K) :
    (orbitAction k K I ρ σ).comp
        ((Algebra.ofId K (MvPolynomial I K)).restrictScalars k) =
      ((Algebra.ofId K (MvPolynomial I K)).restrictScalars k).comp σ.toAlgHom := by
  apply AlgHom.ext
  intro c
  exact orbitAction_C k K I ρ σ c

end PolynomialGalois

namespace Lie

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    (A : Type u) [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A]

/-- A rational point pulled to an affine test is its coefficient extension
under the actual base-change comparison. -/
theorem affineBaseChangeEquiv_constantPoint
    (z : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)) :
    affineBaseChangeEquiv k K G A
        (toUnit ((algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K A))) ≫ z) =
      affineMap G ((Algebra.ofId K A).restrictScalars k)
        (GaloisPointComparison.baseChangeCoeffEquiv k K G z) := by
  apply Over.OverMorphism.ext
  simp only [affineBaseChangeEquiv_left, affineMap_apply,
    GaloisPointComparison.baseChangeCoeffEquiv_left, Over.comp_left]
  rfl

end Lie

namespace SplitPinning.NormalizedRootParametrization

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local instance :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable {p : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)}
    {a : p.base.support} (x : p.NormalizedRootParametrization a)

/-- The whole normalized root homomorphism as a polynomial-valued point of the original group. -/
def coefficientCurve : Lie.AffinePoints G (MvPolynomial (Fin 1) K) :=
  Lie.affineBaseChangeEquiv k K G _ x.hom.hom.hom

/-- Polynomial substitution evaluates the whole actual root map on every affine test. -/
theorem coefficientCurve_evaluate
    (A : Type u) [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A]
    (c : A) :
    Lie.affineMap G
        ((MvPolynomial.aeval (fun _ : Fin 1 => c)).restrictScalars k)
        (coefficientCurve k K G x) =
      Lie.affineBaseChangeEquiv k K G A
        (x.point _ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv c)) := by
  rw [coefficientCurve, ← Lie.affineBaseChangeEquiv_naturality]
  apply congrArg (Lie.affineBaseChangeEquiv k K G A)
  rw [Lie.affineMap_apply, point, VectorGroup.scalarPoint_eq_algSpec_aeval]

/-- Substituting one in the whole root map gives the canonical normalized unit point. -/
theorem coefficientCurve_evaluate_one :
    Lie.affineMap G
        ((MvPolynomial.aeval (fun _ : Fin 1 => (1 : K))).restrictScalars k)
        (coefficientCurve k K G x) =
      GaloisPointComparison.baseChangeCoeffEquiv k K G x.unitPoint := by
  rw [coefficientCurve_evaluate]
  have h :
      x.point ((algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K K))) 1 =
        toUnit _ ≫ x.unitPoint := by
    rw [x.unitPoint_eq]
    simpa only [map_one] using
      (x.point_comp (T := Over.mk (𝟙 (Spec (CommRingCat.of K))))
        (toUnit ((algSpec (CommRingCat.of K)).obj
        (op (CommAlgCat.of K K)))) (1 : Γ(Spec (CommRingCat.of K), ⊤))).symm
  rw [map_one, h, Lie.affineBaseChangeEquiv_constantPoint]
  change Lie.affineMap G (AlgHom.id k K) _ = _
  exact Lie.affineMap_id G _

/-- Coefficient compatibility of entire root maps gives the corresponding
compatibility after substituting a permuted polynomial variable. -/
theorem coefficientCurve_substitute_galois
    {b : p.base.support} (y : p.NormalizedRootParametrization b)
    (I : Type u) (ρ : (K ≃ₐ[k] K) →* Equiv.Perm I)
    (σ : K ≃ₐ[k] K) (i : I)
    (hcurve : Lie.affineMap G (PolynomialGalois.lineConjugate k K σ)
      (coefficientCurve k K G x) = coefficientCurve k K G y) :
    Lie.affineMap G (PolynomialGalois.orbitAction k K I ρ σ)
        (Lie.affineMap G
          ((MvPolynomial.aeval (fun _ : Fin 1 => MvPolynomial.X i)).restrictScalars k)
          (coefficientCurve k K G x)) =
      Lie.affineMap G
        ((MvPolynomial.aeval (fun _ : Fin 1 => MvPolynomial.X (ρ σ i))).restrictScalars k)
        (coefficientCurve k K G y) := by
  rw [← Lie.affineMap_comp, PolynomialGalois.orbitAction_comp_aeval_X,
    Lie.affineMap_comp, hcurve]

end SplitPinning.NormalizedRootParametrization

namespace SplitPinning

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable (p : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))

/-- The supplied simple-root action transports the whole actual normalized
root maps, with the additive-line variable held fixed. -/
def RootMapsGaloisCompatible
    (x : p.NormalizedSimpleRootParametrizations)
    (ρ : (K ≃ₐ[k] K) →* Equiv.Perm p.base.support) : Prop :=
  ∀ (σ : K ≃ₐ[k] K) (a : p.base.support),
    Lie.affineMap G (PolynomialGalois.lineConjugate k K σ)
        ((x a).coefficientCurve k K G) =
      (x (ρ σ a)).coefficientCurve k K G

/-- Whole-map compatibility supplies the unit-point compatibility used by
canonical opposite pairs and reflection representatives. -/
theorem RootMapsGaloisCompatible.unitPoints
    (x : p.NormalizedSimpleRootParametrizations)
    (ρ : (K ≃ₐ[k] K) →* Equiv.Perm p.base.support)
    (hx : RootMapsGaloisCompatible k K p x ρ) :
    UnitPointsGaloisCompatible k K p x ρ := by
  intro σ a
  apply (GaloisPointComparison.baseChangeCoeffEquiv k K G).injective
  rw [GaloisPointComparison.baseChangeCoeffEquiv_rationalConjugate]
  change Lie.affineMap G σ.toAlgHom
    (GaloisPointComparison.baseChangeCoeffEquiv k K G (x a).unitPoint) = _
  rw [← (x a).coefficientCurve_evaluate_one k K G,
    ← (x (ρ σ a)).coefficientCurve_evaluate_one k K G,
    ← Lie.affineMap_comp, ← PolynomialGalois.aeval_one_comp_conjugate,
    Lie.affineMap_comp, hx σ a]

end SplitPinning

namespace SteinbergOrbitImageDescent

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local instance :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable (p : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    {r : ℕ} (I : Type u) (d : Fin r ≃ I)
    (e : Fin r ≃ p.base.support)
    (x : p.NormalizedSimpleRootParametrizations)
    (n : p.SimpleReflectionRepresentatives)

/-- The coordinate-test isomorphism pulls the standard coordinate back to
the polynomial variable with the supplied index. -/
theorem coordinateTestIso_coordinate (j : Fin r) :
    (coordinateTestIso K I d).hom.left.appTop
        (VectorGroup.coordinateSection (CommRingCat.of K) r j) =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial I K))).inv
        (MvPolynomial.X (d j)) := by
  change (Spec.map (CommRingCat.ofHom
    (MvPolynomial.renameEquiv K d).toAlgHom.toRingHom)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin r) K))).inv
        (MvPolynomial.X j)) = _
  have h := congrArg (fun f => f (MvPolynomial.X j))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      (MvPolynomial.renameEquiv K d).toAlgHom.toRingHom))
  change (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial I K))).inv
      ((MvPolynomial.renameEquiv K d) (MvPolynomial.X j)) =
    (Spec.map (CommRingCat.ofHom
      (MvPolynomial.renameEquiv K d).toAlgHom.toRingHom)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin r) K))).inv
        (MvPolynomial.X j)) at h
  simpa only [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X] using h.symm

/-- Each actual factor is the substituted whole root map times the
coefficient extension of the actual rational reflection point. -/
theorem factor_eq_substitutedCurve (i : I) :
    factor k K G p I d e x n i =
      Lie.affineMap G
          ((MvPolynomial.aeval (fun _ : Fin 1 => MvPolynomial.X i)).restrictScalars k)
          ((x (e (d.symm i))).coefficientCurve k K G) *
        Lie.affineMap G
          ((Algebra.ofId K (MvPolynomial I K)).restrictScalars k)
          (GaloisPointComparison.baseChangeCoeffEquiv k K G (n (e (d.symm i))).point) := by
  rw [SplitPinning.NormalizedRootParametrization.coefficientCurve_evaluate]
  unfold factor factorK
  rw [MonObj.comp_mul, map_mul,
    SplitPinning.NormalizedRootParametrization.point_comp,
    coordinateTestIso_coordinate, d.apply_symm_apply]
  congr 1
  rw [← Category.assoc]
  have h := toUnit_unique ((coordinateTestIso K I d).hom ≫ toUnit _) (toUnit _)
  rw [h, Lie.affineBaseChangeEquiv_constantPoint]

/-- Transport the simple-root permutation action to the supplied coordinate indices. -/
def rootCoordinateAction
    (ρ : (K ≃ₐ[k] K) →* Equiv.Perm p.base.support) :
    (K ≃ₐ[k] K) →* Equiv.Perm I where
  toFun σ := (d.symm.trans e).symm.permCongr (ρ σ)
  map_one' := by
    ext i
    simp
  map_mul' σ τ := by
    ext i
    simp

/-- The coordinate action induces precisely the supplied action on simple roots. -/
theorem rootCoordinateAction_root
    (ρ : (K ≃ₐ[k] K) →* Equiv.Perm p.base.support)
    (σ : K ≃ₐ[k] K) (i : I) :
    e (d.symm (rootCoordinateAction k K G p I d e ρ σ i)) =
      ρ σ (e (d.symm i)) := by
  simp [rootCoordinateAction]

/-- Whole-root-map transport and rational reflection-point transport imply
the actual factor law on the permuted polynomial test. -/
theorem factor_orbitAction
    (ρ : (K ≃ₐ[k] K) →* Equiv.Perm p.base.support)
    (hx : SplitPinning.RootMapsGaloisCompatible k K p x ρ)
    (hn : ∀ (σ : K ≃ₐ[k] K) (a : p.base.support),
      GaloisPointComparison.rationalConjugate k K G σ (n a).point =
        (n (ρ σ a)).point)
    (σ : K ≃ₐ[k] K) (i : I) :
    Lie.affineMap G
        (PolynomialGalois.orbitAction k K I (rootCoordinateAction k K G p I d e ρ) σ)
        (factor k K G p I d e x n i) =
      factor k K G p I d e x n (rootCoordinateAction k K G p I d e ρ σ i) := by
  rw [factor_eq_substitutedCurve, factor_eq_substitutedCurve, map_mul]
  congr 1
  · apply SplitPinning.NormalizedRootParametrization.coefficientCurve_substitute_galois
    rw [rootCoordinateAction_root]
    exact hx σ (e (d.symm i))
  · rw [← Lie.affineMap_comp, PolynomialGalois.orbitAction_comp_coefficients,
      Lie.affineMap_comp]
    have hz := congrArg (GaloisPointComparison.baseChangeCoeffEquiv k K G)
      (hn σ (e (d.symm i)))
    rw [GaloisPointComparison.baseChangeCoeffEquiv_rationalConjugate] at hz
    change Lie.affineMap G σ.toAlgHom
      (GaloisPointComparison.baseChangeCoeffEquiv k K G (n (e (d.symm i))).point) =
        _ at hz
    rw [hz, rootCoordinateAction_root]

/-- The full image ideal of the actual canonical Steinberg product descends
from whole-root-map compatibility and distinct orthogonal invariant blocks. -/
def definingIdealDescent_of_compatibleRootMaps [IsGalois k K]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (j : T.toGrp ⟶ G)
    (eT : p.torus ≅ ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (hT : p.inclusion = CommGroupScheme.groupHom eT.hom ≫
      (GroupScheme.baseChange (algebraBaseMap k K)).map j)
    (ρ : (K ≃ₐ[k] K) →* Equiv.Perm p.base.support)
    (hroot : ∀ (σ : K ≃ₐ[k] K) (a : p.base.support),
      characterLattice.congr eT (p.rootDatum.root (ρ σ a)) =
        characterLattice.galoisRepresentation k K T σ
          (characterLattice.congr eT (p.rootDatum.root a)))
    (hx : SplitPinning.RootMapsGaloisCompatible k K p x ρ)
    (blocks : List (List I))
    (horder : blocks.flatten = List.ofFn d)
    (hblocks : ∀ (σ : K ≃ₐ[k] K) l, l ∈ blocks →
      (l.map (rootCoordinateAction k K G p I d e ρ σ)).Perm l)
    (horth : ∀ l, l ∈ blocks → l.Pairwise (fun i j =>
      i ≠ j ∧ p.rootDatum.IsOrthogonal (e (d.symm i)) (e (d.symm j)))) :
    DefiningIdealDescent (pullback.fst G.X.hom (algebraBaseMap k K))
      (SplitPinning.steinbergProduct e x
        (SplitPinning.canonicalSimpleReflectionRepresentatives x)).left.ker :=
  definingIdealDescent_of_orthogonal k K G p I d e x
    (SplitPinning.canonicalSimpleReflectionRepresentatives x)
    (SplitPinning.rootGenerated_canonicalSimpleReflectionRepresentatives x)
    (rootCoordinateAction k K G p I d e ρ) blocks horder hblocks horth
    (factor_orbitAction k K G p I d e x
      (SplitPinning.canonicalSimpleReflectionRepresentatives x) ρ hx
      (SplitPinning.canonicalSimpleReflectionRepresentatives_rationalConjugate
        k K j p eT hT x ρ hroot
        (SplitPinning.RootMapsGaloisCompatible.unitPoints k K p x ρ hx)))

end SteinbergOrbitImageDescent

end Langlands.GroupScheme
