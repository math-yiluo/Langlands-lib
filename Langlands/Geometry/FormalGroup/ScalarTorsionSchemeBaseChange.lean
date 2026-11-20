import Langlands.Geometry.FormalGroup.FiniteKernelSchemeBaseChange
import Langlands.Geometry.FormalGroup.IsogenyBaseChange
import Langlands.Geometry.FormalGroup.ScalarTorsionSchemeHom

/-! # Base change of the scalar-power torsion diagrams -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory Opposite _root_.AlgebraicGeometry
open Langlands.GroupScheme Hom.FiniteKernelModel
open scoped CategoryTheory.MonObj CategoryTheory.Obj

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {π : O}
variable (φ : R →ₐ[O] S)

attribute [local instance] coefficientAlgebra coefficientScalarTower

namespace Hom.FiniteKernelModel

variable {f : Hom M N} {g : Hom (M.map φ) (N.map φ)}
variable (K : FiniteKernelModel f) (L : FiniteKernelModel g)
variable (e : f.map φ = g)

private def pullbackIsoOfEq :
    L.commGroupScheme ≅ (CommGroupScheme.baseChange (coefficientSpecMap φ)).obj K.commGroupScheme := by
  subst g
  exact K.pullbackIso φ L

variable {T : Over (Spec (CommRingCat.of S))}

/-- Use the original kernel's global coordinate values on a scheme pullback test. -/
private def pullbackValue
    (x : T ⟶ ((CommGroupScheme.baseChange (coefficientSpecMap φ)).obj K.commGroupScheme).X) :
    SeriesPoint Γ(T.left, ⊤) σ Empty :=
  (K.globalPointsEquiv ((Over.map (coefficientSpecMap φ)).obj T)
    (GroupScheme.baseChangePointsEquiv (coefficientSpecMap φ) K.commGroupScheme.toGrp T x)).toAdd.val

private theorem pullbackValue_injective :
    Function.Injective (K.pullbackValue φ (T := T)) := by
  intro x y h
  apply (GroupScheme.baseChangePointsEquiv (coefficientSpecMap φ) K.commGroupScheme.toGrp T).injective
  apply (K.globalPointsEquiv ((Over.map (coefficientSpecMap φ)).obj T)).injective
  exact congrArg Multiplicative.ofAdd (Subtype.ext h)

private theorem pullbackValue_isoHom (x : T ⟶ L.commGroupScheme.X) :
    K.pullbackValue φ (x ≫ (K.pullbackIsoOfEq φ L e).hom.toMul.hom.hom) =
      (L.globalPointsEquiv T x).toAdd.val := by
  subst g
  change K.pullbackValue φ (x ≫ (K.pullbackIso φ L).hom.toMul.hom.hom) = _
  rw [K.pullbackIso_hom_points]
  let p := (GroupScheme.baseChangePointsEquiv (coefficientSpecMap φ) K.commGroupScheme.toGrp T).trans
    (K.globalPointsEquiv ((Over.map (coefficientSpecMap φ)).obj T))
  unfold pullbackPointsEquiv
  simp only [MulEquiv.trans_apply]
  change (p (p.symm _)).toAdd.val = _
  rw [p.apply_symm_apply]
  rfl

private theorem pullbackValue_map {υ ω : Type} [Finite υ] [Finite ω]
    {P : ModuleLaw O R υ} {Q : ModuleLaw O R ω} {p : Hom P Q} (J : FiniteKernelModel p)
    (a : f.kernelPointFunctor.{u, v, v} ⟶ p.kernelPointFunctor)
    (x : T ⟶ ((CommGroupScheme.baseChange (coefficientSpecMap φ)).obj K.commGroupScheme).X) :
    J.pullbackValue φ
        (x ≫ ((CommGroupScheme.baseChange (coefficientSpecMap φ)).map
          (K.commGroupSchemeMap J a)).toMul.hom.hom) =
      (a.app (globalAlgebra ((Over.map (coefficientSpecMap φ)).obj T))
        (K.globalPointsEquiv ((Over.map (coefficientSpecMap φ)).obj T)
          (GroupScheme.baseChangePointsEquiv
            (coefficientSpecMap φ) K.commGroupScheme.toGrp T x)).toAdd).val := by
  unfold pullbackValue
  have hb := GroupScheme.baseChangePointsEquiv_comp (coefficientSpecMap φ)
    (K.commGroupSchemeMap J a).toMul T x
  erw [hb]
  let T₀ := (Over.map (coefficientSpecMap φ)).obj T
  let x₀ := GroupScheme.baseChangePointsEquiv (coefficientSpecMap φ) K.commGroupScheme.toGrp T x
  exact congrArg (fun z : Multiplicative (p.kernelPoints (globalAlgebra T₀)) => z.toAdd.val)
    (K.commGroupSchemeMap_globalPoints J a x₀)

end Hom.FiniteKernelModel

private theorem onGlobalPoints_map (f : Hom M N) (T : Over (Spec (CommRingCat.of S)))
    (x : SeriesPoint Γ(T.left, ⊤) σ Empty) :
    (f.map φ).onAlgebraPoints (A := globalAlgebra T) x =
      f.onAlgebraPoints (A := globalAlgebra ((Over.map (coefficientSpecMap φ)).obj T)) x := by
  let A := globalAlgebra T
  let B := globalAlgebra ((Over.map (coefficientSpecMap φ)).obj T)
  have h : (algebraMap S A).comp φ.toRingHom = algebraMap R B := by
    apply RingHom.ext
    intro r
    change T.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of S)).inv (φ r)) =
      (T.hom ≫ coefficientSpecMap φ).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)
    rw [Scheme.Hom.comp_appTop]
    exact congrArg T.hom.appTop
      (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ.toRingHom)) r)
  change SeriesPoint.eval ((f.toHom.toCoordinateMap.map φ.toRingHom).map (algebraMap S A)) x =
    SeriesPoint.eval (f.toHom.toCoordinateMap.map (algebraMap R B)) x
  rw [CoordinateMap.map_ringHom_comp, h]
  rfl

namespace IsPiDivisible

variable (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π)
variable {T : Over (Spec (CommRingCat.of S))}

/-- Scalar-power torsion after coefficient extension is the actual scheme pullback. -/
def torsionPullbackIso (n : ℕ) :
    (hM.map φ).torsionSchemeInclusions.obj n ≅
      (CommGroupScheme.baseChange (coefficientSpecMap φ)).obj (hM.torsionSchemeInclusions.obj n) :=
  (hM.torsionKernelModel n).pullbackIsoOfEq φ ((hM.map φ).torsionKernelModel n)
    (scalarHom_map M (π ^ n) φ)

private theorem torsionPullbackIso_value (n : ℕ)
    (x : T ⟶ ((hM.map φ).torsionSchemeInclusions.obj n).X) :
    (hM.torsionKernelModel n).pullbackValue φ (x ≫ (hM.torsionPullbackIso φ n).hom.toMul.hom.hom) =
      (((hM.map φ).torsionKernelModel n).globalPointsEquiv T x).toAdd.val :=
  (hM.torsionKernelModel n).pullbackValue_isoHom φ ((hM.map φ).torsionKernelModel n)
    (scalarHom_map M (π ^ n) φ) x

private theorem torsionPullbackIso_commutes {m n : ℕ}
    (a : (M.scalarHom (π ^ m)).kernelPointFunctor.{u, v, v} ⟶
      (N.scalarHom (π ^ n)).kernelPointFunctor)
    (a' : ((M.map φ).scalarHom (π ^ m)).kernelPointFunctor.{u, v, v} ⟶
      ((N.map φ).scalarHom (π ^ n)).kernelPointFunctor)
    (ha : ∀ (T : Over (Spec (CommRingCat.of S)))
      (x : ((M.map φ).scalarHom (π ^ m)).kernelPoints (globalAlgebra T))
      (y : (M.scalarHom (π ^ m)).kernelPoints
        (globalAlgebra ((Over.map (coefficientSpecMap φ)).obj T))),
      x.val = y.val → (a'.app _ x).val = (a.app _ y).val) :
    ((hM.map φ).torsionKernelModel m).commGroupSchemeMap
        ((hN.map φ).torsionKernelModel n) a' ≫ (hN.torsionPullbackIso φ n).hom =
      (hM.torsionPullbackIso φ m).hom ≫ (CommGroupScheme.baseChange (coefficientSpecMap φ)).map
        ((hM.torsionKernelModel m).commGroupSchemeMap (hN.torsionKernelModel n) a) := by
  apply congrArg Additive.ofMul
  apply GroupScheme.hom_ext_points
  intro T x
  let K := hM.torsionKernelModel m
  let J := hN.torsionKernelModel n
  let K' := (hM.map φ).torsionKernelModel m
  let J' := (hN.map φ).torsionKernelModel n
  let image := x ≫ (K'.commGroupSchemeMap J' a').toMul.hom.hom
  let transported := x ≫ (hM.torsionPullbackIso φ m).hom.toMul.hom.hom
  let imagePoint := J'.globalPointsEquiv T image
  let sourcePoint := K.globalPointsEquiv ((Over.map (coefficientSpecMap φ)).obj T)
    (GroupScheme.baseChangePointsEquiv (coefficientSpecMap φ) K.commGroupScheme.toGrp T transported)
  simp only [Grp.comp_hom_hom]
  apply (J.pullbackValue_injective φ)
  simp only [← Category.assoc]
  change J.pullbackValue φ (image ≫ (hN.torsionPullbackIso φ n).hom.toMul.hom.hom) =
    J.pullbackValue φ
      (transported ≫ ((CommGroupScheme.baseChange (coefficientSpecMap φ)).map
        (K.commGroupSchemeMap J a)).toMul.hom.hom)
  have hImage : imagePoint.toAdd.val =
      (a'.app (globalAlgebra T) (K'.globalPointsEquiv T x).toAdd).val :=
    congrArg (fun z : Multiplicative (((N.map φ).scalarHom (π ^ n)).kernelPoints
      (globalAlgebra T)) => z.toAdd.val) (K'.commGroupSchemeMap_globalPoints J' a' x)
  have hCoords := ha T (K'.globalPointsEquiv T x).toAdd sourcePoint.toAdd
    (torsionPullbackIso_value φ hM m x).symm
  exact (torsionPullbackIso_value φ hN n image).trans
    (hImage.trans (hCoords.trans (K.pullbackValue_map φ J a transported).symm))

/-- The coefficient comparison respects inclusions of the actual torsion kernels. -/
theorem torsionPullbackIso_inclusion {m n : ℕ} (i : m ⟶ n) :
    (hM.map φ).torsionSchemeInclusions.map i ≫ (hM.torsionPullbackIso φ n).hom =
      (hM.torsionPullbackIso φ m).hom ≫
        (CommGroupScheme.baseChange (coefficientSpecMap φ)).map (hM.torsionSchemeInclusions.map i) := by
  exact torsionPullbackIso_commutes φ hM hM
    (M.torsionIncl π (leOfHom i)) ((M.map φ).torsionIncl π (leOfHom i))
    (fun _ _ _ h => h)

/-- The coefficient comparison respects the actual scalar transitions. -/
theorem torsionPullbackIso_transition {m n : ℕ} (i : m ⟶ n) :
    (hM.map φ).torsionSchemeTower.map i.op ≫ (hM.torsionPullbackIso φ m).hom =
      (hM.torsionPullbackIso φ n).hom ≫
        (CommGroupScheme.baseChange (coefficientSpecMap φ)).map (hM.torsionSchemeTower.map i.op) := by
  refine torsionPullbackIso_commutes φ hM hM
    (M.torsionTransition π (leOfHom i)) ((M.map φ).torsionTransition π (leOfHom i)) ?_
  intro T x y h
  change ((M.map φ).scalarHom (π ^ (n - m))).onAlgebraPoints (A := globalAlgebra T) x.val =
    (M.scalarHom (π ^ (n - m))).onAlgebraPoints
      (A := globalAlgebra ((Over.map (coefficientSpecMap φ)).obj T)) y.val
  rw [← scalarHom_map]
  exact (onGlobalPoints_map φ (M.scalarHom (π ^ (n - m))) T x.val).trans
    (congrArg ((M.scalarHom (π ^ (n - m))).onAlgebraPoints) h)

/-- The coefficient comparison also respects the maps induced by integral formal homomorphisms. -/
theorem torsionPullbackIso_naturality (f : Hom M N) (n : ℕ) :
    (f.map φ).scalarTorsionSchemeMap (hM.map φ) (hN.map φ) n ≫ (hN.torsionPullbackIso φ n).hom =
      (hM.torsionPullbackIso φ n).hom ≫ (CommGroupScheme.baseChange (coefficientSpecMap φ)).map
        (f.scalarTorsionSchemeMap hM hN n) := by
  refine torsionPullbackIso_commutes φ hM hN
    (f.scalarTorsionPointNatTrans π n) ((f.map φ).scalarTorsionPointNatTrans π n) ?_
  intro T x y h
  exact (onGlobalPoints_map φ f T x.val).trans (congrArg f.onAlgebraPoints h)

/-- The torsion pullback comparison is an isomorphism of direct diagrams. -/
def torsionSchemeInclusionsBaseChangeIso :
    (hM.map φ).torsionSchemeInclusions ≅ hM.torsionSchemeInclusions ⋙
      CommGroupScheme.baseChange (coefficientSpecMap φ) :=
  NatIso.ofComponents (hM.torsionPullbackIso φ) (fun i => hM.torsionPullbackIso_inclusion φ i)

/-- The same comparison is an isomorphism of inverse diagrams. -/
def torsionSchemeTowerBaseChangeIso :
    (hM.map φ).torsionSchemeTower ≅ hM.torsionSchemeTower ⋙
      CommGroupScheme.baseChange (coefficientSpecMap φ) :=
  NatIso.ofComponents (fun n => hM.torsionPullbackIso φ n.unop)
    (fun i => hM.torsionPullbackIso_transition φ i.unop)

end IsPiDivisible

end Langlands.FormalGroup.ModuleLaw
