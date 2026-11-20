import Langlands.Geometry.FormalGroup.FiniteKernelBaseChange
import Langlands.Geometry.FormalGroup.FiniteKernelGroupScheme
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange

/-! # Scheme base change of a represented finite formal kernel -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.Hom.FiniteKernelModel

open CategoryTheory Opposite _root_.AlgebraicGeometry
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj CategoryTheory.Obj

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {f : Hom M N}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The scheme morphism of the chosen coefficient map. -/
abbrev coefficientSpecMap (φ : R →ₐ[O] S) :
    Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom φ.toRingHom)

/-- Global sections with the algebra structure from the given scheme morphism. -/
abbrev globalAlgebra {A : Type v} [CommRing A] (T : Over (Spec (CommRingCat.of A))) :
    CommAlgCat.{v} A :=
  ((algΓ (CommRingCat.of A)).obj T).unop

private abbrev restrictTest (φ : R →ₐ[O] S) (T : Over (Spec (CommRingCat.of S))) :
    Over (Spec (CommRingCat.of R)) :=
  (Over.map (coefficientSpecMap φ)).obj T

/-- Restricting scalars on global sections gives the sections of the restricted test. -/
private def restrictGlobalAlgebraIso (φ : R →ₐ[O] S) (T : Over (Spec (CommRingCat.of S))) :
    restrictCoefficientAlgebra φ (globalAlgebra T) ≅ globalAlgebra (restrictTest φ T) := by
  refine CommAlgCat.isoMk
    ({ __ := RingEquiv.refl Γ(T.left, ⊤)
       commutes' := ?_ } :
      restrictCoefficientAlgebra φ (globalAlgebra T) ≃ₐ[R] globalAlgebra (restrictTest φ T))
  intro r
  change T.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of S)).inv (φ r)) =
    (T.hom ≫ coefficientSpecMap φ).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)
  rw [Scheme.Hom.comp_appTop]
  exact congrArg T.hom.appTop
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ.toRingHom)) r)

variable (K : FiniteKernelModel f)

/-- The represented scheme points on any test scheme are the formal kernel points
on its relative global sections. -/
def globalPointsEquiv (T : Over (Spec (CommRingCat.of R))) :
    (T ⟶ K.commGroupScheme.X) ≃* Multiplicative (f.kernelPoints (globalAlgebra T)) :=
  Corepresented.pointsEquiv (R := CommRingCat.of R) (B := K.coordinateAlgebra)
    (f.kernelCommGroupPointFunctor ⋙ forget₂ CommGrpCat GrpCat) K.commCorepresentation T

theorem globalPointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of R))} (a : T' ⟶ T)
    (x : T ⟶ K.commGroupScheme.X) :
    K.globalPointsEquiv T' (a ≫ x) =
      Multiplicative.ofAdd (f.kernelMap ((algΓ (CommRingCat.of R)).map a).unop
        (K.globalPointsEquiv T x).toAdd) :=
  Corepresented.pointsEquiv_naturality (R := CommRingCat.of R) (B := K.coordinateAlgebra)
    (f.kernelCommGroupPointFunctor ⋙ forget₂ CommGrpCat GrpCat) K.commCorepresentation a x

/-- The represented scheme map recovers the kernel transformation on relative global sections. -/
theorem commGroupSchemeMap_globalPoints
    {υ ω : Type} [Finite υ] [Finite ω]
    {P : ModuleLaw O R υ} {Q : ModuleLaw O R ω} {g : Hom P Q}
    (J : FiniteKernelModel g) (a : f.kernelPointFunctor.{u, v, v} ⟶ g.kernelPointFunctor)
    {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ K.commGroupScheme.X) :
    J.globalPointsEquiv T (x ≫ (K.commGroupSchemeMap J a).toMul.hom.hom) =
      Multiplicative.ofAdd (a.app (globalAlgebra T) (K.globalPointsEquiv T x).toAdd) :=
  Corepresented.groupSchemeMap_points (R := CommRingCat.of R)
    (B := K.coordinateAlgebra) (C := J.coordinateAlgebra)
    (F := f.kernelCommGroupPointFunctor ⋙ forget₂ CommGrpCat GrpCat)
    (G := g.kernelCommGroupPointFunctor ⋙ forget₂ CommGrpCat GrpCat)
    K.commCorepresentation J.commCorepresentation
    (Functor.whiskerRight a
      (forget₂ (ModuleCat.{v} O) AddCommGrpCat.{v} ⋙ AddCommGrpCat.toCommGrp ⋙
        forget₂ CommGrpCat GrpCat)) x

variable (φ : R →ₐ[O] S)

/-- The actual kernel on the new global algebra is the old kernel on the restricted test. -/
private def restrictGlobalKernelEquiv (T : Over (Spec (CommRingCat.of S))) :
    (f.map φ).kernelPoints (globalAlgebra T) ≃+
      f.kernelPoints (globalAlgebra (restrictTest φ T)) :=
  (f.coefficientKernelEquiv φ (globalAlgebra T)).toAddEquiv.trans
    (((forget₂ (ModuleCat.{v} O) AddCommGrpCat.{v}).mapIso
      (f.kernelPointFunctor.mapIso (restrictGlobalAlgebraIso φ T))).addCommGroupIsoToAddEquiv)

private theorem restrictGlobalKernelEquiv_naturality
    {T T' : Over (Spec (CommRingCat.of S))} (a : T' ⟶ T)
    (x : (f.map φ).kernelPoints (globalAlgebra T)) :
    restrictGlobalKernelEquiv φ T'
        ((f.map φ).kernelMap ((algΓ (CommRingCat.of S)).map a).unop x) =
      f.kernelMap ((algΓ (CommRingCat.of R)).map ((Over.map (coefficientSpecMap φ)).map a)).unop
        (restrictGlobalKernelEquiv φ T x) := by
  apply Subtype.ext
  apply SeriesPoint.ext
  intro i
  rfl

variable (L : FiniteKernelModel (f.map φ))

private def pullbackKernelPoints (T : Over (Spec (CommRingCat.of S))) :
    (T ⟶ ((CommGroupScheme.baseChange (coefficientSpecMap φ)).obj K.commGroupScheme).X) ≃*
      Multiplicative (f.kernelPoints (globalAlgebra (restrictTest φ T))) :=
  (GroupScheme.baseChangePointsEquiv (coefficientSpecMap φ) K.commGroupScheme.toGrp T).trans
    (K.globalPointsEquiv (restrictTest φ T))

private theorem pullbackKernelPoints_naturality
    {T T' : Over (Spec (CommRingCat.of S))} (a : T' ⟶ T)
    (x : T ⟶ ((CommGroupScheme.baseChange (coefficientSpecMap φ)).obj K.commGroupScheme).X) :
    K.pullbackKernelPoints φ T' (a ≫ x) =
      Multiplicative.ofAdd
        (f.kernelMap ((algΓ (CommRingCat.of R)).map ((Over.map (coefficientSpecMap φ)).map a)).unop
          (K.pullbackKernelPoints φ T x).toAdd) :=
  (congrArg (K.globalPointsEquiv (restrictTest φ T'))
    (GroupScheme.baseChangePointsEquiv_naturality
      (coefficientSpecMap φ) K.commGroupScheme.toGrp a x)).trans
    (K.globalPointsEquiv_naturality ((Over.map (coefficientSpecMap φ)).map a) _)

/-- Compare the new kernel model with the scheme pullback on every test. -/
def pullbackPointsEquiv (T : Over (Spec (CommRingCat.of S))) :
    (T ⟶ L.commGroupScheme.X) ≃*
      (T ⟶ ((CommGroupScheme.baseChange (coefficientSpecMap φ)).obj K.commGroupScheme).X) :=
  (L.globalPointsEquiv T).trans
    ((restrictGlobalKernelEquiv (f := f) φ T).toMultiplicative.trans
      (K.pullbackKernelPoints φ T).symm)

private theorem pullbackPointsEquiv_formula (T : Over (Spec (CommRingCat.of S)))
    (x : T ⟶ L.commGroupScheme.X) :
    K.pullbackKernelPoints φ T (K.pullbackPointsEquiv φ L T x) =
      Multiplicative.ofAdd (restrictGlobalKernelEquiv φ T (L.globalPointsEquiv T x).toAdd) :=
  (K.pullbackKernelPoints φ T).apply_symm_apply _

theorem pullbackPointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of S))} (a : T' ⟶ T)
    (x : T ⟶ L.commGroupScheme.X) :
    K.pullbackPointsEquiv φ L T' (a ≫ x) = a ≫ K.pullbackPointsEquiv φ L T x := by
  apply (K.pullbackKernelPoints φ T').injective
  rw [K.pullbackPointsEquiv_formula, K.pullbackKernelPoints_naturality φ a,
    K.pullbackPointsEquiv_formula, L.globalPointsEquiv_naturality]
  exact congrArg Multiplicative.ofAdd
    (restrictGlobalKernelEquiv_naturality φ a (L.globalPointsEquiv T x).toAdd)

/-- The represented kernel after coefficient extension is the actual pullback group scheme. -/
def pullbackIso :
    L.commGroupScheme ≅ (CommGroupScheme.baseChange (coefficientSpecMap φ)).obj K.commGroupScheme :=
  CommGroupScheme.isoOfGroupIso
    (GroupScheme.isoOfPoints (K.pullbackPointsEquiv φ L) (K.pullbackPointsEquiv_naturality φ L))

theorem pullbackIso_hom_points (T : Over (Spec (CommRingCat.of S)))
    (x : T ⟶ L.commGroupScheme.X) :
    x ≫ (K.pullbackIso φ L).hom.toMul.hom.hom = K.pullbackPointsEquiv φ L T x :=
  GroupScheme.comp_isoOfPoints_hom _ (K.pullbackPointsEquiv_naturality φ L) T x

end Langlands.FormalGroup.ModuleLaw.Hom.FiniteKernelModel
