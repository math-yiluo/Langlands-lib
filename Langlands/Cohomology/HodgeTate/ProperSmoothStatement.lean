import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Langlands.AlgebraicGeometry.Modules.CohomologyPullback
import Langlands.AlgebraicGeometry.Modules.Tensor
import Langlands.AlgebraicGeometry.RelativeDifferentials
import Langlands.AlgebraicGeometry.RelativeDifferentialsMaps
import Langlands.Galois.Local.LabelledHodgeTate
import Langlands.Geometry.EtaleAdicSystem
import Langlands.Geometry.EtaleGaloisAction
import Langlands.Geometry.EtaleInverseImageConstant
import Langlands.Geometry.EtaleSchemeDeckAction
import Mathlib.Algebra.Category.ModuleCat.ExteriorPower

/-!
# Hodge–Tate comparison for proper smooth schemes

The proper smooth, constant-coefficient comparison of Faltings, *p-adic
Hodge theory* (1988), Chapter III, Theorem 4.1, with the twist convention
of the introduction, §1(b).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Geometry
open scoped TensorProduct

universe u uI vI wY wR

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Cohomology.HodgeTate

section Forms

private def exteriorMap {R R' : Type u} [CommRing R] [CommRing R']
    {M : ModuleCat.{u} R} {N : ModuleCat.{u} R'} {φ : R →+* R'}
    (a : M →ₛₗ[φ] N) (j : ℕ) :
    M.exteriorPower j ⟶ (ModuleCat.restrictScalars φ).obj (N.exteriorPower j) :=
  ModuleCat.exteriorPower.desc
    { toFun := fun v => exteriorPower.ιMulti R' j (a ∘ v)
      map_update_add' := by
        intro _ v i x y
        simp only [Function.comp_update, map_add, AlternatingMap.map_update_add]
      map_update_smul' := by
        intro _ v i c x
        rw [Function.comp_update, map_smulₛₗ, AlternatingMap.map_update_smul,
          Function.comp_update]
        rfl
      map_eq_zero_of_eq' := by
        intro v i i' heq hne
        exact (exteriorPower.ιMulti R' j).map_eq_zero_of_eq _ (congrArg a heq) hne }

private theorem exteriorMap_mk {R R' : Type u} [CommRing R] [CommRing R']
    {M : ModuleCat.{u} R} {N : ModuleCat.{u} R'} {φ : R →+* R'}
    (a : M →ₛₗ[φ] N) (j : ℕ) (v : Fin j → M) :
    exteriorMap a j (ModuleCat.exteriorPower.mk v) =
      ModuleCat.exteriorPower.mk (M := N) (a ∘ v) := by
  unfold exteriorMap
  rw [ModuleCat.exteriorPower.desc_mk]
  rfl

variable {I : Type uI} [Category.{vI} I] {S : Iᵒᵖ ⥤ CommRingCat.{u}}

private def exteriorRestriction (M : PresheafOfModulesOfCommRing.{u} S)
    (j : ℕ) {U V : Iᵒᵖ} (f : U ⟶ V) :
    (M.obj U).exteriorPower j ⟶
      (ModuleCat.restrictScalars (S.map f).hom).obj ((M.obj V).exteriorPower j) :=
  exteriorMap (R := S.obj U) (R' := S.obj V) (M.restrictₛₗ f) j

private theorem exteriorRestriction_mk (M : PresheafOfModulesOfCommRing.{u} S)
    (j : ℕ) {U V : Iᵒᵖ} (f : U ⟶ V) (v : Fin j → M.obj U) :
    exteriorRestriction M j f (ModuleCat.exteriorPower.mk v) =
      ModuleCat.exteriorPower.mk (M := M.obj V) (M.restrictₛₗ f ∘ v) :=
  exteriorMap_mk (R := S.obj U) (R' := S.obj V) (M.restrictₛₗ f) j v

private def exteriorPresheaf (M : PresheafOfModulesOfCommRing.{u} S) (j : ℕ) :
    PresheafOfModulesOfCommRing.{u} S :=
  PresheafOfModulesOfCommRing.mk
    (fun U => (M.obj U).exteriorPower j)
    (exteriorRestriction M j)
    (fun U => by
      apply ModuleCat.exteriorPower.hom_ext
      ext v
      change exteriorRestriction M j (𝟙 U) (ModuleCat.exteriorPower.mk v) =
        ModuleCat.exteriorPower.mk v
      rw [exteriorRestriction_mk]
      apply congrArg (ModuleCat.exteriorPower.mk (M := M.obj U) (n := j))
      funext i
      exact M.presheaf.map_id_apply U (v i))
    (fun {U V W} f g => by
      apply ModuleCat.exteriorPower.hom_ext
      ext v
      change exteriorRestriction M j (f ≫ g) (ModuleCat.exteriorPower.mk v) =
        exteriorRestriction M j g (exteriorRestriction M j f (ModuleCat.exteriorPower.mk v))
      rw [exteriorRestriction_mk, exteriorRestriction_mk, exteriorRestriction_mk]
      apply congrArg (ModuleCat.exteriorPower.mk (M := M.obj W) (n := j))
      funext i
      exact M.map_comp_apply f g (v i))

end Forms

/-- The sheaf of relative `j`-forms, obtained by sheafifying the sectionwise
exterior power of the relative Kähler differentials. -/
def differentialForms {X S : Scheme.{u}} (f : X ⟶ S) (j : ℕ) : X.Modules :=
  (Langlands.Scheme.Modules.sheafify X).obj
    (exteriorPresheaf (Langlands.Scheme.relativeDifferentials f).val j)

section PullbackForms

open AlgebraicGeometry.Scheme.Modules Opposite

variable {X Y S : Scheme.{u}} (a : Y ⟶ X) {f : X ⟶ S} {g : Y ⟶ S}

private def differentialSectionMap (over : a ≫ f = g) (U : X.Opensᵒᵖ) :
    (Langlands.Scheme.relativeDifferentials f).val.obj U →ₛₗ[(a.app U.unop).hom]
      (Langlands.Scheme.relativeDifferentials g).val.obj ((TopologicalSpace.Opens.map a.base).op.obj U) :=
  let b := (Langlands.Scheme.relativeDifferentialsPushforwardMap a over).val.app U
  { toFun := b
    map_add' := b.hom.map_add
    map_smul' := b.hom.map_smul }

private def formsPresheafPushforwardMap (over : a ≫ f = g) (j : ℕ) :
    exteriorPresheaf (Langlands.Scheme.relativeDifferentials f).val j ⟶
      ((pushforward a).obj (differentialForms g j)).val := by
  let ΩX := (Langlands.Scheme.relativeDifferentials f).val
  let ΩY := (Langlands.Scheme.relativeDifferentials g).val
  let t : exteriorPresheaf ΩY j ⟶ (differentialForms g j).val :=
    (Langlands.Scheme.Modules.sheafifyAdjunction Y).unit.app (exteriorPresheaf ΩY j)
  let aU := (TopologicalSpace.Opens.map a.base).op
  let b := Langlands.Scheme.relativeDifferentialsPushforwardMap a over
  refine
    { app := fun U => exteriorMap (differentialSectionMap a over U) j ≫
        (ModuleCat.restrictScalars (a.app U.unop).hom).map (t.app (aU.obj U))
      naturality := ?_ }
  intro U V i
  apply ModuleCat.exteriorPower.hom_ext
  ext v
  change t.app (aU.obj V)
      (exteriorMap (differentialSectionMap a over V) j
        (exteriorRestriction ΩX j i (ModuleCat.exteriorPower.mk v))) =
    (differentialForms g j).val.map (aU.map i)
      (t.app (aU.obj U)
        (exteriorMap (differentialSectionMap a over U) j (ModuleCat.exteriorPower.mk v)))
  rw [exteriorRestriction_mk, exteriorMap_mk, exteriorMap_mk]
  refine Eq.trans ?_ (PresheafOfModules.naturality_apply t (aU.map i) _)
  change t.app (aU.obj V) (ModuleCat.exteriorPower.mk (R := Y.presheaf.obj (aU.obj V)) _) =
    t.app (aU.obj V)
      (exteriorRestriction ΩY j (aU.map i)
        (ModuleCat.exteriorPower.mk (R := Y.presheaf.obj (aU.obj U)) _))
  rw [exteriorRestriction_mk]
  apply congrArg (fun w : Fin j → ΩY.obj (aU.obj V) =>
    t.app (aU.obj V) (ModuleCat.exteriorPower.mk (R := Y.presheaf.obj (aU.obj V)) w))
  funext k
  exact PresheafOfModules.naturality_apply b.val i (v k)

/-- Direct-image form of the pullback map on relative differential forms.
On the presheaf of exterior powers it wedges the pullbacks of the
entries, then applies sheafification. -/
def differentialFormsPushforwardMap (over : a ≫ f = g) (j : ℕ) :
    differentialForms f j ⟶ (pushforward a).obj (differentialForms g j) :=
  ((Langlands.Scheme.Modules.sheafifyAdjunction X).homEquiv _ _).symm
    (formsPresheafPushforwardMap a over j)

/-- Pullback of actual relative differential forms along a morphism over
the common base. -/
def differentialFormsPullbackMap (over : a ≫ f = g) (j : ℕ) :
    (Scheme.Modules.pullback a).obj (differentialForms f j) ⟶ differentialForms g j :=
  ((pullbackPushforwardAdjunction a).homEquiv _ _).symm
    (differentialFormsPushforwardMap a over j)

end PullbackForms

section Comparison

open EtaleGaloisAction EtaleCohomologyAction
open Langlands.GaloisRepresentation.HodgeTate

variable {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K))

local notation "Xbar" => baseChange K (AlgebraicClosure K) f
local notation "Galois" => Field.absoluteGaloisGroup K

private abbrev projection : Xbar ⟶ X := pullback.fst _ _

private theorem overProjection (σ : Galois) :
    (aut (galoisAut f) σ).hom ≫ projection f = projection f := by
  change baseChangeMap f σ ≫ pullback.fst _ _ = pullback.fst _ _
  simp [baseChangeMap]

variable (p : ℕ) [Fact p.Prime]
  [HasDerivedCategory.{wY}
    (EtaleDerivedSections.ModuleSheaf (baseChange K (AlgebraicClosure K) f) ℤ_[p])]
  [HasDerivedCategory.{wR} (ModuleCat.{0} ℤ_[p])]

local notation "R" => ℤ_[p]

/-- The diagram with deck action before forming the integral adic cohomology. -/
private def adicEtaleDiagram (q : ℕ) : ℕᵒᵖ ⥤ Action (ModuleCat.{0} R) Galois :=
  EtaleAdicSystem.ellPowerConstantSystem X p (ModuleCat.of R R) ⋙
    EtaleSchemeDeckAction.cohomologyFunctor (galoisAut (L := AlgebraicClosure K) f)
      (projection f) (overProjection f) R q

/-- The ordinary `ℚ_p`-étale cohomology of the geometric scheme and the
Galois action from the algebraic-closure factor. Take the limit with
constant `ℤ_p/p^m` coefficients before extending scalars. -/
def ellAdicEtaleAction (q : ℕ) : Action (ModuleCat.{0} ℚ_[p]) Galois :=
  ((ModuleCat.extendScalars (algebraMap R ℚ_[p])).mapAction Galois).obj
    (limit (adicEtaleDiagram f p q))

variable [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

local notation "C" => Completed p K

private abbrev hodgeGroup (i j : ℕ) : ModuleCat K :=
  (Langlands.AlgebraicGeometry.Modules.DerivedSections.relativeCohomology f i).obj
    (differentialForms f j)

private abbrev hodgeSide (q : ℕ) : Type :=
  (j : Fin (q + 1)) → C ⊗[K] hodgeGroup f (q - j.val) j.val

private abbrev etaleSide (q : ℕ) : Type :=
  C ⊗[ℚ_[p]] (ellAdicEtaleAction f p q).V

private def comparisonEquivariant (q : ℕ) (Φ : hodgeSide f p q ≃ₗ[C] etaleSide f p q) : Prop :=
  let ρ := (Rep.ActionToRep ℚ_[p] Galois).obj (ellAdicEtaleAction f p q)
  ∀ (σ : Galois) (x : hodgeSide f p q),
    Φ (fun j => cyclotomic p σ ^ (-(j.val : ℤ)) •
      LinearMap.rTensor (hodgeGroup f (q - j.val) j.val) (galoisLinearOverBase p K σ) (x j)) =
    TensorProduct.map (galoisLinear p σ) (ρ.ρ σ) (Φ x)

/-- Objectwise proper smooth Hodge–Tate comparison. The summand
`H^(q-j)(X, Ω^j_{X/K}) ⊗_K C_K` has the `-j` cyclotomic twist. -/
def ProperSmoothHodgeTateStatement [Smooth f] [IsProper f] (q : ℕ) : Prop :=
  ∃ Φ : hodgeSide f p q ≃ₗ[C] etaleSide f p q, comparisonEquivariant f p q Φ

end Comparison

section NaturalComparison

open EtaleGaloisAction EtaleDerivedSections
open Langlands.GaloisRepresentation.HodgeTate
open Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {K : Type} [Field K] (p : ℕ) [Fact p.Prime]

local notation "Base" => Spec (CommRingCat.of K)
local notation "R" => ℤ_[p]
local notation "Galois" => Field.absoluteGaloisGroup K

private abbrev geometricScheme (X : Over Base) : Scheme :=
  baseChange K (AlgebraicClosure K) X.hom

private abbrev coefficientReductions : ℕᵒᵖ ⥤ ModuleCat.{0} R :=
  (Langlands.Coefficients.AdicSystem.functor (Ideal.span {(p : R)})).obj (ModuleCat.of R R)

private def overGeometricMap {X Y : Over Base} (a : Y ⟶ X) :
    geometricScheme Y ⟶ geometricScheme X :=
  pullback.map Y.hom (Spec.algebraMap K (AlgebraicClosure K))
    X.hom (Spec.algebraMap K (AlgebraicClosure K)) a.left (𝟙 _) (𝟙 _)
    (by simp) (by simp)

private def geometricAdicDiagramIso (X : Over Base) (q : ℕ)
    [HasDerivedCategory.{wY} (ModuleSheaf (geometricScheme X) R)]
    [HasDerivedCategory.{wR} (ModuleCat R)] :
    adicEtaleDiagram X.hom p q ⋙ Action.forget (ModuleCat R) Galois ≅
      coefficientReductions p ⋙ constantCohomology (geometricScheme X) R q := by
  change (coefficientReductions p ⋙ constantSheaf X.left.smallEtaleTopology (ModuleCat R)) ⋙
    (EtaleInverseImage.inverseImage (projection X.hom) R ⋙
      cohomology (geometricScheme X) R q) ≅ _
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (coefficientReductions p)
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (EtaleInverseImage.inverseImageConstantIso (projection X.hom) R)
          (cohomology (geometricScheme X) R q))

private def constantCohomologyPullback {X Y : Scheme} (a : Y ⟶ X) (q : ℕ)
    [HasDerivedCategory.{wY} (ModuleSheaf X R)]
    [HasDerivedCategory.{wY} (ModuleSheaf Y R)]
    [HasDerivedCategory.{wR} (ModuleCat R)] :
    constantCohomology X R q ⟶ constantCohomology Y R q :=
  Functor.whiskerLeft _ (EtaleDerivedGlobalPullback.cohomologyPullback a R q) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (EtaleInverseImage.inverseImageConstantIso a R).hom _

/-- The pullback on rational geometric étale cohomology of the actual
morphism over `K`. The underlying limits are identified with the limits
of constant-coefficient cohomology on the two geometric schemes. -/
def ellAdicEtalePullback {X Y : Over Base} (a : Y ⟶ X) (q : ℕ)
    [HasDerivedCategory.{wY} (ModuleSheaf (geometricScheme X) R)]
    [HasDerivedCategory.{wY} (ModuleSheaf (geometricScheme Y) R)]
    [HasDerivedCategory.{wR} (ModuleCat R)] :
    (ellAdicEtaleAction X.hom p q).V ⟶ (ellAdicEtaleAction Y.hom p q).V :=
  let U := Action.forget (ModuleCat R) Galois
  let x := preservesLimitIso U (adicEtaleDiagram X.hom p q) ≪≫
    HasLimit.isoOfNatIso (geometricAdicDiagramIso p X q)
  let y := preservesLimitIso U (adicEtaleDiagram Y.hom p q) ≪≫
    HasLimit.isoOfNatIso (geometricAdicDiagramIso p Y q)
  (ModuleCat.extendScalars (algebraMap R ℚ_[p])).map
    (x.hom ≫ limMap (Functor.whiskerLeft (coefficientReductions p)
      (constantCohomologyPullback p (overGeometricMap a) q)) ≫ y.inv)

/-- Pullback on the coherent cohomology of the sheaf of relative `j`-forms. -/
def hodgeCohomologyPullback {X Y : Over Base} (a : Y ⟶ X) (j i : ℕ) :
    (relativeCohomology X.hom i).obj (differentialForms X.hom j) ⟶
      (relativeCohomology Y.hom i).obj (differentialForms Y.hom j) :=
  relativeCohomologyPullback a (differentialForms X.hom j) i ≫
    (relativeCohomology Y.hom i).map (differentialFormsPullbackMap a.left a.w j)

private abbrev ProperSmoothOver := {X : Over Base // Smooth X.hom ∧ IsProper X.hom}

variable [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
  [derivedGeometric : ∀ X : Over (Spec (CommRingCat.of K)),
    HasDerivedCategory.{wY} (ModuleSheaf (geometricScheme X) ℤ_[p])]
  [HasDerivedCategory.{wR} (ModuleCat ℤ_[p])]

local notation "C" => Completed p K

private abbrev comparisonOver (X : Over Base) (q : ℕ) : Type :=
  letI := derivedGeometric X
  hodgeSide X.hom p q ≃ₗ[C] etaleSide.{wY, wR} X.hom p q

private def comparisonOverEquivariant (X : Over Base) (q : ℕ)
    (Φ : comparisonOver.{wY, wR} p X q) : Prop :=
  let := derivedGeometric X
  comparisonEquivariant.{wY, wR} X.hom p q Φ

private def comparisonCommutesWithPullback {X Y : Over Base} (a : Y ⟶ X) (q : ℕ)
    (ΦX : comparisonOver.{wY, wR} p X q) (ΦY : comparisonOver.{wY, wR} p Y q) : Prop :=
  ∀ x : hodgeSide X.hom p q,
    ΦY (fun j => TensorProduct.AlgebraTensorModule.lTensor C C
      (hodgeCohomologyPullback a j.val (q - j.val)).hom (x j)) =
    TensorProduct.AlgebraTensorModule.lTensor C C (ellAdicEtalePullback.{wY, wR} p a q).hom (ΦX x)

/-- The proper smooth comparisons can be chosen simultaneously to
commute with pullback along every morphism over the same p-adic field. -/
def ProperSmoothHodgeTateNaturalStatement (q : ℕ) : Prop :=
  ∃ Φ : ∀ X : ProperSmoothOver (K := K), comparisonOver.{wY, wR} p X.val q,
    (∀ (X : ProperSmoothOver (K := K)), comparisonOverEquivariant.{wY, wR} p X.val q (Φ X)) ∧
    ∀ (X Y : ProperSmoothOver (K := K)) (a : Y.val ⟶ X.val),
      comparisonCommutesWithPullback.{wY, wR} p a q (Φ X) (Φ Y)

/-- Evaluating a natural comparison at one scheme gives the objectwise comparison. -/
theorem properSmoothHodgeTateStatement_of_natural (q : ℕ)
    (h : ProperSmoothHodgeTateNaturalStatement.{wY, wR} (K := K) p q)
    (X : Over Base) [Smooth X.hom] [IsProper X.hom] :
    ProperSmoothHodgeTateStatement.{wY, wR} X.hom p q := by
  obtain ⟨Φ, he, _⟩ := h
  let Y : ProperSmoothOver (K := K) := ⟨X, inferInstance, inferInstance⟩
  exact ⟨Φ Y, he Y⟩

end NaturalComparison

end Langlands.Cohomology.HodgeTate
