import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSubgroupTraceTower
import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSubgroupCohomologyConjugation

/-! # Conjugation of the original finite-fiber compact traces -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory Topology Opposite Langlands.Sheaf.Equivariant
open Langlands.Cohomology.SmoothGodementComparison
open Langlands.LocallyConstantCovering

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P} {U : OpenSubgroup G}

namespace OpenSubgroupTransport.FiniteIndexLevel

local instance finiteTowerFiber {U' : OpenSubgroup G} (d' : ρ.InvariantRationalDomain U')
    {V W : FiniteIndexLevel U'} (f : V ⟶ W) :
    ∀ y : (rationalObject d' W).InducedSpectrum,
      Finite ((rationalArrow d' f).inducedMap ⁻¹' {y}) :=
  finite_rationalArrow_fiber d' f

variable (d : ρ.InvariantRationalDomain U) (g : G)

/-- The two original conjugation homeomorphisms identify the literal subgroup fibers. -/
def conjugationFiberEquiv {V W : FiniteIndexLevel U} (f : V ⟶ W)
    (y : (rationalObject d W).InducedSpectrum) :
    (rationalArrow d f).inducedMap ⁻¹' {y} ≃
      (rationalArrow ((ρ.invariantConjugationEquivalence U g).functor.obj d)
        ((conjugationEquivalence U g).functor.map f)).inducedMap ⁻¹'
          {inducedConjugationHomeomorph d g W y} where
  toFun x := ⟨inducedConjugationHomeomorph d g V x.val,
    (inducedConjugationHomeomorph_naturality d g f x.val).symm.trans
      (congrArg (inducedConjugationHomeomorph d g W) x.property)⟩
  invFun x := ⟨(inducedConjugationHomeomorph d g V).symm x.val, by
    apply (inducedConjugationHomeomorph d g W).injective
    rw [inducedConjugationHomeomorph_naturality,
      Homeomorph.apply_symm_apply]
    exact x.property⟩
  left_inv x := Subtype.ext ((inducedConjugationHomeomorph d g V).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((inducedConjugationHomeomorph d g V).apply_symm_apply x.val)

@[simp]
theorem conjugationFiberEquiv_apply {V W : FiniteIndexLevel U} (f : V ⟶ W)
    (y : (rationalObject d W).InducedSpectrum)
    (x : (rationalArrow d f).inducedMap ⁻¹' {y}) :
    (conjugationFiberEquiv d g f y x).val = inducedConjugationHomeomorph d g V x.val :=
  rfl

/-- Reindex the whole original finite sum, without dividing by the degree. -/
theorem fiberSum_conjugation {V W : FiniteIndexLevel U} (f : V ⟶ W)
    {A : Type u} [AddCommGroup A]
    (s : (rationalObject ((ρ.invariantConjugationEquivalence U g).functor.obj d)
      ((conjugationEquivalence U g).functor.obj V)).InducedSpectrum → A)
    (y : (rationalObject d W).InducedSpectrum) :
    fiberSum (rationalArrow d f).inducedMap
        (s ∘ inducedConjugationHomeomorph d g V) y =
      fiberSum
        (rationalArrow ((ρ.invariantConjugationEquivalence U g).functor.obj d)
          ((conjugationEquivalence U g).functor.map f)).inducedMap s
        (inducedConjugationHomeomorph d g W y) := by
  let := Fintype.ofFinite ((rationalArrow d f).inducedMap ⁻¹' {y})
  let := Fintype.ofFinite
    ((rationalArrow ((ρ.invariantConjugationEquivalence U g).functor.obj d)
      ((conjugationEquivalence U g).functor.map f)).inducedMap ⁻¹'
        {inducedConjugationHomeomorph d g W y})
  exact Fintype.sum_equiv (conjugationFiberEquiv d g f y) _ _ (fun _ => rfl)

variable (R : Type u) [CommRing R]

/-- The same original proper pullbacks give a coefficient isomorphism without local stability. -/
def compactConjugationIso (V : FiniteIndexLevel U) :
    CompactSections.coefficientFunctor
        (rationalObject ((ρ.invariantConjugationEquivalence U g).functor.obj d)
          ((conjugationEquivalence U g).functor.obj V)) ≅
      (CompactSections.coefficientFunctor (rationalObject d V) :
        SmoothRep.{u, u, u} R G ⥤ SmoothRep.{u, u, u} R G) where
  hom := Hom.compactSupportPullbackNatTrans (rationalConjugationIso d g V).hom
    (isProperMap_rationalConjugationIso_hom d g V)
  inv := Hom.compactSupportPullbackNatTrans (rationalConjugationIso d g V).inv
    (isProperMap_rationalConjugationIso_inv d g V)
  hom_inv_id := by
    apply NatTrans.ext
    funext M
    ext s
    apply Subtype.ext
    apply LocallyConstant.ext
    intro z
    exact congrArg s.val ((inducedConjugationHomeomorph d g V).apply_symm_apply z)
  inv_hom_id := by
    apply NatTrans.ext
    funext M
    ext s
    apply Subtype.ext
    apply LocallyConstant.ext
    intro z
    exact congrArg s.val ((inducedConjugationHomeomorph d g V).symm_apply_apply z)

/-- Covariant trace commutes with the original conjugation pullbacks for every coefficient. -/
@[reassoc]
theorem compactConjugationIso_trace_naturality {V W : FiniteIndexLevel U}
    (f : V ⟶ W) :
    (compactTraceTower ((ρ.invariantConjugationEquivalence U g).functor.obj d) R).map
        ((conjugationEquivalence U g).functor.map f) ≫ (compactConjugationIso d g R W).hom =
      (compactConjugationIso d g R V).hom ≫ (compactTraceTower d R).map f := by
  apply NatTrans.ext
  funext M
  ext s
  apply Subtype.ext
  apply LocallyConstant.ext
  intro y
  exact (fiberSum_conjugation d g f s.val y).symm

/-- Conjugation is a natural isomorphism of the actual covariant compact trace towers. -/
def compactTraceTowerConjugationIso :
    (conjugationEquivalence U g).functor ⋙
        compactTraceTower ((ρ.invariantConjugationEquivalence U g).functor.obj d) R ≅
      compactTraceTower d R :=
  NatIso.ofComponents (compactConjugationIso d g R)
    (fun f => compactConjugationIso_trace_naturality d g R f)

/-- The contravariant original pullbacks use precisely the same components. -/
theorem compactConjugationIso_pullback_naturality {V W : FiniteIndexLevel U}
    (f : V ⟶ W) :
    (compactPullbackTower ((ρ.invariantConjugationEquivalence U g).functor.obj d) R).map
        ((conjugationEquivalence U g).functor.map f).op ≫
        (compactConjugationIso d g R V).hom =
      (compactConjugationIso d g R W).hom ≫ (compactPullbackTower d R).map f.op := by
  apply NatTrans.ext
  funext M
  ext s
  apply Subtype.ext
  apply LocallyConstant.ext
  intro z
  change s.val ((rationalArrow
      ((ρ.invariantConjugationEquivalence U g).functor.obj d)
      ((conjugationEquivalence U g).functor.map f)).inducedMap
        (inducedConjugationHomeomorph d g V z)) =
    s.val (inducedConjugationHomeomorph d g W ((rationalArrow d f).inducedMap z))
  exact congrArg s.val (inducedConjugationHomeomorph_naturality d g f z).symm

/-- The original compact pullback towers also conjugate without a local stability premise. -/
def compactPullbackTowerConjugationIso :
    (conjugationEquivalence U g).functor.op ⋙
        compactPullbackTower ((ρ.invariantConjugationEquivalence U g).functor.obj d) R ≅
      compactPullbackTower d R :=
  NatIso.ofComponents (fun V => compactConjugationIso d g R V.unop)
    (fun f => compactConjugationIso_pullback_naturality d g R f.unop)

/-- The same covariant trace isomorphism after whole-group smooth invariants. -/
def invariantCompactTraceTowerConjugationIso :
    (conjugationEquivalence U g).functor ⋙
        invariantCompactTraceTower
          ((ρ.invariantConjugationEquivalence U g).functor.obj d) R ≅
      invariantCompactTraceTower d R :=
  Functor.isoWhiskerRight (compactTraceTowerConjugationIso d g R)
    ((Functor.whiskeringRight _ _ _).obj (smoothInvariants R G))

/-- The same contravariant pullbacks after whole-group smooth invariants. -/
def invariantCompactPullbackTowerConjugationIso :
    (conjugationEquivalence U g).functor.op ⋙
        invariantCompactPullbackTower
          ((ρ.invariantConjugationEquivalence U g).functor.obj d) R ≅
      invariantCompactPullbackTower d R :=
  Functor.isoWhiskerRight (compactPullbackTowerConjugationIso d g R)
    ((Functor.whiskeringRight _ _ _).obj (smoothInvariants R G))

/-- The trace-tower component is precisely the original proper pullback. -/
@[simp]
theorem compactTraceTowerConjugationIso_hom_app (V : FiniteIndexLevel U) :
    (compactTraceTowerConjugationIso d g R).hom.app V =
      Hom.compactSupportPullbackNatTrans (R := R) (rationalConjugationIso d g V).hom
        (isProperMap_rationalConjugationIso_hom d g V) := rfl

/-- Its inverse is precisely the original inverse translation pullback. -/
@[simp]
theorem compactTraceTowerConjugationIso_inv_app (V : FiniteIndexLevel U) :
    (compactTraceTowerConjugationIso d g R).inv.app V =
      Hom.compactSupportPullbackNatTrans (R := R) (rationalConjugationIso d g V).inv
        (isProperMap_rationalConjugationIso_inv d g V) := rfl

/-- Covariant traces and contravariant pullbacks use the identical level components. -/
@[simp]
theorem compactPullbackTowerConjugationIso_app (V : FiniteIndexLevel U) :
    (compactPullbackTowerConjugationIso d g R).app (op V) =
      (compactTraceTowerConjugationIso d g R).app V := rfl

/-- The invariant component restricts the same original proper pullback. -/
@[simp]
theorem invariantCompactTraceTowerConjugationIso_hom_app (V : FiniteIndexLevel U) :
    (invariantCompactTraceTowerConjugationIso d g R).hom.app V =
      Functor.whiskerRight (compactConjugationIso d g R V).hom (smoothInvariants R G) :=
  rfl

/-- Its invariant inverse restricts the original inverse translation pullback. -/
@[simp]
theorem invariantCompactTraceTowerConjugationIso_inv_app (V : FiniteIndexLevel U) :
    (invariantCompactTraceTowerConjugationIso d g R).inv.app V =
      Functor.whiskerRight (compactConjugationIso d g R V).inv (smoothInvariants R G) :=
  rfl

@[simp]
theorem invariantCompactPullbackTowerConjugationIso_app (V : FiniteIndexLevel U) :
    (invariantCompactPullbackTowerConjugationIso d g R).app (op V) =
      (invariantCompactTraceTowerConjugationIso d g R).app V := rfl

/-- The whole function, with its original coefficient, is precomposed with conjugation. -/
@[simp]
theorem compactTraceTowerConjugationIso_apply (V : FiniteIndexLevel U)
    (M : SmoothRep.{u, u, u} R G)
    (s : CompactSections.Functions (R := R) (V := M)
      (rationalObject ((ρ.invariantConjugationEquivalence U g).functor.obj d)
        ((conjugationEquivalence U g).functor.obj V)))
    (z : (rationalObject d V).InducedSpectrum) :
    (SmoothRep.hom (((compactTraceTowerConjugationIso d g R).hom.app V).app M) s).val z =
      s.val (inducedConjugationHomeomorph d g V z) := rfl

/-- The inverse component precomposes with the inverse of the same homeomorphism. -/
@[simp]
theorem compactTraceTowerConjugationIso_inv_apply (V : FiniteIndexLevel U)
    (M : SmoothRep.{u, u, u} R G)
    (s : CompactSections.Functions (R := R) (V := M) (rationalObject d V))
    (z : (rationalObject ((ρ.invariantConjugationEquivalence U g).functor.obj d)
      ((conjugationEquivalence U g).functor.obj V)).InducedSpectrum) :
    (SmoothRep.hom (((compactTraceTowerConjugationIso d g R).inv.app V).app M) s).val z =
      s.val ((inducedConjugationHomeomorph d g V).symm z) := rfl

/-- Evaluation on original quotient representatives retains the inverse group label. -/
theorem compactTraceTowerConjugationIso_apply_mk (V : FiniteIndexLevel U)
    (M : SmoothRep.{u, u, u} R G)
    (s : CompactSections.Functions (R := R) (V := M)
      (rationalObject ((ρ.invariantConjugationEquivalence U g).functor.obj d)
        ((conjugationEquivalence U g).functor.obj V)))
    (a : G) (x : (rationalObject d V).LocalSpectrum) :
    (SmoothRep.hom (((compactTraceTowerConjugationIso d g R).hom.app V).app M) s).val
        ((rationalObject d V).inducedMk a x) =
      s.val ((rationalObject ((ρ.invariantConjugationEquivalence U g).functor.obj d)
        ((conjugationEquivalence U g).functor.obj V)).inducedMk
          (a * g⁻¹) ((rationalConjugationIso d g V).hom.localSpectrumMap x)) := by
  rw [compactTraceTowerConjugationIso_apply, inducedConjugationHomeomorph_mk]

/-- Whole-group invariants retain precisely the same evaluation formula. -/
@[simp]
theorem invariantCompactTraceTowerConjugationIso_apply (V : FiniteIndexLevel U)
    (M : SmoothRep.{u, u, u} R G)
    (s : ((invariantCompactTraceTower
      ((ρ.invariantConjugationEquivalence U g).functor.obj d) R).obj
        ((conjugationEquivalence U g).functor.obj V)).obj M)
    (z : (rationalObject d V).InducedSpectrum) :
    (((((invariantCompactTraceTowerConjugationIso d g R).hom.app V).app M).hom s).val).val z =
      s.val.val (inducedConjugationHomeomorph d g V z) := rfl

/-- Every original pullback-then-trace span commutes with the same conjugation. -/
theorem compactConjugationIso_span {A V W : FiniteIndexLevel U}
    (a : A ⟶ V) (b : A ⟶ W) :
    (compactPullbackTower ((ρ.invariantConjugationEquivalence U g).functor.obj d) R).map
          ((conjugationEquivalence U g).functor.map a).op ≫
        (compactTraceTower ((ρ.invariantConjugationEquivalence U g).functor.obj d) R).map
          ((conjugationEquivalence U g).functor.map b) ≫
        (compactConjugationIso d g R W).hom =
      (compactConjugationIso d g R V).hom ≫
        (compactPullbackTower d R).map a.op ≫ (compactTraceTower d R).map b := by
  apply NatTrans.ext
  funext M
  ext s
  apply Subtype.ext
  apply LocallyConstant.ext
  intro y
  change fiberSum
      (rationalArrow ((ρ.invariantConjugationEquivalence U g).functor.obj d)
        ((conjugationEquivalence U g).functor.map b)).inducedMap
      (s.val ∘ (rationalArrow ((ρ.invariantConjugationEquivalence U g).functor.obj d)
        ((conjugationEquivalence U g).functor.map a)).inducedMap)
      (inducedConjugationHomeomorph d g W y) =
    fiberSum (rationalArrow d b).inducedMap
      ((s.val ∘ inducedConjugationHomeomorph d g V) ∘ (rationalArrow d a).inducedMap) y
  rw [← fiberSum_conjugation d g b]
  apply congrArg (fun t => fiberSum (rationalArrow d b).inducedMap t y)
  funext z
  exact congrArg s.val (inducedConjugationHomeomorph_naturality d g a z).symm

/-- In particular the canonical original intersection-span operators conjugate. -/
theorem commonRefinementCorrespondence_conjugation (V W : FiniteIndexLevel U) :
    commonRefinementCorrespondence
        ((ρ.invariantConjugationEquivalence U g).functor.obj d) R
        ((conjugationEquivalence U g).functor.obj V)
        ((conjugationEquivalence U g).functor.obj W) ≫
        (compactConjugationIso d g R W).hom =
      (compactConjugationIso d g R V).hom ≫ commonRefinementCorrespondence d R V W := by
  exact compactConjugationIso_span d g R
    (homOfLE (commonRefinement_le_left V W))
    (homOfLE (commonRefinement_le_right V W))

/-- The identical canonical intersection-span compatibility after whole-group invariants. -/
theorem invariantCommonRefinementCorrespondence_conjugation (V W : FiniteIndexLevel U) :
    invariantCommonRefinementCorrespondence
        ((ρ.invariantConjugationEquivalence U g).functor.obj d) R
        ((conjugationEquivalence U g).functor.obj V)
        ((conjugationEquivalence U g).functor.obj W) ≫
        (invariantCompactTraceTowerConjugationIso d g R).hom.app W =
      (invariantCompactTraceTowerConjugationIso d g R).hom.app V ≫
        invariantCommonRefinementCorrespondence d R V W := by
  exact congrArg (fun a => Functor.whiskerRight a (smoothInvariants R G))
    (commonRefinementCorrespondence_conjugation d g R V W)

section StableComparison

variable [targetStable : HasStableNeighbourhoods ((inclusion U).obj d).subgroup.toSubgroup
  ((inclusion U).obj d).LocalSpectrum]

local instance :
    HasStableNeighbourhoods
      ((inclusion (conjugateOpenSubgroup U g)).obj
        ((ρ.invariantConjugationEquivalence U g).functor.obj d)).subgroup.toSubgroup
      ((inclusion (conjugateOpenSubgroup U g)).obj
        ((ρ.invariantConjugationEquivalence U g).functor.obj d)).LocalSpectrum :=
  hasStableNeighbourhoods_conjugate_local d g

/-- With local stability, this is the existing compact-function conjugation isomorphism. -/
theorem compactPullbackTowerConjugationIso_eq_compactFunctions :
    compactPullbackTowerConjugationIso d g R =
      compactFunctionsTowerConjugationIso d g R := by
  apply Iso.ext
  apply NatTrans.ext
  funext V
  rfl

/-- Its invariant form agrees with the existing Godement compact-function component. -/
theorem invariantCompactPullbackTowerConjugationIso_eq_compactFunctions :
    invariantCompactPullbackTowerConjugationIso d g R =
      invariantCompactFunctionsTowerConjugationIso d g R := by
  apply Iso.ext
  apply NatTrans.ext
  funext V
  rfl

end StableComparison

end OpenSubgroupTransport.FiniteIndexLevel

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
