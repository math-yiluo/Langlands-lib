import Langlands.AbelianScheme.Tate.WeilCompactOpenLevels
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricPathProof

/-! # Canonical geometric-point comparisons of actual Weil level towers -/

universe u v w
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
noncomputable section
namespace Langlands.AbelianScheme.Tate
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme Langlands.Shimura Langlands.Shimura.PEL
open GroupScheme.Tate (Index)

section Adelic

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A : AbelianScheme S}
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (polarizationMap : A ⟶ dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
    evaluationA stability composition unitCoherence associativity comparison symmetry)
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] Rationalization.End A)
  (V : Type w) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  (ψ : LinearMap.BilinForm ℚ V)
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
  [hμfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom]
  {Ω Ω' Ω'' : Type u} [Field Ω] [Field Ω'] [Field Ω'']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S} {r : Spec (.of Ω'') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  {hr : ∀ Y : Cover S, Finite (Fiber r Y)}

local notation "LevelIndex" => FiniteAdelicScalarExtensionLevel D V ψ
local notation "towerAt" => weilAdelicCompactOpenLevelTower preservation composition unitCoherence associativity
  comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap
  h i V ψ
local notation "levelTransport" => weilAdelicLevelTransport preservation composition unitCoherence associativity comparison symmetry stability
  compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA polarizationMap
  h i V ψ htor hu

/-- Actual path transport assembles to an isomorphism of compact-open level towers. -/
def weilAdelicCompactOpenLevelTransport (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    towerAt s hs htor hu ≅ towerAt t ht htor hu :=
  NatIso.ofComponents (fun K => (levelTransport K.toSubgroup p).toIso) (by
    intro K L f
    ext x
    exact weilAdelicLevelTransport_translate preservation composition unitCoherence associativity comparison symmetry stability
      compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA polarizationMap
      h i V ψ htor hu
      p f.element f.respects x)

local notation "towerTransport" => weilAdelicCompactOpenLevelTransport preservation composition unitCoherence
  associativity comparison symmetry stability compatibility hA geometryA MA evaluationA
  polarizationMap h i V ψ htor hu

/-- The forward component is the existing actual fixed-level path equivalence. -/
@[simp] theorem weilAdelicCompactOpenLevelTransport_hom_app
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (K : LevelIndex)
    (x : (towerAt s hs htor hu).obj K) :
    (towerTransport p).hom.app K x = levelTransport K.toSubgroup p x := rfl

/-- The inverse component is the inverse existing fixed-level equivalence. -/
@[simp] theorem weilAdelicCompactOpenLevelTransport_inv_app
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (K : LevelIndex)
    (x : (towerAt t ht htor hu).obj K) :
    (towerTransport p).inv.app K x = (levelTransport K.toSubgroup p).symm x := rfl

/-- Path independence holds for the whole natural isomorphism. -/
theorem weilAdelicCompactOpenLevelTransport_path_independent
    (p q : fiberFunctor s hs ≅ fiberFunctor t ht) :
    towerTransport p = towerTransport q := by
  apply Iso.ext
  ext K x
  exact congrArg (fun e => e x)
    (weilAdelicLevelTransport_path_independent preservation composition unitCoherence associativity comparison symmetry stability
  compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA polarizationMap
  h i V ψ htor hu K.toSubgroup p q)

/-- Identity paths induce the identity natural isomorphism. -/
@[simp] theorem weilAdelicCompactOpenLevelTransport_refl :
    towerTransport (Iso.refl (fiberFunctor s hs)) = Iso.refl (towerAt s hs htor hu) := by
  apply Iso.ext
  ext K x
  exact congrArg (fun e => e x) (weilAdelicLevelTransport_refl preservation composition unitCoherence associativity comparison symmetry stability
  compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA polarizationMap
  h i V ψ htor hu K.toSubgroup)

/-- Concatenating paths composes the natural isomorphisms in the same order. -/
theorem weilAdelicCompactOpenLevelTransport_trans
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (q : fiberFunctor t ht ≅ fiberFunctor r hr) :
    towerTransport (p ≪≫ q) = towerTransport p ≪≫ towerTransport q := by
  apply Iso.ext
  ext K x
  exact congrArg (fun e => e x) (weilAdelicLevelTransport_trans preservation composition unitCoherence associativity comparison symmetry stability
  compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA polarizationMap
  h i V ψ htor hu K.toSubgroup p q)

/-- Reversing a path gives the inverse natural isomorphism. -/
theorem weilAdelicCompactOpenLevelTransport_symm (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (towerTransport p).symm = towerTransport p.symm := by
  apply Iso.ext
  ext K x
  exact congrArg (fun e => e x) (weilAdelicLevelTransport_symm preservation composition unitCoherence associativity comparison symmetry stability
  compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA polarizationMap
  h i V ψ htor hu K.toSubgroup p)

/-- Point transport commutes with every compact-open transporter map. -/
theorem weilAdelicCompactOpenLevelTransport_arrow
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) {K L : LevelIndex} (f : K ⟶ L)
    (x : (towerAt s hs htor hu).obj K) :
    (towerTransport p).hom.app L ((towerAt s hs htor hu).map f x) =
      (towerAt t ht htor hu).map f ((towerTransport p).hom.app K x) :=
  (towerTransport p).hom.naturality_apply f x

section Geometric
variable [ConnectedSpace S] [IsLocallyNoetherian S]

/-- Canonical comparison of actual Weil level towers at geometric points.
Path existence is proved, and independence removes the auxiliary choice. -/
def weilAdelicCompactOpenLevelGeometricTransport
    {Ωa Ωb : Type u} [Field Ωa] [IsAlgClosed Ωa] [Field Ωb] [IsAlgClosed Ωb]
    (a : Spec (.of Ωa) ⟶ S) (b : Spec (.of Ωb) ⟶ S)
    (ha : ∀ Y : Cover S, Finite (Fiber a Y)) (hb : ∀ Y : Cover S, Finite (Fiber b Y)) :
    towerAt a ha htor hu ≅ towerAt b hb htor hu :=
  towerTransport (Classical.choice (geometricPathExists a b ha hb))

local notation "canonicalTransport" => weilAdelicCompactOpenLevelGeometricTransport preservation composition
  unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA
  evaluationA polarizationMap h i V ψ htor hu

variable [IsAlgClosed Ω] [IsAlgClosed Ω'] [IsAlgClosed Ω'']

/-- Every supplied path computes the canonical comparison. -/
theorem weilAdelicCompactOpenLevelGeometricTransport_eq_path
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    canonicalTransport s t hs ht = towerTransport p :=
  weilAdelicCompactOpenLevelTransport_path_independent preservation composition unitCoherence associativity
    comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap
    h i V ψ htor hu _ p

/-- The canonical comparison at one point is the identity. -/
@[simp] theorem weilAdelicCompactOpenLevelGeometricTransport_refl :
    canonicalTransport s s hs hs = Iso.refl (towerAt s hs htor hu) := by
  rw [weilAdelicCompactOpenLevelGeometricTransport_eq_path preservation composition unitCoherence associativity
    comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap
    h i V ψ htor hu (Iso.refl (fiberFunctor s hs))]
  exact weilAdelicCompactOpenLevelTransport_refl preservation composition unitCoherence associativity
    comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap
    h i V ψ htor hu

/-- The canonical comparisons are transitive, with no path choice in the equation. -/
theorem weilAdelicCompactOpenLevelGeometricTransport_trans :
    canonicalTransport s r hs hr = canonicalTransport s t hs ht ≪≫ canonicalTransport t r ht hr := by
  let p := Classical.choice (geometricPathExists s t hs ht)
  let q := Classical.choice (geometricPathExists t r ht hr)
  rw [weilAdelicCompactOpenLevelGeometricTransport_eq_path preservation composition unitCoherence associativity
    comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap
    h i V ψ htor hu (p ≪≫ q),
    weilAdelicCompactOpenLevelGeometricTransport_eq_path preservation composition unitCoherence associativity
    comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap
    h i V ψ htor hu p,
    weilAdelicCompactOpenLevelGeometricTransport_eq_path preservation composition unitCoherence associativity
    comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap
    h i V ψ htor hu q]
  exact weilAdelicCompactOpenLevelTransport_trans preservation composition unitCoherence associativity
    comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap
    h i V ψ htor hu p q

/-- Reversing endpoints inverts the canonical comparison. -/
theorem weilAdelicCompactOpenLevelGeometricTransport_symm :
    (canonicalTransport s t hs ht).symm = canonicalTransport t s ht hs := by
  let p := Classical.choice (geometricPathExists s t hs ht)
  rw [weilAdelicCompactOpenLevelGeometricTransport_eq_path preservation composition unitCoherence associativity
    comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap
    h i V ψ htor hu p,
    weilAdelicCompactOpenLevelGeometricTransport_eq_path preservation composition unitCoherence associativity
    comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap
    h i V ψ htor hu p.symm]
  exact weilAdelicCompactOpenLevelTransport_symm preservation composition unitCoherence associativity
    comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap
    h i V ψ htor hu p

end Geometric
end Adelic

section PrimeToAdelic

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A : AbelianScheme S}
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (polarizationMap : A ⟶ dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
    evaluationA stability composition unitCoherence associativity comparison symmetry)
  {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] Rationalization.End A)
  (V : Type w) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  (ψ : LinearMap.BilinForm ℚ V)
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
  [hμfin : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S n.val).X.hom]
  {Ω Ω' Ω'' : Type u} [Field Ω] [Field Ω'] [Field Ω'']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S} {r : Spec (.of Ω'') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  {hr : ∀ Y : Cover S, Finite (Fiber r Y)}

local notation "LevelIndex" => PrimeToScalarExtensionLevel D V ψ m
local notation "towerAt" => weilPrimeToAdelicCompactOpenLevelTower preservation composition unitCoherence associativity
  comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap
  hAway i V ψ
local notation "levelTransport" => weilPrimeToAdelicLevelTransport preservation composition unitCoherence associativity comparison symmetry stability
  compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA polarizationMap
  hAway i V ψ htor hu

/-- Actual path transport assembles to an isomorphism of compact-open level towers. -/
def weilPrimeToAdelicCompactOpenLevelTransport (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    towerAt s hs htor hu ≅ towerAt t ht htor hu :=
  NatIso.ofComponents (fun K => (levelTransport K.toSubgroup p).toIso) (by
    intro K L f
    ext x
    exact weilPrimeToAdelicLevelTransport_translate preservation composition unitCoherence associativity comparison symmetry stability
      compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA polarizationMap
      hAway i V ψ htor hu
      p f.element f.respects x)

local notation "towerTransport" => weilPrimeToAdelicCompactOpenLevelTransport preservation composition unitCoherence
  associativity comparison symmetry stability compatibility hA geometryA MA evaluationA
  polarizationMap hAway i V ψ htor hu

/-- The forward component is the existing actual fixed-level path equivalence. -/
@[simp] theorem weilPrimeToAdelicCompactOpenLevelTransport_hom_app
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (K : LevelIndex)
    (x : (towerAt s hs htor hu).obj K) :
    (towerTransport p).hom.app K x = levelTransport K.toSubgroup p x := rfl

/-- The inverse component is the inverse existing fixed-level equivalence. -/
@[simp] theorem weilPrimeToAdelicCompactOpenLevelTransport_inv_app
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (K : LevelIndex)
    (x : (towerAt t ht htor hu).obj K) :
    (towerTransport p).inv.app K x = (levelTransport K.toSubgroup p).symm x := rfl

/-- Path independence holds for the whole natural isomorphism. -/
theorem weilPrimeToAdelicCompactOpenLevelTransport_path_independent
    (p q : fiberFunctor s hs ≅ fiberFunctor t ht) :
    towerTransport p = towerTransport q := by
  apply Iso.ext
  ext K x
  exact congrArg (fun e => e x)
    (weilPrimeToAdelicLevelTransport_path_independent preservation composition unitCoherence associativity comparison symmetry stability
  compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA polarizationMap
  hAway i V ψ htor hu K.toSubgroup p q)

/-- Identity paths induce the identity natural isomorphism. -/
@[simp] theorem weilPrimeToAdelicCompactOpenLevelTransport_refl :
    towerTransport (Iso.refl (fiberFunctor s hs)) = Iso.refl (towerAt s hs htor hu) := by
  apply Iso.ext
  ext K x
  exact congrArg (fun e => e x) (weilPrimeToAdelicLevelTransport_refl preservation composition unitCoherence associativity comparison symmetry stability
  compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA polarizationMap
  hAway i V ψ htor hu K.toSubgroup)

/-- Concatenating paths composes the natural isomorphisms in the same order. -/
theorem weilPrimeToAdelicCompactOpenLevelTransport_trans
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (q : fiberFunctor t ht ≅ fiberFunctor r hr) :
    towerTransport (p ≪≫ q) = towerTransport p ≪≫ towerTransport q := by
  apply Iso.ext
  ext K x
  exact congrArg (fun e => e x) (weilPrimeToAdelicLevelTransport_trans preservation composition unitCoherence associativity comparison symmetry stability
  compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA polarizationMap
  hAway i V ψ htor hu K.toSubgroup p q)

/-- Reversing a path gives the inverse natural isomorphism. -/
theorem weilPrimeToAdelicCompactOpenLevelTransport_symm (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (towerTransport p).symm = towerTransport p.symm := by
  apply Iso.ext
  ext K x
  exact congrArg (fun e => e x) (weilPrimeToAdelicLevelTransport_symm preservation composition unitCoherence associativity comparison symmetry stability
  compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA polarizationMap
  hAway i V ψ htor hu K.toSubgroup p)

/-- Point transport commutes with every compact-open transporter map. -/
theorem weilPrimeToAdelicCompactOpenLevelTransport_arrow
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) {K L : LevelIndex} (f : K ⟶ L)
    (x : (towerAt s hs htor hu).obj K) :
    (towerTransport p).hom.app L ((towerAt s hs htor hu).map f x) =
      (towerAt t ht htor hu).map f ((towerTransport p).hom.app K x) :=
  (towerTransport p).hom.naturality_apply f x

section Geometric
variable [ConnectedSpace S] [IsLocallyNoetherian S]

/-- Canonical comparison of actual Weil level towers at geometric points.
Path existence is proved, and independence removes the auxiliary choice. -/
def weilPrimeToAdelicCompactOpenLevelGeometricTransport
    {Ωa Ωb : Type u} [Field Ωa] [IsAlgClosed Ωa] [Field Ωb] [IsAlgClosed Ωb]
    (a : Spec (.of Ωa) ⟶ S) (b : Spec (.of Ωb) ⟶ S)
    (ha : ∀ Y : Cover S, Finite (Fiber a Y)) (hb : ∀ Y : Cover S, Finite (Fiber b Y)) :
    towerAt a ha htor hu ≅ towerAt b hb htor hu :=
  towerTransport (Classical.choice (geometricPathExists a b ha hb))

local notation "canonicalTransport" => weilPrimeToAdelicCompactOpenLevelGeometricTransport preservation composition
  unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA
  evaluationA polarizationMap hAway i V ψ htor hu

variable [IsAlgClosed Ω] [IsAlgClosed Ω'] [IsAlgClosed Ω'']

/-- Every supplied path computes the canonical comparison. -/
theorem weilPrimeToAdelicCompactOpenLevelGeometricTransport_eq_path
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    canonicalTransport s t hs ht = towerTransport p :=
  weilPrimeToAdelicCompactOpenLevelTransport_path_independent preservation composition unitCoherence associativity
    comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap
    hAway i V ψ htor hu _ p

/-- The canonical comparison at one point is the identity. -/
@[simp] theorem weilPrimeToAdelicCompactOpenLevelGeometricTransport_refl :
    canonicalTransport s s hs hs = Iso.refl (towerAt s hs htor hu) := by
  rw [weilPrimeToAdelicCompactOpenLevelGeometricTransport_eq_path preservation composition unitCoherence associativity
    comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap
    hAway i V ψ htor hu (Iso.refl (fiberFunctor s hs))]
  exact weilPrimeToAdelicCompactOpenLevelTransport_refl preservation composition unitCoherence associativity
    comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap
    hAway i V ψ htor hu

/-- The canonical comparisons are transitive, with no path choice in the equation. -/
theorem weilPrimeToAdelicCompactOpenLevelGeometricTransport_trans :
    canonicalTransport s r hs hr = canonicalTransport s t hs ht ≪≫ canonicalTransport t r ht hr := by
  let p := Classical.choice (geometricPathExists s t hs ht)
  let q := Classical.choice (geometricPathExists t r ht hr)
  rw [weilPrimeToAdelicCompactOpenLevelGeometricTransport_eq_path preservation composition unitCoherence associativity
    comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap
    hAway i V ψ htor hu (p ≪≫ q),
    weilPrimeToAdelicCompactOpenLevelGeometricTransport_eq_path preservation composition unitCoherence associativity
    comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap
    hAway i V ψ htor hu p,
    weilPrimeToAdelicCompactOpenLevelGeometricTransport_eq_path preservation composition unitCoherence associativity
    comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap
    hAway i V ψ htor hu q]
  exact weilPrimeToAdelicCompactOpenLevelTransport_trans preservation composition unitCoherence associativity
    comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap
    hAway i V ψ htor hu p q

/-- Reversing endpoints inverts the canonical comparison. -/
theorem weilPrimeToAdelicCompactOpenLevelGeometricTransport_symm :
    (canonicalTransport s t hs ht).symm = canonicalTransport t s ht hs := by
  let p := Classical.choice (geometricPathExists s t hs ht)
  rw [weilPrimeToAdelicCompactOpenLevelGeometricTransport_eq_path preservation composition unitCoherence associativity
    comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap
    hAway i V ψ htor hu p,
    weilPrimeToAdelicCompactOpenLevelGeometricTransport_eq_path preservation composition unitCoherence associativity
    comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap
    hAway i V ψ htor hu p.symm]
  exact weilPrimeToAdelicCompactOpenLevelTransport_symm preservation composition unitCoherence associativity
    comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap
    hAway i V ψ htor hu p

end Geometric
end PrimeToAdelic

end Langlands.AbelianScheme.Tate
