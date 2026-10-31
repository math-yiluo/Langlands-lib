import Langlands.AbelianScheme.Tate.WeilCompactOpenLevelTransport
import Langlands.AbelianScheme.Tate.TwistMonodromyUnits
import Langlands.AbelianScheme.TorsionFiniteEtale
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof

/-! # Actual geometric Weil-compatible compact-open level towers -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.AbelianScheme.Tate.Geometric

universe u v w
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme Langlands.Shimura Langlands.Shimura.PEL
open GroupScheme.Tate (Index)

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
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] Rationalization.End A)
  (V : Type w) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  (ψ : LinearMap.BilinForm ℚ V)

section Full
variable (h : Global.RationalProfiniteIntegerAdeleComparison)
  (hunit : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))

local notation "LevelIndex" => FiniteAdelicScalarExtensionLevel D V ψ
local notation "G" => ScalarExtensionSimilitudePoints D V (Global.FiniteAdeles ℚ) ψ
local notation "μfin" => TateTwist.Geometry.InvertibleOrders.selectedFinite S (fun _ => True) hunit
local notation "μet" => TateTwist.Geometry.InvertibleOrders.selectedEtale S (fun _ => True) hunit

/-- The actual full Weil-compatible fixed-orbit tower, with torsion and twist geometry proved. -/
def weilAdelicCompactOpenLevelTower
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    LevelIndex ⥤ Type (max u w) :=
  Tate.weilAdelicCompactOpenLevelTower preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap h i V ψ
    s (geometricFiberFinite s) torsionFiniteEtale hunit (hμfin := μfin) (hμet := μet)

local notation "towerAt" => weilAdelicCompactOpenLevelTower preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap i V ψ h hunit
local notation "genericLevel" => Tate.WeilAdelicCompactOpenLevel preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap h i V ψ

/-- The existing actual monodromy-fixed orbit set at a compact open level. -/
abbrev WeilAdelicCompactOpenLevel
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) (K : LevelIndex) :=
  (towerAt s).obj K

/-- The specialized tower has exactly the published actual fixed-orbit objects. -/
@[simp] theorem weilAdelicCompactOpenLevelTower_obj
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) (K : LevelIndex) :
    (towerAt s).obj K = genericLevel s (geometricFiberFinite s) torsionFiniteEtale hunit
      (hμfin := μfin) (hμet := μet) K := rfl

/-- Transporter arrows act by the actual fixed-orbit right translation. -/
@[simp] theorem weilAdelicCompactOpenLevelTower_map
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {K L : LevelIndex} (f : K ⟶ L) (q : (towerAt s).obj K) :
    (towerAt s).map f q =
      Tate.weilAdelicLevelTranslate preservation composition unitCoherence associativity comparison
        symmetry stability compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA
        polarizationMap h i V ψ torsionFiniteEtale hunit
        (s := s) (hs := geometricFiberFinite s) (hμfin := μfin) (hμet := μet)
        f.element f.respects q := rfl

/-- Inclusion arrows are the actual forgetting maps on invariant frame orbits. -/
@[simp] theorem weilAdelicCompactOpenLevelTower_inclusion
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {K L : LevelIndex} (hK : K.toSubgroup ≤ L.toSubgroup) (q : (towerAt s).obj K) :
    (towerAt s).map (CompactOpenLevel.inclusion hK) q =
      Tate.weilAdelicLevelForget preservation composition unitCoherence associativity comparison
        symmetry stability compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA
        polarizationMap h i V ψ torsionFiniteEtale hunit
        (s := s) (hs := geometricFiberFinite s) (hμfin := μfin) (hμet := μet) hK q := rfl

section Hecke
variable [Module.Finite ℚ V]

/-- The first full Hecke leg forgets the actual intermediate compact open subgroup. -/
def weilAdelicCompactOpenHeckeLeft
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K L : LevelIndex) (g : G) :
    (towerAt s).obj (CompactOpenLevel.heckeLevel K L g) → (towerAt s).obj K :=
  (towerAt s).map (CompactOpenLevel.heckeLeft K L g)

/-- The second full Hecke leg translates frames by the actual similitude element. -/
def weilAdelicCompactOpenHeckeRight
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K L : LevelIndex) (g : G) :
    (towerAt s).obj (CompactOpenLevel.heckeLevel K L g) → (towerAt s).obj L :=
  (towerAt s).map (CompactOpenLevel.heckeRight K L g)

end Hecke

section CanonicalTransport
variable [ConnectedSpace S] [IsLocallyNoetherian S]
  {Ω Ω' Ω'' : Type u} [Field Ω] [IsAlgClosed Ω]
  [Field Ω'] [IsAlgClosed Ω'] [Field Ω''] [IsAlgClosed Ω'']
  (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ω') ⟶ S) (r : Spec (.of Ω'') ⟶ S)

/-- Canonical comparison of actual full level towers, with geometric finiteness proved. -/
def weilAdelicCompactOpenLevelGeometricTransport : towerAt s ≅ towerAt t :=
  Tate.weilAdelicCompactOpenLevelGeometricTransport preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap h i V ψ torsionFiniteEtale hunit
    s t (geometricFiberFinite s) (geometricFiberFinite t) (hμfin := μfin) (hμet := μet)

local notation "transport" => weilAdelicCompactOpenLevelGeometricTransport preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap i V ψ h hunit

/-- Every actual etale path gives the same canonical tower comparison. -/
theorem weilAdelicCompactOpenLevelGeometricTransport_eq_path
    (p : fiberFunctor s (geometricFiberFinite s) ≅ fiberFunctor t (geometricFiberFinite t)) :
    transport s t =
      Tate.weilAdelicCompactOpenLevelTransport preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap h i V ψ torsionFiniteEtale hunit
        (hμfin := μfin) (hμet := μet) p :=
  Tate.weilAdelicCompactOpenLevelGeometricTransport_eq_path preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap h i V ψ torsionFiniteEtale hunit
    (hμfin := μfin) (hμet := μet) p

/-- The canonical comparison at a single geometric point is the identity. -/
@[simp] theorem weilAdelicCompactOpenLevelGeometricTransport_refl : transport s s = Iso.refl (towerAt s) :=
  Tate.weilAdelicCompactOpenLevelGeometricTransport_refl preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap h i V ψ torsionFiniteEtale hunit
    (s := s) (hs := geometricFiberFinite s) (hμfin := μfin) (hμet := μet)

/-- Canonical geometric-point comparisons compose transitively. -/
theorem weilAdelicCompactOpenLevelGeometricTransport_trans :
    transport s r = transport s t ≪≫ transport t r :=
  Tate.weilAdelicCompactOpenLevelGeometricTransport_trans preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap h i V ψ torsionFiniteEtale hunit
    (s := s) (t := t) (r := r) (hs := geometricFiberFinite s)
    (ht := geometricFiberFinite t) (hr := geometricFiberFinite r) (hμfin := μfin) (hμet := μet)

/-- The canonical comparison commutes with every transporter, hence also with both Hecke legs. -/
theorem weilAdelicCompactOpenLevelGeometricTransport_arrow {K L : LevelIndex} (f : K ⟶ L)
    (q : (towerAt s).obj K) :
    (transport s t).hom.app L ((towerAt s).map f q) =
      (towerAt t).map f ((transport s t).hom.app K q) :=
  (transport s t).hom.naturality_apply f q

end CanonicalTransport
end Full

section Away
variable {h : Global.RationalProfiniteIntegerAdeleComparison} (m : ℕ)
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
  (hunit : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))

local notation "LevelIndex" => PrimeToScalarExtensionLevel D V ψ m
local notation "G" => ScalarExtensionSimilitudePoints D V (Global.PrimeToFiniteAdeles m) ψ
local notation "μfin" => TateTwist.Geometry.InvertibleOrders.selectedFinite S (fun n => Nat.Coprime n m) hunit
local notation "μet" => TateTwist.Geometry.InvertibleOrders.selectedEtale S (fun n => Nat.Coprime n m) hunit

/-- The actual away Weil-compatible fixed-orbit tower, with torsion and twist geometry proved. -/
def weilPrimeToAdelicCompactOpenLevelTower
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    LevelIndex ⥤ Type (max u w) :=
  Tate.weilPrimeToAdelicCompactOpenLevelTower preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap hAway i V ψ
    s (geometricFiberFinite s) torsionFiniteEtale hunit (hμfin := μfin) (hμet := μet)

local notation "towerAt" => weilPrimeToAdelicCompactOpenLevelTower preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap i V ψ (m := m) hAway hunit
local notation "genericLevel" => Tate.WeilPrimeToAdelicCompactOpenLevel preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap hAway i V ψ

/-- The existing actual monodromy-fixed orbit set at a compact open level. -/
abbrev WeilPrimeToAdelicCompactOpenLevel
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) (K : LevelIndex) :=
  (towerAt s).obj K

/-- The specialized tower has exactly the published actual fixed-orbit objects. -/
@[simp] theorem weilPrimeToAdelicCompactOpenLevelTower_obj
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) (K : LevelIndex) :
    (towerAt s).obj K = genericLevel s (geometricFiberFinite s) torsionFiniteEtale hunit
      (hμfin := μfin) (hμet := μet) K := rfl

/-- Transporter arrows act by the actual fixed-orbit right translation. -/
@[simp] theorem weilPrimeToAdelicCompactOpenLevelTower_map
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {K L : LevelIndex} (f : K ⟶ L) (q : (towerAt s).obj K) :
    (towerAt s).map f q =
      Tate.weilPrimeToAdelicLevelTranslate preservation composition unitCoherence associativity comparison
        symmetry stability compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA
        polarizationMap hAway i V ψ torsionFiniteEtale hunit
        (s := s) (hs := geometricFiberFinite s) (hμfin := μfin) (hμet := μet)
        f.element f.respects q := rfl

/-- Inclusion arrows are the actual forgetting maps on invariant frame orbits. -/
@[simp] theorem weilPrimeToAdelicCompactOpenLevelTower_inclusion
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {K L : LevelIndex} (hK : K.toSubgroup ≤ L.toSubgroup) (q : (towerAt s).obj K) :
    (towerAt s).map (CompactOpenLevel.inclusion hK) q =
      Tate.weilPrimeToAdelicLevelForget preservation composition unitCoherence associativity comparison
        symmetry stability compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA
        polarizationMap hAway i V ψ torsionFiniteEtale hunit
        (s := s) (hs := geometricFiberFinite s) (hμfin := μfin) (hμet := μet) hK q := rfl

section Hecke
variable [Module.Finite ℚ V]

/-- The first away Hecke leg forgets the actual intermediate compact open subgroup. -/
def weilPrimeToAdelicCompactOpenHeckeLeft
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K L : LevelIndex) (g : G) :
    (towerAt s).obj (CompactOpenLevel.heckeLevel K L g) → (towerAt s).obj K :=
  (towerAt s).map (CompactOpenLevel.heckeLeft K L g)

/-- The second away Hecke leg translates frames by the actual similitude element. -/
def weilPrimeToAdelicCompactOpenHeckeRight
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K L : LevelIndex) (g : G) :
    (towerAt s).obj (CompactOpenLevel.heckeLevel K L g) → (towerAt s).obj L :=
  (towerAt s).map (CompactOpenLevel.heckeRight K L g)

end Hecke

section CanonicalTransport
variable [ConnectedSpace S] [IsLocallyNoetherian S]
  {Ω Ω' Ω'' : Type u} [Field Ω] [IsAlgClosed Ω]
  [Field Ω'] [IsAlgClosed Ω'] [Field Ω''] [IsAlgClosed Ω'']
  (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ω') ⟶ S) (r : Spec (.of Ω'') ⟶ S)

/-- Canonical comparison of actual away level towers, with geometric finiteness proved. -/
def weilPrimeToAdelicCompactOpenLevelGeometricTransport : towerAt s ≅ towerAt t :=
  Tate.weilPrimeToAdelicCompactOpenLevelGeometricTransport preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap hAway i V ψ torsionFiniteEtale hunit
    s t (geometricFiberFinite s) (geometricFiberFinite t) (hμfin := μfin) (hμet := μet)

local notation "transport" => weilPrimeToAdelicCompactOpenLevelGeometricTransport preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap i V ψ (m := m) hAway hunit

/-- Every actual etale path gives the same canonical tower comparison. -/
theorem weilPrimeToAdelicCompactOpenLevelGeometricTransport_eq_path
    (p : fiberFunctor s (geometricFiberFinite s) ≅ fiberFunctor t (geometricFiberFinite t)) :
    transport s t =
      Tate.weilPrimeToAdelicCompactOpenLevelTransport preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap hAway i V ψ torsionFiniteEtale hunit
        (hμfin := μfin) (hμet := μet) p :=
  Tate.weilPrimeToAdelicCompactOpenLevelGeometricTransport_eq_path preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap hAway i V ψ torsionFiniteEtale hunit
    (hμfin := μfin) (hμet := μet) p

/-- The canonical comparison at a single geometric point is the identity. -/
@[simp] theorem weilPrimeToAdelicCompactOpenLevelGeometricTransport_refl : transport s s = Iso.refl (towerAt s) :=
  Tate.weilPrimeToAdelicCompactOpenLevelGeometricTransport_refl preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap hAway i V ψ torsionFiniteEtale hunit
    (s := s) (hs := geometricFiberFinite s) (hμfin := μfin) (hμet := μet)

/-- Canonical geometric-point comparisons compose transitively. -/
theorem weilPrimeToAdelicCompactOpenLevelGeometricTransport_trans :
    transport s r = transport s t ≪≫ transport t r :=
  Tate.weilPrimeToAdelicCompactOpenLevelGeometricTransport_trans preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap hAway i V ψ torsionFiniteEtale hunit
    (s := s) (t := t) (r := r) (hs := geometricFiberFinite s)
    (ht := geometricFiberFinite t) (hr := geometricFiberFinite r) (hμfin := μfin) (hμet := μet)

/-- The canonical comparison commutes with every transporter, hence also with both Hecke legs. -/
theorem weilPrimeToAdelicCompactOpenLevelGeometricTransport_arrow {K L : LevelIndex} (f : K ⟶ L)
    (q : (towerAt s).obj K) :
    (transport s t).hom.app L ((towerAt s).map f q) =
      (towerAt t).map f ((transport s t).hom.app K q) :=
  (transport s t).hom.naturality_apply f q

end CanonicalTransport
end Away

end Langlands.AbelianScheme.Tate.Geometric
