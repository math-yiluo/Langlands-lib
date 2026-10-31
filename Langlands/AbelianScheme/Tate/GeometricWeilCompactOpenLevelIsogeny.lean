import Langlands.AbelianScheme.Tate.GeometricWeilCompactOpenLevels
import Langlands.AbelianScheme.Tate.WeilCompactOpenLevelIsogeny

/-! # Rational isogenies of actual geometric Weil-compatible level towers -/

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
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A B C : AbelianScheme S}
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (lamA : A ⟶ dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
    evaluationA stability composition unitCoherence associativity comparison symmetry)
  (hB : HasDualScheme B) (geometryB : DualSchemeGeometry B hB)
  (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
    structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (lamB : B ⟶ dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
    evaluationB stability composition unitCoherence associativity comparison symmetry)
  (hC : HasDualScheme C) (geometryC : DualSchemeGeometry C hC)
  (MC : LineBundle ((relativeSpace C.X.hom).obj (dualScheme C hC)))
  (evaluationC : tensorObj (poincareFamily C hC).obj.carrier MC.obj ≅
    structureSheaf ((relativeSpace C.X.hom).obj (dualScheme C hC)))
  (lamC : C ⟶ dualAbelianSchemeFromEvaluation C hC geometryC preservation MC
    evaluationC stability composition unitCoherence associativity comparison symmetry)
  (additivityAA : DualSchemeMapAdditivity preservation stability A A hA hA)
  (additivityAB : DualSchemeMapAdditivity preservation stability A B hA hB)
  (additivityBC : DualSchemeMapAdditivity preservation stability B C hB hC)
  (additivityAC : DualSchemeMapAdditivity preservation stability A C hA hC)
  (additivityBA : DualSchemeMapAdditivity preservation stability B A hB hA)
  (additivityBB : DualSchemeMapAdditivity preservation stability B B hB hB)
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  {D : Type v} [Ring D] [Algebra ℚ D]
  (iA : D →ₐ[ℚ] Rationalization.End A) (iB : D →ₐ[ℚ] Rationalization.End B)
  (iC : D →ₐ[ℚ] Rationalization.End C)
  (V : Type w) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  (ψ : LinearMap.BilinForm ℚ V)

section Full
variable (h : Global.RationalProfiniteIntegerAdeleComparison)
  (hunit : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)

local notation "μfin" => TateTwist.Geometry.InvertibleOrders.selectedFinite S (fun _ => True) hunit
local notation "μet" => TateTwist.Geometry.InvertibleOrders.selectedEtale S (fun _ => True) hunit
local notation "LevelIndex" => FiniteAdelicScalarExtensionLevel D V ψ
local notation "G" => ScalarExtensionSimilitudePoints D V (Global.FiniteAdeles ℚ) ψ
local notation "multipleAB" => IsRationalDualPullbackMultiple preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB
local notation "multipleBC" => IsRationalDualPullbackMultiple preservation composition unitCoherence associativity comparison symmetry stability hB hC geometryB geometryC MB evaluationB MC evaluationC additivityBC
local notation "TowerA" => weilAdelicCompactOpenLevelTower preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA lamA iA V ψ h hunit s
local notation "TowerB" => weilAdelicCompactOpenLevelTower preservation composition unitCoherence associativity comparison symmetry stability compatibility hB geometryB MB evaluationB lamB iB V ψ h hunit s
local notation "TowerC" => weilAdelicCompactOpenLevelTower preservation composition unitCoherence associativity comparison symmetry stability compatibility hC geometryC MC evaluationC lamC iC V ψ h hunit s
local notation "genericAB" => Tate.weilAdelicCompactOpenLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB compatibility h iA iB V ψ s (geometricFiberFinite s) torsionFiniteEtale hunit (hμfin := μfin) (hμet := μet)
local notation "fixedAB" => Tate.weilAdelicLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB lamA lamB compatibility rationalWeilFunctoriality rationalWeilGeometricTransport h iA iB V ψ s (geometricFiberFinite s) torsionFiniteEtale hunit (hμfin := μfin) (hμet := μet)

/-- Actual geometric full tower isogeny, with finite-fibre and finite-etale witnesses proved. -/
def weilAdelicCompactOpenLevelIsogeny (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) : TowerA ≅ TowerB :=
  genericAB q e he hqe

local notation "isogenyAA" => weilAdelicCompactOpenLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hA geometryA MA evaluationA lamA additivityAA compatibility iA iA V ψ h hunit s
local notation "isogenyAB" => weilAdelicCompactOpenLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB compatibility iA iB V ψ h hunit s
local notation "isogenyBC" => weilAdelicCompactOpenLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hB geometryB MB evaluationB lamB hC geometryC MC evaluationC lamC additivityBC compatibility iB iC V ψ h hunit s

/-- The forward component is the actual fixed-level rational-isogeny equivalence. -/
@[simp] theorem weilAdelicCompactOpenLevelIsogeny_hom_app (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (K : LevelIndex) (x : (TowerA).obj K) :
    (isogenyAB q e he hqe).hom.app K x = fixedAB K.toSubgroup q e he hqe x := rfl

/-- The inverse component is the inverse actual fixed-level equivalence. -/
@[simp] theorem weilAdelicCompactOpenLevelIsogeny_inv_app (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (K : LevelIndex) (x : (TowerB).obj K) :
    (isogenyAB q e he hqe).inv.app K x =
      (fixedAB K.toSubgroup q e he hqe).symm x := rfl

/-- Isogeny transport commutes with every transporter arrow, including level forgetting. -/
theorem weilAdelicCompactOpenLevelIsogeny_arrow (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    {K L : LevelIndex} (f : K ⟶ L) (x : (TowerA).obj K) :
    (isogenyAB q e he hqe).hom.app L ((TowerA).map f x) =
      (TowerB).map f ((isogenyAB q e he hqe).hom.app K x) :=
  (isogenyAB q e he hqe).hom.naturality_apply f x

section Hecke
variable [Module.Finite ℚ V]

/-- Isogeny transport commutes with the first actual compact-open Hecke leg. -/
theorem weilAdelicCompactOpenLevelIsogeny_heckeLeft (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (K L : LevelIndex) (g : G)
    (x : (TowerA).obj (CompactOpenLevel.heckeLevel K L g)) :
    (isogenyAB q e he hqe).hom.app K
        ((TowerA).map (CompactOpenLevel.heckeLeft K L g) x) =
      (TowerB).map (CompactOpenLevel.heckeLeft K L g)
        ((isogenyAB q e he hqe).hom.app (CompactOpenLevel.heckeLevel K L g) x) :=
  (isogenyAB q e he hqe).hom.naturality_apply _ x

/-- Isogeny transport commutes with the second actual compact-open Hecke leg. -/
theorem weilAdelicCompactOpenLevelIsogeny_heckeRight (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (K L : LevelIndex) (g : G)
    (x : (TowerA).obj (CompactOpenLevel.heckeLevel K L g)) :
    (isogenyAB q e he hqe).hom.app L
        ((TowerA).map (CompactOpenLevel.heckeRight K L g) x) =
      (TowerB).map (CompactOpenLevel.heckeRight K L g)
        ((isogenyAB q e he hqe).hom.app (CompactOpenLevel.heckeLevel K L g) x) :=
  (isogenyAB q e he hqe).hom.naturality_apply _ x

end Hecke

/-- Identity isogeny transport uses the derived unit multiplier and is the identity. -/
@[simp] theorem weilAdelicCompactOpenLevelIsogeny_refl :
    isogenyAA 1 (Iso.refl _) (rationalIntertwines_identity iA)
        (IsRationalDualPullbackMultiple.id preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
          additivityAA (Rationalization.ofHom lamA)) = Iso.refl (TowerA) :=
  Tate.weilAdelicCompactOpenLevelIsogeny_refl preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA additivityAA compatibility h iA V ψ s (geometricFiberFinite s) torsionFiniteEtale hunit (hμfin := μfin) (hμet := μet)

/-- Direct composite transport uses the geometrically derived product multiplier. -/
def weilAdelicCompactOpenLevelIsogenyComp (q r : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (f : Rationalization.of B ≅ Rationalization.of C)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : ∀ d, Rationalization.comp B B C (iB d) f.hom =
      Rationalization.comp B C C f.hom (iC d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (hrf : multipleBC (r : ℚ) f.hom
      (Rationalization.ofHom lamB) (Rationalization.ofHom lamC)) : TowerA ≅ TowerC :=
  Tate.weilAdelicCompactOpenLevelIsogenyComp preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hC geometryC MC evaluationC lamC additivityAB additivityBC additivityAC compatibility h iA iB iC V ψ s (geometricFiberFinite s) torsionFiniteEtale hunit (hμfin := μfin) (hμet := μet) q r e f he hf hqe hrf

local notation "isogenyComp" => weilAdelicCompactOpenLevelIsogenyComp preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hC geometryC MC evaluationC lamC additivityAB additivityBC additivityAC compatibility iA iB iC V ψ h hunit s

/-- Composite rational-isogeny transport equals successive tower comparisons. -/
theorem weilAdelicCompactOpenLevelIsogenyComp_eq_trans (q r : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (f : Rationalization.of B ≅ Rationalization.of C)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : ∀ d, Rationalization.comp B B C (iB d) f.hom =
      Rationalization.comp B C C f.hom (iC d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (hrf : multipleBC (r : ℚ) f.hom
      (Rationalization.ofHom lamB) (Rationalization.ofHom lamC)) :
    isogenyComp q r e f he hf hqe hrf =
      isogenyAB q e he hqe ≪≫ isogenyBC r f hf hrf :=
  Tate.weilAdelicCompactOpenLevelIsogenyComp_eq_trans preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hC geometryC MC evaluationC lamC additivityAB additivityBC additivityAC compatibility h iA iB iC V ψ s (geometricFiberFinite s) torsionFiniteEtale hunit (hμfin := μfin) (hμet := μet) q r e f he hf hqe hrf

/-- Direct inverse transport uses the geometrically derived reciprocal multiplier. -/
def weilAdelicCompactOpenLevelIsogenyInverse (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) : TowerB ≅ TowerA :=
  Tate.weilAdelicCompactOpenLevelIsogenyInverse preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB additivityBA additivityBB compatibility h iA iB V ψ s (geometricFiberFinite s) torsionFiniteEtale hunit (hμfin := μfin) (hμet := μet) q e he hqe

local notation "isogenyInverse" => weilAdelicCompactOpenLevelIsogenyInverse preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB additivityBA additivityBB compatibility iA iB V ψ h hunit s

/-- Reversing an actual rational isogeny inverts the natural tower comparison. -/
theorem weilAdelicCompactOpenLevelIsogeny_symm (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) :
    (isogenyAB q e he hqe).symm = isogenyInverse q e he hqe :=
  Tate.weilAdelicCompactOpenLevelIsogeny_symm preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB additivityBA additivityBB compatibility h iA iB V ψ s (geometricFiberFinite s) torsionFiniteEtale hunit (hμfin := μfin) (hμet := μet) q e he hqe

end Full

section Away
variable {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
  (hunit : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)

local notation "μfin" => TateTwist.Geometry.InvertibleOrders.selectedFinite S (fun n => Nat.Coprime n m) hunit
local notation "μet" => TateTwist.Geometry.InvertibleOrders.selectedEtale S (fun n => Nat.Coprime n m) hunit
local notation "LevelIndex" => PrimeToScalarExtensionLevel D V ψ m
local notation "G" => ScalarExtensionSimilitudePoints D V (Global.PrimeToFiniteAdeles m) ψ
local notation "multipleAB" => IsRationalDualPullbackMultiple preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB
local notation "multipleBC" => IsRationalDualPullbackMultiple preservation composition unitCoherence associativity comparison symmetry stability hB hC geometryB geometryC MB evaluationB MC evaluationC additivityBC
local notation "TowerA" => weilPrimeToAdelicCompactOpenLevelTower preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA lamA iA V ψ (m := m) hAway hunit s
local notation "TowerB" => weilPrimeToAdelicCompactOpenLevelTower preservation composition unitCoherence associativity comparison symmetry stability compatibility hB geometryB MB evaluationB lamB iB V ψ (m := m) hAway hunit s
local notation "TowerC" => weilPrimeToAdelicCompactOpenLevelTower preservation composition unitCoherence associativity comparison symmetry stability compatibility hC geometryC MC evaluationC lamC iC V ψ (m := m) hAway hunit s
local notation "genericAB" => Tate.weilPrimeToAdelicCompactOpenLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB compatibility h iA iB V ψ s (geometricFiberFinite s) torsionFiniteEtale hAway hunit (hμfin := μfin) (hμet := μet)
local notation "fixedAB" => Tate.weilPrimeToAdelicLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB lamA lamB compatibility rationalWeilFunctoriality rationalWeilGeometricTransport h iA iB V ψ s (geometricFiberFinite s) torsionFiniteEtale hAway hunit (hμfin := μfin) (hμet := μet)

/-- Actual geometric away tower isogeny, with finite-fibre and finite-etale witnesses proved. -/
def weilPrimeToAdelicCompactOpenLevelIsogeny (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) : TowerA ≅ TowerB :=
  genericAB q e he hqe

local notation "isogenyAA" => weilPrimeToAdelicCompactOpenLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hA geometryA MA evaluationA lamA additivityAA compatibility iA iA V ψ (m := m) hAway hunit s
local notation "isogenyAB" => weilPrimeToAdelicCompactOpenLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB compatibility iA iB V ψ (m := m) hAway hunit s
local notation "isogenyBC" => weilPrimeToAdelicCompactOpenLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hB geometryB MB evaluationB lamB hC geometryC MC evaluationC lamC additivityBC compatibility iB iC V ψ (m := m) hAway hunit s

/-- The forward component is the actual fixed-level rational-isogeny equivalence. -/
@[simp] theorem weilPrimeToAdelicCompactOpenLevelIsogeny_hom_app (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (K : LevelIndex) (x : (TowerA).obj K) :
    (isogenyAB q e he hqe).hom.app K x = fixedAB K.toSubgroup q e he hqe x := rfl

/-- The inverse component is the inverse actual fixed-level equivalence. -/
@[simp] theorem weilPrimeToAdelicCompactOpenLevelIsogeny_inv_app (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (K : LevelIndex) (x : (TowerB).obj K) :
    (isogenyAB q e he hqe).inv.app K x =
      (fixedAB K.toSubgroup q e he hqe).symm x := rfl

/-- Isogeny transport commutes with every transporter arrow, including level forgetting. -/
theorem weilPrimeToAdelicCompactOpenLevelIsogeny_arrow (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    {K L : LevelIndex} (f : K ⟶ L) (x : (TowerA).obj K) :
    (isogenyAB q e he hqe).hom.app L ((TowerA).map f x) =
      (TowerB).map f ((isogenyAB q e he hqe).hom.app K x) :=
  (isogenyAB q e he hqe).hom.naturality_apply f x

section Hecke
variable [Module.Finite ℚ V]

/-- Isogeny transport commutes with the first actual compact-open Hecke leg. -/
theorem weilPrimeToAdelicCompactOpenLevelIsogeny_heckeLeft (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (K L : LevelIndex) (g : G)
    (x : (TowerA).obj (CompactOpenLevel.heckeLevel K L g)) :
    (isogenyAB q e he hqe).hom.app K
        ((TowerA).map (CompactOpenLevel.heckeLeft K L g) x) =
      (TowerB).map (CompactOpenLevel.heckeLeft K L g)
        ((isogenyAB q e he hqe).hom.app (CompactOpenLevel.heckeLevel K L g) x) :=
  (isogenyAB q e he hqe).hom.naturality_apply _ x

/-- Isogeny transport commutes with the second actual compact-open Hecke leg. -/
theorem weilPrimeToAdelicCompactOpenLevelIsogeny_heckeRight (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (K L : LevelIndex) (g : G)
    (x : (TowerA).obj (CompactOpenLevel.heckeLevel K L g)) :
    (isogenyAB q e he hqe).hom.app L
        ((TowerA).map (CompactOpenLevel.heckeRight K L g) x) =
      (TowerB).map (CompactOpenLevel.heckeRight K L g)
        ((isogenyAB q e he hqe).hom.app (CompactOpenLevel.heckeLevel K L g) x) :=
  (isogenyAB q e he hqe).hom.naturality_apply _ x

end Hecke

/-- Identity isogeny transport uses the derived unit multiplier and is the identity. -/
@[simp] theorem weilPrimeToAdelicCompactOpenLevelIsogeny_refl :
    isogenyAA 1 (Iso.refl _) (rationalIntertwines_identity iA)
        (IsRationalDualPullbackMultiple.id preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
          additivityAA (Rationalization.ofHom lamA)) = Iso.refl (TowerA) :=
  Tate.weilPrimeToAdelicCompactOpenLevelIsogeny_refl preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA additivityAA compatibility h iA V ψ s (geometricFiberFinite s) torsionFiniteEtale hAway hunit (hμfin := μfin) (hμet := μet)

/-- Direct composite transport uses the geometrically derived product multiplier. -/
def weilPrimeToAdelicCompactOpenLevelIsogenyComp (q r : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (f : Rationalization.of B ≅ Rationalization.of C)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : ∀ d, Rationalization.comp B B C (iB d) f.hom =
      Rationalization.comp B C C f.hom (iC d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (hrf : multipleBC (r : ℚ) f.hom
      (Rationalization.ofHom lamB) (Rationalization.ofHom lamC)) : TowerA ≅ TowerC :=
  Tate.weilPrimeToAdelicCompactOpenLevelIsogenyComp preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hC geometryC MC evaluationC lamC additivityAB additivityBC additivityAC compatibility h iA iB iC V ψ s (geometricFiberFinite s) torsionFiniteEtale hAway hunit (hμfin := μfin) (hμet := μet) q r e f he hf hqe hrf

local notation "isogenyComp" => weilPrimeToAdelicCompactOpenLevelIsogenyComp preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hC geometryC MC evaluationC lamC additivityAB additivityBC additivityAC compatibility iA iB iC V ψ (m := m) hAway hunit s

/-- Composite rational-isogeny transport equals successive tower comparisons. -/
theorem weilPrimeToAdelicCompactOpenLevelIsogenyComp_eq_trans (q r : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (f : Rationalization.of B ≅ Rationalization.of C)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : ∀ d, Rationalization.comp B B C (iB d) f.hom =
      Rationalization.comp B C C f.hom (iC d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (hrf : multipleBC (r : ℚ) f.hom
      (Rationalization.ofHom lamB) (Rationalization.ofHom lamC)) :
    isogenyComp q r e f he hf hqe hrf =
      isogenyAB q e he hqe ≪≫ isogenyBC r f hf hrf :=
  Tate.weilPrimeToAdelicCompactOpenLevelIsogenyComp_eq_trans preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hC geometryC MC evaluationC lamC additivityAB additivityBC additivityAC compatibility h iA iB iC V ψ s (geometricFiberFinite s) torsionFiniteEtale hAway hunit (hμfin := μfin) (hμet := μet) q r e f he hf hqe hrf

/-- Direct inverse transport uses the geometrically derived reciprocal multiplier. -/
def weilPrimeToAdelicCompactOpenLevelIsogenyInverse (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) : TowerB ≅ TowerA :=
  Tate.weilPrimeToAdelicCompactOpenLevelIsogenyInverse preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB additivityBA additivityBB compatibility h iA iB V ψ s (geometricFiberFinite s) torsionFiniteEtale hAway hunit (hμfin := μfin) (hμet := μet) q e he hqe

local notation "isogenyInverse" => weilPrimeToAdelicCompactOpenLevelIsogenyInverse preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB additivityBA additivityBB compatibility iA iB V ψ (m := m) hAway hunit s

/-- Reversing an actual rational isogeny inverts the natural tower comparison. -/
theorem weilPrimeToAdelicCompactOpenLevelIsogeny_symm (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) :
    (isogenyAB q e he hqe).symm = isogenyInverse q e he hqe :=
  Tate.weilPrimeToAdelicCompactOpenLevelIsogeny_symm preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB additivityBA additivityBB compatibility h iA iB V ψ s (geometricFiberFinite s) torsionFiniteEtale hAway hunit (hμfin := μfin) (hμet := μet) q e he hqe

end Away

end Langlands.AbelianScheme.Tate.Geometric
