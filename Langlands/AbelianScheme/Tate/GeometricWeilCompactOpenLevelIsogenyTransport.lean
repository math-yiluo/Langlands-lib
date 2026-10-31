import Langlands.AbelianScheme.Tate.GeometricWeilCompactOpenLevelIsogeny

/-! # Rational isogenies between geometric-point Weil level towers -/

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
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A B : AbelianScheme S}
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
  (additivityAB : DualSchemeMapAdditivity preservation stability A B hA hB)
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  {D : Type v} [Ring D] [Algebra ℚ D]
  (iA : D →ₐ[ℚ] Rationalization.End A) (iB : D →ₐ[ℚ] Rationalization.End B)
  (V : Type w) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  (ψ : LinearMap.BilinForm ℚ V)

section Full
variable (h : Global.RationalProfiniteIntegerAdeleComparison)
  (hunit : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
  {Ω Ω' : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
  (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ω') ⟶ S)

local notation "μfin" => TateTwist.Geometry.InvertibleOrders.selectedFinite S (fun _ => True) hunit
local notation "μet" => TateTwist.Geometry.InvertibleOrders.selectedEtale S (fun _ => True) hunit
local notation "LevelIndex" => FiniteAdelicScalarExtensionLevel D V ψ
local notation "G" => ScalarExtensionSimilitudePoints D V (Global.FiniteAdeles ℚ) ψ
local notation "multipleAB" => IsRationalDualPullbackMultiple preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB
local notation "TowerA" => weilAdelicCompactOpenLevelTower preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA lamA iA V ψ h hunit
local notation "TowerB" => weilAdelicCompactOpenLevelTower preservation composition unitCoherence associativity comparison symmetry stability compatibility hB geometryB MB evaluationB lamB iB V ψ h hunit
local notation "isogenyAB" => weilAdelicCompactOpenLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB compatibility iA iB V ψ h hunit
local notation "pathA" => Tate.weilAdelicCompactOpenLevelTransport preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA lamA h iA V ψ torsionFiniteEtale hunit (hμfin := μfin) (hμet := μet)
local notation "pathB" => Tate.weilAdelicCompactOpenLevelTransport preservation composition unitCoherence associativity comparison symmetry stability compatibility hB geometryB MB evaluationB lamB h iB V ψ torsionFiniteEtale hunit (hμfin := μfin) (hμet := μet)

/-- Isogeny followed by actual fibre-functor path transport compares the two geometric towers. -/
def weilAdelicCompactOpenLevelIsogenyPath
    (p : fiberFunctor s (geometricFiberFinite s) ≅ fiberFunctor t (geometricFiberFinite t))
    (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) : TowerA s ≅ TowerB t :=
  isogenyAB s q e he hqe ≪≫ pathB p

local notation "pathIsogeny" => weilAdelicCompactOpenLevelIsogenyPath preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB compatibility iA iB V ψ h hunit s t

/-- The two orders of isogeny and actual path transport agree as natural isomorphisms. -/
theorem weilAdelicCompactOpenLevelIsogenyPath_eq_transport_isogeny
    (p : fiberFunctor s (geometricFiberFinite s) ≅ fiberFunctor t (geometricFiberFinite t))
    (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) :
    pathIsogeny p q e he hqe = pathA p ≪≫ isogenyAB t q e he hqe := by
  apply Iso.ext
  ext K x
  exact Tate.weilAdelicLevelIsogeny_transport preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB lamA lamB compatibility rationalWeilFunctoriality rationalWeilGeometricTransport h iA iB V ψ s (geometricFiberFinite s) torsionFiniteEtale hunit (hμfin := μfin) (hμet := μet) K.toSubgroup q e he hqe p x

/-- The mixed comparison on fixed-orbit towers is independent of the supplied path. -/
theorem weilAdelicCompactOpenLevelIsogenyPath_independent
    (p p' : fiberFunctor s (geometricFiberFinite s) ≅ fiberFunctor t (geometricFiberFinite t))
    (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) :
    pathIsogeny p q e he hqe = pathIsogeny p' q e he hqe := by
  unfold weilAdelicCompactOpenLevelIsogenyPath
  rw [Tate.weilAdelicCompactOpenLevelTransport_path_independent preservation composition unitCoherence associativity comparison symmetry stability compatibility hB geometryB MB evaluationB lamB h iB V ψ torsionFiniteEtale hunit (hμfin := μfin) (hμet := μet) p p']

section Canonical
variable [ConnectedSpace S] [IsLocallyNoetherian S]

local notation "transportA" => weilAdelicCompactOpenLevelGeometricTransport preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA lamA iA V ψ h hunit
local notation "transportB" => weilAdelicCompactOpenLevelGeometricTransport preservation composition unitCoherence associativity comparison symmetry stability compatibility hB geometryB MB evaluationB lamB iB V ψ h hunit

/-- Canonical rational-isogeny comparison between actual towers at different geometric points. -/
def weilAdelicCompactOpenLevelGeometricIsogeny
    (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) : TowerA s ≅ TowerB t :=
  isogenyAB s q e he hqe ≪≫ transportB s t

local notation "geometricIsogeny" => weilAdelicCompactOpenLevelGeometricIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB compatibility iA iB V ψ h hunit s t

/-- Every actual path computes the canonical mixed comparison. -/
theorem weilAdelicCompactOpenLevelGeometricIsogeny_eq_path
    (p : fiberFunctor s (geometricFiberFinite s) ≅ fiberFunctor t (geometricFiberFinite t))
    (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) :
    geometricIsogeny q e he hqe = pathIsogeny p q e he hqe := by
  unfold weilAdelicCompactOpenLevelGeometricIsogeny weilAdelicCompactOpenLevelIsogenyPath
  rw [weilAdelicCompactOpenLevelGeometricTransport_eq_path preservation composition unitCoherence associativity comparison symmetry stability compatibility hB geometryB MB evaluationB lamB iB V ψ h hunit s t p]

/-- Canonical point transport followed by the target-point isogeny is the same comparison. -/
theorem weilAdelicCompactOpenLevelGeometricIsogeny_eq_transport_isogeny
    (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) :
    geometricIsogeny q e he hqe = transportA s t ≪≫ isogenyAB t q e he hqe := by
  let p := Classical.choice (geometricPathExists s t (geometricFiberFinite s) (geometricFiberFinite t))
  rw [weilAdelicCompactOpenLevelGeometricIsogeny_eq_path preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB compatibility iA iB V ψ h hunit s t p q e he hqe,
    weilAdelicCompactOpenLevelGeometricTransport_eq_path preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA lamA iA V ψ h hunit s t p]
  exact weilAdelicCompactOpenLevelIsogenyPath_eq_transport_isogeny preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB compatibility iA iB V ψ h hunit s t p q e he hqe

/-- Its forward component applies the actual isogeny and then canonical point transport. -/
@[simp] theorem weilAdelicCompactOpenLevelGeometricIsogeny_hom_app
    (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (K : LevelIndex) (x : (TowerA s).obj K) :
    (geometricIsogeny q e he hqe).hom.app K x =
      (transportB s t).hom.app K ((isogenyAB s q e he hqe).hom.app K x) := rfl

/-- Its inverse component applies inverse point transport and then the inverse actual isogeny. -/
@[simp] theorem weilAdelicCompactOpenLevelGeometricIsogeny_inv_app
    (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (K : LevelIndex) (x : (TowerB t).obj K) :
    (geometricIsogeny q e he hqe).inv.app K x =
      (isogenyAB s q e he hqe).inv.app K ((transportB s t).inv.app K x) := rfl

/-- At equal geometric endpoints the mixed comparison recovers the fixed-point isogeny. -/
@[simp] theorem weilAdelicCompactOpenLevelGeometricIsogeny_samePoint
    (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) :
    weilAdelicCompactOpenLevelGeometricIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB compatibility iA iB V ψ h hunit s s q e he hqe =
      isogenyAB s q e he hqe := by
  unfold weilAdelicCompactOpenLevelGeometricIsogeny
  rw [weilAdelicCompactOpenLevelGeometricTransport_refl preservation composition unitCoherence associativity comparison symmetry stability compatibility hB geometryB MB evaluationB lamB iB V ψ h hunit s]
  exact Iso.trans_refl _

/-- The canonical mixed comparison commutes with every compact-open transporter map. -/
theorem weilAdelicCompactOpenLevelGeometricIsogeny_arrow
    (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    {K L : LevelIndex} (f : K ⟶ L) (x : (TowerA s).obj K) :
    (geometricIsogeny q e he hqe).hom.app L ((TowerA s).map f x) =
      (TowerB t).map f ((geometricIsogeny q e he hqe).hom.app K x) :=
  (geometricIsogeny q e he hqe).hom.naturality_apply f x

section Hecke
variable [Module.Finite ℚ V]

/-- The mixed comparison commutes with the first actual compact-open Hecke leg. -/
theorem weilAdelicCompactOpenLevelGeometricIsogeny_heckeLeft
    (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (K L : LevelIndex) (g : G)
    (x : (TowerA s).obj (CompactOpenLevel.heckeLevel K L g)) :
    (geometricIsogeny q e he hqe).hom.app K
        ((TowerA s).map (CompactOpenLevel.heckeLeft K L g) x) =
      (TowerB t).map (CompactOpenLevel.heckeLeft K L g)
        ((geometricIsogeny q e he hqe).hom.app (CompactOpenLevel.heckeLevel K L g) x) :=
  (geometricIsogeny q e he hqe).hom.naturality_apply _ x

/-- The mixed comparison commutes with the second actual compact-open Hecke leg. -/
theorem weilAdelicCompactOpenLevelGeometricIsogeny_heckeRight
    (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (K L : LevelIndex) (g : G)
    (x : (TowerA s).obj (CompactOpenLevel.heckeLevel K L g)) :
    (geometricIsogeny q e he hqe).hom.app L
        ((TowerA s).map (CompactOpenLevel.heckeRight K L g) x) =
      (TowerB t).map (CompactOpenLevel.heckeRight K L g)
        ((geometricIsogeny q e he hqe).hom.app (CompactOpenLevel.heckeLevel K L g) x) :=
  (geometricIsogeny q e he hqe).hom.naturality_apply _ x

end Hecke

variable {Ω'' : Type u} [Field Ω''] [IsAlgClosed Ω''] (r : Spec (.of Ω'') ⟶ S)

/-- A subsequent canonical change of target point composes with the mixed comparison. -/
theorem weilAdelicCompactOpenLevelGeometricIsogeny_target_trans
    (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) :
    weilAdelicCompactOpenLevelGeometricIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB compatibility iA iB V ψ h hunit s r q e he hqe =
      geometricIsogeny q e he hqe ≪≫ transportB t r := by
  unfold weilAdelicCompactOpenLevelGeometricIsogeny
  rw [weilAdelicCompactOpenLevelGeometricTransport_trans preservation composition unitCoherence associativity comparison symmetry stability compatibility hB geometryB MB evaluationB lamB iB V ψ h hunit s t r]
  exact (Iso.trans_assoc _ _ _).symm

/-- A preceding canonical change of source point gives the same mixed comparison. -/
theorem weilAdelicCompactOpenLevelGeometricIsogeny_source_trans
    (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) :
    weilAdelicCompactOpenLevelGeometricIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB compatibility iA iB V ψ h hunit s r q e he hqe =
      transportA s t ≪≫ weilAdelicCompactOpenLevelGeometricIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB compatibility iA iB V ψ h hunit t r q e he hqe := by
  rw [weilAdelicCompactOpenLevelGeometricIsogeny_target_trans preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB compatibility iA iB V ψ h hunit s t r q e he hqe,
    weilAdelicCompactOpenLevelGeometricIsogeny_eq_transport_isogeny preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB compatibility iA iB V ψ h hunit s t q e he hqe]
  exact Iso.trans_assoc _ _ _

end Canonical
end Full

section Away
variable {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
  (hunit : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
  {Ω Ω' : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
  (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ω') ⟶ S)

local notation "μfin" => TateTwist.Geometry.InvertibleOrders.selectedFinite S (fun n => Nat.Coprime n m) hunit
local notation "μet" => TateTwist.Geometry.InvertibleOrders.selectedEtale S (fun n => Nat.Coprime n m) hunit
local notation "LevelIndex" => PrimeToScalarExtensionLevel D V ψ m
local notation "G" => ScalarExtensionSimilitudePoints D V (Global.PrimeToFiniteAdeles m) ψ
local notation "multipleAB" => IsRationalDualPullbackMultiple preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB
local notation "TowerA" => weilPrimeToAdelicCompactOpenLevelTower preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA lamA iA V ψ (m := m) hAway hunit
local notation "TowerB" => weilPrimeToAdelicCompactOpenLevelTower preservation composition unitCoherence associativity comparison symmetry stability compatibility hB geometryB MB evaluationB lamB iB V ψ (m := m) hAway hunit
local notation "isogenyAB" => weilPrimeToAdelicCompactOpenLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB compatibility iA iB V ψ (m := m) hAway hunit
local notation "pathA" => Tate.weilPrimeToAdelicCompactOpenLevelTransport preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA lamA hAway iA V ψ torsionFiniteEtale hunit (hμfin := μfin) (hμet := μet)
local notation "pathB" => Tate.weilPrimeToAdelicCompactOpenLevelTransport preservation composition unitCoherence associativity comparison symmetry stability compatibility hB geometryB MB evaluationB lamB hAway iB V ψ torsionFiniteEtale hunit (hμfin := μfin) (hμet := μet)

/-- Isogeny followed by actual fibre-functor path transport compares the two geometric towers. -/
def weilPrimeToAdelicCompactOpenLevelIsogenyPath
    (p : fiberFunctor s (geometricFiberFinite s) ≅ fiberFunctor t (geometricFiberFinite t))
    (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) : TowerA s ≅ TowerB t :=
  isogenyAB s q e he hqe ≪≫ pathB p

local notation "pathIsogeny" => weilPrimeToAdelicCompactOpenLevelIsogenyPath preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB compatibility iA iB V ψ (m := m) hAway hunit s t

/-- The two orders of isogeny and actual path transport agree as natural isomorphisms. -/
theorem weilPrimeToAdelicCompactOpenLevelIsogenyPath_eq_transport_isogeny
    (p : fiberFunctor s (geometricFiberFinite s) ≅ fiberFunctor t (geometricFiberFinite t))
    (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) :
    pathIsogeny p q e he hqe = pathA p ≪≫ isogenyAB t q e he hqe := by
  apply Iso.ext
  ext K x
  exact Tate.weilPrimeToAdelicLevelIsogeny_transport preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB lamA lamB compatibility rationalWeilFunctoriality rationalWeilGeometricTransport h iA iB V ψ s (geometricFiberFinite s) torsionFiniteEtale hAway hunit (hμfin := μfin) (hμet := μet) K.toSubgroup q e he hqe p x

/-- The mixed comparison on fixed-orbit towers is independent of the supplied path. -/
theorem weilPrimeToAdelicCompactOpenLevelIsogenyPath_independent
    (p p' : fiberFunctor s (geometricFiberFinite s) ≅ fiberFunctor t (geometricFiberFinite t))
    (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) :
    pathIsogeny p q e he hqe = pathIsogeny p' q e he hqe := by
  unfold weilPrimeToAdelicCompactOpenLevelIsogenyPath
  rw [Tate.weilPrimeToAdelicCompactOpenLevelTransport_path_independent preservation composition unitCoherence associativity comparison symmetry stability compatibility hB geometryB MB evaluationB lamB hAway iB V ψ torsionFiniteEtale hunit (hμfin := μfin) (hμet := μet) p p']

section Canonical
variable [ConnectedSpace S] [IsLocallyNoetherian S]

local notation "transportA" => weilPrimeToAdelicCompactOpenLevelGeometricTransport preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA lamA iA V ψ (m := m) hAway hunit
local notation "transportB" => weilPrimeToAdelicCompactOpenLevelGeometricTransport preservation composition unitCoherence associativity comparison symmetry stability compatibility hB geometryB MB evaluationB lamB iB V ψ (m := m) hAway hunit

/-- Canonical rational-isogeny comparison between actual towers at different geometric points. -/
def weilPrimeToAdelicCompactOpenLevelGeometricIsogeny
    (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) : TowerA s ≅ TowerB t :=
  isogenyAB s q e he hqe ≪≫ transportB s t

local notation "geometricIsogeny" => weilPrimeToAdelicCompactOpenLevelGeometricIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB compatibility iA iB V ψ (m := m) hAway hunit s t

/-- Every actual path computes the canonical mixed comparison. -/
theorem weilPrimeToAdelicCompactOpenLevelGeometricIsogeny_eq_path
    (p : fiberFunctor s (geometricFiberFinite s) ≅ fiberFunctor t (geometricFiberFinite t))
    (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) :
    geometricIsogeny q e he hqe = pathIsogeny p q e he hqe := by
  unfold weilPrimeToAdelicCompactOpenLevelGeometricIsogeny weilPrimeToAdelicCompactOpenLevelIsogenyPath
  rw [weilPrimeToAdelicCompactOpenLevelGeometricTransport_eq_path preservation composition unitCoherence associativity comparison symmetry stability compatibility hB geometryB MB evaluationB lamB iB V ψ (m := m) hAway hunit s t p]

/-- Canonical point transport followed by the target-point isogeny is the same comparison. -/
theorem weilPrimeToAdelicCompactOpenLevelGeometricIsogeny_eq_transport_isogeny
    (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) :
    geometricIsogeny q e he hqe = transportA s t ≪≫ isogenyAB t q e he hqe := by
  let p := Classical.choice (geometricPathExists s t (geometricFiberFinite s) (geometricFiberFinite t))
  rw [weilPrimeToAdelicCompactOpenLevelGeometricIsogeny_eq_path preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB compatibility iA iB V ψ (m := m) hAway hunit s t p q e he hqe,
    weilPrimeToAdelicCompactOpenLevelGeometricTransport_eq_path preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA lamA iA V ψ (m := m) hAway hunit s t p]
  exact weilPrimeToAdelicCompactOpenLevelIsogenyPath_eq_transport_isogeny preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB compatibility iA iB V ψ (m := m) hAway hunit s t p q e he hqe

/-- Its forward component applies the actual isogeny and then canonical point transport. -/
@[simp] theorem weilPrimeToAdelicCompactOpenLevelGeometricIsogeny_hom_app
    (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (K : LevelIndex) (x : (TowerA s).obj K) :
    (geometricIsogeny q e he hqe).hom.app K x =
      (transportB s t).hom.app K ((isogenyAB s q e he hqe).hom.app K x) := rfl

/-- Its inverse component applies inverse point transport and then the inverse actual isogeny. -/
@[simp] theorem weilPrimeToAdelicCompactOpenLevelGeometricIsogeny_inv_app
    (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (K : LevelIndex) (x : (TowerB t).obj K) :
    (geometricIsogeny q e he hqe).inv.app K x =
      (isogenyAB s q e he hqe).inv.app K ((transportB s t).inv.app K x) := rfl

/-- At equal geometric endpoints the mixed comparison recovers the fixed-point isogeny. -/
@[simp] theorem weilPrimeToAdelicCompactOpenLevelGeometricIsogeny_samePoint
    (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) :
    weilPrimeToAdelicCompactOpenLevelGeometricIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB compatibility iA iB V ψ (m := m) hAway hunit s s q e he hqe =
      isogenyAB s q e he hqe := by
  unfold weilPrimeToAdelicCompactOpenLevelGeometricIsogeny
  rw [weilPrimeToAdelicCompactOpenLevelGeometricTransport_refl preservation composition unitCoherence associativity comparison symmetry stability compatibility hB geometryB MB evaluationB lamB iB V ψ (m := m) hAway hunit s]
  exact Iso.trans_refl _

/-- The canonical mixed comparison commutes with every compact-open transporter map. -/
theorem weilPrimeToAdelicCompactOpenLevelGeometricIsogeny_arrow
    (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    {K L : LevelIndex} (f : K ⟶ L) (x : (TowerA s).obj K) :
    (geometricIsogeny q e he hqe).hom.app L ((TowerA s).map f x) =
      (TowerB t).map f ((geometricIsogeny q e he hqe).hom.app K x) :=
  (geometricIsogeny q e he hqe).hom.naturality_apply f x

section Hecke
variable [Module.Finite ℚ V]

/-- The mixed comparison commutes with the first actual compact-open Hecke leg. -/
theorem weilPrimeToAdelicCompactOpenLevelGeometricIsogeny_heckeLeft
    (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (K L : LevelIndex) (g : G)
    (x : (TowerA s).obj (CompactOpenLevel.heckeLevel K L g)) :
    (geometricIsogeny q e he hqe).hom.app K
        ((TowerA s).map (CompactOpenLevel.heckeLeft K L g) x) =
      (TowerB t).map (CompactOpenLevel.heckeLeft K L g)
        ((geometricIsogeny q e he hqe).hom.app (CompactOpenLevel.heckeLevel K L g) x) :=
  (geometricIsogeny q e he hqe).hom.naturality_apply _ x

/-- The mixed comparison commutes with the second actual compact-open Hecke leg. -/
theorem weilPrimeToAdelicCompactOpenLevelGeometricIsogeny_heckeRight
    (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (K L : LevelIndex) (g : G)
    (x : (TowerA s).obj (CompactOpenLevel.heckeLevel K L g)) :
    (geometricIsogeny q e he hqe).hom.app L
        ((TowerA s).map (CompactOpenLevel.heckeRight K L g) x) =
      (TowerB t).map (CompactOpenLevel.heckeRight K L g)
        ((geometricIsogeny q e he hqe).hom.app (CompactOpenLevel.heckeLevel K L g) x) :=
  (geometricIsogeny q e he hqe).hom.naturality_apply _ x

end Hecke

variable {Ω'' : Type u} [Field Ω''] [IsAlgClosed Ω''] (r : Spec (.of Ω'') ⟶ S)

/-- A subsequent canonical change of target point composes with the mixed comparison. -/
theorem weilPrimeToAdelicCompactOpenLevelGeometricIsogeny_target_trans
    (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) :
    weilPrimeToAdelicCompactOpenLevelGeometricIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB compatibility iA iB V ψ (m := m) hAway hunit s r q e he hqe =
      geometricIsogeny q e he hqe ≪≫ transportB t r := by
  unfold weilPrimeToAdelicCompactOpenLevelGeometricIsogeny
  rw [weilPrimeToAdelicCompactOpenLevelGeometricTransport_trans preservation composition unitCoherence associativity comparison symmetry stability compatibility hB geometryB MB evaluationB lamB iB V ψ (m := m) hAway hunit s t r]
  exact (Iso.trans_assoc _ _ _).symm

/-- A preceding canonical change of source point gives the same mixed comparison. -/
theorem weilPrimeToAdelicCompactOpenLevelGeometricIsogeny_source_trans
    (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) :
    weilPrimeToAdelicCompactOpenLevelGeometricIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB compatibility iA iB V ψ (m := m) hAway hunit s r q e he hqe =
      transportA s t ≪≫ weilPrimeToAdelicCompactOpenLevelGeometricIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB compatibility iA iB V ψ (m := m) hAway hunit t r q e he hqe := by
  rw [weilPrimeToAdelicCompactOpenLevelGeometricIsogeny_target_trans preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB compatibility iA iB V ψ (m := m) hAway hunit s t r q e he hqe,
    weilPrimeToAdelicCompactOpenLevelGeometricIsogeny_eq_transport_isogeny preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB compatibility iA iB V ψ (m := m) hAway hunit s t q e he hqe]
  exact Iso.trans_assoc _ _ _

end Canonical
end Away

end Langlands.AbelianScheme.Tate.Geometric
