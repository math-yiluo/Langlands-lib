import Langlands.Topology.Rationalization.Lattice
import Langlands.AbelianScheme.Tate.MultiplicationTopologyProof
import Langlands.AbelianScheme.Tate.RationalMonodromy

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.AbelianScheme.Tate

universe u
open Langlands.AlgebraicGeometry.FiniteEtale
open GroupScheme.Tate (Index)

variable {S : Scheme.{u}} (A : AbelianScheme S) (T : Over S) (P : ℕ → Prop)

/-- The final topology of the actual integral Tate lattice on its rationalization. -/
@[instance_reducible] def rationalTopology : TopologicalSpace (Rational A T P) :=
  Langlands.Topology.Rationalization.finalTopology (Integral A T P)

attribute [local instance] rationalTopology

/-- The topology is specified by all rational charts on the actual integral limit. -/
theorem isOpen_rationalTopology_iff {U : Set (Rational A T P)} :
    IsOpen U ↔ ∀ q : ℚ, IsOpen ((fun x : Integral A T P => q ⊗ₜ[ℤ] x) ⁻¹' U) :=
  Iff.rfl

/-- Continuity of every rational chart, including the zero chart. -/
theorem continuous_rationalChart (q : ℚ) :
    Continuous (fun x : Integral A T P => q ⊗ₜ[ℤ] x) :=
  Langlands.Topology.Rationalization.continuous_tmul q

/-- Fixed rational scalar multiplication is continuous. -/
theorem continuous_rational_smul (q : ℚ) :
    Continuous (fun x : Rational A T P => q • x) :=
  Langlands.Topology.Rationalization.continuous_smul q

/-- The actual integral-to-rational map is continuous. -/
theorem continuous_toRational : Continuous (GroupScheme.Tate.toRational A.toGrp T P) :=
  continuous_rationalChart A T P 1

variable {A} {B : AbelianScheme S}

/-- Existing homomorphism-induced rational Tate maps are continuous. -/
theorem continuous_rationalMap (f : A ⟶ B) : Continuous (rationalMap T P f) :=
  Langlands.Topology.Rationalization.continuous_baseChange (map T P f)
    (continuous_map T P f)

variable (A)

/-- The existing full-to-away rational restriction is continuous. -/
theorem continuous_rationalRestrictAway (m : ℕ) :
    Continuous (GroupScheme.Tate.rationalRestrictAway A.toGrp T m) :=
  Langlands.Topology.Rationalization.continuous_baseChange (restrictAway A T m)
    (continuous_restrictAway A T m)

/-- The full integral limit is an open subspace of its rationalization. -/
theorem isOpenEmbedding_full_toRational :
    Topology.IsOpenEmbedding (GroupScheme.Tate.toRational A.toGrp T (fun _ => True)) :=
  Langlands.Topology.Rationalization.isOpenEmbedding_integral
    (GroupScheme.Tate.fullMultiplicationOpenEmbeddings A.toGrp T)

/-- Every away integral limit is an open subspace of its rationalization. -/
theorem isOpenEmbedding_away_toRational (m : ℕ) :
    Topology.IsOpenEmbedding
      (GroupScheme.Tate.toRational A.toGrp T (fun n => Nat.Coprime n m)) :=
  Langlands.Topology.Rationalization.isOpenEmbedding_integral
    (GroupScheme.Tate.awayMultiplicationOpenEmbeddings A.toGrp T m)

/-- The full rational Tate module is a topological additive group. Install locally. -/
theorem rationalFull_topologicalAddGroup : IsTopologicalAddGroup (RationalFull A T) :=
  Langlands.Topology.Rationalization.topologicalAddGroup
    (GroupScheme.Tate.fullMultiplicationOpenEmbeddings A.toGrp T)

/-- The away rational Tate module is a topological additive group. Install locally. -/
theorem rationalAway_topologicalAddGroup (m : ℕ) : IsTopologicalAddGroup (RationalAway A T m) :=
  Langlands.Topology.Rationalization.topologicalAddGroup
    (GroupScheme.Tate.awayMultiplicationOpenEmbeddings A.toGrp T m)

/-- Hausdorffness uses the existing product-subspace topology on the full limit. -/
theorem rationalFull_t2Space : T2Space (RationalFull A T) :=
  Langlands.Topology.Rationalization.hausdorff
    (GroupScheme.Tate.fullMultiplicationOpenEmbeddings A.toGrp T)

/-- Hausdorffness for every prime-to-modulus rational Tate carrier. -/
theorem rationalAway_t2Space (m : ℕ) : T2Space (RationalAway A T m) :=
  Langlands.Topology.Rationalization.hausdorff
    (GroupScheme.Tate.awayMultiplicationOpenEmbeddings A.toGrp T m)

section Geometric
variable {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S)
  (hfin : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u})

include hfin htor in
/-- Actual geometric finite levels make the full integral image compact and open. -/
theorem rationalFull_compactOpen_integral
    (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤))) :
    IsCompact (Set.range (GroupScheme.Tate.toRational A.toGrp (Over.mk s) (fun _ => True))) ∧
      IsOpen (Set.range (GroupScheme.Tate.toRational A.toGrp (Over.mk s) (fun _ => True))) := by
  let := integralMonodromy_compactSpace s hfin htor A (fun _ => True) hu
  exact Langlands.Topology.Rationalization.compactOpen_integral
    (GroupScheme.Tate.fullMultiplicationOpenEmbeddings A.toGrp (Over.mk s))

include hfin htor in
/-- The away integral image is compact and open under invertibility of retained orders. -/
theorem rationalAway_compactOpen_integral (m : ℕ)
    (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤))) :
    IsCompact (Set.range (GroupScheme.Tate.toRational A.toGrp (Over.mk s)
      (fun n => Nat.Coprime n m))) ∧
      IsOpen (Set.range (GroupScheme.Tate.toRational A.toGrp (Over.mk s)
        (fun n => Nat.Coprime n m))) := by
  let := integralMonodromy_compactSpace s hfin htor A (fun n => Nat.Coprime n m) hu
  exact Langlands.Topology.Rationalization.compactOpen_integral
    (GroupScheme.Tate.awayMultiplicationOpenEmbeddings A.toGrp (Over.mk s) m)

include hfin htor in
/-- Local compactness of the full rational Tate module from actual geometric finiteness. -/
theorem rationalFull_locallyCompactSpace
    (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤))) :
    LocallyCompactSpace (RationalFull A (Over.mk s)) := by
  let := integralMonodromy_compactSpace s hfin htor A (fun _ => True) hu
  exact Langlands.Topology.Rationalization.locallyCompact
    (GroupScheme.Tate.fullMultiplicationOpenEmbeddings A.toGrp (Over.mk s))

include hfin htor in
/-- Local compactness of the away rational Tate module. -/
theorem rationalAway_locallyCompactSpace (m : ℕ)
    (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤))) :
    LocallyCompactSpace (RationalAway A (Over.mk s) m) := by
  let := integralMonodromy_compactSpace s hfin htor A (fun n => Nat.Coprime n m) hu
  exact Langlands.Topology.Rationalization.locallyCompact
    (GroupScheme.Tate.awayMultiplicationOpenEmbeddings A.toGrp (Over.mk s) m)

private theorem continuous_rationalMonodromy_of_openMultiplication
    (hu : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤)))
    (hM : ∀ n : ℕ, 0 < n → Topology.IsOpenEmbedding
      (fun x : Integral A (Over.mk s) P => n • x)) :
    Continuous (fun z : FundamentalGroup s hfin × Rational A (Over.mk s) P =>
      rationalMonodromy s hfin htor A P hu z.1 z.2) := by
  let := integralMonodromyAction s hfin htor A P hu
  let := integralMonodromyAction_continuousSMul s hfin htor A P hu
  exact Langlands.Topology.Rationalization.continuous_actionMap hM

/-- Joint continuity of the existing full rational geometric monodromy action. -/
theorem continuous_rationalFullMonodromy
    (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤))) :
    Continuous (fun z : FundamentalGroup s hfin × RationalFull A (Over.mk s) =>
      rationalFullMonodromy s hfin htor A hu z.1 z.2) :=
  continuous_rationalMonodromy_of_openMultiplication A (fun _ => True) s hfin htor hu
    (GroupScheme.Tate.fullMultiplicationOpenEmbeddings A.toGrp (Over.mk s))

/-- Joint continuity of the existing away rational geometric monodromy action. -/
theorem continuous_rationalAwayMonodromy (m : ℕ)
    (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤))) :
    Continuous (fun z : FundamentalGroup s hfin × RationalAway A (Over.mk s) m =>
      rationalAwayMonodromy s hfin htor A m hu z.1 z.2) :=
  continuous_rationalMonodromy_of_openMultiplication A (fun n => Nat.Coprime n m) s hfin htor hu
    (GroupScheme.Tate.awayMultiplicationOpenEmbeddings A.toGrp (Over.mk s) m)

/-- Continuity for the already published full action instance, available locally. -/
theorem rationalFullMonodromyAction_continuousSMul
    (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤))) :
    let := rationalMonodromyAction s hfin htor A (fun _ => True) hu
    ContinuousSMul (FundamentalGroup s hfin) (RationalFull A (Over.mk s)) := by
  let := rationalMonodromyAction s hfin htor A (fun _ => True) hu
  exact ⟨continuous_rationalFullMonodromy A s hfin htor hu⟩

/-- Continuity for the already published away action instance, available locally. -/
theorem rationalAwayMonodromyAction_continuousSMul (m : ℕ)
    (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤))) :
    let := rationalMonodromyAction s hfin htor A (fun n => Nat.Coprime n m) hu
    ContinuousSMul (FundamentalGroup s hfin) (RationalAway A (Over.mk s) m) := by
  let := rationalMonodromyAction s hfin htor A (fun n => Nat.Coprime n m) hu
  exact ⟨continuous_rationalAwayMonodromy A s hfin htor m hu⟩

end Geometric
end Langlands.AbelianScheme.Tate
