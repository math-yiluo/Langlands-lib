import Langlands.AbelianScheme.Tate.AbelianScheme
import Mathlib.Topology.Category.Profinite.Basic

set_option maxHeartbeats 800000

/-! # Profinite topology on actual integral Tate limits -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Tate

universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X]
  (T : Over S) (P : ℕ → Prop)

/-- Coherence cuts out a closed subgroup of the product of discrete torsion levels. -/
theorem isClosed_coherent :
    IsClosed (coherent G T P : Set (∀ n : Index P, Level G T n.val)) := by
  change IsClosed {x : ∀ k : Index P, Level G T k.val |
    ∀ (n : Index P) (m : Index P) (h : n.val ∣ m.val), transition G T h (x m) = x n}
  simp only [Set.ofPred_forall]
  refine isClosed_iInter (fun n => isClosed_iInter (fun m => isClosed_iInter (fun h => ?_)))
  exact isClosed_eq ((continuous_of_discreteTopology : Continuous (transition G T h)).comp
    (continuous_apply m)) (continuous_apply n)

instance : T2Space (Integral G T P) :=
  inferInstanceAs (T2Space ↥(coherent G T P))

instance : TotallyDisconnectedSpace (Integral G T P) :=
  inferInstanceAs (TotallyDisconnectedSpace ↥(coherent G T P))

/-- Finiteness is needed only at the selected positive levels. -/
instance [∀ n : Index P, Finite (Level G T n.val)] : CompactSpace (Integral G T P) :=
  isCompact_iff_compactSpace.mp (isClosed_coherent G T P).isCompact

/-- Continuity into the Tate limit is equivalent to continuity of all coordinates. -/
theorem continuous_iff_evaluation {X : Type*} [TopologicalSpace X]
    (f : X → Integral G T P) :
    Continuous f ↔ ∀ n, Continuous (fun x => evaluation G T P n (f x)) := by
  constructor
  · intro hf n
    exact (continuous_evaluation G T P n).comp hf
  · intro hf
    exact (continuous_pi hf).subtype_mk (fun x => (f x).property)

/-- The existing integral Tate group, bundled as a profinite space when levels are finite. -/
def profinite [∀ n : Index P, Finite (Level G T n.val)] : Profinite :=
  Profinite.of (Integral G T P)

variable {G} {H K : Grp (Over S)} [IsCommMonObj H.X] [IsCommMonObj K.X]

/-- The already constructed Tate map as a morphism of profinite spaces. -/
def profiniteMap [∀ n : Index P, Finite (Level G T n.val)]
    [∀ n : Index P, Finite (Level H T n.val)] (f : G ⟶ H) :
    profinite G T P ⟶ profinite H T P :=
  CompHausLike.ofHom _ ⟨map T P f, continuous_map T P f⟩

@[simp]
theorem profiniteMap_apply [∀ n : Index P, Finite (Level G T n.val)]
    [∀ n : Index P, Finite (Level H T n.val)] (f : G ⟶ H) (x : Integral G T P) :
    profiniteMap T P f x = map T P f x := rfl

@[simp]
theorem profiniteMap_id [∀ n : Index P, Finite (Level G T n.val)] :
    profiniteMap T P (𝟙 G) = 𝟙 (profinite G T P) := by
  apply ConcreteCategory.hom_ext
  intro x
  exact DFunLike.congr_fun (map_id T P) x

theorem profiniteMap_comp [∀ n : Index P, Finite (Level G T n.val)]
    [∀ n : Index P, Finite (Level H T n.val)]
    [∀ n : Index P, Finite (Level K T n.val)] (f : G ⟶ H) (g : H ⟶ K) :
    profiniteMap T P (f ≫ g) = profiniteMap T P f ≫ profiniteMap T P g := by
  apply ConcreteCategory.hom_ext
  intro x
  exact DFunLike.congr_fun (map_comp T P f g) x

end Langlands.GroupScheme.Tate

namespace Langlands.AbelianScheme.Tate

universe u
variable {S : Scheme.{u}} (A : AbelianScheme S) (T : Over S) (P : ℕ → Prop)

/-- The actual integral Tate group of an abelian scheme as a profinite space. -/
abbrev profinite [∀ n : GroupScheme.Tate.Index P, Finite (Level A T n.val)] : Profinite :=
  GroupScheme.Tate.profinite A.toGrp T P

/-- The full Tate group is profinite under finiteness of every positive torsion level. -/
abbrev fullProfinite
    [∀ n : GroupScheme.Tate.Index (fun _ => True), Finite (Level A T n.val)] : Profinite :=
  profinite A T (fun _ => True)

/-- The away-from-p Tate group only requires finiteness at coprime levels. -/
abbrev awayProfinite (p : ℕ)
    [∀ n : GroupScheme.Tate.Index (fun n => Nat.Coprime n p), Finite (Level A T n.val)] :
    Profinite := profinite A T (fun n => Nat.Coprime n p)

end Langlands.AbelianScheme.Tate
