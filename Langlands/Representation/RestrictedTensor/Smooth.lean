import Langlands.Representation.RestrictedTensor.Action
import Langlands.Representation.Smooth.Definitions
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-! # Smoothness of the algebraic restricted tensor product action -/

noncomputable section
open scoped Classical TensorProduct

universe uK uI uG uV

namespace Langlands.RestrictedTensor

variable {K : Type uK} [Field K] {ι : Type uI}
variable {G : ι → Type uG} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
variable {V : ι → Type uV}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- An open subgroup with prescribed open coordinates on a finite set and the
reference subgroups at every other coordinate. -/
def stageOpenSubgroup (H : ∀ i, Subgroup (G i))
    (hH : ∀ i, IsOpen (H i : Set (G i))) (S : Finset ι)
    (L : ∀ i : S, OpenSubgroup (G i)) : OpenSubgroup (RestrictedGroup G H) where
  carrier := {g | (∀ i : S, g i ∈ L i) ∧ ∀ i ∉ S, g i ∈ H i}
  one_mem' := ⟨fun i => (L i).one_mem, fun i _ => (H i).one_mem⟩
  mul_mem' hg hh := ⟨fun i => (L i).mul_mem (hg.1 i) (hh.1 i),
    fun i hi => (H i).mul_mem (hg.2 i hi) (hh.2 i hi)⟩
  inv_mem' hg := ⟨fun i => (L i).inv_mem (hg.1 i),
    fun i hi => (H i).inv_mem (hg.2 i hi)⟩
  isOpen' := by
    have hfinite : IsOpen {g : RestrictedGroup G H | ∀ i : S, g i ∈ L i} := by
      convert isOpen_iInter_of_finite (fun i : S =>
        (L i).isOpen.preimage (RestrictedProduct.continuous_eval i.1)) using 1
      ext g
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
      rfl
    exact hfinite.inter (RestrictedProduct.isOpen_forall_imp_mem hH)

/-- Every finite elementary tensor is smooth for the constructed action. -/
theorem isSmoothVector_pure (H : ∀ i, Subgroup (G i))
    (hH : ∀ i, IsOpen (H i : Set (G i)))
    (ρ : ∀ i, Representation K (G i) (V i)) (hρ : ∀ i, Langlands.IsSmooth (ρ i))
    (E : Finset ι) (e : ∀ i, V i)
    (he : ∀ i ∉ E, ∀ g ∈ H i, ρ i g (e i) = e i)
    (S : Index E) (v : ∀ i : S.1, V i) :
    Langlands.IsSmoothVector (representation H ρ E e he) (pure E e S v) := by
  choose L hL using fun i : S.1 => hρ i (v i)
  refine ⟨stageOpenSubgroup H hH S.1 L, ?_⟩
  change ∀ g : (stageOpenSubgroup H hH S.1 L).toSubgroup,
    representation H ρ E e he g.1 (pure E e S v) = pure E e S v
  intro g
  rw [representation_pure_of_mem H ρ E e he g.1 S g.2.2]
  congr 1
  funext i
  exact hL i ⟨g.1 i, g.2.1 i⟩

/-- Local smoothness and openness of the reference subgroups imply smoothness
of the genuine restricted-product action. Compactness is not needed. -/
theorem isSmooth_representation (H : ∀ i, Subgroup (G i))
    (hH : ∀ i, IsOpen (H i : Set (G i)))
    (ρ : ∀ i, Representation K (G i) (V i)) (hρ : ∀ i, Langlands.IsSmooth (ρ i))
    (E : Finset ι) (e : ∀ i, V i)
    (he : ∀ i ∉ E, ∀ g ∈ H i, ρ i g (e i) = e i) :
    Langlands.IsSmooth (representation H ρ E e he) := by
  intro x
  induction x using Langlands.RestrictedTensor.induction with
  | hpure S v => exact isSmoothVector_pure H hH ρ hρ E e he S v
  | hadd x y hx hy =>
    obtain ⟨L, hL⟩ := hx
    obtain ⟨M, hM⟩ := hy
    refine ⟨L ⊓ M, ?_⟩
    change ∀ g : (L ⊓ M).toSubgroup,
      representation H ρ E e he g.1 (x + y) = x + y
    intro g
    have hx : representation H ρ E e he g.1 x = x := hL ⟨g.1, g.2.1⟩
    have hy : representation H ρ E e he g.1 y = y := hM ⟨g.1, g.2.2⟩
    rw [map_add, hx, hy]
  | hsmul a x hx =>
    obtain ⟨L, hL⟩ := hx
    refine ⟨L, ?_⟩
    exact (Langlands.fixedVectors (representation H ρ E e he) L.toSubgroup).smul_mem a hL

/-- Smoothness for the usual nonzero-reference-vector input. In particular this
applies when the local reference subgroups are compact open. -/
theorem isSmooth_productRepresentation (H : ∀ i, Subgroup (G i))
    (hH : ∀ i, IsOpen (H i : Set (G i)))
    (ρ : ∀ i, Representation K (G i) (V i)) (hρ : ∀ i, Langlands.IsSmooth (ρ i))
    (E : Finset ι) (r : ReferenceVectors V E)
    (hr : ∀ i (hi : i ∉ E), ∀ g ∈ H i, ρ i g (r.vector i hi) = r.vector i hi) :
    Langlands.IsSmooth (productRepresentation H ρ E r hr) :=
  isSmooth_representation H hH ρ hρ E r.family _

end Langlands.RestrictedTensor
