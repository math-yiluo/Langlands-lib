import Langlands.Representation.RestrictedTensor.Maps
import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic

/-! # The genuine restricted-product representation on restricted tensor products -/

noncomputable section
open scoped Classical TensorProduct

universe uK uI uG uV uW

namespace Langlands.RestrictedTensor

variable {K : Type uK} [Field K] {ι : Type uI}
variable {G : ι → Type uG} [∀ i, Group (G i)]
variable {V : ι → Type uV} {W : ι → Type uW}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
variable [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]

/-- The acting group is Mathlib's actual cofinite restricted product. -/
abbrev RestrictedGroup (G : ι → Type uG) [∀ i, Group (G i)]
    (H : ∀ i, Subgroup (G i)) :=
  RestrictedProduct G (fun i => (H i : Set (G i))) Filter.cofinite

/-- The local operators associated to a restricted-product element preserve the
reference family at all but finitely many places. -/
theorem action_preserves (H : ∀ i, Subgroup (G i))
    (ρ : ∀ i, Representation K (G i) (V i)) (E : Finset ι) (e : ∀ i, V i)
    (he : ∀ i ∉ E, ∀ g ∈ H i, ρ i g (e i) = e i)
    (g : RestrictedGroup G H) :
    ∀ᶠ i in Filter.cofinite, ρ i (g i) (e i) = e i :=
  (E.eventually_cofinite_notMem.and g.2).mono fun i hi => he i hi.1 (g i) hi.2

/-- The actual representation obtained by applying the component representations.
Its carrier is the algebraic direct limit; no dimension or topology on a local
carrier is required. -/
def representation (H : ∀ i, Subgroup (G i))
    (ρ : ∀ i, Representation K (G i) (V i)) (E : Finset ι) (e : ∀ i, V i)
    (he : ∀ i ∉ E, ∀ g ∈ H i, ρ i g (e i) = e i) :
    Representation K (RestrictedGroup G H) (Space K V E e) where
  toFun g := map E E e e (fun i => ρ i (g i)) (action_preserves H ρ E e he g)
  map_one' := by
    change map E E e e (fun i => ρ i ((1 : RestrictedGroup G H) i)) _ = LinearMap.id
    have h : (fun i => ρ i ((1 : RestrictedGroup G H) i)) =
        (fun i => (LinearMap.id : V i →ₗ[K] V i)) := by
      funext i
      exact (ρ i).map_one
    simp only [h, map_id]
  map_mul' g h := by
    change map E E e e (fun i => ρ i ((g * h) i)) _ =
      (map E E e e (fun i => ρ i (g i)) _).comp
        (map E E e e (fun i => ρ i (h i)) _)
    rw [map_comp]
    have hmul : (fun i => ρ i ((g * h) i)) =
        (fun i => (ρ i (g i)).comp (ρ i (h i))) := by
      funext i
      exact (ρ i).map_mul (g i) (h i)
    simp only [hmul]

/-- A uniform elementary-tensor formula, enlarging the stage if necessary. -/
theorem representation_pure (H : ∀ i, Subgroup (G i))
    (ρ : ∀ i, Representation K (G i) (V i)) (E : Finset ι) (e : ∀ i, V i)
    (he : ∀ i ∉ E, ∀ g ∈ H i, ρ i g (e i) = e i)
    (g : RestrictedGroup G H) (S : Index E) (v : ∀ i : S.1, V i) :
    representation H ρ E e he g (pure E e S v) =
      pure E e ⟨S.1 ∪ mapBound E (action_preserves H ρ E e he g),
        (subset_mapBound E _).trans Finset.subset_union_right⟩
        (fun i => ρ i (g i) (extend e v i)) :=
  map_pure E E e e _ _ S v

/-- If the group element lies in the reference subgroups outside the tensor's
stage, the action is componentwise on that very stage. -/
theorem representation_pure_of_mem (H : ∀ i, Subgroup (G i))
    (ρ : ∀ i, Representation K (G i) (V i)) (E : Finset ι) (e : ∀ i, V i)
    (he : ∀ i ∉ E, ∀ g ∈ H i, ρ i g (e i) = e i)
    (g : RestrictedGroup G H) (S : Index E)
    (hg : ∀ i ∉ S.1, g i ∈ H i) (v : ∀ i : S.1, V i) :
    representation H ρ E e he g (pure E e S v) =
      pure E e S (fun i => ρ i (g i) (v i)) := by
  exact map_pure_of_preserves E E e e _ _ S S.2
    (fun i hi => he i (fun hiE => hi (S.2 hiE)) (g i) (hg i hi)) v

/-- Component intertwiners preserving reference vectors almost everywhere induce
an intertwiner for the genuine restricted-product actions. -/
theorem map_intertwines (H : ∀ i, Subgroup (G i))
    (ρ : ∀ i, Representation K (G i) (V i))
    (σ : ∀ i, Representation K (G i) (W i))
    (E E' : Finset ι) (e : ∀ i, V i) (e' : ∀ i, W i)
    (he : ∀ i ∉ E, ∀ g ∈ H i, ρ i g (e i) = e i)
    (he' : ∀ i ∉ E', ∀ g ∈ H i, σ i g (e' i) = e' i)
    (f : ∀ i, V i →ₗ[K] W i)
    (hf : ∀ᶠ i in Filter.cofinite, f i (e i) = e' i)
    (hint : ∀ i g, (f i).comp (ρ i g) = (σ i g).comp (f i))
    (g : RestrictedGroup G H) :
    (map E E' e e' f hf).comp (representation H ρ E e he g) =
      (representation H σ E' e' he' g).comp (map E E' e e' f hf) := by
  change (map E E' e e' f hf).comp (map E E e e (fun i => ρ i (g i)) _) =
    (map E' E' e' e' (fun i => σ i (g i)) _).comp (map E E' e e' f hf)
  rw [map_comp, map_comp]
  have h : (fun i => (f i).comp (ρ i (g i))) =
      (fun i => (σ i (g i)).comp (f i)) := funext fun i => hint i (g i)
  simp only [h]

/-- The usual nonzero-reference-vector version of the representation. -/
def productRepresentation (H : ∀ i, Subgroup (G i))
    (ρ : ∀ i, Representation K (G i) (V i)) (E : Finset ι)
    (r : ReferenceVectors V E)
    (hr : ∀ i (hi : i ∉ E), ∀ g ∈ H i, ρ i g (r.vector i hi) = r.vector i hi) :
    Representation K (RestrictedGroup G H) (Product K V E r) :=
  representation H ρ E r.family (fun i hi g hg => by
    simpa only [ReferenceVectors.family_of_not_mem r hi] using hr i hi g hg)

end Langlands.RestrictedTensor
