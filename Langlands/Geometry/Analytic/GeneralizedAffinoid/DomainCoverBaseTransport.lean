import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBaseTransport
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainTopology

/-! # Finite full-domain covers under actual bounded base equivalences -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {A B : PresentedAffinoidAlgebra K} {V : Domain K A}

/-- The actual base-spectrum homeomorphism preserves and reflects pointwise
coverage of a full domain by a supplied family of full domains. -/
theorem familyCovers_transportBase_iff (e : BoundedAlgEquiv K A B)
    {ι : Type v} (obj : ι → Domain K A) :
    (∀ x ∈ (Domain.transportBase e V).locus,
      ∃ i, x ∈ (Domain.transportBase e (obj i)).locus) ↔
    (∀ x ∈ V.locus, ∃ i, x ∈ (obj i).locus) := by
  constructor
  · intro h x hx
    obtain ⟨y, rfl⟩ := e.spectrumHomeomorph.surjective x
    exact h y hx
  · intro h x hx
    exact h (e.spectrumHomeomorph x) hx

/-- Transport every actual full component and bounded target restriction along
the bounded base equivalence, retaining the finite index set and algebras. -/
def transportBase (e : BoundedAlgEquiv K A B) (c : FiniteCover V) :
    FiniteCover (Domain.transportBase e V) where
  size := c.size
  obj i := Domain.transportBase e (c.obj i)
  map i := Domain.transportBaseMap e (c.map i)
  covers := (familyCovers_transportBase_iff e c.obj).2 c.covers

@[simp] theorem transportBase_size (e : BoundedAlgEquiv K A B) (c : FiniteCover V) :
    (c.transportBase e).size = c.size := rfl

@[simp] theorem transportBase_obj (e : BoundedAlgEquiv K A B) (c : FiniteCover V)
    (i : Fin c.size) :
    (c.transportBase e).obj i = Domain.transportBase e (c.obj i) := rfl

/-- Every transported component retains its actual quotient algebra. -/
@[simp] theorem transportBase_obj_algebra (e : BoundedAlgEquiv K A B)
    (c : FiniteCover V) (i : Fin c.size) :
    ((c.transportBase e).obj i).algebra = (c.obj i).algebra := rfl

/-- The actual bounded restriction map is unchanged by transport. -/
@[simp] theorem transportBase_map_restriction (e : BoundedAlgEquiv K A B)
    (c : FiniteCover V) (i : Fin c.size) :
    ((c.transportBase e).map i).restriction = (c.map i).restriction := rfl

/-- The concrete identity cover transports to the concrete identity cover. -/
@[simp] theorem transportBase_singleton (e : BoundedAlgEquiv K A B) (V : Domain K A) :
    (singleton V).transportBase e = singleton (Domain.transportBase e V) := rfl

/-- Each unchanged component spectrum maps to the corresponding locus point
under the homeomorphism induced by the actual bounded base equivalence. -/
theorem transportBase_componentMap (e : BoundedAlgEquiv K A B) (c : FiniteCover V)
    (i : Fin c.size) :
    (Domain.transportBaseLocusHomeomorph e V :
      C((Domain.transportBase e V).locus, V.locus)).comp
      ((c.transportBase e).componentMap i) = c.componentMap i := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change e.spectrumHomeomorph ((Domain.transportBase e (c.obj i)).spectrumMap x) =
    (c.obj i).spectrumMap x
  exact Domain.transportBase_spectrumMap e (c.obj i) x

/-- The whole finite spectrum-cover diagram commutes over the actual locus
homeomorphism. Its source is definitionally the same disjoint union. -/
theorem transportBase_totalMap (e : BoundedAlgEquiv K A B) (c : FiniteCover V) :
    (Domain.transportBaseLocusHomeomorph e V :
      C((Domain.transportBase e V).locus, V.locus)).comp
      (c.transportBase e).totalMap = c.totalMap := by
  apply ContinuousMap.ext
  intro x
  exact congrArg
    (fun f : C(BanachSpectrum (c.obj x.1).algebra, V.locus) => f x.2)
    (transportBase_componentMap e c x.1)

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover
