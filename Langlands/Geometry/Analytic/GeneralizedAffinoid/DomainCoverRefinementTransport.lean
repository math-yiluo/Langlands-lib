import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCoverBaseTransport
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCoverRefinement

/-! # Finite-cover refinement categories under bounded base equivalences -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {A B : PresentedAffinoidAlgebra K} {V : Domain K A}

namespace Refinement

variable {a c d : FiniteCover V}

/-- Keep every chosen index and actual bounded component restriction while
transporting the ambient algebra. -/
def transportBase (e : BoundedAlgEquiv K A B) (r : Refinement d c) :
    Refinement (d.transportBase e) (c.transportBase e) where
  index := r.index
  map i := Domain.transportBaseMap e (r.map i)

@[simp] theorem transportBase_index (e : BoundedAlgEquiv K A B)
    (r : Refinement d c) : (r.transportBase e).index = r.index := rfl

@[simp] theorem transportBase_map_restriction (e : BoundedAlgEquiv K A B)
    (r : Refinement d c) (i : Fin d.size) :
    ((r.transportBase e).map i).restriction = (r.map i).restriction := rfl

@[simp] theorem transportBase_id (e : BoundedAlgEquiv K A B) (c : FiniteCover V) :
    (Refinement.id c).transportBase e = Refinement.id (c.transportBase e) :=
  Refinement.ext rfl

@[simp] theorem transportBase_comp (e : BoundedAlgEquiv K A B)
    (r : Refinement a d) (s : Refinement d c) :
    (r.comp s).transportBase e = (r.transportBase e).comp (s.transportBase e) :=
  Refinement.ext rfl

/-- On the retained disjoint unions of actual quotient spectra, transport
retains the whole continuous refinement map. -/
@[simp] theorem transportBase_spectrumMap (e : BoundedAlgEquiv K A B)
    (r : Refinement d c) : (r.transportBase e).spectrumMap = r.spectrumMap := rfl

end Refinement

/-- The published object transport extends to the actual chosen-index
refinement category. -/
def transportBaseFunctor (e : BoundedAlgEquiv K A B) :
    FiniteCover V ⥤ FiniteCover (Domain.transportBase e V) where
  obj c := c.transportBase e
  map r := Refinement.transportBase e r
  map_id _ := Refinement.ext rfl
  map_comp _ _ := Refinement.ext rfl

/-- Transport a cover back and then use the concrete round-trip domain
isomorphism to restore the original target. -/
def transportBaseInverseObj (e : BoundedAlgEquiv K A B)
    (c : FiniteCover (Domain.transportBase e V)) : FiniteCover V where
  size := c.size
  obj i := Domain.transportBase e.symm (c.obj i)
  map i := Domain.transportBaseMap e.symm (c.map i) ≫
    (Domain.transportBaseRoundTripIso e V).hom
  covers x hx := (c.transportBase e.symm).covers x
    (by simpa only [Domain.transportBase_symm_locus] using hx)

/-- The inverse functor also retains the chosen indices and bounded
restrictions; only its target comparison uses the round-trip isomorphism. -/
def transportBaseInverse (e : BoundedAlgEquiv K A B) :
    FiniteCover (Domain.transportBase e V) ⥤ FiniteCover V where
  obj := transportBaseInverseObj e
  map r := {
    index := r.index
    map i := Domain.transportBaseMap e.symm (r.map i) }
  map_id _ := Refinement.ext rfl
  map_comp _ _ := Refinement.ext rfl

/-- Both unit directions select the same component, with identity bounded
algebra maps supplied by the actual domain round-trip isomorphisms. -/
def transportBaseUnitIso (e : BoundedAlgEquiv K A B) (c : FiniteCover V) :
    c ≅ (transportBaseInverse e).obj ((transportBaseFunctor e).obj c) where
  hom := {
    index := fun i => i
    map i := (Domain.transportBaseRoundTripIso e (c.obj i)).inv }
  inv := {
    index := fun i => i
    map i := (Domain.transportBaseRoundTripIso e (c.obj i)).hom }
  hom_inv_id := Refinement.ext rfl
  inv_hom_id := Refinement.ext rfl

/-- The counit is the corresponding actual round trip on the new base,
again retaining every component index. -/
def transportBaseCounitIso (e : BoundedAlgEquiv K A B)
    (c : FiniteCover (Domain.transportBase e V)) :
    (transportBaseFunctor e).obj ((transportBaseInverse e).obj c) ≅ c where
  hom := {
    index := fun i => i
    map i := (Domain.transportBaseRoundTripIso e.symm (c.obj i)).hom }
  inv := {
    index := fun i => i
    map i := (Domain.transportBaseRoundTripIso e.symm (c.obj i)).inv }
  hom_inv_id := Refinement.ext rfl
  inv_hom_id := Refinement.ext rfl

/-- An actual bounded equivalence of ambient affinoid algebras gives an
equivalence of their finite full-domain cover refinement categories. -/
def transportBaseEquivalence (e : BoundedAlgEquiv K A B) :
    FiniteCover V ≌ FiniteCover (Domain.transportBase e V) where
  functor := transportBaseFunctor e
  inverse := transportBaseInverse e
  unitIso := NatIso.ofComponents (transportBaseUnitIso e)
    (by intro c d r; apply Refinement.ext; rfl)
  counitIso := NatIso.ofComponents (transportBaseCounitIso e)
    (by intro c d r; apply Refinement.ext; rfl)
  functor_unitIso_comp c := Refinement.ext rfl

/-- Transporting the canonical arrow to the singleton keeps that concrete
terminal arrow, not just an unspecified terminal-object isomorphism. -/
@[simp] theorem transportBase_toSingleton (e : BoundedAlgEquiv K A B)
    (c : FiniteCover V) :
    (Refinement.toSingleton c).transportBase e =
      Refinement.toSingleton (c.transportBase e) :=
  Refinement.ext rfl

/-- The transported refinement still lies over the original target locus
after the actual base-spectrum homeomorphism. -/
theorem transportBase_spectrumMap_over_target (e : BoundedAlgEquiv K A B)
    {c d : FiniteCover V} (r : Refinement d c) :
    (Domain.transportBaseLocusHomeomorph e V :
      C((Domain.transportBase e V).locus, V.locus)).comp
      ((c.transportBase e).totalMap.comp (r.transportBase e).spectrumMap) =
        d.totalMap := by
  rw [(r.transportBase e).spectrumMap_over_target, transportBase_totalMap]

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover
