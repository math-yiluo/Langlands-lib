import Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictComparison
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! # Functorial radius-one comparison of actual affinoid presentations -/

noncomputable section

universe u

namespace Langlands.Analytic

open CategoryTheory

variable (K : Type u) [NormedField K] [IsUltrametricDist K]

namespace PresentedAffinoidAlgebra

/-- Transport a bounded map through the actual radius-one quotient equivalences. -/
def ofStrictMap {P Q : PresentedStrictAffinoidAlgebra K}
    (f : BoundedAlgHom K P Q) : BoundedAlgHom K (ofStrict K P) (ofStrict K Q) :=
  (strictEquiv K Q).symm.toBoundedAlgHom.comp
    (f.comp (strictEquiv K P).toBoundedAlgHom)

@[simp] theorem ofStrictMap_apply {P Q : PresentedStrictAffinoidAlgebra K}
    (f : BoundedAlgHom K P Q) (a : ofStrict K P) :
    ofStrictMap K f a = (strictEquiv K Q).symm (f (strictEquiv K P a)) := rfl

/-- Transport back along the same equivalences, without choosing representatives. -/
def fromStrictMap {P Q : PresentedStrictAffinoidAlgebra K}
    (f : BoundedAlgHom K (ofStrict K P) (ofStrict K Q)) : BoundedAlgHom K P Q :=
  (strictEquiv K Q).toBoundedAlgHom.comp
    (f.comp (strictEquiv K P).symm.toBoundedAlgHom)

@[simp] theorem fromStrictMap_apply {P Q : PresentedStrictAffinoidAlgebra K}
    (f : BoundedAlgHom K (ofStrict K P) (ofStrict K Q)) (a : P) :
    fromStrictMap K f a = strictEquiv K Q (f ((strictEquiv K P).symm a)) := rfl

@[simp] theorem fromStrictMap_ofStrictMap {P Q : PresentedStrictAffinoidAlgebra K}
    (f : BoundedAlgHom K P Q) : fromStrictMap K (ofStrictMap K f) = f := by
  apply BoundedAlgHom.ext
  intro a
  simp

@[simp] theorem ofStrictMap_fromStrictMap {P Q : PresentedStrictAffinoidAlgebra K}
    (f : BoundedAlgHom K (ofStrict K P) (ofStrict K Q)) :
    ofStrictMap K (fromStrictMap K f) = f := by
  apply BoundedAlgHom.ext
  intro a
  simp

/-- Every bounded map between the embedded presentations comes from exactly one
bounded map between the original strict presentations. -/
def strictHomEquiv (P Q : PresentedStrictAffinoidAlgebra K) :
    BoundedAlgHom K P Q ≃ BoundedAlgHom K (ofStrict K P) (ofStrict K Q) where
  toFun := ofStrictMap K
  invFun := fromStrictMap K
  left_inv := fromStrictMap_ofStrictMap K
  right_inv := ofStrictMap_fromStrictMap K

/-- The actual radius-one comparison respects identity maps and composition. -/
def ofStrictFunctor : PresentedStrictAffinoidAlgebra K ⥤ PresentedAffinoidAlgebra K where
  obj := ofStrict K
  map := ofStrictMap K
  map_id P := by
    apply BoundedAlgHom.ext
    intro a
    change (strictEquiv K P).symm (strictEquiv K P a) = a
    exact BoundedAlgEquiv.symm_apply_apply _ _
  map_comp {P Q R} f g := by
    change BoundedAlgHom K P Q at f
    change BoundedAlgHom K Q R at g
    apply BoundedAlgHom.ext
    intro a
    change (strictEquiv K R).symm (g (f (strictEquiv K P a))) =
      (strictEquiv K R).symm
        (g (strictEquiv K Q ((strictEquiv K Q).symm (f (strictEquiv K P a)))))
    rw [BoundedAlgEquiv.apply_symm_apply]

/-- An explicit inverse on morphisms for the radius-one comparison functor. -/
def ofStrictFullyFaithful : (ofStrictFunctor K).FullyFaithful where
  preimage := fromStrictMap K
  map_preimage := ofStrictMap_fromStrictMap K
  preimage_map := fromStrictMap_ofStrictMap K

instance : (ofStrictFunctor K).Full where
  map_surjective := (strictHomEquiv K _ _).surjective

instance : (ofStrictFunctor K).Faithful where
  map_injective {P Q} := by
    intro f g h
    exact (strictHomEquiv K P Q).injective h

/-- The concrete spectrum homeomorphisms commute with every bounded map.
This pointwise naturality does not require coefficient completeness. -/
theorem strictSpectrumHomeomorph_naturality
    {P Q : PresentedStrictAffinoidAlgebra K} (f : BoundedAlgHom K P Q)
    (x : BanachSpectrum Q) :
    strictSpectrumHomeomorph K P (BanachSpectrum.comap f.toBoundedRingHom x) =
      BanachSpectrum.comap (ofStrictMap K f).toBoundedRingHom
        (strictSpectrumHomeomorph K Q x) := by
  apply BanachSpectrum.ext
  intro a
  change x (f (strictEquiv K P a)) =
    x (strictEquiv K Q ((strictEquiv K Q).symm (f (strictEquiv K P a))))
  rw [BoundedAlgEquiv.apply_symm_apply]

end PresentedAffinoidAlgebra

/-- The induced functor between the opposite categories of presentations. -/
def ofStrictSpaceFunctor : PresentedStrictAffinoidSpace K ⥤ PresentedAffinoidSpace K :=
  (PresentedAffinoidAlgebra.ofStrictFunctor K).op

/-- The existing strict spectrum functor agrees naturally with the weighted
spectrum functor after the radius-one comparison. Its completeness hypothesis
comes from the existing strict spectrum functor. -/
def strictSpectrumComparison [CompleteSpace K] :
    strictAffinoidSpectrumFunctor K ≅ ofStrictSpaceFunctor K ⋙ affinoidSpectrumFunctor K :=
  NatIso.ofComponents
    (fun P => TopCat.isoOfHomeo
      (PresentedAffinoidAlgebra.strictSpectrumHomeomorph K P.unop))
    (fun {P Q} f => by
      apply TopCat.ext
      intro x
      exact PresentedAffinoidAlgebra.strictSpectrumHomeomorph_naturality K f.unop x)

end Langlands.Analytic
