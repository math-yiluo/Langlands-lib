import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCoverBaseTransport
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainAlgebraSheaf
import Mathlib.CategoryTheory.Sites.Equivalence

/-! # Finite full-domain sites and algebra sheaves under bounded base equivalences -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open CategoryTheory Opposite

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : PresentedAffinoidAlgebra K}

private theorem hom_unique {C : PresentedAffinoidAlgebra K}
    {U V : Domain K C} (f g : U ⟶ V) : f = g :=
  @Subsingleton.elim (Inclusion U V) inferInstance f g

/-- A finite covering sieve lifts through the actual inverse base transport,
retaining its finite index, quotient algebras and bounded restrictions. -/
instance transportBaseFunctor_isCocontinuous (e : BoundedAlgEquiv K A B) :
    (transportBaseFunctor e).IsCocontinuous
      (finiteDomainTopology K A) (finiteDomainTopology K B) where
  cover_lift {U} {S} hS := by
    obtain ⟨I, hI, D, f, hf, hc⟩ := hS
    let E : I → Domain K A := fun i => transportBase e.symm (D i)
    let a : ∀ i, E i ⟶ U := fun i =>
      transportBaseMap e.symm (f i) ≫ (transportBaseEquivalence e).unitIso.inv.app U
    refine ⟨I, hI, E, a, ?_, ?_⟩
    · intro i
      change S ((transportBaseFunctor e).map (a i))
      have heq : (transportBaseFunctor e).map (a i) =
          (transportBaseEquivalence e).counitIso.hom.app (D i) ≫ f i :=
        hom_unique _ _
      rw [heq]
      exact S.downward_closed (hf i) _
    · have hc' := (FiniteCover.familyCovers_transportBase_iff e.symm D).2 hc
      intro x hx
      apply hc' x
      change x ∈ (transportBase e.symm (transportBase e U)).locus
      rw [transportBase_symm_locus]
      exact hx

instance transportBaseEquivalence_functor_isCocontinuous
    (e : BoundedAlgEquiv K A B) :
    (transportBaseEquivalence e).functor.IsCocontinuous
      (finiteDomainTopology K A) (finiteDomainTopology K B) :=
  transportBaseFunctor_isCocontinuous e

instance transportBaseEquivalence_inverse_isCocontinuous
    (e : BoundedAlgEquiv K A B) :
    (transportBaseEquivalence e).inverse.IsCocontinuous
      (finiteDomainTopology K B) (finiteDomainTopology K A) :=
  transportBaseFunctor_isCocontinuous e.symm

instance transportBaseEquivalence_inverse_isDenseSubsite
    (e : BoundedAlgEquiv K A B) :
    (transportBaseEquivalence e).inverse.IsDenseSubsite
      (finiteDomainTopology K B) (finiteDomainTopology K A) :=
  (transportBaseEquivalence e).isDenseSubsite_inverse_of_isCocontinuous
    (finiteDomainTopology K A) (finiteDomainTopology K B)

instance transportBaseFunctor_isDenseSubsite (e : BoundedAlgEquiv K A B) :
    (transportBaseFunctor e).IsDenseSubsite
      (finiteDomainTopology K A) (finiteDomainTopology K B) :=
  (transportBaseEquivalence e).isDenseSubsite_functor_of_isCocontinuous
    (finiteDomainTopology K A) (finiteDomainTopology K B)

/-- The actual bounded base equivalence induces an equivalence of sheaves
for the finite full-domain topologies, with arbitrary coefficient category. -/
def transportBaseSheafEquivalence (e : BoundedAlgEquiv K A B)
    (T : Type v) [Category.{w} T] :
    Sheaf (finiteDomainTopology K A) T ≌ Sheaf (finiteDomainTopology K B) T :=
  (transportBaseEquivalence e).sheafCongr
    (finiteDomainTopology K A) (finiteDomainTopology K B) T

@[simp]
theorem transportBaseSheafEquivalence_functor_obj (e : BoundedAlgEquiv K A B)
    {T : Type v} [Category.{w} T] (F : Sheaf (finiteDomainTopology K A) T) :
    ((transportBaseSheafEquivalence e T).functor.obj F).obj =
      (transportBaseFunctor e.symm).op ⋙ F.obj := rfl

@[simp]
theorem transportBaseSheafEquivalence_inverse_obj (e : BoundedAlgEquiv K A B)
    {T : Type v} [Category.{w} T] (F : Sheaf (finiteDomainTopology K B) T) :
    ((transportBaseSheafEquivalence e T).inverse.obj F).obj =
      (transportBaseFunctor e).op ⋙ F.obj := rfl

/-- Base transport retains the entire presheaf of actual presentations
and bounded restrictions. -/
theorem transportBase_boundedPresheaf (e : BoundedAlgEquiv K A B) :
    (transportBaseFunctor e).op ⋙ boundedPresheaf K B = boundedPresheaf K A := rfl

/-- The same equality retains all commutative algebra objects and arrows. -/
theorem transportBase_algebraPresheaf (e : BoundedAlgEquiv K A B) :
    (transportBaseFunctor e).op ⋙ algebraPresheaf K B = algebraPresheaf K A := rfl

/-- The image of the actual stored algebra sheaf is the actual stored
algebra sheaf on the transported site, with identity components. -/
def transportBaseAlgebraSheafIso (e : BoundedAlgEquiv K A B) :
    (transportBaseSheafEquivalence e (CommAlgCat K)).functor.obj
        (algebraSheaf K A) ≅ algebraSheaf K B :=
  ObjectProperty.isoMk _ (Iso.refl _)

@[simp]
theorem transportBaseAlgebraSheafIso_hom_apply (e : BoundedAlgEquiv K A B)
    (U : Domain K B) (a : U.algebra) :
    (transportBaseAlgebraSheafIso e).hom.hom.app (op U) a = a := rfl

@[simp]
theorem transportBaseAlgebraSheafIso_inv_apply (e : BoundedAlgEquiv K A B)
    (U : Domain K B) (a : U.algebra) :
    (transportBaseAlgebraSheafIso e).inv.hom.app (op U) a = a := rfl

/-- The transported restriction map remains the supplied actual bounded
restriction, on every original section. -/
@[simp]
theorem transportBaseAlgebraSheaf_map_apply (e : BoundedAlgEquiv K A B)
    {U V : Domain K B} (f : U ⟶ V) (a : V.algebra) :
    ((transportBaseSheafEquivalence e (CommAlgCat K)).functor.obj
      (algebraSheaf K A)).obj.map f.op a = f.restriction a := rfl

/-- The original base section is transported through the given forward
bounded equivalence before applying the new structural map. -/
@[simp]
theorem transportBaseAlgebraSheafIso_hom_baseMap (e : BoundedAlgEquiv K A B)
    (U : Domain K B) (a : A) :
    (transportBaseAlgebraSheafIso e).hom.hom.app (op U)
        ((transportBase e.symm U).baseMap a) =
      U.baseMap (e a) := rfl

/-- The inverse sheaf equivalence likewise identifies the two original
stored algebra sheaves using identity maps on their retained algebras. -/
def inverseTransportBaseAlgebraSheafIso (e : BoundedAlgEquiv K A B) :
    (transportBaseSheafEquivalence e (CommAlgCat K)).inverse.obj
        (algebraSheaf K B) ≅ algebraSheaf K A :=
  ObjectProperty.isoMk _ (Iso.refl _)

@[simp]
theorem inverseTransportBaseAlgebraSheafIso_hom_apply (e : BoundedAlgEquiv K A B)
    (U : Domain K A) (a : U.algebra) :
    (inverseTransportBaseAlgebraSheafIso e).hom.hom.app (op U) a = a := rfl

@[simp]
theorem inverseTransportBaseAlgebraSheafIso_inv_apply (e : BoundedAlgEquiv K A B)
    (U : Domain K A) (a : U.algebra) :
    (inverseTransportBaseAlgebraSheafIso e).inv.hom.app (op U) a = a := rfl

@[simp]
theorem inverseTransportBaseAlgebraSheaf_map_apply (e : BoundedAlgEquiv K A B)
    {U V : Domain K A} (f : U ⟶ V) (a : V.algebra) :
    ((transportBaseSheafEquivalence e (CommAlgCat K)).inverse.obj
      (algebraSheaf K B)).obj.map f.op a = f.restriction a := rfl

/-- In the inverse direction the structural section uses precisely the
given inverse bounded base map. -/
@[simp]
theorem inverseTransportBaseAlgebraSheafIso_hom_baseMap
    (e : BoundedAlgEquiv K A B) (U : Domain K A) (b : B) :
    (inverseTransportBaseAlgebraSheafIso e).hom.hom.app (op U)
        ((transportBase e U).baseMap b) =
      U.baseMap (e.symm b) := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
