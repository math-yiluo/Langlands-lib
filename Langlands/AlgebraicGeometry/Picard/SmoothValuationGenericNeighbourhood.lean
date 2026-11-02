import Langlands.AlgebraicGeometry.Picard.SmoothValuationGenericChart
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Total neighbourhoods trivializing a generic line bundle -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.Picard

/-- An actual total open neighbourhood and a trivialization over its inverse
image under the given map. -/
structure GenericTrivializingNeighbourhood {X Y : Scheme.{u}} (q : Y ⟶ X)
    (D : LineBundle Y) (x : X) where
  neighbourhood : X.Opens
  mem : x ∈ neighbourhood
  trivialization : D.obj.restrict (q ⁻¹ᵁ neighbourhood).ι ≅
    SheafOfModules.unit (q ⁻¹ᵁ neighbourhood).toScheme.ringCatSheaf

/-- Trivializations on inverse images of total open neighbourhoods. -/
def HasGenericTrivializingNeighbourhoods {X Y : Scheme.{u}} (q : Y ⟶ X)
    (D : LineBundle Y) : Prop :=
  ∀ x : X, Nonempty (GenericTrivializingNeighbourhood q D x)

/-- An actual trivialization descends along an isomorphism of schemes. -/
theorem nonempty_trivialization_of_pullback_iso {X Y : Scheme.{u}}
    (e : X ≅ Y) (M : Y.Modules)
    (h : Nonempty ((Scheme.Modules.pullback e.hom).obj M ≅
      SheafOfModules.unit X.ringCatSheaf)) :
    Nonempty (M ≅ SheafOfModules.unit Y.ringCatSheaf) := by
  obtain ⟨a⟩ := h
  exact ⟨((Scheme.Modules.pullbackId Y).app M).symm ≪≫
    ((Scheme.Modules.pullbackCongr e.inv_hom_id).app M).symm ≪≫
      ((Scheme.Modules.pullbackComp e.inv e.hom).app M).symm ≪≫
        (Scheme.Modules.pullback e.inv).mapIso a ≪≫
          Langlands.Scheme.Modules.pullbackUnitIso e.inv⟩

/-- Changing only the generic scheme by an isomorphism preserves the
existence of total trivializing neighbourhoods. -/
theorem hasGenericTrivializingNeighbourhoods_of_iso
    {X Y Y' : Scheme.{u}} (q : Y ⟶ X) (e : Y' ≅ Y) (D : LineBundle Y)
    (h : HasGenericTrivializingNeighbourhoods (e.hom ≫ q)
      ((LineBundle.pullback e.hom).obj D)) :
    HasGenericTrivializingNeighbourhoods q D := by
  intro x
  obtain ⟨a⟩ := h x
  let f := e.hom ∣_ (q ⁻¹ᵁ a.neighbourhood)
  have : IsIso f := inferInstance
  obtain ⟨t⟩ := nonempty_trivialization_of_pullback_iso (asIso f)
    (D.obj.restrict (q ⁻¹ᵁ a.neighbourhood).ι)
    ⟨(restrictPullbackIso e.hom (q ⁻¹ᵁ a.neighbourhood) D.obj).symm ≪≫
      a.trivialization⟩
  exact ⟨⟨a.neighbourhood, a.mem, t⟩⟩

variable {R A : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
  [CommRing A] [Algebra R A] [Algebra.Smooth R A]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The generic tensor spectrum has total principal trivializing
neighbourhoods at every point of the smooth affine total spectrum. -/
theorem hasGenericTrivializingNeighbourhoods_tensorSpec
    (D : LineBundle (Spec (CommRingCat.of (A ⊗[R] K)))) :
    HasGenericTrivializingNeighbourhoods
      (Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] K)))) D := by
  intro x
  obtain ⟨a, ha, ⟨t⟩⟩ := exists_generic_principal_lineBundle_trivialization
    (R := R) (A := A) K x.asIdeal D
  let B : CommRingCat.{u} := .of (A ⊗[R] K)
  let c : B := algebraMap A B a
  let W : (Spec B).Opens := PrimeSpectrum.basicOpen c
  let e := basicOpenIsoSpecAway c
  let f := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away c)))
  have he : e.hom ≫ f = W.ι := basicOpenIsoSpecAway_hom_SpecMap c
  let t' : D.obj.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf :=
    (Scheme.Modules.restrictFunctorIsoPullback W.ι).app D.obj ≪≫
      ((Scheme.Modules.pullbackCongr he).app D.obj).symm ≪≫
        ((Scheme.Modules.pullbackComp e.hom f).app D.obj).symm ≪≫
          (Scheme.Modules.pullback e.hom).mapIso t ≪≫
            Langlands.Scheme.Modules.pullbackUnitIso e.hom
  exact ⟨⟨PrimeSpectrum.basicOpen a, ha, t'⟩⟩

/-- The statement uses the actual affine fibre product and its canonical
projection, rather than replacing that projection by a class map. -/
theorem hasGenericTrivializingNeighbourhoods_affinePullback
    (D : LineBundle (pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :
    HasGenericTrivializingNeighbourhoods (pullback.fst _ _) D := by
  apply hasGenericTrivializingNeighbourhoods_of_iso _ (pullbackSpecIso R A K).symm D
  simpa only [Iso.symm_hom, pullbackSpecIso_inv_fst'] using
    hasGenericTrivializingNeighbourhoods_tensorSpec (R := R) (A := A) K
      ((LineBundle.pullback (pullbackSpecIso R A K).inv).obj D)

/-- Choose an actual total neighbourhood and actual generic restriction
trivialization for an affine smooth valuation scheme. -/
def affineGenericTrivializingNeighbourhood
    (D : LineBundle (pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (x : Spec (CommRingCat.of A)) :
    GenericTrivializingNeighbourhood (pullback.fst _ _) D x :=
  (hasGenericTrivializingNeighbourhoods_affinePullback (R := R) (A := A) K D x).some

end Langlands.AlgebraicGeometry.Picard
