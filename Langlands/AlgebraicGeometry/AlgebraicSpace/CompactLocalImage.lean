import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenChartUnion
import Langlands.AlgebraicGeometry.AlgebraicSpace.RelativeHelpers

/-! # Compact representations of local chart images -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.CompactLocalImage

variable {S : Scheme.{u}} {F : Presheaf S}

/-- A subfunctor is represented by an actual compact scheme over the fixed base. -/
def HasCompactRepresentation (A : Subfunctor F) : Prop :=
  ∃ W : Over S, CompactSpace W.left ∧
    Nonempty ((schemeYoneda S).obj W ≅ A.toFunctor)

theorem localClosure_mono {A B : Subfunctor F} (h : A ≤ B) :
    A.sheafify (fppfTopology S) ≤ B.sheafify (fppfTopology S) := by
  intro T x hx
  exact (fppfTopology S).superset_covering (fun U f hf => h _ hf) hx

/-- Closing either summand before taking a local union does not change it. -/
theorem sheafify_sup_sheafify (hF : Presheaf.IsSheaf (fppfTopology S) F)
    (A B : Subfunctor F) :
    (A ⊔ B.sheafify (fppfTopology S)).sheafify (fppfTopology S) =
      (A ⊔ B).sheafify (fppfTopology S) := by
  have hF' := (CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).mp hF
  apply le_antisymm
  · have h : A ⊔ B.sheafify (fppfTopology S) ≤
        (A ⊔ B).sheafify (fppfTopology S) :=
      sup_le (le_sup_left.trans ((A ⊔ B).le_sheafify _))
        (localClosure_mono le_sup_right)
    exact (localClosure_mono h).trans_eq
      ((A ⊔ B).sheafify_sheafify hF')
  · exact localClosure_mono
      (sup_le le_sup_left ((B.le_sheafify _).trans le_sup_right))

/-- An open chart with compact source represents its own local image. -/
theorem of_open_chart {V : Over S} [CompactSpace V.left]
    (a : (schemeYoneda S).obj V ⟶ F) (ha : IsOpenImmersion a) :
    HasCompactRepresentation
      ((Subfunctor.range a).sheafify (fppfTopology S)) := by
  let := SliceOpenGluing.open_mono ha
  have hr : Subfunctor.range a =
      (Subfunctor.range a).sheafify (fppfTopology S) := by
    apply le_antisymm ((Subfunctor.range a).le_sheafify _)
    intro T x hx
    exact OpenSubfunctorImages.mem_of_coveringSieve
      (OpenSubfunctorLifting.range_open a ha) x hx
  exact ⟨V, inferInstance,
    ⟨asIso (Subfunctor.toRange a) ≪≫
      eqToIso (congrArg Subfunctor.toFunctor hr)⟩⟩

/-- The local union of a compact open chart and a compact represented etale
image is again represented by a compact scheme. -/
theorem of_union {V D : Over S} [CompactSpace V.left]
    (hF : Presheaf.IsSheaf (fppfTopology S) F)
    (a : (schemeYoneda S).obj V ⟶ F) (ha : IsOpenImmersion a)
    (c : (schemeYoneda S).obj D ⟶ F) (hc : IsEtale c)
    (hC : HasCompactRepresentation
      ((Subfunctor.range c).sheafify (fppfTopology S))) :
    HasCompactRepresentation
      ((Subfunctor.range a ⊔ Subfunctor.range c).sheafify (fppfTopology S)) := by
  obtain ⟨W, hW, ⟨e⟩⟩ := hC
  let := hW
  let C := (Subfunctor.range c).sheafify (fppfTopology S)
  let b : (schemeYoneda S).obj W ⟶ F := e.hom ≫ C.ι
  have hb : IsOpenImmersion b :=
    IsOpenImmersion.iso_comp e
      (OpenSubfunctorImages.sheafify_range_open c hc)
  have hr : Subfunctor.range b = C := by
    change Subfunctor.range (e.hom ≫ C.ι) = C
    rw [Subfunctor.range_comp e.hom C.ι, Subfunctor.range_eq_top e.hom,
      Subfunctor.image_top, Subfunctor.range_ι]
  let U : ULift.{u} Bool → Over S := fun i =>
    match i.down with | false => V | true => W
  let q : ∀ i, (schemeYoneda S).obj (U i) ⟶ F
    | ⟨false⟩ => a | ⟨true⟩ => b
  have hq : ∀ i, IsOpenImmersion (q i) := by
    rintro ⟨i⟩
    cases i
    · exact ha
    · exact hb
  let : ∀ i, CompactSpace (U i).left := by
    rintro ⟨i⟩
    cases i <;> infer_instance
  have heq : OpenChartUnion.union q =
      (Subfunctor.range a ⊔ Subfunctor.range c).sheafify (fppfTopology S) := by
    rw [OpenChartUnion.union_eq_sheafify_iSup]
    have hs : (⨆ i, Subfunctor.range (q i)) =
        Subfunctor.range a ⊔ Subfunctor.range b := by
      apply le_antisymm
      · apply iSup_le
        rintro ⟨i⟩
        cases i
        · exact le_sup_left
        · exact le_sup_right
      · exact sup_le (le_iSup (fun i => Subfunctor.range (q i)) ⟨false⟩)
          (le_iSup (fun i => Subfunctor.range (q i)) ⟨true⟩)
    rw [hs, hr]
    exact sheafify_sup_sheafify hF (Subfunctor.range a) (Subfunctor.range c)
  exact ⟨OpenChartUnion.scheme q hq, inferInstance,
    ⟨OpenChartUnion.iso q hF hq ≪≫
      eqToIso (congrArg Subfunctor.toFunctor heq)⟩⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace.CompactLocalImage
