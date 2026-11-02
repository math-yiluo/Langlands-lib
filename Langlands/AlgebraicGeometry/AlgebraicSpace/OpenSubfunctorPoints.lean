import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubfunctorLifting
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Testing membership in open subfunctors on scheme points -/

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubfunctorPoints

variable {S : Scheme.{u}} {F : Presheaf S} {A : Subfunctor F}

/-- Membership after a scheme map is equivalent to containment in the
topological range of the represented open pullback. -/
theorem mem_app_iff_range_subset (hA : IsOpenImmersion A.ι)
    {T U : Over S} (g : (schemeYoneda S).obj T ⟶ F) (f : U ⟶ T) :
    g.app (op U) (ULift.up f) ∈ A.obj (op U) ↔
      Set.range f.left ⊆ Set.range (hA.rep.snd g).left := by
  let q := hA.rep.snd g
  let : _root_.AlgebraicGeometry.IsOpenImmersion q.left := hA.property_snd g
  have hr := OpenSubfunctorLifting.range_eq_preimage_of_isPullback (hA.rep.isPullback g)
  rw [Subfunctor.range_ι] at hr
  have he : g.app (op U) (ULift.up f) ∈ A.obj (op U) ↔
      ULift.up f ∈ (Subfunctor.range ((schemeYoneda S).map q)).obj (op U) := by
    rw [hr]
    rfl
  rw [he, ← OpenSubfunctorLifting.factors_through_open_iff q f]
  constructor
  · rintro ⟨⟨b⟩, hb⟩
    exact ⟨b, ULift.up_injective hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨ULift.up b, congrArg ULift.up hb⟩

/-- The section version of the represented-open range criterion. -/
theorem mem_map_iff_range_subset (hA : IsOpenImmersion A.ι)
    {T U : Over S} (x : F.obj (op T)) (f : U ⟶ T) :
    F.map f.op x ∈ A.obj (op U) ↔
      Set.range f.left ⊆ Set.range (hA.rep.snd (uliftYonedaEquiv.symm x)).left := by
  simpa using mem_app_iff_range_subset hA (uliftYonedaEquiv.symm x) f

/-- A jointly surjective family of arbitrary scheme maps detects
membership in a representable open subfunctor. -/
theorem mem_of_jointly_surjective (hA : IsOpenImmersion A.ι)
    {T : Over S} {I : Type v} {U : I → Over S} (f : ∀ i, U i ⟶ T)
    (hf : ∀ t : T.left, ∃ i, t ∈ Set.range (f i).left)
    (x : F.obj (op T))
    (hx : ∀ i, F.map (f i).op x ∈ A.obj (op (U i))) :
    x ∈ A.obj (op T) := by
  suffices hx' : F.map (𝟙 T).op x ∈ A.obj (op T) by simpa using hx'
  apply (mem_map_iff_range_subset hA x (𝟙 T)).mpr
  rintro t _
  obtain ⟨i, hi⟩ := hf t
  exact (mem_map_iff_range_subset hA x (f i)).mp (hx i) hi

/-- Membership descends along any surjective morphism of test schemes. -/
theorem mem_of_surjective (hA : IsOpenImmersion A.ι)
    {T U : Over S} (f : U ⟶ T) [_root_.AlgebraicGeometry.Surjective f.left]
    (x : F.obj (op T)) (hx : F.map f.op x ∈ A.obj (op U)) :
    x ∈ A.obj (op T) := by
  apply mem_of_jointly_surjective hA (fun _ : Unit => f) ?_ x (fun _ => hx)
  intro t
  exact ⟨(), f.left.surjective t⟩

/-- Pullback along a surjective scheme map preserves and reflects
membership in an open subfunctor. -/
theorem mem_iff_of_surjective (hA : IsOpenImmersion A.ι)
    {T U : Over S} (f : U ⟶ T) [_root_.AlgebraicGeometry.Surjective f.left]
    (x : F.obj (op T)) :
    x ∈ A.obj (op T) ↔ F.map f.op x ∈ A.obj (op U) :=
  ⟨fun hx => A.map f.op hx, mem_of_surjective hA f x⟩

/-- The spectrum of a test scheme's residue field, as a scheme over the
fixed base. -/
def residueFieldTest (T : Over S) (t : T.left) : Over S :=
  Over.mk (T.left.fromSpecResidueField t ≫ T.hom)

/-- The canonical residue-field point is a morphism over the fixed base. -/
def residueFieldPoint (T : Over S) (t : T.left) : residueFieldTest T t ⟶ T :=
  Over.homMk (T.left.fromSpecResidueField t)

/-- Membership in an open subfunctor is detected at every residue-field
point of the test scheme. -/
theorem mem_iff_residueField (hA : IsOpenImmersion A.ι)
    {T : Over S} (x : F.obj (op T)) :
    x ∈ A.obj (op T) ↔
      ∀ t : T.left, F.map (residueFieldPoint T t).op x ∈
        A.obj (op (residueFieldTest T t)) := by
  constructor
  · intro hx t
    exact A.map _ hx
  · intro hx
    apply mem_of_jointly_surjective hA (residueFieldPoint T) ?_ x hx
    intro t
    refine ⟨t, (default : Spec (T.left.residueField t)), ?_⟩
    exact T.left.fromSpecResidueField_apply t _

/-- It is enough to check membership after every field-valued point of
the test scheme, with the field in the scheme universe. -/
theorem mem_of_field_tests (hA : IsOpenImmersion A.ι)
    {T : Over S} (x : F.obj (op T))
    (hx : ∀ (K : Type u) [Field K] (f : Spec (CommRingCat.of K) ⟶ T.left),
      F.map (Over.homMk f : Over.mk (f ≫ T.hom) ⟶ T).op x ∈
        A.obj (op (Over.mk (f ≫ T.hom)))) :
    x ∈ A.obj (op T) := by
  apply (mem_iff_residueField hA x).mpr
  intro t
  exact hx (T.left.residueField t) (T.left.fromSpecResidueField t)

/-- Two representable open subfunctors agree if they agree on every
field-valued test scheme over the base. -/
theorem eq_of_field_tests {B : Subfunctor F}
    (hA : IsOpenImmersion A.ι) (hB : IsOpenImmersion B.ι)
    (h : ∀ (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ S),
      A.obj (op (Over.mk s)) = B.obj (op (Over.mk s))) :
    A = B := by
  ext T x
  rw [mem_iff_residueField hA x, mem_iff_residueField hB x]
  apply forall_congr'
  intro t
  rw [show A.obj (op (residueFieldTest T.unop t)) =
      B.obj (op (residueFieldTest T.unop t)) from
    h (T.unop.left.residueField t)
      (T.unop.left.fromSpecResidueField t ≫ T.unop.hom)]

/-- Invariance along fibres of a natural transformation can be checked
only on field-valued test schemes when the subfunctor is open. -/
theorem invariant_of_field_tests (hA : IsOpenImmersion A.ι)
    {G : Presheaf S} (π : F ⟶ G)
    (h : ∀ (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ S)
      (x y : F.obj (op (Over.mk s))),
      π.app _ x = π.app _ y →
        (x ∈ A.obj (op (Over.mk s)) ↔ y ∈ A.obj (op (Over.mk s)))) :
    ∀ (T : (Over S)ᵒᵖ) (x y : F.obj T), π.app T x = π.app T y →
      (x ∈ A.obj T ↔ y ∈ A.obj T) := by
  intro T x y hxy
  rw [mem_iff_residueField hA x, mem_iff_residueField hA y]
  apply forall_congr'
  intro t
  apply h (T.unop.left.residueField t)
    (T.unop.left.fromSpecResidueField t ≫ T.unop.hom)
  exact (π.naturality_apply (residueFieldPoint T.unop t).op x).trans
    ((congrArg (fun z => G.map (residueFieldPoint T.unop t).op z) hxy).trans
      (π.naturality_apply (residueFieldPoint T.unop t).op y).symm)

end Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubfunctorPoints
