import Langlands.AlgebraicGeometry.AlgebraicSpace.FieldSchemePoints

/-! # Covering an atlas by checking closed points -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace OpenSubfunctorPoints

variable {S : Scheme.{u}} {F : Presheaf S} {A : Subfunctor F}

/-- The value of a section at a residue-field point belongs to an open
subfunctor exactly when that point lies in its represented open pullback. -/
theorem mem_residueField_iff_mem_range (hA : IsOpenImmersion A.ι)
    {T : Over S} (s : F.obj (op T)) (x : T.left) :
    F.map (residueFieldPoint T x).op s ∈ A.obj (op (residueFieldTest T x)) ↔
      x ∈ Set.range (hA.rep.snd (uliftYonedaEquiv.symm s)).left := by
  rw [mem_map_iff_range_subset hA s (residueFieldPoint T x)]
  constructor
  · intro h
    apply h
    exact ⟨(default : Spec (T.left.residueField x)), T.left.fromSpecResidueField_apply x _⟩
  · rintro h _ ⟨z, rfl⟩
    exact (T.left.fromSpecResidueField_apply x z).symm ▸ h

/-- Residue-field membership in an open subfunctor is stable under
generization of the point of the test scheme. -/
theorem mem_residueField_of_specializes (hA : IsOpenImmersion A.ι)
    {T : Over S} (s : F.obj (op T)) {x y : T.left} (hxy : x ⤳ y)
    (hy : F.map (residueFieldPoint T y).op s ∈
      A.obj (op (residueFieldTest T y))) :
    F.map (residueFieldPoint T x).op s ∈
      A.obj (op (residueFieldTest T x)) := by
  rw [mem_residueField_iff_mem_range hA] at hy ⊢
  let q := hA.rep.snd (uliftYonedaEquiv.symm s)
  let : _root_.AlgebraicGeometry.IsOpenImmersion q.left :=
    hA.property_snd (uliftYonedaEquiv.symm s)
  exact hxy.mem_open q.left.isOpenEmbedding.isOpen_range hy

/-- Over a field, a section of a locally finite type test scheme belongs
to an open subfunctor if and only if all its closed-point values do. -/
theorem mem_iff_closed_residueField {k : Type u} [Field k]
    {F : Presheaf (Spec (CommRingCat.of k))} {A : Subfunctor F}
    (hA : IsOpenImmersion A.ι)
    {T : Over (Spec (CommRingCat.of k))} [LocallyOfFiniteType T.hom]
    (s : F.obj (op T)) :
    s ∈ A.obj (op T) ↔
      ∀ x : T.left, IsClosed ({x} : Set T.left) →
        F.map (residueFieldPoint T x).op s ∈
          A.obj (op (residueFieldTest T x)) := by
  constructor
  · intro hs x _
    exact A.map _ hs
  · intro hs
    apply (mem_iff_residueField hA s).mpr
    intro x
    obtain ⟨y, hy, hxy⟩ := FieldSchemePoints.exists_closed_specialization T.hom x
    exact mem_residueField_of_specializes hA s hxy (hs y hy)

end OpenSubfunctorPoints

namespace OpenChartCoverage

variable {k : Type u} [Field k] {F : Presheaf (Spec (CommRingCat.of k))}

/-- Open charts covering the closed-point values of a locally finite type
scheme section cover all its residue-field values. -/
theorem residueField_coverage_of_closed
    {U : Over (Spec (CommRingCat.of k))} [LocallyOfFiniteType U.hom]
    (a : (schemeYoneda _).obj U ⟶ F)
    {I : Type u} {V : I → Over (Spec (CommRingCat.of k))}
    (b : ∀ i, (schemeYoneda _).obj (V i) ⟶ F)
    (hb : ∀ i, IsOpenImmersion (b i))
    (hcov : ∀ x : U.left, IsClosed ({x} : Set U.left) → ∃ i,
      F.map (OpenSubfunctorPoints.residueFieldPoint U x).op (uliftYonedaEquiv a) ∈
        (Subfunctor.range (b i)).obj
          (op (OpenSubfunctorPoints.residueFieldTest U x))) :
    ∀ x : U.left, ∃ i,
      F.map (OpenSubfunctorPoints.residueFieldPoint U x).op (uliftYonedaEquiv a) ∈
        (Subfunctor.range (b i)).obj
          (op (OpenSubfunctorPoints.residueFieldTest U x)) := by
  intro x
  obtain ⟨y, hy, hxy⟩ := FieldSchemePoints.exists_closed_specialization U.hom x
  obtain ⟨i, hi⟩ := hcov y hy
  exact ⟨i, OpenSubfunctorPoints.mem_residueField_of_specializes
    (OpenSubfunctorLifting.range_open (b i) (hb i)) (uliftYonedaEquiv a) hxy hi⟩

/-- Closed-point coverage on a locally finite type etale surjective atlas
gives the locally surjective family required for gluing open scheme charts. -/
theorem isLocallySurjective_sigma_of_closed_residueField
    {U : Over (Spec (CommRingCat.of k))} [LocallyOfFiniteType U.hom]
    (a : (schemeYoneda _).obj U ⟶ F)
    (ha : IsEtale a) (hs : IsSurjective a)
    {I : Type u} {V : I → Over (Spec (CommRingCat.of k))}
    (b : ∀ i, (schemeYoneda _).obj (V i) ⟶ F)
    (hb : ∀ i, IsOpenImmersion (b i))
    (hcov : ∀ x : U.left, IsClosed ({x} : Set U.left) → ∃ i,
      F.map (OpenSubfunctorPoints.residueFieldPoint U x).op (uliftYonedaEquiv a) ∈
        (Subfunctor.range (b i)).obj
          (op (OpenSubfunctorPoints.residueFieldTest U x))) :
    CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology _) (Sigma.desc b) :=
  isLocallySurjective_sigma_of_residueField a ha hs b hb
    (residueField_coverage_of_closed a b hb hcov)

end OpenChartCoverage

end Langlands.AlgebraicGeometry.AlgebraicSpace
