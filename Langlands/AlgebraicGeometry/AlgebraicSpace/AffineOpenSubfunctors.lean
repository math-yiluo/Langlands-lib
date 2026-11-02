import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineIntersections
import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubfunctorLifting
import Mathlib.Order.CompleteLattice.Finset

/-! # Finite intersections of affine open subfunctors -/

universe u v

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.AffineOpenSubfunctors

variable {S : Scheme.{u}} {F : Presheaf S}

/-- An open subfunctor represented by an actual affine scheme over the base. -/
def IsAffineOpen (A : Subfunctor F) : Prop :=
  IsOpenImmersion A.ι ∧
    ∃ V : Over S, IsAffine V.left ∧ Nonempty ((schemeYoneda S).obj V ≅ A.toFunctor)

private abbrev openProperty : MorphismProperty (Presheaf S) :=
  (SliceOpenGluing.openProperty S).relative (schemeYoneda S)

/-- Scheme Yoneda carries a scheme open immersion to a representable open
immersion of presheaves. -/
theorem isOpenImmersion_schemeYoneda_map {V W : Over S} (p : V ⟶ W)
    (hp : _root_.AlgebraicGeometry.IsOpenImmersion p.left) :
    IsOpenImmersion ((schemeYoneda S).map p) := by
  apply MorphismProperty.relative.of_exists
  intro T g
  obtain ⟨g, rfl⟩ := (schemeYoneda S).map_surjective g
  let h := IsPullback.of_hasPullback p g
  exact ⟨_, _, _, h.map (schemeYoneda S),
    MorphismProperty.of_isPullback (P := @_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      (h.map (Over.forget S)) hp⟩

/-- Pulling a subfunctor back by an isomorphism changes its parametrization
by an actual natural isomorphism. -/
theorem isIso_fromPreimage {G : Presheaf S} (e : F ≅ G) (A : Subfunctor G) :
    IsIso (A.fromPreimage e.hom) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro T
  rw [isIso_iff_bijective]
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply (CategoryTheory.mono_iff_injective (e.hom.app T)).mp inferInstance
    exact congrArg Subtype.val hxy
  · rintro ⟨x, hx⟩
    refine ⟨⟨e.inv.app T x, ?_⟩, ?_⟩
    · change e.hom.app T (e.inv.app T x) ∈ A.obj T
      simpa using hx
    · apply Subtype.ext
      exact e.inv_hom_id_app_apply T x

/-- An affine open remains affine open after a change of coordinates in
the ambient presheaf. No affineness assumption on the base is needed. -/
theorem IsAffineOpen.preimage_iso {G : Presheaf S} (e : F ≅ G)
    {A : Subfunctor G} (hA : IsAffineOpen A) :
    IsAffineOpen (A.preimage e.hom) := by
  obtain ⟨hA, V, hV, ⟨eV⟩⟩ := hA
  let b := A.fromPreimage e.hom
  have : IsIso b := isIso_fromPreimage e A
  have hb : b ≫ A.ι = (A.preimage e.hom).ι ≫ e.hom := A.fromPreimage_ι e.hom
  refine ⟨?_, V, hV, ⟨eV ≪≫ (asIso b).symm⟩⟩
  apply (openProperty.cancel_right_of_respectsIso (A.preimage e.hom).ι e.hom).mp
  rw [← hb]
  exact (openProperty.cancel_left_of_respectsIso b A.ι).mpr hA

/-- The range of the map from a represented intersection is the intersection
of the two chart ranges. -/
theorem range_intersection
    {V V1 V2 : Over S} (a1 : (schemeYoneda S).obj V1 ⟶ F)
    (a2 : (schemeYoneda S).obj V2 ⟶ F) (p1 : V ⟶ V1) (p2 : V ⟶ V2)
    (h : IsPullback ((schemeYoneda S).map p1) ((schemeYoneda S).map p2) a1 a2) :
    Subfunctor.range ((schemeYoneda S).map p1 ≫ a1) =
      Subfunctor.range a1 ⊓ Subfunctor.range a2 := by
  rw [Subfunctor.range_comp,
    OpenSubfunctorLifting.range_eq_preimage_of_isPullback h.flip]
  ext T x
  change x ∈ (a1.app T) '' ((a1.app T) ⁻¹' Set.range (a2.app T)) ↔
    x ∈ Set.range (a1.app T) ∩ Set.range (a2.app T)
  rw [Set.image_preimage_eq_inter_range, Set.inter_comm]

/-- The intersection of two affine open subfunctors is affine open if the
ambient presheaf has closed diagonal and the base is affine. -/
theorem IsAffineOpen.inf [IsAffine S]
    (hF : IsClosedImmersion (Limits.diag F))
    {A B : Subfunctor F} (hA : IsAffineOpen A) (hB : IsAffineOpen B) :
    IsAffineOpen (A ⊓ B) := by
  obtain ⟨hA, V1, hV1, ⟨e1⟩⟩ := hA
  obtain ⟨hB, V2, hV2, ⟨e2⟩⟩ := hB
  let : IsAffine V1.left := hV1
  let : IsAffine V2.left := hV2
  let a1 := e1.hom ≫ A.ι
  let a2 := e2.hom ≫ B.ι
  have ha1 : IsOpenImmersion a1 :=
    (openProperty.cancel_left_of_respectsIso e1.hom A.ι).mpr hA
  have ha2 : IsOpenImmersion a2 :=
    (openProperty.cancel_left_of_respectsIso e2.hom B.ι).mpr hB
  obtain ⟨V, p1, p2, hV, hp1, _, h⟩ :=
    exists_affine_open_intersection hF a1 ha1 a2 ha2
  let a := (schemeYoneda S).map p1 ≫ a1
  have hpa : IsOpenImmersion ((schemeYoneda S).map p1) :=
    isOpenImmersion_schemeYoneda_map p1 hp1
  have ha : IsOpenImmersion a := openProperty.comp_mem _ _ hpa ha1
  have hr1 : Subfunctor.range a1 = A := by
    simp [a1, Subfunctor.range_comp, Subfunctor.range_eq_top, Subfunctor.image_top]
  have hr2 : Subfunctor.range a2 = B := by
    simp [a2, Subfunctor.range_comp, Subfunctor.range_eq_top, Subfunctor.image_top]
  have hr : Subfunctor.range a = A ⊓ B := by
    rw [range_intersection a1 a2 p1 p2 h, hr1, hr2]
  let b := Subfunctor.lift a (le_of_eq hr)
  have hb : b ≫ (A ⊓ B).ι = a := Subfunctor.lift_ι _ _
  let : Mono a := SliceOpenGluing.open_mono ha
  have : Mono b := mono_of_mono_fac hb
  have : IsIso b := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro T
    rw [isIso_iff_bijective]
    constructor
    · exact (CategoryTheory.mono_iff_injective (b.app T)).mp inferInstance
    · rintro ⟨x, hx⟩
      have hx' : x ∈ (Subfunctor.range a).obj T := by rwa [hr]
      obtain ⟨y, hy⟩ := hx'
      exact ⟨y, Subtype.ext hy⟩
  refine ⟨?_, V, hV, ⟨asIso b⟩⟩
  apply (openProperty.cancel_left_of_respectsIso b (A ⊓ B).ι).mp
  rwa [hb]

/-- A nonempty finite intersection of affine open subfunctors is affine open. -/
theorem isAffineOpen_biInf_finset [IsAffine S]
    (hF : IsClosedImmersion (Limits.diag F))
    {I : Type v} (s : Finset I) (hs : s.Nonempty) (A : I → Subfunctor F)
    (hA : ∀ i ∈ s, IsAffineOpen (A i)) :
    IsAffineOpen (⨅ i ∈ s, A i) := by
  classical
  revert hs hA
  induction s using Finset.induction_on with
  | empty => intro hs; exact (Finset.not_nonempty_empty hs).elim
  | @insert i s hi ih =>
    intro _ hA
    obtain rfl | hs := s.eq_empty_or_nonempty
    · simpa using hA i (by simp)
    · rw [Finset.iInf_insert]
      exact (hA i (by simp)).inf hF
        (ih hs (fun j hj => hA j (Finset.mem_insert_of_mem hj)))

/-- The nonempty finite-type-indexed intersection is affine open, with no
restriction on the universe of the index type. -/
theorem isAffineOpen_iInf [IsAffine S]
    (hF : IsClosedImmersion (Limits.diag F))
    {I : Type v} [Finite I] [Nonempty I] (A : I → Subfunctor F)
    (hA : ∀ i, IsAffineOpen (A i)) :
    IsAffineOpen (⨅ i, A i) := by
  classical
  let := Fintype.ofFinite I
  simpa using isAffineOpen_biInf_finset hF Finset.univ Finset.univ_nonempty A
    (fun i _ => hA i)

/-- Intersecting finitely many coordinate translates of an affine open
produces an affine open in a presheaf with closed diagonal over an affine base. -/
theorem IsAffineOpen.iInf_preimage_iso [IsAffine S]
    (hF : IsClosedImmersion (Limits.diag F))
    {I : Type v} [Finite I] [Nonempty I] (e : I → (F ≅ F))
    {A : Subfunctor F} (hA : IsAffineOpen A) :
    IsAffineOpen (⨅ i, A.preimage (e i).hom) :=
  isAffineOpen_iInf hF _ (fun i => hA.preimage_iso (e i))

end Langlands.AlgebraicGeometry.AlgebraicSpace.AffineOpenSubfunctors
