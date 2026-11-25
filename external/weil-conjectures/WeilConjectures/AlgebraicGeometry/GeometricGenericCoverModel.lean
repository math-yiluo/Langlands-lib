/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.GenericFibreClosedAvoidance
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import WeilConjectures.AlgebraicGeometry.GenericFibreClosedCoverSpread
import WeilConjectures.AlgebraicGeometry.CompatibleEtaleGenericFibreModel
import WeilConjectures.AlgebraicGeometry.ClosedFamilyGeometricFibreShrink

/-! # A closed geometric cover on an étale model

Source: Stacks Project, Tags 0551, 054Y, 0559 and 054W.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Topology
namespace AlgebraicGeometry

/-- The empty-index case of the geometric generic cover construction: if the empty family
covers the generic fibre after the finite étale extension, then an open neighbourhood of the
generic point of `S` has empty preimage in `X`.

Source: Stacks Project, Tag 054W. -/
private theorem exists_generic_cover_model_of_isEmpty {X S : Scheme.{u}}
    [IrreducibleSpace S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    {L : Type u} [Field L]
    (yη : Spec (CommRingCat.of L) ⟶
      Spec (CommRingCat.of (S.residueField (genericPoint S))))
    {I : Type u} [IsEmpty I]
    (A : I → Set ↥(pullback (f.fiberToSpecResidueField (genericPoint S)) yη))
    (hcover : (⋃ i, A i) = Set.univ) :
    ∃ (T : Scheme.{u}) (g : T ⟶ S) (η : T), Etale g ∧ IsGenericPoint η Set.univ ∧
      g η = genericPoint S ∧ IsEmpty ↥(pullback f g) := by
  classical
  have hempty : IsEmpty ↥(pullback (f.fiberToSpecResidueField (genericPoint S)) yη) := by
    constructor
    intro x
    have hx : x ∈ ⋃ i, A i := hcover ▸ Set.mem_univ x
    simp at hx
  have hgeneric : f ⁻¹' {genericPoint S} ⊆ (∅ : Set X) ∪ ∅ := by
    intro x hx
    let a := (f.fiberHomeo (genericPoint S)).symm ⟨x, hx⟩
    have ha : a ∈ Set.range (pullback.fst
        (f.fiberToSpecResidueField (genericPoint S)) yη) := by
      rw [Scheme.Pullback.range_fst]
      exact Function.surjective_to_subsingleton yη _
    obtain ⟨b, _⟩ := ha
    exact (hempty.false b).elim
  obtain ⟨V, hV, hηV, hvanish⟩ := exists_open_generic_fibre_closed_avoidance
    f (genericPoint S) Set.univ isClosed_univ (by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      simpa using hgeneric hx.1)
  let U : S.Opens := ⟨V, hV⟩
  let η : U.toScheme := ⟨genericPoint S, hηV⟩
  have hη : IsGenericPoint η Set.univ := by
    apply isGenericPoint_iff_specializes.mpr
    intro t
    simp only [Set.mem_univ, iff_true]
    exact (subtype_specializes_iff _ _).mpr (genericPoint_specializes t.1)
  have hemptyU : IsEmpty ↥(pullback f U.ι) := by
    constructor
    intro x
    have hx : f (pullback.fst f U.ι x) ∈ V := by
      have he := congrArg (fun k : pullback f U.ι ⟶ S ↦ k x) pullback.condition
      simpa only [Scheme.Hom.comp_apply] using he ▸ (pullback.snd f U.ι x).2
    exact Set.disjoint_left.mp hvanish
      ⟨hx, by rw [genericPoint_closure]; trivial⟩ (Set.mem_univ _)
  exact ⟨U.toScheme, U.ι, η, inferInstance, hη, rfl, hemptyU⟩

private theorem geometric_fibre_subset_isIrreducible_of_isPullback
    {P' P T' T : Scheme.{u}} {r : P' ⟶ P} {q : P' ⟶ T'}
    {p : P ⟶ T} {v : T' ⟶ T} (H : IsPullback r q p v) (C : Set P) (t : T')
    (hgeom : ∀ (E : Type u) (_ : Field E)
      (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of (T.residueField (v t)))),
      IsIrreducible ((pullback.fst (p.fiberToSpecResidueField (v t)) z ≫
        p.fiberι (v t)) ⁻¹' C)) :
    ∀ (E : Type u) (_ : Field E)
      (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of (T'.residueField t))),
      IsIrreducible ((pullback.fst (q.fiberToSpecResidueField t) z ≫
        q.fiberι t) ⁻¹' (r ⁻¹' C)) := by
  intro E hE z
  let c := Spec.map (v.residueFieldMap t)
  let b : q.fiber t ⟶ p.fiber (v t) :=
    pullback.map q (T'.fromSpecResidueField t) p (T.fromSpecResidueField (v t))
      r c v H.w.symm (by simp [c])
  have Hb : IsPullback b (q.fiberToSpecResidueField t)
      (p.fiberToSpecResidueField (v t)) c :=
    isPullback_fiberToSpecResidueField_of_isPullback H t
  have Hz := (IsPullback.of_hasPullback (q.fiberToSpecResidueField t) z).paste_horiz Hb
  let e := Hz.isoPullback
  have hb : b ≫ p.fiberι (v t) = q.fiberι t ≫ r := by
    simp [b, Scheme.Hom.fiberι]
  have he : e.hom ≫ pullback.fst (p.fiberToSpecResidueField (v t)) (z ≫ c) ≫
      p.fiberι (v t) =
      pullback.fst (q.fiberToSpecResidueField t) z ≫ q.fiberι t ≫ r := by
    rw [← Category.assoc, Hz.isoPullback_hom_fst, Category.assoc, hb]
  have heq : (pullback.fst (q.fiberToSpecResidueField t) z ≫
      q.fiberι t) ⁻¹' (r ⁻¹' C) =
      e.hom ⁻¹' ((pullback.fst (p.fiberToSpecResidueField (v t)) (z ≫ c) ≫
        p.fiberι (v t)) ⁻¹' C) := by
    ext x
    change r (q.fiberι t ((pullback.fst _ z) x)) ∈ C ↔
      p.fiberι (v t) ((pullback.fst _ (z ≫ c)) (e.hom x)) ∈ C
    exact (congrArg
      (fun k : pullback (q.fiberToSpecResidueField t) z ⟶ P ↦ k x ∈ C) he.symm).to_iff
  rw [heq]
  apply (hgeom E hE (z ≫ c)).preimage e.hom.isOpenEmbedding
  rw [e.hom.surjective.range_eq, Set.inter_univ]
  exact (hgeom E hE (z ≫ c)).nonempty

/-- Spread the closed cover and geometric irreducibility, before spreading intersections.

Source: Stacks Project, Tag 055G, the model and closure construction preceding the
intersection-image argument; Tags 0551, 054Y, 0559 and 054W.
Proof: on an affine neighbourhood of the generic point, realize the supplied finite
separable extension by the monic-polynomial construction of Tag 0551. Localize away
from the image of the non-étale locus. The resulting model has one generic point
with residue field L. Form the pullback of X and take closures of the supplied A_i.
On the reduction of the model their reduced closed subschemes have the given generic
fibres. Tag 054Y shrinks the base so their union covers, and Tag 0559, once for each
index, shrinks it so their fibres are geometrically irreducible and nonempty.
Represent this open in the original model using the reduction homeomorphism, and
restrict the model to it. The resulting map to S is étale; its generic point still
maps to the original generic point. The pulled-back closed subsets cover the total
space and have the asserted geometrically irreducible traces on all field fibres.
Their generic traces identify with A_i, giving the generic intersection implication.
For an empty index type use Tag 054W to make the whole pulled-back total space empty;
the geometric irreducibility and intersection assertions are then vacuous.
In Lean the empty-index case is the private lemma above. In the nonempty-index case,
the compatible étale model theorem supplies the embedding a and its field-base-change
identifications. Set C_i = closure (a '' A_i). The
embedding and closedness of A_i prove a⁻¹(C_i) = A_i. Use the closed-family shrinking
theorem and the existing closed-cover shrinking theorem; intersect their opens.
Pullback pasting proves the field-fibre assertion on this restricted model, and the
range formula for pullback.map lifts every given generic intersection.
No persistence of intersections at nongeneric points is asserted here.

(blueprint: lem-sbc-geometric-generic-cover-model) -/
theorem exists_geometric_generic_cover_model {X S : Scheme.{u}}
    [IrreducibleSpace S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    {L : Type u} [Field L]
    (yη : Spec (CommRingCat.of L) ⟶
      Spec (CommRingCat.of (S.residueField (genericPoint S))))
    [IsFinite yη] [Etale yη] {I : Type u} [Finite I]
    (A : I → Set ↥(pullback (f.fiberToSpecResidueField (genericPoint S)) yη))
    (hclosed : ∀ i, IsClosed (A i)) (hcover : (⋃ i, A i) = Set.univ)
    (hgeom : ∀ i, ∀ (E : Type u) (_ : Field E)
      (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of L)),
      IsIrreducible ((pullback.fst
        (pullback.snd (f.fiberToSpecResidueField (genericPoint S)) yη) z) ⁻¹' A i)) :
    ∃ (T : Scheme.{u}) (g : T ⟶ S) (η : T)
      (C : I → Set ↥(pullback f g)), Etale g ∧ IsGenericPoint η Set.univ ∧
      g η = genericPoint S ∧ (∀ i, IsClosed (C i)) ∧ (⋃ i, C i) = Set.univ ∧
      (∀ i t, ∀ (E : Type u) (_ : Field E)
        (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of (T.residueField t))),
        IsIrreducible ((pullback.fst
          ((pullback.snd f g).fiberToSpecResidueField t) z ≫
          (pullback.snd f g).fiberι t) ⁻¹' C i)) ∧
      ∀ i j, (A i ∩ A j).Nonempty →
        (C i ∩ C j ∩ (pullback.snd f g) ⁻¹' {η}).Nonempty := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hI =>
    let := hI
    obtain ⟨T, g, η, hg, hη, hgη, hT⟩ :=
      exists_generic_cover_model_of_isEmpty f yη A hcover
    refine ⟨T, g, η, fun _ ↦ ∅, hg, hη, hgη, fun _ ↦ isClosed_empty,
      Set.eq_univ_of_forall fun x ↦ (hT.false x).elim, ?_, ?_⟩
    · intro i
      exact (hI.false i).elim
    · intro i
      exact (hI.false i).elim
  | inr hI =>
    let := hI
    obtain ⟨T, g, η, a, hg, hη, hgη, ha, harange, hcompat⟩ :=
      exists_compatible_etale_generic_fibre_model f yη
    have : Etale g := hg
    let p := pullback.snd f g
    let C : I → Set ↥(pullback f g) := fun i ↦ closure (a '' A i)
    have hCclosed (i : I) : IsClosed (C i) := isClosed_closure
    have htrace (i : I) : a ⁻¹' C i = A i := by
      change a ⁻¹' closure (a '' A i) = A i
      rw [← ha.closure_eq_preimage_closure_image, (hclosed i).closure_eq]
    have hCgeneric : p ⁻¹' {η} ⊆ (⋃ i, C i) ∪ ∅ := by
      intro x hx
      obtain ⟨b, rfl⟩ := harange.symm ▸ hx
      have hb : b ∈ ⋃ i, A i := hcover ▸ Set.mem_univ b
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hb
      exact Or.inl (Set.mem_iUnion.mpr ⟨i, subset_closure ⟨b, hi, rfl⟩⟩)
    have hCgeom : ∀ i, ∀ (E : Type u) (_ : Field E)
        (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of (T.residueField η))),
        IsIrreducible ((pullback.fst (p.fiberToSpecResidueField η) z ≫
          p.fiberι η) ⁻¹' C i) := by
      intro i E hE z
      obtain ⟨zL, e, he⟩ := hcompat E hE z
      have heq : (pullback.fst (p.fiberToSpecResidueField η) z ≫
          p.fiberι η) ⁻¹' C i =
          e.hom ⁻¹' ((pullback.fst
            (pullback.snd (f.fiberToSpecResidueField (genericPoint S)) yη) zL) ⁻¹' A i) := by
        rw [← he]
        ext b
        change a ((pullback.fst _ zL) (e.hom b)) ∈ C i ↔
          (pullback.fst _ zL) (e.hom b) ∈ A i
        exact Set.ext_iff.mp (htrace i) _
      rw [heq]
      apply (hgeom i E hE zL).preimage e.hom.isOpenEmbedding
      rw [e.hom.surjective.range_eq, Set.inter_univ]
      exact (hgeom i E hE zL).nonempty
    obtain ⟨U, hηU, hUgeom⟩ := exists_open_closed_family_geometric_fibre_shrink
      p η hη C hCclosed hCgeom
    obtain ⟨W, hW, hηW, hWcover⟩ := exists_open_generic_fibre_closed_cover
      p η (⋃ i, C i) ∅ (isClosed_iUnion_of_finite hCclosed) isClosed_empty hCgeneric
    let V : T.Opens := U ⊓ ⟨W, hW⟩
    have hηV : η ∈ V := ⟨hηU, hηW⟩
    let ηV : V.toScheme := ⟨η, hηV⟩
    let gV : V.toScheme ⟶ S := V.ι ≫ g
    let r : pullback f gV ⟶ pullback f g :=
      pullback.map f gV f g (𝟙 X) V.ι (𝟙 S) (by simp) (by simp [gV])
    let q := pullback.snd f gV
    have hrp : r ≫ p = q ≫ V.ι := by simp [r, p, q]
    have hηVgeneric : IsGenericPoint ηV Set.univ := by
      apply isGenericPoint_iff_specializes.mpr
      intro t
      simp only [Set.mem_univ, iff_true]
      exact (subtype_specializes_iff _ _).mpr (hη.specializes (Set.mem_univ t.1))
    refine ⟨V.toScheme, gV, ηV, fun i ↦ r ⁻¹' C i, inferInstance,
      hηVgeneric, ?_, fun i ↦ (hCclosed i).preimage r.continuous, ?_, ?_, ?_⟩
    · simpa only [gV, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] using hgη
    · apply Set.eq_univ_of_forall
      intro x
      have hx : p (r x) ∈ W ∩ closure {η} := by
        constructor
        · have he := congrArg (fun k : pullback f gV ⟶ T ↦ k x) hrp
          rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at he
          rw [he]
          exact (q x).2.2
        · rw [hη.def]
          trivial
      have hc : r x ∈ ⋃ i, C i := by simpa using hWcover hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hc
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    · intro i t E hE z
      have H : IsPullback r q p V.ι :=
        isPullback_pullback_map f gV g V.ι rfl
      exact geometric_fibre_subset_isIrreducible_of_isPullback H (C i) t
        (hUgeom i t.1 t.2.1) E hE z
    · intro i j hij
      obtain ⟨x, hxi, hxj⟩ := hij
      have haxη : p (a x) = η := by
        have hx : a x ∈ Set.range a := Set.mem_range_self x
        rw [harange] at hx
        exact hx
      have haxr : a x ∈ Set.range r := by
        dsimp [r]
        rw [Scheme.Pullback.range_map]
        refine ⟨⟨pullback.fst f g (a x), by simp⟩, ?_⟩
        exact ⟨ηV, haxη.symm⟩
      obtain ⟨b, hb⟩ := haxr
      refine ⟨b, ⟨?_, ?_⟩, ?_⟩
      · change r b ∈ C i
        rw [hb]
        exact subset_closure ⟨x, hxi, rfl⟩
      · change r b ∈ C j
        rw [hb]
        exact subset_closure ⟨x, hxj, rfl⟩
      · change q b = ηV
        apply Subtype.ext
        change V.ι (q b) = η
        have he := congrArg (fun k : pullback f gV ⟶ T ↦ k b) hrp
        simpa only [Scheme.Hom.comp_apply, hb, haxη] using he.symm

end AlgebraicGeometry
