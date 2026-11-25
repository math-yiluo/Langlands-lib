/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Compatible flat base change on finite intersections of compact opens

Source: Stacks Project, Tag 0APJ, proof of `lemma-affine-base-change`, and Tag 02KH.
(blueprint: lem-a1-qc-open-flat-section-diagram)
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

/-- The ordinary section algebra on an open, with scalars supplied by the structure map.
Source: Stacks, Tag 0APJ (blueprint: lem-a1-qc-open-flat-section-diagram). -/
def qcOpenSectionAlgebra {R : CommRingCat.{u}} {Y : Scheme.{u}}
    (f : Y ⟶ Spec R) (V : Y.Opens) : CommAlgCat.{u} R :=
  letI := ((ΓSpecIso R).inv ≫ f.appTop ≫ Y.presheaf.map
    (homOfLE (le_top : V ≤ ⊤)).op).hom.toAlgebra
  CommAlgCat.of R Γ(Y, V)

/-- Ordinary restriction as a map of the structural section algebras.
Source: Stacks, Tag 0APJ (blueprint: lem-a1-qc-open-flat-section-diagram). -/
def qcOpenSectionRestriction {R : CommRingCat.{u}} {Y : Scheme.{u}}
    (f : Y ⟶ Spec R) {V W : Y.Opens} (i : W ⟶ V) :
    qcOpenSectionAlgebra f V ⟶ qcOpenSectionAlgebra f W :=
  CommAlgCat.ofHom (X := qcOpenSectionAlgebra f V) (Y := qcOpenSectionAlgebra f W)
    { (Y.presheaf.map i.op).hom with
      commutes' := fun r ↦ by
        change (Y.presheaf.map i.op)
          (((ΓSpecIso R).inv ≫ f.appTop ≫
            Y.presheaf.map (homOfLE le_top).op) r) =
          ((ΓSpecIso R).inv ≫ f.appTop ≫
            Y.presheaf.map (homOfLE le_top).op) r
        simp only [← ConcreteCategory.comp_apply, Category.assoc, ← Functor.map_comp]
        rfl }

/-- The actual tensor of open sections with T, with its right-factor T-algebra structure.
Source: Stacks, Tag 0APJ (blueprint: lem-a1-qc-open-flat-section-diagram). -/
def qcOpenSectionTensor {R T : CommRingCat.{u}} (r : R ⟶ T) {Y : Scheme.{u}}
    (f : Y ⟶ Spec R) (V : Y.Opens) : CommAlgCat.{u} T :=
  letI := r.hom.toAlgebra
  letI := Algebra.TensorProduct.rightAlgebra
    (R := R) (A := qcOpenSectionAlgebra f V) (B := T)
  CommAlgCat.of T ((qcOpenSectionAlgebra f V) ⊗[R] T)

/-- Pure tensors in the structural open-section tensor algebra.
Source: Stacks, Tag 0APJ (blueprint: lem-a1-qc-open-flat-section-diagram). -/
def qcOpenSectionPure {R T : CommRingCat.{u}} (r : R ⟶ T) {Y : Scheme.{u}}
    (f : Y ⟶ Spec R) (V : Y.Opens) (a : Γ(Y, V)) (t : T) :
    qcOpenSectionTensor r f V :=
  letI := r.hom.toAlgebra
  (a : qcOpenSectionAlgebra f V) ⊗ₜ[R] t

/-- Restriction on the first tensor factor and identity on T.
Source: Stacks, Tag 0APJ (blueprint: lem-a1-qc-open-flat-section-diagram). -/
def qcOpenSectionTensorRestriction {R T : CommRingCat.{u}} (r : R ⟶ T)
    {Y : Scheme.{u}} (f : Y ⟶ Spec R) {V W : Y.Opens} (i : W ⟶ V) :
    qcOpenSectionTensor r f V ⟶ qcOpenSectionTensor r f W := by
  letI := r.hom.toAlgebra
  letI := Algebra.TensorProduct.rightAlgebra
    (R := R) (A := qcOpenSectionAlgebra f V) (B := T)
  letI := Algebra.TensorProduct.rightAlgebra
    (R := R) (A := qcOpenSectionAlgebra f W) (B := T)
  let m := Algebra.TensorProduct.map (qcOpenSectionRestriction f i).hom (AlgHom.id R T)
  exact CommAlgCat.ofHom
    { m.toRingHom with
      commutes' := fun t ↦ by
        change m (1 ⊗ₜ[R] t) = 1 ⊗ₜ[R] t
        simp [m] }

/-- The finite-intersection refinement, indexed by nonempty finite subsets.
Source: Stacks, Tag 0APJ, first sentence of the proof
(blueprint: lem-a1-qc-open-flat-section-diagram). -/
def qcFiniteIntersection {Y : Scheme.{u}} {I : Type v} (U : I → Y.Opens)
    (F : {F : Finset I // F.Nonempty}) : Y.Opens :=
  ⨅ i : F.val, U i.val

/-- An inclusion F ⊆ G gives the inclusion V_G into V_F.
Source: Stacks, Tag 0APJ, finite-intersection refinement
(blueprint: lem-a1-qc-open-flat-section-diagram). -/
def qcFiniteIntersectionInclusion {Y : Scheme.{u}} {I : Type v} (U : I → Y.Opens)
    {F G : {F : Finset I // F.Nonempty}} (h : F ≤ G) :
    qcFiniteIntersection U G ⟶ qcFiniteIntersection U F :=
  homOfLE (le_iInf fun i ↦ iInf_le_of_le (⟨i.val, h i.property⟩ : G.val) le_rfl)

private theorem qcOpen_component {R T : CommRingCat.{u}} (r : R ⟶ T)
    [Flat (Spec.map r)] {Y : Scheme.{u}} (f : Y ⟶ Spec R) [QuasiSeparatedSpace Y]
    (V : Y.Opens) (hV : IsCompact (V : Set Y)) :
    ∃ e : qcOpenSectionTensor r f V ≅
      qcOpenSectionAlgebra (pullback.snd f (Spec.map r))
        (pullback.fst f (Spec.map r) ⁻¹ᵁ V),
      ∀ (a : Γ(Y, V)) (t : T), e.hom (qcOpenSectionPure r f V a t) =
        @id (qcOpenSectionAlgebra (pullback.snd f (Spec.map r))
          (pullback.fst f (Spec.map r) ⁻¹ᵁ V))
          ((pullback.fst f (Spec.map r)).app V a) *
        algebraMap T (qcOpenSectionAlgebra (pullback.snd f (Spec.map r))
          (pullback.fst f (Spec.map r) ⁻¹ᵁ V)) t := by
  let g := pullback.fst f (Spec.map r)
  let q := pullback.snd f (Spec.map r)
  let W := g ⁻¹ᵁ V
  have hi := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (IsPullback.of_hasPullback f (Spec.map r)) (US := ⊤) (UT := ⊤) (UX := V)
    (by simp) (by simp) (UY := W) (by simp [W, g])
    (isAffineOpen_top _) (isAffineOpen_top _) hV
    (IsQuasiSeparated.of_quasiSeparatedSpace _)
  have H := (isIso_pushoutSection_iff
    (IsPullback.of_hasPullback f (Spec.map r)) (US := ⊤) (UT := ⊤) (UX := V)
    (by simp) (by simp) (UY := W) (by simp [W, g])).mp hi
  let aR : R ⟶ Γ(Y, V) := (ΓSpecIso R).inv ≫ f.appTop ≫
    Y.presheaf.map (homOfLE le_top).op
  let bT : T ⟶ Γ(pullback f (Spec.map r), W) := (ΓSpecIso T).inv ≫ q.appTop ≫
    (pullback f (Spec.map r)).presheaf.map (homOfLE le_top).op
  have H' : IsPushout aR r (g.app V) bT := by
    apply H.of_iso (ΓSpecIso R) (Iso.refl _) (ΓSpecIso T) (Iso.refl _)
    · simp [aR, Scheme.Hom.appLE, Scheme.Hom.appTop]
    · simp [Scheme.Hom.appLE]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      exact g.appLE_eq_app
    · simp [bT, q, Scheme.Hom.appLE, Scheme.Hom.appTop]
  let := r.hom.toAlgebra
  let A := qcOpenSectionAlgebra f V
  let B := qcOpenSectionAlgebra q W
  let Ht := CommRingCat.isPushout_tensorProduct R A T
  let er := Ht.isoPushout ≪≫ H'.isoPushout.symm
  have hl (a : A) : er.hom (a ⊗ₜ[R] (1 : T)) = g.app V a := by
    change (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ er.hom) a = _
    simp [er]
    rfl
  have hr (t : T) : er.hom ((1 : A) ⊗ₜ[R] t) = algebraMap T B t := by
    change (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫ er.hom) t = _
    simp [er]
    rfl
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := T)
  let ea : (A ⊗[R] T) ≃ₐ[T] B :=
    { toRingEquiv := er.commRingCatIsoToRingEquiv
      commutes' := hr }
  refine ⟨CommAlgCat.isoMk ea, ?_⟩
  intro a t
  change er.hom (a ⊗ₜ[R] t) = _
  have ht := Algebra.TensorProduct.tmul_mul_tmul (R := R) (A := A) (B := T)
    (a : A) (1 : A) (1 : T) t
  simp only [mul_one, one_mul] at ht
  rw [← ht, map_mul, hl, hr]
  rfl

/-- The finite-intersection diagrams have canonical, compatible flat tensor isomorphisms.
The isomorphisms are specified on every pure tensor, uniquely determining their forward
maps. The last equality is the square on all tensor elements, expressed as equality of
T-algebra morphisms. Thus the component inverses also give a diagram isomorphism.

Source: Stacks Project, Tag 0APJ, proof of `lemma-affine-base-change`; Tag 02KH, degree zero.
(blueprint: lem-a1-qc-open-flat-section-diagram).

Proof:
1. A singleton gives a nonempty finite subset; union gives a common upper bound.
   Restrictions run from F to G when F is contained in G, by presheaf functoriality.
2. The quasi-separated affine-cover criterion
   (lem-weil-pbc-quasi-separated-affine-cover-criterion, Tag 01KO) makes intersections
   of affine opens compact. Finite affine covers then make intersections of compact
   opens compact. Induction proves this for every nonempty finite intersection.
   The same affine-cover criterion proves all open subschemes quasi-separated.
3. A map between spectra is affine (lem-weil-pbc-morphism-affine-schemes-affine).
   Base change preserves affineness (lem-weil-pbc-affine-morphism-permanence), so the
   projection is quasi-compact and quasi-separated. The qcqs permanence theorem
   (lem-weil-pbc-qcqs-morphism-permanence) gives quasi-separatedness of the pullback
   and compactness of every inverse-image open. Open immersions are stable under
   base change (lem-weil-pbc-open-immersion-base-change). The fibre-product universal
   property identifies that inverse-image open with V_F times Spec T over Spec R,
   respecting both projections; it is quasi-separated as an open of the pullback.
4. Apply flat qcqs base change for global sections
   (lem-weil-pbc-flat-base-change-global-sections-qcqs, Tag 02KH) on each V_F.
   Identify sections of the two spectra with R and T. Tensor-pushout universality
   (lem-weil-pbc-algebra-tensor-pushout-universal-property) identifies the comparison
   with a tensor t mapped to g-sharp(a) times t. It respects T, as does its inverse.
5. Naturality of the scheme comorphism and of scalar restriction makes the displayed
   square commute on pure tensors. Tensor-pushout uniqueness gives equality of the
   algebra maps. Restriction identity and composition give the diagrams; composing
   the squares with the component inverses gives the inverse natural transformation. -/
theorem qc_open_flat_section_diagram {R T : CommRingCat.{u}} (r : R ⟶ T)
    [Flat (Spec.map r)] {Y : Scheme.{u}} (f : Y ⟶ Spec R) [QuasiSeparatedSpace Y]
    {I : Type v} [Nonempty I] (U : I → Y.Opens)
    (hU : ∀ i : I, IsCompact (U i : Set Y)) :
    Nonempty {F : Finset I // F.Nonempty} ∧
    Directed (· ≤ ·) (fun F : {F : Finset I // F.Nonempty} ↦ F) ∧
    QuasiSeparatedSpace (pullback f (Spec.map r) : Scheme.{u}) ∧
    (∀ F : {F : Finset I // F.Nonempty},
      IsCompact (qcFiniteIntersection U F : Set Y) ∧
      QuasiSeparatedSpace (qcFiniteIntersection U F).toScheme ∧
      IsCompact (pullback.fst f (Spec.map r) ⁻¹ᵁ qcFiniteIntersection U F :
        Set (pullback f (Spec.map r) : Scheme.{u})) ∧
      QuasiSeparatedSpace
        (pullback.fst f (Spec.map r) ⁻¹ᵁ qcFiniteIntersection U F).toScheme) ∧
    ∃ e : ∀ F : {F : Finset I // F.Nonempty},
      qcOpenSectionTensor r f (qcFiniteIntersection U F) ≅
        qcOpenSectionAlgebra (pullback.snd f (Spec.map r))
          (pullback.fst f (Spec.map r) ⁻¹ᵁ qcFiniteIntersection U F),
      (∀ (F : {F : Finset I // F.Nonempty})
        (a : Γ(Y, qcFiniteIntersection U F)) (t : T),
        (e F).hom (qcOpenSectionPure r f (qcFiniteIntersection U F) a t) =
          @id (qcOpenSectionAlgebra (pullback.snd f (Spec.map r))
              (pullback.fst f (Spec.map r) ⁻¹ᵁ qcFiniteIntersection U F))
            ((pullback.fst f (Spec.map r)).app (qcFiniteIntersection U F) a) *
            algebraMap T
              (qcOpenSectionAlgebra (pullback.snd f (Spec.map r))
                (pullback.fst f (Spec.map r) ⁻¹ᵁ qcFiniteIntersection U F)) t) ∧
      (∀ (F G : {F : Finset I // F.Nonempty}) (h : F ≤ G),
        qcOpenSectionTensorRestriction r f (qcFiniteIntersectionInclusion U h) ≫
            (e G).hom =
          (e F).hom ≫ qcOpenSectionRestriction (pullback.snd f (Spec.map r))
            ((Opens.map (pullback.fst f (Spec.map r)).base).map
              (qcFiniteIntersectionInclusion U h))) := by
  classical
  let g := pullback.fst f (Spec.map r)
  let q := pullback.snd f (Spec.map r)
  have hX : QuasiSeparatedSpace (pullback f (Spec.map r) : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated g
  let := hX
  have hc (F : {F : Finset I // F.Nonempty}) :
      IsCompact (qcFiniteIntersection U F : Set Y) := by
    let : Nonempty F.val := F.property.to_subtype
    rw [qcFiniteIntersection, Opens.coe_iInf, ← Set.sInter_range]
    exact QuasiSeparatedSpace.isCompact_sInter_of_nonempty (Set.finite_range _)
      (Set.range_nonempty _) (by rintro _ ⟨i, rfl⟩; exact Or.inl (U i.val).isOpen)
      (by rintro _ ⟨i, rfl⟩; exact hU i.val)
  refine ⟨?_, ?_, hX, ?_, ?_⟩
  · exact ⟨⟨{Classical.choice inferInstance}, Finset.singleton_nonempty _⟩⟩
  · intro F G
    exact ⟨⟨F.val ∪ G.val, F.property.mono Finset.subset_union_left⟩,
      Finset.subset_union_left, Finset.subset_union_right⟩
  · intro F
    exact ⟨hc F, (qcFiniteIntersection U F).isOpen.isOpenEmbedding_subtypeVal.quasiSeparatedSpace,
      g.isCompact_preimage (hc F),
      (g ⁻¹ᵁ qcFiniteIntersection U F).isOpen.isOpenEmbedding_subtypeVal.quasiSeparatedSpace⟩
  · choose e he using fun F ↦ qcOpen_component r f (qcFiniteIntersection U F) (hc F)
    refine ⟨e, he, ?_⟩
    intro F G h
    let i := qcFiniteIntersectionInclusion U h
    let j := (Opens.map g.base).map i
    let := r.hom.toAlgebra
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul a t =>
      change (e G).hom
        ((qcOpenSectionTensorRestriction r f i)
          (qcOpenSectionPure r f (qcFiniteIntersection U F) a t)) =
        (qcOpenSectionRestriction q j)
          ((e F).hom (qcOpenSectionPure r f (qcFiniteIntersection U F) a t))
      have ht : (qcOpenSectionTensorRestriction r f i)
          (qcOpenSectionPure r f (qcFiniteIntersection U F) a t) =
          qcOpenSectionPure r f (qcFiniteIntersection U G)
            ((Y.presheaf.map i.op) a) t := by
        change (Algebra.TensorProduct.map (qcOpenSectionRestriction f i).hom
          (AlgHom.id R T)) (a ⊗ₜ[R] t) = _
        exact Algebra.TensorProduct.map_tmul _ _ _ _
      rw [ht, he, he]
      change _ = (pullback f (Spec.map r)).presheaf.map j.op (_ * _)
      rw [map_mul]
      congr 1
      · exact congrArg (fun k : Γ(Y, qcFiniteIntersection U F) ⟶
            Γ(pullback f (Spec.map r), g ⁻¹ᵁ qcFiniteIntersection U G) ↦ k a)
          (g.naturality i.op)
      · exact ((qcOpenSectionRestriction q j).hom.commutes t).symm

end AlgebraicGeometry.Scheme
