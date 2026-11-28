import Langlands.AlgebraicGeometry.SmoothDvrFibreGenericPoints
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Generic points of fibres and fibre products -/

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology

namespace Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction

variable {X Y S : Scheme.{u}}

/-- The point `y` has no proper generization in its fibre under `p`. For a morphism of schemes
`p` this says that `y` is the generic point of an irreducible component of its fibre. -/
def IsFibreGeneric {T B : Type*} [TopologicalSpace T] (p : T → B) (y : T) : Prop :=
  ∀ y' : T, y' ⤳ y → p y' = p y → y' = y

/-- The points of `fibreGenericPoints g` are exactly the points with no proper generization in
their fibre. -/
theorem mem_fibreGenericPoints_iff (g : Y ⟶ S) (y : Y) :
    y ∈ fibreGenericPoints g ↔ IsFibreGeneric g y := by
  constructor
  · intro hy y' hy' hgy'
    obtain ⟨s, z, hz, rfl⟩ := Set.mem_iUnion.mp hy
    exact SmoothDvrFibreGenericPoints.noProperGenerization_in_fibre g s z hz y' hy'
      (hgy'.trans (g.fiberHomeo s z).2)
  · intro hy
    obtain ⟨y₀, hy₀, hgy, hy₀y⟩ := exists_fibreGenericPoint_specializes g y
    rwa [← hy y₀ hy₀y hgy]

/-- Let `q` be a point of `X ×_S Y` and let `y'` be a generization of its second projection in
its fibre over `S`. Then `q` has a generization `q'` with the same first projection and with
second projection `y'`. -/
theorem exists_specializes_of_specializes_snd (f : X ⟶ S) (g : Y ⟶ S) (q : ↑(pullback f g))
    (y' : Y) (hy' : y' ⤳ pullback.snd f g q) (hgy' : g y' = g (pullback.snd f g q)) :
    ∃ q' : ↑(pullback f g), q' ⤳ q ∧ pullback.fst f g q' = pullback.fst f g q ∧
      pullback.snd f g q' = y' := by
  set x := pullback.fst f g q with hx
  set s := f x with hs
  have hgs : g (pullback.snd f g q) = s := by
    have := congrArg (fun h => h.base q) (pullback.condition (f := f) (g := g))
    exact this.symm
  let ιx := X.fromSpecResidueField x
  let ιs := S.fromSpecResidueField s
  let φ : Spec (X.residueField x) ⟶ Spec (S.residueField s) := Spec.map (f.residueFieldMap x)
  have hφ : φ ≫ ιs = ιx ≫ f := Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f x
  let W := pullback (g.fiberToSpecResidueField s) φ
  let w₁ : W ⟶ g.fiber s := pullback.fst _ _
  let w₂ : W ⟶ Spec (X.residueField x) := pullback.snd _ _
  have hcond : w₁ ≫ g.fiberToSpecResidueField s = w₂ ≫ φ := pullback.condition
  have hfib : g.fiberι s ≫ g = g.fiberToSpecResidueField s ≫ ιs := pullback.condition
  let ψ : W ⟶ pullback f g := pullback.lift (w₂ ≫ ιx) (w₁ ≫ g.fiberι s) (by
    rw [Category.assoc, Category.assoc, hfib, ← hφ, ← Category.assoc, ← Category.assoc, hcond])
  -- The fibre of the first projection over `x` maps to `W`.
  let F₁ := (pullback.fst f g).fiber x
  let a : F₁ ⟶ pullback f g := (pullback.fst f g).fiberι x
  let b : F₁ ⟶ Spec (X.residueField x) := (pullback.fst f g).fiberToSpecResidueField x
  have hab : a ≫ pullback.fst f g = b ≫ ιx := pullback.condition
  let m₁ : F₁ ⟶ g.fiber s := pullback.lift (a ≫ pullback.snd f g) (b ≫ φ) (by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hab, Category.assoc,
      Category.assoc, hφ])
  let χ : F₁ ⟶ W := pullback.lift m₁ b (pullback.lift_snd _ _ _)
  have e1 : χ ≫ w₁ = m₁ := pullback.lift_fst _ _ _
  have e2 : m₁ ≫ g.fiberι s = a ≫ pullback.snd f g := pullback.lift_fst _ _ _
  have e3 : ψ ≫ pullback.snd f g = w₁ ≫ g.fiberι s := pullback.lift_snd _ _ _
  have e4 : χ ≫ w₂ = b := pullback.lift_snd _ _ _
  have e5 : ψ ≫ pullback.fst f g = w₂ ≫ ιx := pullback.lift_fst _ _ _
  have hχψ : χ ≫ ψ = a := by
    apply pullback.hom_ext
    · rw [Category.assoc, e5, ← Category.assoc, e4, hab]
    · rw [Category.assoc, e3, ← Category.assoc, e1, e2]
  set w := χ ((pullback.fst f g).asFiber q) with hw
  have hψw : ψ w = q := by
    have := congrArg (fun h => h.base ((pullback.fst f g).asFiber q)) hχψ
    simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] at this
    rw [hw]
    convert this using 1
    exact ((pullback.fst f g).fiberι_asFiber q).symm
  have hψ₂ (v : W) : pullback.snd f g (ψ v) = g.fiberι s (w₁ v) := by
    exact congrArg (fun h => h.base v) e3
  have hψ₁ (v : W) : pullback.fst f g (ψ v) = x := by
    have := congrArg (fun h => h.base v) e5
    exact this.trans (Scheme.fromSpecResidueField_apply x _)
  -- The point `y'` as a point of the fibre of `g` over `s`.
  let y'' := (g.fiberHomeo s).symm ⟨y', hgy'.trans hgs⟩
  have hy'' : g.fiberι s y'' = y' := g.fiberι_fiberHomeo_symm s _
  have hspec : y'' ⤳ w₁ w := by
    rw [← (g.fiberι s).isEmbedding.isInducing.specializes_iff, hy'', ← hψ₂, hψw]
    exact hy'
  obtain ⟨w', hw'w, hw'⟩ := (Flat.generalizingMap w₁) hspec
  refine ⟨ψ w', ?_, ?_, ?_⟩
  · rw [← hψw]; exact hw'w.map ψ.continuous
  · rw [hψ₁]
  · rw [hψ₂, hw', hy'']

/-- Let `q` be a point of `X ×_S Y` and let `x'` be a generization of its first projection in
its fibre over `S`. Then `q` has a generization `q'` with the same second projection and with
first projection `x'`. -/
theorem exists_specializes_of_specializes_fst (f : X ⟶ S) (g : Y ⟶ S) (q : ↑(pullback f g))
    (x' : X) (hx' : x' ⤳ pullback.fst f g q) (hfx' : f x' = f (pullback.fst f g q)) :
    ∃ q' : ↑(pullback f g), q' ⤳ q ∧ pullback.snd f g q' = pullback.snd f g q ∧
      pullback.fst f g q' = x' := by
  let e := pullbackSymmetry f g
  have hinv (z : ↑(pullback f g)) : e.inv (e.hom z) = z := by
    have := congrArg (fun h => h.base z) e.hom_inv_id
    exact this
  have h1 (z : ↑(pullback f g)) : pullback.snd g f (e.hom z) = pullback.fst f g z :=
    congrArg (fun h => h.base z) (pullbackSymmetry_hom_comp_snd f g)
  have h2 (z : ↑(pullback f g)) : pullback.fst g f (e.hom z) = pullback.snd f g z :=
    congrArg (fun h => h.base z) (pullbackSymmetry_hom_comp_fst f g)
  have h3 (z : ↑(pullback g f)) : pullback.snd f g (e.inv z) = pullback.fst g f z :=
    congrArg (fun h => h.base z) (pullbackSymmetry_inv_comp_snd f g)
  have h4 (z : ↑(pullback g f)) : pullback.fst f g (e.inv z) = pullback.snd g f z :=
    congrArg (fun h => h.base z) (pullbackSymmetry_inv_comp_fst f g)
  obtain ⟨r', hr', hr'1, hr'2⟩ := exists_specializes_of_specializes_snd g f (e.hom q) x'
    (by rw [h1]; exact hx') (by rw [h1]; exact hfx')
  refine ⟨e.inv r', ?_, ?_, ?_⟩
  · rw [← hinv q]; exact hr'.map e.inv.continuous
  · rw [h3, hr'1, h2]
  · rw [h4, hr'2]

/-- A point of `X ×_S Y` that is generic in its fibre over `X` maps to a point of `Y` that is
generic in its fibre over `S`. -/
theorem isFibreGeneric_snd (f : X ⟶ S) (g : Y ⟶ S) {q : ↑(pullback f g)}
    (hq : IsFibreGeneric (pullback.fst f g) q) : IsFibreGeneric g (pullback.snd f g q) := by
  intro y' hy' hgy'
  obtain ⟨q', hq'q, hq'1, hq'2⟩ := exists_specializes_of_specializes_snd f g q y' hy' hgy'
  rw [← hq'2, hq q' hq'q hq'1]

/-- A point of `X ×_S Y` that is generic in its fibre over `Y` maps to a point of `X` that is
generic in its fibre over `S`. -/
theorem isFibreGeneric_fst (f : X ⟶ S) (g : Y ⟶ S) {q : ↑(pullback f g)}
    (hq : IsFibreGeneric (pullback.snd f g) q) : IsFibreGeneric f (pullback.fst f g q) := by
  intro x' hx' hfx'
  obtain ⟨q', hq'q, hq'2, hq'1⟩ := exists_specializes_of_specializes_fst f g q x' hx' hfx'
  rw [← hq'1, hq q' hq'q hq'2]

end Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction
