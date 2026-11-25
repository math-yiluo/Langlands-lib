/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.Compactification.Defs

/-!
# The coordinate tower used by the affine-space trace

Source: blueprint sec-smooth-purity/sk-prop-an, Steps 5(b) and 6
(blueprint: def-amb-affine-trace-tower).

## Main definitions

- `affineTraceTower`, `affineTraceProjection`, `affineTraceMap`: the ordered tower.
- `affineTraceToAffineSpace`: its canonical polynomial-coordinate identification.
- `affineTraceLineCompactification`: each standard projective-line compactification.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The coordinate model of affine space: start with the base and adjoin one coordinate
at a time. Over Spec B this is Spec B[t₁,…,t_d]. Source: blueprint
proposition-purity-vector-bundles, Step 6 (blueprint: def-amb-affine-trace-tower). -/
def affineTraceTower (S : Scheme.{u}) : ℕ → Scheme.{u}
  | 0 => S
  | d + 1 => AffineSpace PUnit.{u + 1} (affineTraceTower S d)

/-- The projection of the coordinate tower, including the identity in dimension zero.
Source: blueprint proposition-purity-vector-bundles, Step 6 (blueprint:
def-amb-affine-trace-tower). -/
def affineTraceProjection (S : Scheme.{u}) : (d : ℕ) → affineTraceTower S d ⟶ S
  | 0 => 𝟙 S
  | d + 1 => (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d) ≫
      affineTraceProjection S d

/-- Coordinatewise base change in the tower. Source: blueprint proposition-purity-vector-bundles,
Step 6 (blueprint: def-amb-affine-trace-tower). -/
def affineTraceMap {S' S : Scheme.{u}} (f : S' ⟶ S) :
    (d : ℕ) → affineTraceTower S' d ⟶ affineTraceTower S d
  | 0 => f
  | d + 1 => AffineSpace.map PUnit.{u + 1} (affineTraceMap f d)

/-- The ordered polynomial coordinates on the iterated affine-line model.
Source: blueprint proposition-purity-vector-bundles, Step 6 (blueprint:
def-amb-affine-trace-tower). -/
def affineTraceCoordinate (S : Scheme.{u}) :
    (d : ℕ) → Fin d → Γ(affineTraceTower S d, ⊤)
  | 0, i => Fin.elim0 i
  | d + 1, i => Fin.lastCases
      (AffineSpace.coord (affineTraceTower S d) PUnit.unit)
      (fun j ↦ (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘
        affineTraceTower S d).appTop.hom (affineTraceCoordinate S d j)) i

/-- The canonical coordinate map to Mathlib's affine d-space, with no chosen isomorphism.
Source: blueprint proposition-purity-vector-bundles, Step 6 (blueprint:
def-amb-affine-trace-tower). -/
def affineTraceToAffineSpace (S : Scheme.{u}) (d : ℕ) :
    affineTraceTower S d ⟶ AffineSpace (ULift.{u} (Fin d)) S :=
  AffineSpace.homOfVector (affineTraceProjection S d)
    (fun i ↦ affineTraceCoordinate S d i.down)

private def affineTraceFromVector {X S : Scheme.{u}} (f : X ⟶ S) :
    (d : ℕ) → (Fin d → Γ(X, ⊤)) → (X ⟶ affineTraceTower S d)
  | 0, _ => f
  | d + 1, v => AffineSpace.homOfVector
      (affineTraceFromVector f d (fun j ↦ v j.castSucc)) (fun _ ↦ v (Fin.last d))

set_option backward.isDefEq.respectTransparency.types false in
private lemma affineTraceFromVector_over {X S : Scheme.{u}} (f : X ⟶ S)
    (d : ℕ) (v : Fin d → Γ(X, ⊤)) :
    affineTraceFromVector f d v ≫ affineTraceProjection S d = f := by
  induction d with
  | zero =>
    change f ≫ 𝟙 S = f
    exact Category.comp_id f
  | succ d ih =>
    simp only [affineTraceFromVector, affineTraceProjection,
      AffineSpace.homOfVector_over_assoc]
    exact ih _

set_option backward.isDefEq.respectTransparency.types false in
private lemma affineTraceFromVector_coord {X S : Scheme.{u}} (f : X ⟶ S)
    (d : ℕ) (v : Fin d → Γ(X, ⊤)) (i : Fin d) :
    (affineTraceFromVector f d v).appTop (affineTraceCoordinate S d i) = v i := by
  induction d with
  | zero => exact Fin.elim0 i
  | succ d ih =>
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [affineTraceCoordinate, Fin.lastCases_last, affineTraceFromVector] using!
        (AffineSpace.homOfVector_appTop_coord
          (affineTraceFromVector f d (fun j ↦ v j.castSucc))
          (fun _ : PUnit.{u + 1} ↦ v (Fin.last d)) PUnit.unit)
    · simp only [affineTraceCoordinate, Fin.lastCases_castSucc]
      change (affineTraceFromVector f (d + 1) v).appTop
        ((AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘
          affineTraceTower S d).appTop (affineTraceCoordinate S d j)) = _
      erw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
      change ((affineTraceFromVector f (d + 1) v) ≫
        AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d).appTop
          (affineTraceCoordinate S d j) = _
      rw [affineTraceFromVector, AffineSpace.homOfVector_over]
      exact ih _ _

set_option backward.isDefEq.respectTransparency.types false in
private lemma affineTraceTower_hom_ext {X S : Scheme.{u}} (d : ℕ)
    {f g : X ⟶ affineTraceTower S d}
    (hp : f ≫ affineTraceProjection S d = g ≫ affineTraceProjection S d)
    (hc : ∀ i, f.appTop (affineTraceCoordinate S d i) =
      g.appTop (affineTraceCoordinate S d i)) : f = g := by
  induction d with
  | zero =>
    change f ≫ 𝟙 S = g ≫ 𝟙 S at hp
    exact (cancel_mono (𝟙 S)).mp hp
  | succ d ih =>
    dsimp only [affineTraceTower] at f g
    apply AffineSpace.hom_ext
    · apply ih
      · simpa only [Category.assoc, affineTraceProjection] using hp
      · intro i
        simpa only [affineTraceCoordinate, Fin.lastCases_castSucc,
          Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using! hc i.castSucc
    · rintro ⟨⟩
      simpa only [affineTraceCoordinate, Fin.lastCases_last] using! hc (Fin.last d)

/-- The coordinate map identifies the tower with the recorded affine-space definition.
Source: blueprint proposition-purity-vector-bundles, Step 6 (blueprint: def-amb-affine-trace-tower).
Proof: on an affine open Spec B of S, the d successive affine-line steps have ring
B[t₁,…,t_d]. The displayed map is the identity on B and sends each polynomial variable
to the corresponding coordinate. It is therefore an isomorphism on these affine opens.
These opens cover S, so the morphism is an isomorphism. For d=0 this is the canonical
isomorphism from S to its zero-dimensional affine space. -/
theorem affineTraceToAffineSpace_isIso (S : Scheme.{u}) (d : ℕ) :
    IsIso (affineTraceToAffineSpace S d) := by
  let g := affineTraceFromVector (AffineSpace (ULift.{u} (Fin d)) S ↘ S) d
    (fun i ↦ AffineSpace.coord S (ULift.up i))
  refine ⟨⟨g, ?_, ?_⟩⟩
  · apply affineTraceTower_hom_ext d
    · simp [g, Category.assoc, affineTraceFromVector_over, affineTraceToAffineSpace]
    · intro i
      simp [g, affineTraceFromVector_coord, affineTraceToAffineSpace]
  · apply AffineSpace.hom_ext
    · simp [affineTraceToAffineSpace, g, affineTraceFromVector_over]
    · rintro ⟨i⟩
      simp [affineTraceToAffineSpace, g, affineTraceFromVector_coord]

/-- The canonical affine-space identification, whose inverse is uniquely determined by
the concrete coordinate map. Source: blueprint proposition-purity-vector-bundles, Step 6
(blueprint: def-amb-affine-trace-tower). -/
def affineTraceAffineSpaceIso (S : Scheme.{u}) (d : ℕ) :
    affineTraceTower S d ≅ AffineSpace (ULift.{u} (Fin d)) S :=
  letI := affineTraceToAffineSpace_isIso S d
  asIso (affineTraceToAffineSpace S d)

/-- Every finite coordinate stage over a Noetherian base is Noetherian.
Source: blueprint proposition-purity-vector-bundles, Step 6 (blueprint: def-amb-affine-trace-tower).
Proof: the zero stage is S. Each successive affine-line projection is affine and of
finite presentation, so its source is locally Noetherian and quasi-compact over its
Noetherian base. Induction proves Noetherianity at every stage. -/
theorem affineTraceNoetherian (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) :
    IsNoetherian (affineTraceTower S d) := by
  induction d with
  | zero => exact inferInstanceAs (IsNoetherian S)
  | succ d ih =>
    let := ih
    let := LocallyOfFiniteType.isLocallyNoetherian
      (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
    have := QuasiCompact.compactSpace_of_compactSpace
      (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
    change IsNoetherian (AffineSpace PUnit.{u + 1} (affineTraceTower S d))
    exact ⟨⟩

/-- The standard projective-line compactification of one coordinate step.
Source: blueprint proposition-purity-vector-bundles, Step 5(b) (blueprint:
def-amb-affine-trace-tower). -/
def affineTraceLineCompactification (S : Scheme.{u}) :
    Compactification (AffineSpace PUnit.{u + 1} S ↘ S) where
  Z := ProjectiveLine S
  i := ProjectiveLine.affineChart S
  g := ProjectiveLine S ↘ S
  comm := (ProjectiveLine.affineChart_over S).symm
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- The standard affine chart commutes with arbitrary base change and is Cartesian.
Source: blueprint proposition-purity-vector-bundles, Steps 5(b), 6
(blueprint: def-amb-affine-trace-tower).
Proof: the chart is D₊(T₁); its coordinate T₀/T₁ pulls back to the same coordinate.
The base change of this open is the corresponding standard open. On affine bases the
square is the polynomial-ring base-change square, and these identifications glue. -/
theorem affineTraceChart_isPullback {S' S : Scheme.{u}} (f : S' ⟶ S) :
    IsPullback (AffineSpace.map PUnit.{u + 1} f) (ProjectiveLine.affineChart S')
      (ProjectiveLine.affineChart S) (ProjectiveSpace.map (ULift.{u} (Fin 2)) f) := by
  have hcoord :
      (fun i ↦ (AffineSpace.map PUnit.{u + 1} f).appTop.hom
        (ProjectiveLine.pairSections (AffineSpace.coord S PUnit.unit) 1 i)) =
      ProjectiveLine.pairSections (AffineSpace.coord S' PUnit.unit) 1 := by
    funext ⟨i⟩
    fin_cases i <;> simp [ProjectiveLine.pairSections, AffineSpace.map_appTop_coord]
  have hcomm : AffineSpace.map PUnit.{u + 1} f ≫ ProjectiveLine.affineChart S =
      ProjectiveLine.affineChart S' ≫ ProjectiveSpace.map (ULift.{u} (Fin 2)) f := by
    rw [ProjectiveLine.affineChart_eq_homOfSections, ProjectiveSpace.comp_homOfSections]
    apply ProjectiveSpace.hom_ext
    · simp [AffineSpace.map_over, ProjectiveSpace.map_over]
    · rw [ProjectiveSpace.homOfSections_toProjInt, Category.assoc,
        ProjectiveSpace.map_toProjInt, ProjectiveLine.affineChart_eq_homOfSections,
        ProjectiveSpace.homOfSections_toProjInt]
      congr 1
      exact congrArg ProjectiveSpace.evalSections hcoord
  apply IsPullback.of_bot _ hcomm
    (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) f)
  simpa only [ProjectiveLine.affineChart_over] using
    (AffineSpace.isPullback_map (n := PUnit.{u + 1}) f)

/-- The projection of the coordinate tower is separated, locally of finite type and
quasi-compact. Source: blueprint proposition-purity-vector-bundles, Step 6
(blueprint: def-amb-affine-trace-tower).
Proof: the identity has all three properties. Each next projection is an affine-line
projection, hence affine and of finite presentation. Compose the three properties at
each stage. Equivalently on Spec B the diagonal is cut out by tᵢ-uᵢ, and the coordinate
algebra has the finite generating set t₁,…,t_d. -/
theorem affineTraceProjection_properties (S : Scheme.{u}) (d : ℕ) :
    IsSeparated (affineTraceProjection S d) ∧
      LocallyOfFiniteType (affineTraceProjection S d) ∧
      QuasiCompact (affineTraceProjection S d) := by
  induction d with
  | zero =>
    change IsSeparated (𝟙 S) ∧ LocallyOfFiniteType (𝟙 S) ∧ QuasiCompact (𝟙 S)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  | succ d ih =>
    let := ih.1
    let := ih.2.1
    let := ih.2.2
    dsimp only [affineTraceProjection]
    exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Separatedness of the tower projection, from its named geometric property theorem.
Source: blueprint proposition-purity-vector-bundles, Step 6 (blueprint:
def-amb-affine-trace-tower). -/
instance affineTraceProjection_isSeparated (S : Scheme.{u}) (d : ℕ) :
    IsSeparated (affineTraceProjection S d) := (affineTraceProjection_properties S d).1

/-- Finite type locally on the tower projection.
Source: blueprint proposition-purity-vector-bundles, Step 6 (blueprint:
def-amb-affine-trace-tower). -/
instance affineTraceProjection_locallyOfFiniteType (S : Scheme.{u}) (d : ℕ) :
    LocallyOfFiniteType (affineTraceProjection S d) :=
  (affineTraceProjection_properties S d).2.1

/-- Quasi-compactness of the tower projection.
Source: blueprint proposition-purity-vector-bundles, Step 6 (blueprint:
def-amb-affine-trace-tower). -/
instance affineTraceProjection_quasiCompact (S : Scheme.{u}) (d : ℕ) :
    QuasiCompact (affineTraceProjection S d) := (affineTraceProjection_properties S d).2.2

/-- Pull invertibility of N along the actual tower projection.
Source: blueprint proposition-purity-vector-bundles, Step 6 (blueprint: def-amb-affine-trace-tower).
Proof: apply the global-sections ring homomorphism of p_d to a unit representing N;
ring homomorphisms preserve units and natural-number casts. -/
theorem affineTraceInvertible (N : ℕ) (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    IsUnit (N : Γ(affineTraceTower S d, ⊤)) :=
  by
    simpa only [map_natCast] using hS.map (affineTraceProjection S d).appTop.hom

/-- Invertibility on the base is preserved by every change of base.
Source: blueprint proposition-purity-vector-bundles, Step 6 (blueprint: def-amb-affine-trace-tower).
Proof: apply the global-sections ring map of f to a unit representing N; ring maps
preserve units and natural-number casts. No flatness assumption is used. -/
theorem affineTracePullbackInvertible (N : ℕ) {S' S : Scheme.{u}} (f : S' ⟶ S)
    (hS : IsUnit (N : Γ(S, ⊤))) : IsUnit (N : Γ(S', ⊤)) := by
  simpa only [map_natCast] using hS.map f.appTop.hom

/-- Pullback of N-invertibility to the projective-line compactification.
Source: blueprint proposition-purity-vector-bundles, Step 5(b) (blueprint:
def-amb-affine-trace-tower). Proof: apply the global-sections ring homomorphism of q to a unit
representing N; ring homomorphisms preserve units and natural-number casts. -/
theorem affineTraceProjectiveInvertible (N : ℕ) (S : Scheme.{u})
    (hS : IsUnit (N : Γ(S, ⊤))) : IsUnit (N : Γ(ProjectiveLine S, ⊤)) :=
  by
    simpa only [map_natCast] using hS.map (ProjectiveLine S ↘ S).appTop.hom

end AlgebraicGeometry
