/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.DualNumber
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.AlgebraicGeometry.DualNumberSchemePushout

/-! Additive and scalar operations on dual-number tangent vectors.
(blueprint: lem-sc-tangent-vectors-operations)

Source: Stacks Project, Tag 0B2B, proof of Lemma 33.16.2.

Proof: construct addition from the unique two-copy gluing and scalar multiplication
from the coefficient-scaling map. The point and projection identities show closure
in the relative tangent-vector subtype. Coordinate exchange proves commutativity,
and the three-copy gluing proves associativity. Gluing two scalar multiples of the
same vector proves the zero and inverse laws and additivity in the scalar. Scaling
both coordinates of a two-copy gluing proves distributivity over vector addition.
Functoriality proves the remaining scalar laws. Assemble these into AddCommGroup
and Module instances; uniqueness gives the addition formula for every gluing. -/

@[expose] public section
universe u
open CategoryTheory
noncomputable section

namespace AlgebraicGeometry.TangentVectorGluing

variable {K : Type u} [Field K]

private abbrev Thickening (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V] :=
  Spec (.of (TrivSqZeroExt K V))

private abbrev coordinate {V W : Type u} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V]
    [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W] (f : V →ₗ[K] W) :
    Thickening (K := K) W ⟶ Thickening (K := K) V :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map f).toRingHom)

private abbrev point (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V] :
    Spec (.of K) ⟶ Thickening (K := K) V :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K V).toRingHom)

private abbrev projection (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V] :
    Thickening (K := K) V ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom K V))

private lemma coordinate_comp {V W U : Type u} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V]
    [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W] [AddCommGroup U]
    [Module K U] [Module Kᵐᵒᵖ U] [IsCentralScalar K U]
    (f : V →ₗ[K] W) (g : W →ₗ[K] U) :
    coordinate g ≫ coordinate f = coordinate (g.comp f) := by
  rw [coordinate, coordinate, coordinate, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact congrArg AlgHom.toRingHom (TrivSqZeroExt.map_comp_map f g).symm

@[simp] private lemma point_coordinate {V W : Type u} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V]
    [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W] (f : V →ₗ[K] W) :
    point W ≫ coordinate f = point V := by
  rw [point, coordinate, point, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext z
  simp

@[simp] private lemma coordinate_projection {V W : Type u} [AddCommGroup V] [Module K V]
    [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V]
    [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W] (f : V →ₗ[K] W) :
    coordinate f ≫ projection V = projection W := by
  rw [coordinate, projection, projection, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply RingHom.ext
  intro z
  exact TrivSqZeroExt.map_inl f z

@[simp] private lemma point_projection (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V] :
    point (K := K) V ≫ projection V = 𝟙 _ := by
  rw [point, projection, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h : (TrivSqZeroExt.fstHom K K V).toRingHom.comp
      (TrivSqZeroExt.inlHom K V) = RingHom.id K := by ext z; rfl
  rw [h]
  exact Spec.map_id _

variable {X Y : Scheme.{u}} (b : Spec (.of K) ⟶ X) (p : X ⟶ Y)

private abbrev Vector :=
  {θ : Thickening (K := K) K ⟶ X //
    point K ≫ θ = b ∧ θ ≫ p = projection K ≫ b ≫ p}

/-- The common-point condition supplies the unique two-coordinate gluing. -/
private lemma extension_exists (a d : Vector b p) :
    ∃! F : Thickening (K := K) (Fin 2 → K) ⟶ X,
      ∀ i : Fin 2, coordinate (LinearMap.proj i) ≫ F = (![a.val, d.val] i) := by
  apply existsUnique_dualNumberScheme_extension K 2 (by decide) X
  intro i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact a.property.1.trans d.property.1.symm
  · exact d.property.1.trans a.property.1.symm
  · rfl

/-- The unique gluing, determined by its two restrictions, rather than an arbitrary witness. -/
private noncomputable def extension (a d : Vector b p) :
    Thickening (K := K) (Fin 2 → K) ⟶ X :=
  Classical.choose (extension_exists b p a d)

private lemma extension_restrict (a d : Vector b p) (i : Fin 2) :
    coordinate (LinearMap.proj i) ≫ extension b p a d = (![a.val, d.val] i) :=
  (Classical.choose_spec (extension_exists b p a d)).1 i

private lemma extension_unique (a d : Vector b p)
    (F : Thickening (K := K) (Fin 2 → K) ⟶ X)
    (h : ∀ i : Fin 2, coordinate (LinearMap.proj i) ≫ F = (![a.val, d.val] i)) :
    F = extension b p a d :=
  (Classical.choose_spec (extension_exists b p a d)).2 F h

private lemma extension_point (a d : Vector b p) :
    point (Fin 2 → K) ≫ extension b p a d = b := by
  rw [← point_coordinate (LinearMap.proj 0 : (Fin 2 → K) →ₗ[K] K), Category.assoc]
  rw [extension_restrict]
  exact a.property.1

private lemma extension_over (a d : Vector b p) :
    extension b p a d ≫ p = projection (Fin 2 → K) ≫ b ≫ p := by
  have h := existsUnique_dualNumberScheme_extension K 2 (by decide) Y
    (fun _ => projection K ≫ b ≫ p) (by intros; rfl)
  apply h.unique
  · intro i
    rw [← Category.assoc, extension_restrict]
    fin_cases i
    · exact a.property.2
    · exact d.property.2
  · intro i
    simp only [← Category.assoc, coordinate_projection]

/-- Constant tangent vector, with both triangles verified. -/
private def zero : Vector b p :=
  ⟨projection K ≫ b, by simp [← Category.assoc]⟩

/-- Addition is precomposition of the unique gluing with the sum of coordinates. -/
private noncomputable def add (a d : Vector b p) : Vector b p :=
  ⟨coordinate ((LinearMap.proj 0 : (Fin 2 → K) →ₗ[K] K) + LinearMap.proj 1) ≫
      extension b p a d, by
    constructor
    · rw [← Category.assoc, point_coordinate, extension_point]
    · rw [Category.assoc, extension_over]
      simp only [← Category.assoc, coordinate_projection]⟩

/-- Scalar multiplication is induced by multiplication on the infinitesimal coefficient. -/
private def scale (t : K) (a : Vector b p) : Vector b p :=
  ⟨coordinate (t • (LinearMap.id : K →ₗ[K] K)) ≫ a.val, by
    constructor
    · rw [← Category.assoc, point_coordinate]
      exact a.property.1
    · rw [Category.assoc, a.property.2]
      simp only [← Category.assoc, coordinate_projection]⟩

@[simp] private lemma coordinate_id (V : Type u) [AddCommGroup V] [Module K V]
    [Module Kᵐᵒᵖ V] [IsCentralScalar K V] :
    coordinate (LinearMap.id : V →ₗ[K] V) = 𝟙 _ := by
  simp only [coordinate, TrivSqZeroExt.map_id]
  exact Spec.map_id _

private lemma coordinate_zero {V W : Type u} [AddCommGroup V] [Module K V]
    [Module Kᵐᵒᵖ V] [IsCentralScalar K V] [AddCommGroup W] [Module K W]
    [Module Kᵐᵒᵖ W] [IsCentralScalar K W] :
    coordinate (0 : V →ₗ[K] W) = projection W ≫ point V := by
  rw [coordinate, projection, point, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext z <;> simp

private lemma scale_zero (a : Vector b p) : scale b p 0 a = zero b p := by
  apply Subtype.ext
  change coordinate (0 • (LinearMap.id : K →ₗ[K] K)) ≫ a.val = projection K ≫ b
  rw [zero_smul, coordinate_zero, Category.assoc, a.property.1]

private lemma scale_one (a : Vector b p) : scale b p 1 a = a := by
  apply Subtype.ext
  change coordinate (1 • (LinearMap.id : K →ₗ[K] K)) ≫ a.val = a.val
  rw [one_smul, coordinate_id, Category.id_comp]

/-- Linear maps with prescribed coordinates produce the prescribed two-copy gluing. -/
private lemma extension_of_pair (a : Vector b p) (r t : K) :
    extension b p (scale b p r a) (scale b p t a) =
      coordinate (LinearMap.pi ![r • LinearMap.id, t • LinearMap.id]) ≫ a.val := by
  symm
  apply extension_unique
  intro i
  rw [← Category.assoc, coordinate_comp]
  fin_cases i <;> rfl

private lemma add_scales (a : Vector b p) (r t : K) :
    add b p (scale b p r a) (scale b p t a) = scale b p (r + t) a := by
  apply Subtype.ext
  change coordinate _ ≫ extension b p (scale b p r a) (scale b p t a) = _
  rw [extension_of_pair, ← Category.assoc, coordinate_comp]
  have hlin :
      ((LinearMap.proj 0 : (Fin 2 → K) →ₗ[K] K) + LinearMap.proj 1).comp
        (LinearMap.pi ![r • LinearMap.id, t • LinearMap.id]) =
      (r + t) • (LinearMap.id : K →ₗ[K] K) := by
    apply LinearMap.ext; intro z
    simp [add_mul]
  rw [hlin]
  rfl

private lemma add_zero_left (a : Vector b p) : add b p (zero b p) a = a := by
  have h := add_scales b p a 0 1
  simpa only [scale_zero, scale_one, zero_add] using h

private lemma add_zero_right (a : Vector b p) : add b p a (zero b p) = a := by
  have h := add_scales b p a 1 0
  simpa only [scale_zero, scale_one, add_zero] using h

private lemma add_neg_left (a : Vector b p) :
    add b p (scale b p (-1) a) a = zero b p := by
  conv_lhs => arg 4; rw [← scale_one b p a]
  rw [add_scales, neg_add_cancel, scale_zero]

private lemma add_commute (a d : Vector b p) : add b p a d = add b p d a := by
  let swap : (Fin 2 → K) →ₗ[K] (Fin 2 → K) :=
    LinearMap.pi ![LinearMap.proj 1, LinearMap.proj 0]
  have h : extension b p d a = coordinate swap ≫ extension b p a d := by
    symm
    apply extension_unique
    intro i
    rw [← Category.assoc, coordinate_comp]
    fin_cases i
    · change coordinate ((LinearMap.proj 0).comp swap) ≫ extension b p a d = d.val
      have hs : (LinearMap.proj 0).comp swap = LinearMap.proj 1 := by
        apply LinearMap.ext
        intro z
        rfl
      rw [hs, extension_restrict]
      rfl
    · change coordinate ((LinearMap.proj 1).comp swap) ≫ extension b p a d = a.val
      have hs : (LinearMap.proj 1).comp swap = LinearMap.proj 0 := by
        apply LinearMap.ext
        intro z
        rfl
      rw [hs, extension_restrict]
      rfl
  apply Subtype.ext
  change coordinate _ ≫ extension b p a d = coordinate _ ≫ extension b p d a
  rw [h, ← Category.assoc, coordinate_comp]
  have hlin :
      ((LinearMap.proj 0 : (Fin 2 → K) →ₗ[K] K) + LinearMap.proj 1).comp swap =
      (LinearMap.proj 0 : (Fin 2 → K) →ₗ[K] K) + LinearMap.proj 1 := by
    apply LinearMap.ext; intro z
    exact add_comm (z 1) (z 0)
  rw [hlin]

private lemma extension_from_linear {V : Type u} [AddCommGroup V] [Module K V]
    [Module Kᵐᵒᵖ V] [IsCentralScalar K V] (a d : Vector b p)
    (F : Thickening (K := K) V ⟶ X) (f : V →ₗ[K] (Fin 2 → K))
    (h : ∀ i : Fin 2, coordinate ((LinearMap.proj i).comp f) ≫ F = ![a.val, d.val] i) :
    extension b p a d = coordinate f ≫ F := by
  symm
  apply extension_unique
  intro i
  rw [← Category.assoc, coordinate_comp]
  exact h i

private lemma add_associate (a d e : Vector b p) :
    add b p (add b p a d) e = add b p a (add b p d e) := by
  have hθ : ∀ i j : Fin 3,
      point K ≫ (![a.val, d.val, e.val] i) =
      point K ≫ (![a.val, d.val, e.val] j) := by
    intro i j
    have hi : point K ≫ (![a.val, d.val, e.val] i) = b := by
      fin_cases i
      · exact a.property.1
      · exact d.property.1
      · exact e.property.1
    have hj : point K ≫ (![a.val, d.val, e.val] j) = b := by
      fin_cases j
      · exact a.property.1
      · exact d.property.1
      · exact e.property.1
    exact hi.trans hj.symm
  obtain ⟨F, hF, _⟩ := existsUnique_dualNumberScheme_extension K 3 (by decide) X
    ![a.val, d.val, e.val] hθ
  change ∀ i : Fin 3, coordinate (LinearMap.proj i) ≫ F = ![a.val, d.val, e.val] i at hF
  let P (i : Fin 3) : (Fin 3 → K) →ₗ[K] K := LinearMap.proj i
  let sum := (LinearMap.proj 0 : (Fin 2 → K) →ₗ[K] K) + LinearMap.proj 1
  let leftPair := LinearMap.pi ![P 0, P 1]
  let rightPair := LinearMap.pi ![P 1, P 2]
  have hL : extension b p a d = coordinate leftPair ≫ F := by
    apply extension_from_linear
    intro i
    fin_cases i
    · change coordinate ((LinearMap.proj 0).comp leftPair) ≫ F = a.val
      have h : (LinearMap.proj 0).comp leftPair = P 0 := by
        apply LinearMap.ext
        intro z
        rfl
      rw [h]
      exact hF 0
    · change coordinate ((LinearMap.proj 1).comp leftPair) ≫ F = d.val
      have h : (LinearMap.proj 1).comp leftPair = P 1 := by
        apply LinearMap.ext
        intro z
        rfl
      rw [h]
      exact hF 1
  have hR : extension b p d e = coordinate rightPair ≫ F := by
    apply extension_from_linear
    intro i
    fin_cases i
    · change coordinate ((LinearMap.proj 0).comp rightPair) ≫ F = d.val
      have h : (LinearMap.proj 0).comp rightPair = P 1 := by
        apply LinearMap.ext
        intro z
        rfl
      rw [h]
      exact hF 1
    · change coordinate ((LinearMap.proj 1).comp rightPair) ≫ F = e.val
      have h : (LinearMap.proj 1).comp rightPair = P 2 := by
        apply LinearMap.ext
        intro z
        rfl
      rw [h]
      exact hF 2
  have hvL : (add b p a d).val = coordinate (P 0 + P 1) ≫ F := by
    change coordinate sum ≫ extension b p a d = _
    rw [hL, ← Category.assoc, coordinate_comp]
    rfl
  have hvR : (add b p d e).val = coordinate (P 1 + P 2) ≫ F := by
    change coordinate sum ≫ extension b p d e = _
    rw [hR, ← Category.assoc, coordinate_comp]
    rfl
  let leftGroup := LinearMap.pi ![P 0 + P 1, P 2]
  let rightGroup := LinearMap.pi ![P 0, P 1 + P 2]
  have hgL : extension b p (add b p a d) e = coordinate leftGroup ≫ F := by
    apply extension_from_linear
    intro i
    fin_cases i
    · change coordinate ((LinearMap.proj 0).comp leftGroup) ≫ F = (add b p a d).val
      have h : (LinearMap.proj 0).comp leftGroup = P 0 + P 1 := by
        apply LinearMap.ext
        intro z
        rfl
      rw [h, hvL]
    · change coordinate ((LinearMap.proj 1).comp leftGroup) ≫ F = e.val
      have h : (LinearMap.proj 1).comp leftGroup = P 2 := by
        apply LinearMap.ext
        intro z
        rfl
      rw [h]
      exact hF 2
  have hgR : extension b p a (add b p d e) = coordinate rightGroup ≫ F := by
    apply extension_from_linear
    intro i
    fin_cases i
    · change coordinate ((LinearMap.proj 0).comp rightGroup) ≫ F = a.val
      have h : (LinearMap.proj 0).comp rightGroup = P 0 := by
        apply LinearMap.ext
        intro z
        rfl
      rw [h]
      exact hF 0
    · change coordinate ((LinearMap.proj 1).comp rightGroup) ≫ F = (add b p d e).val
      have h : (LinearMap.proj 1).comp rightGroup = P 1 + P 2 := by
        apply LinearMap.ext
        intro z
        rfl
      rw [h, hvR]
  apply Subtype.ext
  change coordinate sum ≫ extension b p (add b p a d) e =
    coordinate sum ≫ extension b p a (add b p d e)
  rw [hgL, hgR, ← Category.assoc, ← Category.assoc, coordinate_comp, coordinate_comp]
  have h : sum.comp leftGroup = sum.comp rightGroup := by
    apply LinearMap.ext; intro z
    exact add_assoc (z 0) (z 1) (z 2)
  rw [h]

private lemma scale_zero_vector (t : K) : scale b p t (zero b p) = zero b p := by
  apply Subtype.ext
  change coordinate _ ≫ projection K ≫ b = projection K ≫ b
  rw [← Category.assoc, coordinate_projection]

private lemma scale_multiply (r t : K) (a : Vector b p) :
    scale b p (r * t) a = scale b p r (scale b p t a) := by
  apply Subtype.ext
  change coordinate ((r * t) • (LinearMap.id : K →ₗ[K] K)) ≫ a.val =
    coordinate (r • (LinearMap.id : K →ₗ[K] K)) ≫
      coordinate (t • (LinearMap.id : K →ₗ[K] K)) ≫ a.val
  simp only [← Category.assoc, coordinate_comp]
  have h : (r • (LinearMap.id : K →ₗ[K] K)).comp (t • LinearMap.id) =
      (r * t) • (LinearMap.id : K →ₗ[K] K) := by
    apply LinearMap.ext
    intro z
    change r * (t * z) = (r * t) * z
    exact (mul_assoc r t z).symm
  rw [h]

private lemma scale_addition (t : K) (a d : Vector b p) :
    scale b p t (add b p a d) = add b p (scale b p t a) (scale b p t d) := by
  let diagonal : (Fin 2 → K) →ₗ[K] (Fin 2 → K) := t • LinearMap.id
  let sum := (LinearMap.proj 0 : (Fin 2 → K) →ₗ[K] K) + LinearMap.proj 1
  have hE : extension b p (scale b p t a) (scale b p t d) =
      coordinate diagonal ≫ extension b p a d := by
    apply extension_from_linear
    intro i
    have h : (LinearMap.proj i).comp diagonal =
        (t • (LinearMap.id : K →ₗ[K] K)).comp (LinearMap.proj i) := by
      apply LinearMap.ext
      intro z
      rfl
    rw [h, ← coordinate_comp, Category.assoc, extension_restrict]
    fin_cases i <;> rfl
  apply Subtype.ext
  change coordinate (t • (LinearMap.id : K →ₗ[K] K)) ≫
    coordinate sum ≫ extension b p a d =
    coordinate sum ≫ extension b p (scale b p t a) (scale b p t d)
  rw [hE, ← Category.assoc, ← Category.assoc, coordinate_comp, coordinate_comp]
  have h : (t • (LinearMap.id : K →ₗ[K] K)).comp sum = sum.comp diagonal := by
    apply LinearMap.ext
    intro z
    change t * (z 0 + z 1) = t * z 0 + t * z 1
    exact mul_add t (z 0) (z 1)
  rw [h]

end AlgebraicGeometry.TangentVectorGluing

namespace AlgebraicGeometry


/-- Additive and scalar operations on dual-number tangent vectors.
(blueprint: lem-sc-tangent-vectors-operations)

Source: Stacks Project, Tag 0B2B, proof of Lemma 33.16.2.

Proof in words: the finite-copy pushout theorem supplies unique gluing. The explicit
coordinate maps give operations preserving the two required triangles. Exchanging
two coordinates proves commutativity; grouping the first two or the last two of
three coordinates proves associativity. The gluing of scale(r,θ) and scale(t,θ)
is induced by z ↦ (rz,tz), so its sum restriction is scale(r+t,θ). Taking scalars
0, 1, and -1 proves the zero and inverse laws. Scaling both coordinates of the
gluing proves scalar distributivity; composition proves multiplicativity and the
identity scalar law. Finally assemble the structures and use gluing uniqueness to
verify the specified addition formula for arbitrary compatible Θ. -/
theorem tangentVectors_operations
    (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (.of k)) (x : X) :
    let K := X.residueField x
    let D := Spec (.of (DualNumber K))
    let E := Spec (.of (TrivSqZeroExt K (Fin 2 → K)))
    let b := X.fromSpecResidueField x
    let c : Spec K ⟶ D :=
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom)
    let q : D ⟶ Spec K :=
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom K K))
    let j : Fin 2 → (D ⟶ E) := fun i =>
      Spec.map (CommRingCat.ofHom
        (TrivSqZeroExt.map (LinearMap.proj i : (Fin 2 → K) →ₗ[K] K)).toRingHom)
    let s : D ⟶ E := Spec.map (CommRingCat.ofHom
      (TrivSqZeroExt.map
        ((LinearMap.proj 0 : (Fin 2 → K) →ₗ[K] K) + LinearMap.proj 1)).toRingHom)
    let m : K → (D ⟶ D) := fun t => Spec.map (CommRingCat.ofHom
      (TrivSqZeroExt.map (t • (LinearMap.id : K →ₗ[K] K))).toRingHom)
    let T := {θ : D ⟶ X // c ≫ θ = b ∧ θ ≫ p = q ≫ b ≫ p}
    ∃ a : AddCommGroup T, letI := a;
      ∃ v : Module K T, letI := v;
        (0 : T).val = q ≫ b ∧
        (∀ θ₁ θ₂ : T, ∀ Θ : E ⟶ X,
          j 0 ≫ Θ = θ₁.val → j 1 ≫ Θ = θ₂.val → (θ₁ + θ₂).val = s ≫ Θ) ∧
        (∀ (t : K) (θ : T), (t • θ).val = m t ≫ θ.val) := by
  dsimp only
  let b := X.fromSpecResidueField x
  let : Zero (TangentVectorGluing.Vector b p) := ⟨TangentVectorGluing.zero b p⟩
  let : Add (TangentVectorGluing.Vector b p) := ⟨TangentVectorGluing.add b p⟩
  let : Neg (TangentVectorGluing.Vector b p) := ⟨TangentVectorGluing.scale b p (-1)⟩
  let a : AddCommGroup (TangentVectorGluing.Vector b p) :=
    { add := TangentVectorGluing.add b p
      zero := TangentVectorGluing.zero b p
      neg := TangentVectorGluing.scale b p (-1)
      add_assoc := TangentVectorGluing.add_associate b p
      add_comm := TangentVectorGluing.add_commute b p
      zero_add := TangentVectorGluing.add_zero_left b p
      add_zero := TangentVectorGluing.add_zero_right b p
      neg_add_cancel := TangentVectorGluing.add_neg_left b p
      nsmul := nsmulRec
      zsmul := zsmulRec }
  refine ⟨a, ?_⟩
  let v : Module (X.residueField x) (TangentVectorGluing.Vector b p) :=
    { smul := TangentVectorGluing.scale b p
      one_smul := TangentVectorGluing.scale_one b p
      mul_smul := TangentVectorGluing.scale_multiply b p
      smul_zero := TangentVectorGluing.scale_zero_vector b p
      smul_add := TangentVectorGluing.scale_addition b p
      add_smul := fun r t θ => (TangentVectorGluing.add_scales b p θ r t).symm
      zero_smul := TangentVectorGluing.scale_zero b p }
  refine ⟨v, rfl, ?_, ?_⟩
  · intro θ₁ θ₂ Θ h₁ h₂
    change TangentVectorGluing.coordinate _ ≫ TangentVectorGluing.extension b p θ₁ θ₂ = _
    have h : Θ = TangentVectorGluing.extension b p θ₁ θ₂ := by
      apply TangentVectorGluing.extension_unique
      intro i
      fin_cases i
      · exact h₁
      · exact h₂
    rw [h]
  · intro t θ
    rfl

end AlgebraicGeometry
