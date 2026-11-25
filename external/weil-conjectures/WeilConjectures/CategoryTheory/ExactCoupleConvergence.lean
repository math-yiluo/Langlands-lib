/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ExactCouple
public import WeilConjectures.CategoryTheory.PBCFiltration

import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.CategoryTheory.SubobjectHomologyStep

/-!
# Convergence of bigraded exact couples

Source: blueprint, def-sp-convergence; Stacks Project, Homology, Sections 12.20 and 12.21,
and Definition 12.24.9 (Tag 012U) (blueprint: def-sp-convergence).

The natural-number index `r` below represents page `r + 2`. Colimits and inverse limits
are expressed by their universal properties on the consecutive arrows of the integer chain.
No infinite (co)limits or complete lattice of subobjects are assumed in the ambient category.
-/

@[expose] public section

universe u v

open CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Cycles and boundaries inside the initial page, with its canonical quotient maps.
The successor projection is induced by the preceding projection on cycles; this rules out
arbitrary identifications of the quotient with the next page.
Source: blueprint def-sp-convergence, cycle/boundary recursion; Stacks Section 12.20
(blueprint: def-sp-convergence). -/
structure CycleBoundaryTower (X : BigradedExactCouple C 0) where
  Z : ℕ → ∀ p q : ℤ, Subobject (X.E p q)
  B : ℕ → ∀ p q : ℤ, Subobject (X.E p q)
  B_le_Z : ∀ r p q, B r p q ≤ Z r p q
  Z_zero : ∀ p q, Z 0 p q = ⊤
  B_zero : ∀ p q, B 0 p q = ⊥
  projection : ∀ r p q, (Z r p q : C) ⟶ (X.pageCouple r).E p q
  projection_epi : ∀ r p q, Epi (projection r p q)
  projection_kernel : ∀ r p q,
    kernelSubobject (projection r p q) =
      Subobject.mk (Subobject.ofLE (B r p q) (Z r p q) (B_le_Z r p q))
  projection_zero : ∀ p q, projection 0 p q = (Z 0 p q).arrow
  Z_succ : ∀ r p q, Z (r + 1) p q =
    (Subobject.«exists» (Z r p q).arrow).obj
      ((Subobject.pullback (projection r p q)).obj
        (kernelSubobject ((X.pageCouple r).d p q)))
  B_succ : ∀ r p q, B (r + 1) p q =
    (Subobject.«exists» (Z r p q).arrow).obj
      ((Subobject.pullback (projection r p q)).obj
        (imageSubobject ((X.pageCouple r).dInto p q)))
  Z_decreasing : ∀ r p q, Z (r + 1) p q ≤ Z r p q
  B_increasing : ∀ r p q, B r p q ≤ B (r + 1) p q
  cycleLift : ∀ r p q,
    (Z (r + 1) p q : C) ⟶ kernel ((X.pageCouple r).d p q)
  cycleLift_comm : ∀ r p q,
    cycleLift r p q ≫ kernel.ι ((X.pageCouple r).d p q) =
      Subobject.ofLE _ _ (Z_decreasing r p q) ≫ projection r p q
  projection_succ : ∀ r p q,
    projection (r + 1) p q =
      cycleLift r p q ≫ (X.pageCouple r).derivedEProjection p q

private structure TowerStage (X : BigradedExactCouple C 0) (r : ℕ) where
  Z : ∀ p q : ℤ, Subobject (X.E p q)
  B : ∀ p q : ℤ, Subobject (X.E p q)
  B_le_Z : ∀ p q, B p q ≤ Z p q
  projection : ∀ p q, (Z p q : C) ⟶ (X.pageCouple r).E p q
  projection_epi : ∀ p q, Epi (projection p q)
  projection_kernel : ∀ p q,
    kernelSubobject (projection p q) =
      Subobject.mk (Subobject.ofLE (B p q) (Z p q) (B_le_Z p q))

private noncomputable def stageCycles {X : BigradedExactCouple C 0} {r : ℕ}
    (S : TowerStage X r) (p q : ℤ) : Subobject (X.E p q) :=
  (Subobject.«exists» (S.Z p q).arrow).obj
    ((Subobject.pullback (S.projection p q)).obj
      (kernelSubobject ((X.pageCouple r).d p q)))

private noncomputable def stageBoundaries {X : BigradedExactCouple C 0} {r : ℕ}
    (S : TowerStage X r) (p q : ℤ) : Subobject (X.E p q) :=
  (Subobject.«exists» (S.Z p q).arrow).obj
    ((Subobject.pullback (S.projection p q)).obj
      (imageSubobject ((X.pageCouple r).dInto p q)))

private structure StageTransition {X : BigradedExactCouple C 0} {r : ℕ}
    (S : TowerStage X r) (p q : ℤ) where
  decreasing : stageCycles S p q ≤ S.Z p q
  increasing : S.B p q ≤ stageBoundaries S p q
  boundary_le_cycle : stageBoundaries S p q ≤ stageCycles S p q
  lift : (stageCycles S p q : C) ⟶ kernel ((X.pageCouple r).d p q)
  comm : lift ≫ kernel.ι ((X.pageCouple r).d p q) =
    Subobject.ofLE _ _ decreasing ≫ S.projection p q
  epi : Epi (lift ≫ (X.pageCouple r).derivedEProjection p q)
  kernel_eq : kernelSubobject (lift ≫ (X.pageCouple r).derivedEProjection p q) =
    Subobject.mk (Subobject.ofLE _ _ boundary_le_cycle)

private theorem stageTransition_exists {X : BigradedExactCouple C 0} {r : ℕ}
    (S : TowerStage X r) (p q : ℤ) : Nonempty (StageTransition S p q) := by
  let : Epi (S.projection p q) := S.projection_epi p q
  obtain ⟨hZ, hB, hBZ, l, hl, hepi, hker⟩ :=
    subobjectHomology_step (S.Z p q) (S.B p q) (S.B_le_Z p q)
      (S.projection p q) (S.projection_kernel p q)
      ((X.pageCouple r).dInto p q) ((X.pageCouple r).d p q)
      ((X.pageCouple r).dInto_comp_d p q)
  exact ⟨⟨hZ, hB, hBZ, l, hl, hepi, hker⟩⟩

-- The subobjects are explicit pullbacks/images. Only their unique kernel lift is chosen:
-- its composite with the monomorphic kernel inclusion is specified by `comm`.
private noncomputable def stageTransition {X : BigradedExactCouple C 0} {r : ℕ}
    (S : TowerStage X r) (p q : ℤ) : StageTransition S p q :=
  Classical.choice (stageTransition_exists S p q)

private noncomputable def nextStage {X : BigradedExactCouple C 0} {r : ℕ}
    (S : TowerStage X r) : TowerStage X (r + 1) where
  Z := stageCycles S
  B := stageBoundaries S
  B_le_Z p q := (stageTransition S p q).boundary_le_cycle
  projection p q := (stageTransition S p q).lift ≫
    (X.pageCouple r).derivedEProjection p q
  projection_epi p q := (stageTransition S p q).epi
  projection_kernel p q := (stageTransition S p q).kernel_eq

private noncomputable def initialStage (X : BigradedExactCouple C 0) : TowerStage X 0 where
  Z _ _ := ⊤
  B _ _ := ⊥
  B_le_Z _ _ := bot_le
  projection p q := (⊤ : Subobject (X.E p q)).arrow
  projection_epi _ _ := inferInstance
  projection_kernel p q := by
    have hk : kernelSubobject (⊤ : Subobject (X.E p q)).arrow = ⊥ :=
      Subobject.mk_eq_bot_iff_zero.mpr (kernel.ι_of_mono _)
    have hb : Subobject.ofLE (⊥ : Subobject (X.E p q)) ⊤ bot_le = 0 := by
      apply (cancel_mono (⊤ : Subobject (X.E p q)).arrow).mp
      simp
    exact hk.trans (Subobject.mk_eq_bot_iff_zero.mpr hb).symm

private noncomputable def towerStages (X : BigradedExactCouple C 0) :
    ∀ r : ℕ, TowerStage X r
  | 0 => initialStage X
  | r + 1 => nextStage (towerStages X r)

/-- The canonical cycle/boundary tower exists. Start with the whole initial page and zero,
with its identity quotient. Inductively pull back the kernel and image of the differential
along the quotient, and embed these pullbacks in the initial page. Since the differential
squares to zero, boundaries lie in cycles. The epimorphic quotient of the lifted cycles by
the lifted boundaries is the homology object defining the next derived couple. Its projection
is the kernel lift followed by `derivedEProjection`. Pullback along an epimorphism preserves
these quotient presentations. This also gives the decreasing and increasing inclusions.
Source: blueprint def-sp-convergence; Stacks Sections 12.20--12.21
(blueprint: def-sp-convergence). -/
theorem cycleBoundaryTower_exists (X : BigradedExactCouple C 0) :
    Nonempty (CycleBoundaryTower X) := by
  refine ⟨{
    Z := fun r ↦ (towerStages X r).Z
    B := fun r ↦ (towerStages X r).B
    B_le_Z := fun r ↦ (towerStages X r).B_le_Z
    Z_zero := fun _ _ ↦ rfl
    B_zero := fun _ _ ↦ rfl
    projection := fun r ↦ (towerStages X r).projection
    projection_epi := fun r ↦ (towerStages X r).projection_epi
    projection_kernel := fun r ↦ (towerStages X r).projection_kernel
    projection_zero := fun _ _ ↦ rfl
    Z_succ := fun _ _ _ ↦ rfl
    B_succ := fun _ _ _ ↦ rfl
    Z_decreasing := fun r p q ↦ (stageTransition (towerStages X r) p q).decreasing
    B_increasing := fun r p q ↦ (stageTransition (towerStages X r) p q).increasing
    cycleLift := fun r p q ↦ (stageTransition (towerStages X r) p q).lift
    cycleLift_comm := fun r p q ↦ (stageTransition (towerStages X r) p q).comm
    projection_succ := fun _ _ _ ↦ rfl }⟩

/-- The cycle/boundary tower constructed recursively from the exact couple.
Source: blueprint def-sp-convergence (blueprint: def-sp-convergence). -/
noncomputable def cycleBoundaryTower (X : BigradedExactCouple C 0) : CycleBoundaryTower X :=
  Classical.choice (cycleBoundaryTower_exists X)

/-- Regularity means eventual constancy of boundaries at every bidegree, with a bound that may
vary with the bidegree, i.e. the incoming differentials vanish for `r ≫ 0`.
Source: blueprint def-sp-convergence; Stacks Section 12.20
(blueprint: def-sp-convergence). -/
def IsRegular (X : BigradedExactCouple C 0) : Prop :=
  ∀ p q : ℤ, ∃ r : ℕ, ∀ t : ℕ, r ≤ t →
    X.cycleBoundaryTower.B t p q = X.cycleBoundaryTower.B r p q

/-- Iterate `alpha` to the left along a fixed total degree.
Source: blueprint def-sp-convergence, completeness clause (blueprint: def-sp-convergence). -/
def alphaIter (X : BigradedExactCouple C 0) :
    ∀ (r : ℕ) (p q : ℤ), X.D p q ⟶ X.D (p - r) (q + r)
  | 0, p, q => eqToHom (by congr 1 <;> omega)
  | r + 1, p, q => X.alpha p q ≫ alphaIter X r (p - 1) (q + 1) ≫
      eqToHom (by congr 1 <;> omega)

/-- The incoming `r`-fold iterate, with its endpoint transported to `(p,q)`.
Source: blueprint def-sp-convergence (blueprint: def-sp-convergence). -/
def incomingAlphaIter (X : BigradedExactCouple C 0) (r : ℕ) (p q : ℤ) :
    X.D (p + r) (q - r) ⟶ X.D p q :=
  X.alphaIter r (p + r) (q - r) ≫ eqToHom (by congr 1 <;> omega)

/-- Completeness of the couple: the intersection of all incoming `alpha` images is zero.
Expressing this as every common lower bound being zero does not assume other intersections.
Source: blueprint def-sp-convergence (blueprint: def-sp-convergence). -/
def IsComplete (X : BigradedExactCouple C 0) : Prop :=
  ∀ (p q : ℤ) (S : Subobject (X.D p q)),
    (∀ r : ℕ, S ≤ imageSubobject (X.incomingAlphaIter r p q)) → S = ⊥

/-- Boundedness requires finite support on each total-degree diagonal of the initial page.
Source: blueprint def-sp-convergence (blueprint: def-sp-convergence). -/
def IsBounded (X : BigradedExactCouple C 0) : Prop :=
  ∀ n : ℤ, Set.Finite {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧ ¬ IsZero (X.E pq.1 pq.2)}

/-- The limiting cycles and boundaries, when their greatest lower and least upper bounds
exist. Source: blueprint def-sp-convergence (blueprint: def-sp-convergence). -/
structure LimitSubobjects (X : BigradedExactCouple C 0) where
  Z : ∀ p q : ℤ, Subobject (X.E p q)
  B : ∀ p q : ℤ, Subobject (X.E p q)
  Z_glb : ∀ p q, IsGLB (Set.range (fun r ↦ X.cycleBoundaryTower.Z r p q)) (Z p q)
  B_lub : ∀ p q, IsLUB (Set.range (fun r ↦ X.cycleBoundaryTower.B r p q)) (B p q)

/-- Every limiting boundary lies in every limiting cycle. For any two finite indices,
move to their maximum: increasing boundaries lie in the cycles there, which lie in the
earlier cycles. The universal properties of the union and intersection give the result.
Source: blueprint def-sp-convergence (blueprint: def-sp-convergence). -/
theorem limitBoundary_le_cycle (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (p q : ℤ) : L.B p q ≤ L.Z p q := by
  let T := X.cycleBoundaryTower
  have hB : Monotone (fun r ↦ T.B r p q) :=
    monotone_nat_of_le_succ (fun r ↦ T.B_increasing r p q)
  have hZ : Antitone (fun r ↦ T.Z r p q) :=
    antitone_nat_of_succ_le (fun r ↦ T.Z_decreasing r p q)
  apply (L.Z_glb p q).2
  rintro _ ⟨r, rfl⟩
  apply (L.B_lub p q).2
  rintro _ ⟨s, rfl⟩
  exact (hB (Nat.le_max_left s r)).trans
    ((T.B_le_Z (max s r) p q).trans (hZ (Nat.le_max_right s r)))

/-- The infinite page is the quotient of limiting cycles by limiting boundaries.
Source: blueprint def-sp-convergence (blueprint: def-sp-convergence). -/
noncomputable def pageInfinity (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (p q : ℤ) : C :=
  cokernel (Subobject.ofLE (L.B p q) (L.Z p q) (limitBoundary_le_cycle X L p q))

/-- The initial `g`, transported from its type-zero target to `(p,q)`.
Source: blueprint def-sp-convergence (blueprint: def-sp-convergence). -/
def initialG (X : BigradedExactCouple C 0) (p q : ℤ) : X.D p q ⟶ X.E p q :=
  X.g p q ≫ eqToHom (by congr 1 <;> omega)

/-- The initial `g` lands in every finite cycle object, hence in their intersection.
The exact-couple cycle formula is `Z_{r+2} = f⁻¹(im alpha^r)` inside the initial page,
with the component indices determined by the bidegrees. Prove it by induction from
`Z₂ = E₂`, using the derived-couple restriction equations and the successor projection.
Since `g ≫ f = 0`, the image of the initial `g` lies in every such inverse image:
the zero morphism factors through each incoming iterate of `alpha`. Thus its image is
a common lower bound of the finite cycles, so `L.Z_glb` places it below `L.Z`.
The image factorization then gives the required morphism into the limiting cycles.
Source: blueprint def-sp-convergence; Stacks Section 12.21
(blueprint: def-sp-convergence). -/
theorem g_factors_limitCycles (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (p q : ℤ) : (L.Z p q).Factors (X.initialG p q) := by
  let T := X.cycleBoundaryTower
  have hfinite : ∀ r : ℕ, ∃ a : X.D p q ⟶ (T.Z r p q : C),
      a ≫ (T.Z r p q).arrow = X.initialG p q ∧
      a ≫ T.projection r p q ≫ (X.pageCouple r).f p q = 0 := by
    intro r
    induction r with
    | zero =>
      have hfac : (T.Z 0 p q).Factors (X.initialG p q) := by
        rw [T.Z_zero]
        exact Subobject.top_factors _
      refine ⟨(T.Z 0 p q).factorThru _ hfac, by simp, ?_⟩
      rw [T.projection_zero, ← Category.assoc, Subobject.factorThru_arrow]
      change X.initialG p q ≫ X.f p q = 0
      rw [initialG, Category.assoc,
        ← eqToHom_naturality (fun pq : ℤ × ℤ ↦ X.f pq.1 pq.2)
          (show (p + (0 : ℕ), q - (0 : ℕ)) = (p, q) by ext <;> simp),
        ← Category.assoc, X.f_g_zero, zero_comp]
    | succ r ih =>
      obtain ⟨a, ha, hf⟩ := ih
      let P := (Subobject.pullback (T.projection r p q)).obj
        (kernelSubobject ((X.pageCouple r).d p q))
      have hpa : P.Factors a := by
        apply pullback_factors
        apply kernelSubobject_factors
        simpa only [d, Category.assoc, zero_comp] using
          congrArg (fun z ↦ z ≫ (X.pageCouple r).g (p + 2) (q - 1)) hf
      have hfac : (T.Z (r + 1) p q).Factors (X.initialG p q) := by
        rw [T.Z_succ, Subobject.exists_obj_eq_imageSubobject]
        rw [← ha, ← P.factorThru_arrow a hpa, Category.assoc]
        exact imageSubobject_factors_comp_self _ _
      let b := (T.Z (r + 1) p q).factorThru (X.initialG p q) hfac
      have hb : b ≫ Subobject.ofLE _ _ (T.Z_decreasing r p q) = a := by
        apply (cancel_mono (T.Z r p q).arrow).mp
        simp [b, ha, Category.assoc]
      refine ⟨b, by simp [b], ?_⟩
      let Y := X.pageCouple r
      let M := Classical.choice Y.derivedMaps_exists
      have hmono : Mono (Y.derivedDInclusion (p + 2) (q - 1)) := by
        dsimp [derivedDInclusion]
        infer_instance
      let := hmono
      apply (cancel_mono (Y.derivedDInclusion (p + 2) (q - 1))).mp
      change (b ≫ T.projection (r + 1) p q ≫ M.f p q) ≫
        Y.derivedDInclusion (p + 2) (q - 1) = _
      rw [Category.assoc]
      rw [T.projection_succ, Category.assoc, Category.assoc, M.f_comm, zero_comp]
      change b ≫ T.cycleLift r p q ≫
        kernel.ι ((X.pageCouple r).d p q) ≫ (X.pageCouple r).f p q = _
      rw [← Category.assoc (T.cycleLift r p q), T.cycleLift_comm]
      simp only [← Category.assoc]
      rw [hb]
      simpa only [Category.assoc] using hf
  apply (Subobject.imageSubobject_le_iff _ _).mp
  apply (L.Z_glb p q).2
  rintro _ ⟨r, rfl⟩
  obtain ⟨a, ha, _⟩ := hfinite r
  exact imageSubobject_le _ a ha

/-- The canonical map from `D` to the infinite page, induced by `g`.
Source: blueprint def-sp-convergence (blueprint: def-sp-convergence). -/
noncomputable def toPageInfinity (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (p q : ℤ) : X.D p q ⟶ X.pageInfinity L p q :=
  (L.Z p q).factorThru (X.initialG p q) (g_factors_limitCycles X L p q) ≫
    cokernel.π (Subobject.ofLE (L.B p q) (L.Z p q) (limitBoundary_le_cycle X L p q))

/-- The consecutive transition on the total-degree-`n` diagonal.
Source: blueprint def-sp-convergence (blueprint: def-sp-convergence). -/
def alphaDiagonal (X : BigradedExactCouple C 0) (n p : ℤ) :
    X.D (p + 1) (n - (p + 1)) ⟶ X.D p (n - p) :=
  X.alpha (p + 1) (n - (p + 1)) ≫ eqToHom (by congr 1 <;> omega)

/-- A colimit of the `D` diagonal along `alpha`, directed towards negative infinity.
The universal property for consecutive arrows is the colimit universal property: every
arrow of the ordered integer chain is a finite composite of these arrows.
Source: blueprint def-sp-convergence (blueprint: def-sp-convergence). -/
structure AlphaColimit (X : BigradedExactCouple C 0) (n : ℤ) where
  obj : C
  ι : ∀ p : ℤ, X.D p (n - p) ⟶ obj
  comm : ∀ p, X.alphaDiagonal n p ≫ ι p = ι (p + 1)
  isColimit : ∀ (T : C) (f : ∀ p : ℤ, X.D p (n - p) ⟶ T),
    (∀ p, X.alphaDiagonal n p ≫ f p = f (p + 1)) →
    ∃! h : obj ⟶ T, ∀ p, ι p ≫ h = f p

/-- The image filtration is decreasing. The cocone equation factors the next canonical
map through the current one, so its image is contained in the current image. Iterating
this inclusion a finite number of times proves antitonicity for arbitrary integers.
Source: blueprint def-sp-convergence (blueprint: def-sp-convergence). -/
theorem imageFiltration_antitone (X : BigradedExactCouple C 0) (n : ℤ)
    (A : AlphaColimit X n) : Antitone (fun p ↦ imageSubobject (A.ι p)) := by
  apply antitone_int_of_succ_le
  intro p
  rw [← A.comm p]
  exact imageSubobject_comp_le _ _

/-- The decreasing filtration on the alpha-colimit by images of its canonical maps.
Source: blueprint def-sp-convergence (blueprint: def-sp-convergence). -/
noncomputable def imageFiltration (X : BigradedExactCouple C 0) (n : ℤ)
    (A : AlphaColimit X n) : PBCDecreasingFiltration A.obj where
  step p := imageSubobject (A.ι p)
  antitone_step := imageFiltration_antitone X n A

/-- The canonical map from `D^{p,q}` onto the graded piece of its image filtration.
Source: blueprint def-sp-convergence (blueprint: def-sp-convergence). -/
noncomputable def toGradedPiece (X : BigradedExactCouple C 0)
    (A : ∀ n : ℤ, AlphaColimit X n) (p q : ℤ) :
    X.D p q ⟶ (X.imageFiltration (p + q) (A (p + q))).gradedPiece p :=
  eqToHom (by congr 1; omega) ≫ factorThruImageSubobject ((A (p + q)).ι p) ≫
    cokernel.π (Subobject.ofLE _ _
      ((X.imageFiltration (p + q) (A (p + q))).antitone_step (by omega)))

/-- Weak convergence: the two canonical maps are epimorphic and have identical kernels.
Source: blueprint def-sp-convergence; Stacks Tag 012U (blueprint: def-sp-convergence). -/
def WeaklyConvergesTo (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (A : ∀ n : ℤ, AlphaColimit X n) : Prop :=
  ∀ p q : ℤ, Epi (X.toPageInfinity L p q) ∧ Epi (X.toGradedPiece A p q) ∧
    kernelSubobject (X.toPageInfinity L p q) = kernelSubobject (X.toGradedPiece A p q)

/-- The canonical associated-graded isomorphisms induced by weak convergence exist.
Both targets are the quotient of `D^{p,q}` by the same kernel, because both maps are
epimorphisms in an abelian category. The first isomorphism theorem gives their unique
comparison isomorphism commuting with the two quotient maps.
Source: blueprint def-sp-convergence; Stacks Tag 012U (blueprint: def-sp-convergence). -/
theorem weakConvergence_comparison (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (A : ∀ n : ℤ, AlphaColimit X n) (h : X.WeaklyConvergesTo L A) (p q : ℤ) :
    ∃! e : X.pageInfinity L p q ≅
      (X.imageFiltration (p + q) (A (p + q))).gradedPiece p,
      X.toPageInfinity L p q ≫ e.hom = X.toGradedPiece A p q := by
  let f := X.toPageInfinity L p q
  let g := X.toGradedPiece A p q
  obtain ⟨hf, hg, hk⟩ := h p q
  let : Epi f := hf
  let : Epi g := hg
  have hfg : kernel.ι f ≫ g = 0 := by
    apply (kernelSubobject_factors_iff g _).mp
    rw [← hk]
    exact kernelSubobject_factors f _ (kernel.condition f)
  have hgf : kernel.ι g ≫ f = 0 := by
    apply (kernelSubobject_factors_iff f _).mp
    rw [hk]
    exact kernelSubobject_factors g _ (kernel.condition g)
  let e : X.pageInfinity L p q ≅
      (X.imageFiltration (p + q) (A (p + q))).gradedPiece p :=
    { hom := Abelian.epiDesc f g hfg
      inv := Abelian.epiDesc g f hgf
      hom_inv_id := by
        apply (cancel_epi f).1
        simp
      inv_hom_id := by
        apply (cancel_epi g).1
        simp }
  refine ⟨e, Abelian.comp_epiDesc f g hfg, ?_⟩
  intro e' he'
  apply Iso.ext
  apply (cancel_epi f).1
  exact he'.trans (Abelian.comp_epiDesc f g hfg).symm

/-- Abutting means weak convergence and separated, exhaustive image filtrations.
Source: blueprint def-sp-convergence; Stacks Tag 012U (blueprint: def-sp-convergence). -/
def AbutsTo (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (A : ∀ n : ℤ, AlphaColimit X n) : Prop :=
  X.WeaklyConvergesTo L A ∧ ∀ n : ℤ,
    (X.imageFiltration n (A n)).IsSeparated ∧ (X.imageFiltration n (A n)).IsExhaustive

/-- A later filtration step is killed by the earlier quotient map: its inclusion factors
through the earlier step, whose composite with its cokernel projection is zero.
Source: blueprint def-sp-convergence, inverse-limit clause (blueprint: def-sp-convergence). -/
theorem filtrationStep_comp_quotient_zero {T : C} (F : PBCDecreasingFiltration T) (p : ℤ) :
    (F.step (p + 1)).arrow ≫ cokernel.π (F.step p).arrow = 0 := by
  rw [← Subobject.ofLE_arrow (F.antitone_step (show p ≤ p + 1 by omega)), Category.assoc]
  simp

/-- The transition `A/F^{p+1} → A/F^p` of the inverse system of quotients.
Source: blueprint def-sp-convergence; Stacks Tag 012U (blueprint: def-sp-convergence). -/
noncomputable def quotientTransition {T : C} (F : PBCDecreasingFiltration T) (p : ℤ) :
    cokernel (F.step (p + 1)).arrow ⟶ cokernel (F.step p).arrow :=
  cokernel.desc (F.step (p + 1)).arrow (cokernel.π (F.step p).arrow)
    (filtrationStep_comp_quotient_zero F p)

/-- The canonical cone `A → A/F^p` is an inverse limit. This is equivalent to the
canonical map `A → lim_p A/F^p` being an isomorphism, and includes existence of that limit.
Source: blueprint def-sp-convergence; Stacks Tag 012U (blueprint: def-sp-convergence). -/
def IsInverseLimit {T : C} (F : PBCDecreasingFiltration T) : Prop :=
  ∀ (S : C) (f : ∀ p : ℤ, S ⟶ cokernel (F.step p).arrow),
    (∀ p, f (p + 1) ≫ quotientTransition F p = f p) →
    ∃! h : S ⟶ T, ∀ p, h ≫ cokernel.π (F.step p).arrow = f p

/-- Convergence means regularity, abutting, and completeness of every abutment filtration
in the inverse-limit sense. Completeness of the couple itself is the separate predicate
`IsComplete` above. Source: blueprint def-sp-convergence; Stacks Tag 012U
(blueprint: def-sp-convergence). -/
def ConvergesTo (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (A : ∀ n : ℤ, AlphaColimit X n) : Prop :=
  X.IsRegular ∧ X.AbutsTo L A ∧ ∀ n : ℤ, IsInverseLimit (X.imageFiltration n (A n))

end CategoryTheory.BigradedExactCouple
