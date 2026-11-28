import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.Units
import Mathlib.Data.PNat.Defs
import Mathlib.Data.Set.Lattice.Image
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.PresentedGroup

/-!
# The Steinberg presentation and its torus-defect quotient

The relators follow Steinberg, *Lectures on Chevalley Groups* (AMS, 2016),
Chapter 3, Lemma 15 and Chapter 6, Theorem 8 and its proof.
-/

namespace Langlands.Covering.BrylinskiDeligne

universe u v w z

/-- The rank branch of the Steinberg presentation. -/
inductive SteinbergRank where
  | one
  | atLeastTwo

/-- A term indexed by the root `γ = iα + jβ` in an ordered Chevalley commutator product. -/
structure SteinbergCommTerm (ι : Type u) where
  root : ι
  leftExponent : ℕ+
  rightExponent : ℕ+
  coefficient : ℤ

/-- The scalar `c t^i u^j` of a commutator term, with the coefficient cast to the field. -/
def SteinbergCommTerm.parameter {ι : Type u} (term : SteinbergCommTerm ι)
    {F : Type v} [Field F] (t u : F) : F :=
  (term.coefficient : F) * t ^ (term.leftExponent : ℕ) * u ^ (term.rightExponent : ℕ)

/-- Data for the presentation on a type of root indices. The lists specify the order of
the factors in (B) for each pair of nonopposite roots. -/
structure SteinbergPresentationData (ι : Type u) where
  rank : SteinbergRank
  opposite : ι → ι
  opposite_involutive : Function.Involutive opposite
  commutatorTerms (α β : ι) (h : β ≠ opposite α) : List (SteinbergCommTerm ι)

variable {ι : Type u} {F : Type v} [Field F]
variable {G : Type w} [Group G] {H : Type z} [Group H]

open scoped commutatorElement

namespace SteinbergPresentationData

variable (D : SteinbergPresentationData ι) (x : ι → F → G)

/-- The ordered right side of (B), evaluated at a family of root generators. -/
def commutatorProduct (α β : ι) (h : β ≠ D.opposite α) (t u : F) : G :=
  ((D.commutatorTerms α β h).map (fun term ↦ x term.root (term.parameter t u))).prod

/-- The Weyl word `x_α(a) x_{−α}(−a⁻¹) x_α(a)`. -/
def weylWord (α : ι) (a : Fˣ) : G :=
  x α (a : F) * x (D.opposite α) (-(a : F)⁻¹) * x α (a : F)

/-- The torus word `w_α(a) w_α(−1)`. -/
def torusWord (α : ι) (a : Fˣ) : G :=
  D.weylWord x α a * D.weylWord x α (-1)

/-- The torus defect `h_α(a) h_α(b) h_α(ab)⁻¹`. -/
def torusDefectWord (α : ι) (a b : Fˣ) : G :=
  D.torusWord x α a * D.torusWord x α b * (D.torusWord x α (a * b))⁻¹

@[simp] theorem map_commutatorProduct (f : G →* H) (α β : ι) (h : β ≠ D.opposite α)
    (t u : F) :
    f (D.commutatorProduct x α β h t u) =
      D.commutatorProduct (fun γ s ↦ f (x γ s)) α β h t u := by
  simp only [commutatorProduct, map_list_prod, List.map_map, Function.comp_def]

@[simp] theorem map_weylWord (f : G →* H) (α : ι) (a : Fˣ) :
    f (D.weylWord x α a) = D.weylWord (fun γ t ↦ f (x γ t)) α a := by
  simp only [weylWord, map_mul]

@[simp] theorem map_torusWord (f : G →* H) (α : ι) (a : Fˣ) :
    f (D.torusWord x α a) = D.torusWord (fun γ t ↦ f (x γ t)) α a := by
  simp only [torusWord, map_mul, map_weylWord]

@[simp] theorem map_torusDefectWord (f : G →* H) (α : ι) (a b : Fˣ) :
    f (D.torusDefectWord x α a b) = D.torusDefectWord (fun γ t ↦ f (x γ t)) α a b := by
  simp only [torusDefectWord, map_mul, map_inv, map_torusWord]

/-- A root generator before imposing the relators. -/
def freeRootGenerator (α : ι) (t : F) : FreeGroup (ι × F) :=
  FreeGroup.of (α, t)

/-- The free-group relators for root additivity (A). -/
def additiveRelations : Set (FreeGroup (ι × F)) :=
  ⋃ (α : ι) (s : F) (t : F),
    {freeRootGenerator α s * freeRootGenerator α t * (freeRootGenerator α (s + t))⁻¹}

/-- The free-group relators for the commutator formula (B). -/
def commutatorRelations : Set (FreeGroup (ι × F)) :=
  ⋃ (α : ι) (β : ι) (h : β ≠ D.opposite α) (t : F) (u : F),
    {⁅freeRootGenerator α t, freeRootGenerator β u⁆ *
      (D.commutatorProduct freeRootGenerator α β h t u)⁻¹}

/-- The free-group relators for the rank-one Weyl conjugation formula (B′). -/
def rankOneRelations : Set (FreeGroup (ι × F)) :=
  ⋃ (α : ι) (a : Fˣ) (u : F),
    {D.weylWord freeRootGenerator α a * freeRootGenerator α u *
      D.weylWord freeRootGenerator α (-a) *
      (freeRootGenerator (D.opposite α) (-((a : F) ^ (-2 : ℤ)) * u))⁻¹}

/-- Root additivity together with the relations for the supplied rank branch. -/
def steinbergRelations : Set (FreeGroup (ι × F)) :=
  additiveRelations ∪
    match D.rank with
    | .one => D.rankOneRelations
    | .atLeastTwo => D.commutatorRelations

/-- The free-group relators for torus multiplicativity (C). -/
def torusRelations : Set (FreeGroup (ι × F)) :=
  ⋃ (α : ι) (a : Fˣ) (b : Fˣ), {D.torusDefectWord freeRootGenerator α a b}

/-- The relations for the torus-defect quotient. -/
def torusQuotientRelations : Set (FreeGroup (ι × F)) :=
  D.steinbergRelations ∪ D.torusRelations

/-- The equations (A) and either (B′) or (B) in the target group. -/
def SatisfiesSteinbergRelations : Prop :=
  (∀ α s t, x α s * x α t = x α (s + t)) ∧
    match D.rank with
    | .one => ∀ (α : ι) (a : Fˣ) (u : F),
        D.weylWord x α a * x α u * D.weylWord x α (-a) =
          x (D.opposite α) (-((a : F) ^ (-2 : ℤ)) * u)
    | .atLeastTwo => ∀ (α β : ι) (h : β ≠ D.opposite α) (t u : F),
        ⁅x α t, x β u⁆ = D.commutatorProduct x α β h t u

/-- The equation (C) in the target group. -/
def SatisfiesTorusRelations : Prop :=
  ∀ (α : ι) (a b : Fˣ), D.torusWord x α a * D.torusWord x α b = D.torusWord x α (a * b)

/-- The Steinberg equations hold exactly when free evaluation kills the Steinberg relators. -/
theorem lift_eq_one_iff_steinberg :
    (∀ r ∈ D.steinbergRelations, FreeGroup.lift (fun p : ι × F ↦ x p.1 p.2) r = 1) ↔
      D.SatisfiesSteinbergRelations x := by
  have hadd :
      (∀ r ∈ additiveRelations, FreeGroup.lift (fun p : ι × F ↦ x p.1 p.2) r = 1) ↔
        ∀ α s t, x α s * x α t = x α (s + t) := by
    simp only [additiveRelations, Set.forall_mem_iUnion, Set.forall_mem_singleton,
      map_mul, map_inv, freeRootGenerator, FreeGroup.lift_apply_of, mul_inv_eq_one]
  rw [steinbergRelations, Set.forall_mem_union, SatisfiesSteinbergRelations, hadd]
  apply and_congr_right'
  cases D.rank
  · simp only [rankOneRelations, Set.forall_mem_iUnion, Set.forall_mem_singleton,
      map_mul, map_inv, map_weylWord, freeRootGenerator, FreeGroup.lift_apply_of, mul_inv_eq_one]
  · simp only [commutatorRelations, Set.forall_mem_iUnion, Set.forall_mem_singleton,
      map_mul, map_inv, map_commutatorElement, map_commutatorProduct, freeRootGenerator,
      FreeGroup.lift_apply_of, mul_inv_eq_one]

/-- Torus multiplicativity holds exactly when free evaluation kills the torus relators. -/
theorem lift_eq_one_iff_torus :
    (∀ r ∈ D.torusRelations, FreeGroup.lift (fun p : ι × F ↦ x p.1 p.2) r = 1) ↔
      D.SatisfiesTorusRelations x := by
  simp only [torusRelations, Set.forall_mem_iUnion, Set.forall_mem_singleton,
    map_torusDefectWord, freeRootGenerator, FreeGroup.lift_apply_of]
  simp only [torusDefectWord, mul_inv_eq_one, SatisfiesTorusRelations]

end SteinbergPresentationData

/-- The abstract Steinberg group on the given presentation data over `F`. -/
abbrev SteinbergGroup (F : Type v) [Field F] (D : SteinbergPresentationData ι) :=
  PresentedGroup (D.steinbergRelations (F := F))

/-- The presentation with the additional torus multiplicativity relators (C). -/
abbrev TorusDefectQuotient (F : Type v) [Field F] (D : SteinbergPresentationData ι) :=
  PresentedGroup (D.torusQuotientRelations (F := F))

variable (D : SteinbergPresentationData ι)

private theorem lift_presentedGenerators {A : Type*} (rels : Set (FreeGroup A)) :
    FreeGroup.lift (PresentedGroup.of (rels := rels)) = PresentedGroup.mk rels :=
  FreeGroup.ext_hom _ _ (fun _ ↦ FreeGroup.lift_apply_of)

namespace SteinbergGroup

/-- The distinguished root generator of the Steinberg group. -/
def rootGenerator (α : ι) (t : F) : SteinbergGroup F D :=
  PresentedGroup.of (α, t)

/-- The Weyl word of the Steinberg group. -/
abbrev weylWord (α : ι) (a : Fˣ) : SteinbergGroup F D :=
  D.weylWord (rootGenerator D) α a

/-- The torus word of the Steinberg group. -/
abbrev torusWord (α : ι) (a : Fˣ) : SteinbergGroup F D :=
  D.torusWord (rootGenerator D) α a

/-- The torus defect as an element of the Steinberg group. -/
abbrev torusDefect (α : ι) (a b : Fˣ) : SteinbergGroup F D :=
  D.torusDefectWord (rootGenerator D) α a b

/-- The distinguished root generators satisfy the Steinberg equations. -/
theorem rootGenerator_satisfiesSteinbergRelations :
    D.SatisfiesSteinbergRelations (rootGenerator (F := F) D) := by
  refine (D.lift_eq_one_iff_steinberg _).mp fun r hr ↦ ?_
  change FreeGroup.lift PresentedGroup.of r = 1
  rw [lift_presentedGenerators]
  exact PresentedGroup.one_of_mem hr

/-- Evaluation in a group whose chosen elements satisfy the Steinberg equations. -/
def evaluate (x : ι → F → G) (hx : D.SatisfiesSteinbergRelations x) :
    SteinbergGroup F D →* G :=
  PresentedGroup.toGroup ((D.lift_eq_one_iff_steinberg x).mpr hx)

@[simp] theorem evaluate_rootGenerator (x : ι → F → G)
    (hx : D.SatisfiesSteinbergRelations x) (α : ι) (t : F) :
    evaluate D x hx (rootGenerator D α t) = x α t :=
  PresentedGroup.toGroup.of _

/-- The images of the root generators determine a homomorphism from the Steinberg group. -/
theorem hom_ext {f g : SteinbergGroup F D →* G}
    (h : ∀ α t, f (rootGenerator D α t) = g (rootGenerator D α t)) : f = g :=
  PresentedGroup.ext (fun ⟨α, t⟩ ↦ h α t)

end SteinbergGroup

namespace TorusDefectQuotient

/-- The distinguished root generator of the torus-defect quotient. -/
def rootGenerator (α : ι) (t : F) : TorusDefectQuotient F D :=
  PresentedGroup.of (α, t)

/-- The Weyl word of the torus-defect quotient. -/
abbrev weylWord (α : ι) (a : Fˣ) : TorusDefectQuotient F D :=
  D.weylWord (rootGenerator D) α a

/-- The torus word of the torus-defect quotient. -/
abbrev torusWord (α : ι) (a : Fˣ) : TorusDefectQuotient F D :=
  D.torusWord (rootGenerator D) α a

/-- The distinguished root generators satisfy the Steinberg equations. -/
theorem rootGenerator_satisfiesSteinbergRelations :
    D.SatisfiesSteinbergRelations (rootGenerator (F := F) D) := by
  refine (D.lift_eq_one_iff_steinberg _).mp fun r hr ↦ ?_
  change FreeGroup.lift PresentedGroup.of r = 1
  rw [lift_presentedGenerators]
  exact PresentedGroup.one_of_mem (Or.inl hr)

/-- The distinguished root generators satisfy torus multiplicativity. -/
theorem rootGenerator_satisfiesTorusRelations :
    D.SatisfiesTorusRelations (rootGenerator (F := F) D) := by
  refine (D.lift_eq_one_iff_torus _).mp fun r hr ↦ ?_
  change FreeGroup.lift PresentedGroup.of r = 1
  rw [lift_presentedGenerators]
  exact PresentedGroup.one_of_mem (Or.inr hr)

/-- Evaluation when the chosen elements satisfy the Steinberg and torus equations. -/
def evaluate (x : ι → F → G) (hx : D.SatisfiesSteinbergRelations x)
    (ht : D.SatisfiesTorusRelations x) : TorusDefectQuotient F D →* G :=
  PresentedGroup.toGroup (Set.forall_mem_union.mpr
    ⟨(D.lift_eq_one_iff_steinberg x).mpr hx, (D.lift_eq_one_iff_torus x).mpr ht⟩)

@[simp] theorem evaluate_rootGenerator (x : ι → F → G)
    (hx : D.SatisfiesSteinbergRelations x) (ht : D.SatisfiesTorusRelations x) (α : ι) (t : F) :
    evaluate D x hx ht (rootGenerator D α t) = x α t :=
  PresentedGroup.toGroup.of _

/-- The images of the root generators determine a homomorphism from the torus-defect quotient. -/
theorem hom_ext {f g : TorusDefectQuotient F D →* G}
    (h : ∀ α t, f (rootGenerator D α t) = g (rootGenerator D α t)) : f = g :=
  PresentedGroup.ext (fun ⟨α, t⟩ ↦ h α t)

end TorusDefectQuotient

namespace SteinbergGroup

/-- Adding the torus relators induces the map that sends each root generator to its counterpart. -/
def toTorusDefectQuotient : SteinbergGroup F D →* TorusDefectQuotient F D :=
  PresentedGroup.map (MonoidHom.id _) (fun _ hr ↦ Or.inl hr)

@[simp] theorem toTorusDefectQuotient_rootGenerator (α : ι) (t : F) :
    toTorusDefectQuotient D (rootGenerator D α t) = TorusDefectQuotient.rootGenerator D α t :=
  rfl

theorem toTorusDefectQuotient_surjective :
    Function.Surjective (toTorusDefectQuotient (F := F) D) := by
  intro y
  obtain ⟨r, rfl⟩ := PresentedGroup.mk_surjective _ y
  exact ⟨PresentedGroup.mk _ r, rfl⟩

/-- The map to the torus-defect quotient kills exactly the normal closure of the torus defects. -/
theorem ker_toTorusDefectQuotient :
    (toTorusDefectQuotient (F := F) D).ker =
      Subgroup.normalClosure (⋃ (α : ι) (a : Fˣ) (b : Fˣ), {torusDefect D α a b}) := by
  unfold toTorusDefectQuotient PresentedGroup.map
  erw [QuotientGroup.ker_map]
  rw [Subgroup.comap_id, SteinbergPresentationData.torusQuotientRelations,
    Subgroup.normalClosure_union, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
    Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective _)]
  simp only [SteinbergPresentationData.torusRelations, Set.image_iUnion, Set.image_singleton,
    SteinbergPresentationData.map_torusDefectWord]
  rfl

/-- Evaluation after the quotient map agrees with Steinberg evaluation. -/
theorem evaluate_comp_toTorusDefectQuotient (x : ι → F → G)
    (hx : D.SatisfiesSteinbergRelations x) (ht : D.SatisfiesTorusRelations x) :
    (TorusDefectQuotient.evaluate D x hx ht).comp (toTorusDefectQuotient D) = evaluate D x hx := by
  apply hom_ext D
  intro α t
  simp only [MonoidHom.comp_apply, toTorusDefectQuotient_rootGenerator,
    TorusDefectQuotient.evaluate_rootGenerator, evaluate_rootGenerator]

end SteinbergGroup

end Langlands.Covering.BrylinskiDeligne
