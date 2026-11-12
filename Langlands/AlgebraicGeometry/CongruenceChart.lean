import Langlands.GroupScheme.IntegralModel.CongruenceTower
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Actual pointed congruence fibres of an open chart -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace Langlands.AlgebraicGeometry.CongruenceChart

open Langlands.GroupScheme.IntegralModel

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The actual positive quotient spectrum as a test over the original ring. -/
def congruenceTestMap (n : ℕ+) :
    Over.mk (congruenceBaseMap R n) ⟶ Over.mk (𝟙 (Spec (CommRingCat.of R))) :=
  Over.homMk (congruenceBaseMap R n) (by simp)

/-- Sections congruent to a specified section modulo the actual `n`th power
of the maximal ideal. No group structure on the scheme is needed. -/
def sectionFiber (X : Over (Spec (CommRingCat.of R))) (n : ℕ+)
    (s : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ X) : Type u :=
  {x : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ X //
    congruenceTestMap R n ≫ x = congruenceTestMap R n ≫ s}

variable {R} {X Y : Over (Spec (CommRingCat.of R))}

/-- Actual chart postcomposition on the pointed congruence fibres. -/
def sectionFiberMap (c : X ⟶ Y)
    (s : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ X) (n : ℕ+) :
    sectionFiber R X n s → sectionFiber R Y n (s ≫ c) :=
  fun x => ⟨x.val ≫ c, by
    simpa only [Category.assoc] using congrArg (fun z => z ≫ c) x.property⟩

/-- Positive-level congruent sections have the same closed-point image. -/
theorem closedPoint_eq (n : ℕ+)
    (s x : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Y)
    (hx : congruenceTestMap R n ≫ x = congruenceTestMap R n ≫ s) :
    x.left (IsLocalRing.closedPoint R) = s.left (IsLocalRing.closedPoint R) := by
  let t := (congruenceResidueBaseIso R).hom ≫
    congruenceTransitionBaseMap R (show (1 : ℕ+) ≤ n from one_le)
  have ht : t ≫ congruenceBaseMap R n = residueBaseMap R := by
    dsimp only [t]
    rw [Category.assoc, congruenceTransitionBaseMap_comm, congruenceResidueBaseIso_comm]
  have hleft : congruenceBaseMap R n ≫ x.left =
      congruenceBaseMap R n ≫ s.left :=
    congrArg (fun z => z.left) hx
  have hres : residueBaseMap R ≫ x.left = residueBaseMap R ≫ s.left := by
    simpa only [← Category.assoc, ht] using congrArg (fun z => t ≫ z) hleft
  have hp := congrArg
    (fun g : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ Y.left =>
      g (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) hres
  change x.left ((residueBaseMap R)
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) =
    s.left ((residueBaseMap R)
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) at hp
  have hc : residueBaseMap R (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) =
      IsLocalRing.closedPoint R :=
    IsLocalRing.comap_closedPoint (IsLocalRing.residue R)
  rwa [hc] at hp

/-- The open chart map is bijective on every positive pointed congruence fibre,
even when the chart morphism is not a group homomorphism. -/
theorem sectionFiberMap_bijective (c : X ⟶ Y) [IsOpenImmersion c.left]
    (s : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ X) (n : ℕ+) :
    Function.Bijective (sectionFiberMap c s n) := by
  let : Mono c := Over.mono_of_mono_left c
  constructor
  · intro x y h
    apply Subtype.ext
    exact (cancel_mono c).mp (congrArg Subtype.val h)
  · intro x
    have hpoint : x.val.left (IsLocalRing.closedPoint R) ∈ Set.range c.left := by
      rw [closedPoint_eq n (s ≫ c) x.val x.property]
      exact ⟨s.left (IsLocalRing.closedPoint R), rfl⟩
    have hrange : Set.range x.val.left ⊆ Set.range c.left := by
      rintro _ ⟨z, rfl⟩
      exact ((IsLocalRing.specializes_closedPoint z).map x.val.left.continuous).mem_open
        (IsOpenImmersion.isOpen_range _) hpoint
    let l := IsOpenImmersion.lift c.left x.val.left hrange
    have hl : l ≫ c.left = x.val.left := IsOpenImmersion.lift_fac _ _ _
    let y : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ X :=
      Over.homMk l (by rw [← Over.w c, ← Category.assoc, hl, Over.w x.val])
    have hy : y ≫ c = x.val := by
      apply Over.OverMorphism.ext
      exact hl
    have hycong : congruenceTestMap R n ≫ y = congruenceTestMap R n ≫ s := by
      apply (cancel_mono c).mp
      simpa only [Category.assoc, hy] using x.property
    exact ⟨⟨y, hycong⟩, Subtype.ext hy⟩

/-- The actual equivalence on pointed congruence fibres induced by an open chart. -/
def openSectionFiberEquiv (c : X ⟶ Y) [IsOpenImmersion c.left]
    (s : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ X) (n : ℕ+) :
    sectionFiber R X n s ≃ sectionFiber R Y n (s ≫ c) :=
  Equiv.ofBijective (sectionFiberMap c s n) (sectionFiberMap_bijective c s n)

@[simp] theorem openSectionFiberEquiv_val (c : X ⟶ Y) [IsOpenImmersion c.left]
    (s : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ X) (n : ℕ+)
    (x : sectionFiber R X n s) :
    (openSectionFiberEquiv c s n x).val = x.val ≫ c := rfl

/-- Pointed congruence fibres commute with the actual product over the original
integral base. -/
def productSectionFiberEquiv
    (s : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ X)
    (t : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Y) (n : ℕ+) :
    sectionFiber R (X ⊗ Y) n (lift s t) ≃
      sectionFiber R X n s × sectionFiber R Y n t where
  toFun p := (⟨p.val ≫ fst X Y, by
      have h := congrArg (fun z => z ≫ fst X Y) p.property
      simpa only [Category.assoc, lift_fst] using h⟩,
    ⟨p.val ≫ snd X Y, by
      have h := congrArg (fun z => z ≫ snd X Y) p.property
      simpa only [Category.assoc, lift_snd] using h⟩)
  invFun p := ⟨lift p.1.val p.2.val, by
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [Category.assoc, lift_fst] using p.1.property
    · simpa only [Category.assoc, lift_snd] using p.2.property⟩
  left_inv p := by
    apply Subtype.ext
    apply CartesianMonoidalCategory.hom_ext <;> simp only [lift_fst, lift_snd]
  right_inv p := by
    apply Prod.ext <;> apply Subtype.ext
    · exact lift_fst _ _
    · exact lift_snd _ _

end Langlands.AlgebraicGeometry.CongruenceChart
