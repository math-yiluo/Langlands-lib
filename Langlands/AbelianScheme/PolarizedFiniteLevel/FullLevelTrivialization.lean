import Langlands.AbelianScheme.PolarizedFiniteLevel.FullLevelEnumeration
import Langlands.AbelianScheme.TorsionFiniteEtale
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # The actual torsion-scheme trivialization from a supplied full level -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open GroupScheme.Tate

private theorem section_isOpenImmersion {S Y : Scheme.{u}} (p : Y ⟶ S)
    [LocallyOfFiniteType p] [FormallyUnramified p] (f : S ⟶ Y) (hf : f ≫ p = 𝟙 S) :
    IsOpenImmersion f := by
  let : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion
      (@LocallyOfFiniteType ⊓ @FormallyUnramified) := by
    rw [MorphismProperty.hasOfPostcompProperty_iff_le_diagonal]
    intro X Y q ⟨hqft, hqfu⟩
    exact inferInstanceAs (IsOpenImmersion (pullback.diagonal q))
  apply MorphismProperty.of_postcomp @IsOpenImmersion
    (W' := @LocallyOfFiniteType ⊓ @FormallyUnramified) f p
    ⟨inferInstance, inferInstance⟩
  rw [hf]
  infer_instance

private theorem section_comp_of_range_subset {S Y Z : Scheme.{u}} (p : Y ⟶ S)
    (f : S ⟶ Y) [IsOpenImmersion f] (hf : f ≫ p = 𝟙 S) (t : Z ⟶ Y)
    (ht : Set.range t ⊆ Set.range f) :
    (t ≫ p) ≫ f = t := by
  let l := IsOpenImmersion.lift f t ht
  calc
    (t ≫ p) ≫ f = ((l ≫ f) ≫ p) ≫ f := by
      rw [IsOpenImmersion.lift_fac]
    _ = l ≫ f := by rw [Category.assoc l f p, hf, Category.comp_id]
    _ = t := IsOpenImmersion.lift_fac f t ht

variable {S : Scheme.{u}} {A : AbelianScheme S} {g n : ℕ}

/-- Every enumerated section is open when positive torsion is invertible on the base. -/
theorem torsionSection_isOpenImmersion (v : SectionTuple A g n)
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) (a : Fin (2 * g) → ZMod n) :
    IsOpenImmersion (torsionSection v a).left := by
  obtain ⟨hfin, het⟩ := torsionFiniteEtale S A n hn hunit
  let X := (GroupScheme.kernel (GroupScheme.multiplication A.toGrp (n : ℤ))).X
  have : Etale X.hom := het
  exact section_isOpenImmersion X.hom (torsionSection v a).left
    (torsionSection v a).w

/-- The enumerated actual sections cover every point of the torsion scheme. -/
theorem FullLevel.torsionSection_cover (v : FullLevel A g n)
    (z : (GroupScheme.kernel (GroupScheme.multiplication A.toGrp (n : ℤ))).X.left) :
    ∃ (a : Fin (2 * g) → ZMod n) (x : S), (torsionSection v.sections a).left x = z := by
  let X := (GroupScheme.kernel (GroupScheme.multiplication A.toGrp (n : ℤ))).X
  let K := AlgebraicClosure (X.left.residueField z)
  let t : Spec (CommRingCat.of K) ⟶ X.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.left.residueField z) K)) ≫
      X.left.fromSpecResidueField z
  let s : Spec (CommRingCat.of K) ⟶ S := t ≫ X.hom
  obtain ⟨a, ha, _⟩ := v.existsUnique_torsionSection K s (Over.homMk t rfl)
  let w : Spec (CommRingCat.of K) := default
  refine ⟨a, s w, ?_⟩
  have heq := congrArg (fun f : Over.mk s ⟶ X => f.left w) ha
  change ((Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫
    torsionSection v.sections a).left w = t w at heq
  exact heq.trans (Scheme.fromSpecResidueField_apply z _)

/-- Distinct coefficient tuples give disjoint open sections of the actual torsion scheme. -/
theorem FullLevel.torsionSection_pairwise_disjoint (v : FullLevel A g n)
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) :
    Pairwise (fun a b : Fin (2 * g) → ZMod n =>
      Disjoint (Set.range (torsionSection v.sections a).left)
        (Set.range (torsionSection v.sections b).left)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx⟩ ⟨y, hy⟩
  let X := (GroupScheme.kernel (GroupScheme.multiplication A.toGrp (n : ℤ))).X
  let K := AlgebraicClosure (X.left.residueField z)
  let t : Spec (CommRingCat.of K) ⟶ X.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.left.residueField z) K)) ≫
      X.left.fromSpecResidueField z
  let s : Spec (CommRingCat.of K) ⟶ S := t ≫ X.hom
  have ht : ∀ w, t w = z := fun w => Scheme.fromSpecResidueField_apply z _
  have hta : Set.range t ⊆ Set.range (torsionSection v.sections a).left := by
    rintro _ ⟨w, rfl⟩
    exact ⟨x, hx.trans (ht w).symm⟩
  have htb : Set.range t ⊆ Set.range (torsionSection v.sections b).left := by
    rintro _ ⟨w, rfl⟩
    exact ⟨y, hy.trans (ht w).symm⟩
  have : IsOpenImmersion (torsionSection v.sections a).left :=
    torsionSection_isOpenImmersion v.sections hn hunit a
  have : IsOpenImmersion (torsionSection v.sections b).left :=
    torsionSection_isOpenImmersion v.sections hn hunit b
  have ha : (Over.homMk s (by simp)) ≫ torsionSection v.sections a =
      (Over.homMk t rfl : Over.mk s ⟶ X) := by
    apply Over.OverMorphism.ext
    exact section_comp_of_range_subset X.hom (torsionSection v.sections a).left
      (torsionSection v.sections a).w t hta
  have hb : (Over.homMk s (by simp)) ≫ torsionSection v.sections b =
      (Over.homMk t rfl : Over.mk s ⟶ X) := by
    apply Over.OverMorphism.ext
    exact section_comp_of_range_subset X.hom (torsionSection v.sections b).left
      (torsionSection v.sections b).w t htb
  obtain ⟨c, _, hc⟩ := v.existsUnique_torsionSection K s (Over.homMk t rfl)
  exact hab ((hc a ha).trans (hc b hb).symm)

/-- The map from the actual coproduct of copies of the base, indexed by coefficients. -/
def torsionCoproductMap (v : SectionTuple A g n) :
    (∐ fun _ : Fin (2 * g) → ZMod n => S) ⟶
      (GroupScheme.kernel (GroupScheme.multiplication A.toGrp (n : ℤ))).X.left :=
  Sigma.desc (fun a => (torsionSection v a).left)

@[reassoc (attr := simp)]
theorem torsionCoproductMap_ι (v : SectionTuple A g n) (a : Fin (2 * g) → ZMod n) :
    Sigma.ι (fun _ : Fin (2 * g) → ZMod n => S) a ≫ torsionCoproductMap v =
      (torsionSection v a).left :=
  Sigma.ι_comp_desc _ _

/-- The actual coproduct map from a full level is an isomorphism. -/
theorem FullLevel.torsionCoproductMap_isIso (v : FullLevel A g n)
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) :
    IsIso (torsionCoproductMap v.sections) := by
  have : ∀ a : Fin (2 * g) → ZMod n, IsOpenImmersion (torsionSection v.sections a).left :=
    torsionSection_isOpenImmersion v.sections hn hunit
  have hopen : IsOpenImmersion (torsionCoproductMap v.sections) :=
    isOpenImmersion_sigmaDesc _ _ (v.torsionSection_pairwise_disjoint hn hunit)
  have hsurj : Surjective (torsionCoproductMap v.sections) := by
    constructor
    intro z
    obtain ⟨a, x, hx⟩ := v.torsionSection_cover z
    refine ⟨Sigma.ι (fun _ : Fin (2 * g) → ZMod n => S) a x, ?_⟩
    rw [← Scheme.Hom.comp_apply, torsionCoproductMap_ι]
    exact hx
  exact (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨hopen, hsurj⟩

/-- A supplied full level trivializes the actual torsion scheme over its base. -/
def FullLevel.torsionCoproductIso (v : FullLevel A g n)
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) :
    Over.mk (Sigma.desc (fun _ : Fin (2 * g) → ZMod n => 𝟙 S)) ≅
      (GroupScheme.kernel (GroupScheme.multiplication A.toGrp (n : ℤ))).X := by
  have := v.torsionCoproductMap_isIso hn hunit
  refine Over.isoMk (asIso (torsionCoproductMap v.sections)) ?_
  change torsionCoproductMap v.sections ≫ _ =
    Sigma.desc (fun _ : Fin (2 * g) → ZMod n => 𝟙 S)
  apply Sigma.hom_ext
  intro a
  simp only [torsionCoproductMap_ι_assoc, Sigma.ι_comp_desc]
  exact (torsionSection v.sections a).w

end Langlands.AbelianScheme.PolarizedFiniteLevel
