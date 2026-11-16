import Langlands.GroupScheme.HomogeneousCosetRelation
import Langlands.GroupScheme.NormalQuotientGroup
import Langlands.AlgebraicGeometry.FiniteLocallyFreeEquivalenceRelationAffineQuotientProof

/-! # Finite flat normal subgroup quotients over affine bases -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace HomogeneousCosetRelation

variable {S : Scheme.{u}} {G N : GroupScheme S} (i : N ⟶ G)

/-- The underlying coset arrows are jointly monic for a monomorphic subgroup. -/
theorem scheme_arrow_unique [Mono i.hom.hom] {T : Scheme.{u}}
    {a b : T ⟶ (arrows i).left}
    (hs : a ≫ (source i).left = b ≫ (source i).left)
    (ht : a ≫ (target i).left = b ≫ (target i).left) : a = b := by
  let T₀ := Over.mk (a ≫ (arrows i).hom)
  let a₀ : T₀ ⟶ arrows i := Over.homMk a rfl
  have hb : b ≫ (arrows i).hom = a ≫ (arrows i).hom := by
    rw [← Over.w (source i), ← Category.assoc, ← Category.assoc, ← hs]
  let b₀ : T₀ ⟶ arrows i := Over.homMk b hb
  exact congrArg (fun e => e.left)
    (arrow_unique i (a := a₀) (b := b₀)
      (Over.OverMorphism.ext hs) (Over.OverMorphism.ext ht))

/-- The actual coset arrows define an equivalence relation on every scheme test. -/
theorem scheme_equivalence (T : Scheme.{u}) :
    _root_.Equivalence fun x y : T ⟶ G.X.left =>
      ∃ a : T ⟶ (arrows i).left,
        a ≫ (source i).left = x ∧ a ≫ (target i).left = y := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    let T₀ := Over.mk (x ≫ G.X.hom)
    let x₀ : T₀ ⟶ G.X := Over.homMk x rfl
    obtain ⟨a, ha, hb⟩ := (exists_arrow_iff i x₀ x₀).mpr (by simp)
    exact ⟨a.left, congrArg (fun e => e.left) ha, congrArg (fun e => e.left) hb⟩
  · rintro x y ⟨a, ha, hb⟩
    let T₀ := Over.mk (a ≫ (arrows i).hom)
    let a₀ : T₀ ⟶ arrows i := Over.homMk a rfl
    have hm := (exists_arrow_iff i (a₀ ≫ source i) (a₀ ≫ target i)).mp
      ⟨a₀, rfl, rfl⟩
    obtain ⟨b, hbs, hbt⟩ :=
      (exists_arrow_iff i (a₀ ≫ target i) (a₀ ≫ source i)).mpr
        (by simpa using ((SubgroupFunctor.range i).carrier T₀).inv_mem hm)
    exact ⟨b.left, (congrArg (fun e => e.left) hbs).trans hb,
      (congrArg (fun e => e.left) hbt).trans ha⟩
  · rintro x y z ⟨a, has, hat⟩ ⟨b, hbs, hbt⟩
    let T₀ := Over.mk (a ≫ (arrows i).hom)
    let a₀ : T₀ ⟶ arrows i := Over.homMk a rfl
    have hb : b ≫ (arrows i).hom = a ≫ (arrows i).hom := by
      calc
        b ≫ (arrows i).hom = (b ≫ (source i).left) ≫ G.X.hom := by
          rw [Category.assoc, Over.w]
        _ = (a ≫ (target i).left) ≫ G.X.hom := by rw [hbs, hat]
        _ = a ≫ (arrows i).hom := by rw [Category.assoc, Over.w]
    let b₀ : T₀ ⟶ arrows i := Over.homMk b hb
    have hab : a₀ ≫ target i = b₀ ≫ source i :=
      Over.OverMorphism.ext (hat.trans hbs.symm)
    have hm₁ := (exists_arrow_iff i (a₀ ≫ source i) (a₀ ≫ target i)).mp
      ⟨a₀, rfl, rfl⟩
    have hm₂ := (exists_arrow_iff i (b₀ ≫ source i) (b₀ ≫ target i)).mp
      ⟨b₀, rfl, rfl⟩
    rw [← hab] at hm₂
    obtain ⟨c, hcs, hct⟩ :=
      (exists_arrow_iff i (a₀ ≫ source i) (b₀ ≫ target i)).mpr
        (by simpa [mul_assoc] using ((SubgroupFunctor.range i).carrier T₀).mul_mem hm₁ hm₂)
    exact ⟨c.left, (congrArg (fun e => e.left) hcs).trans has,
      (congrArg (fun e => e.left) hct).trans hbt⟩

end HomogeneousCosetRelation

/-- A finite flat normal subgroup of an affine group over an affine base has
an actual finite fppf quotient with the specified full kernel. -/
theorem exists_affine_quotient_of_finite_flat_normal_subgroup
    {S : Scheme.{u}} [IsAffine S] {G N : GroupScheme S}
    [IsAffineHom G.X.hom] (i : N ⟶ G) [Mono i.hom.hom]
    [IsFinite N.X.hom] [Flat N.X.hom] [LocallyOfFinitePresentation N.X.hom]
    (hn : (SubgroupFunctor.range i).IsNormal) :
    ∃ (Q : GroupScheme S) (q : G ⟶ Q),
      IsAffineHom Q.X.hom ∧ IsFinite q.hom.hom.left ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q := by
  let s := HomogeneousCosetRelation.source i
  let t := HomogeneousCosetRelation.target i
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsFinite s.left := inferInstanceAs (IsFinite (pullback.fst G.X.hom N.X.hom))
  have : Flat s.left := inferInstanceAs (Flat (pullback.fst G.X.hom N.X.hom))
  have : LocallyOfFinitePresentation s.left :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.fst G.X.hom N.X.hom))
  have : IsIso (HomogeneousCosetRelation.translationIso i).hom.left :=
    (Over.forget S).map_isIso (HomogeneousCosetRelation.translationIso i).hom
  have ht : t.left = (HomogeneousCosetRelation.translationIso i).hom.left ≫ s.left :=
    congrArg (fun e => e.left)
      (HomogeneousCosetRelation.translationIso_hom_source i).symm
  have : IsFinite t.left := by rw [ht]; infer_instance
  have : Flat t.left := by rw [ht]; infer_instance
  have : LocallyOfFinitePresentation t.left := by rw [ht]; infer_instance
  obtain ⟨Y, hY, p, w, hpfin, hpflat, hplfp, hpsurj, hpb, ⟨hc⟩⟩ :=
    Langlands.AlgebraicGeometry.FiniteLocallyFreeQuotient.existsAffineQuotient
      s.left t.left (fun _ _ hs ht => HomogeneousCosetRelation.scheme_arrow_unique i hs ht)
      (HomogeneousCosetRelation.scheme_equivalence i)
  let : IsAffine Y := hY
  let : IsFinite p := hpfin
  let : Flat p := hpflat
  let : LocallyOfFinitePresentation p := hplfp
  let : Surjective p := hpsurj
  have hw : s.left ≫ G.X.hom = t.left ≫ G.X.hom :=
    (Over.w s).trans (Over.w t).symm
  let r : Y ⟶ S := Cofork.IsColimit.desc hc G.X.hom hw
  have hpr : p ≫ r = G.X.hom := Cofork.IsColimit.π_desc' hc G.X.hom hw
  let Q₀ : Over S := Over.mk r
  let q₀ : G.X ⟶ Q₀ := Over.homMk p hpr
  have : IsFinite q₀.left := hpfin
  have : Flat q₀.left := hpflat
  have : Surjective q₀.left := hpsurj
  have : LocallyOfFinitePresentation q₀.left := hplfp
  have hfib : ∀ (T : Over S) (g h : T ⟶ G.X),
      g ≫ q₀ = h ≫ q₀ ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T := by
    intro T g h
    rw [← HomogeneousCosetRelation.exists_arrow_iff]
    constructor
    · intro he
      let a := hpb.lift g.left h.left (congrArg (fun e => e.left) he)
      have has : a ≫ s.left = g.left := hpb.lift_fst _ _ _
      have hat : a ≫ t.left = h.left := hpb.lift_snd _ _ _
      have ha : a ≫ (HomogeneousCosetRelation.arrows i).hom = T.hom := by
        rw [← Over.w s, ← Category.assoc, has, Over.w]
      exact ⟨Over.homMk a ha, Over.OverMorphism.ext has, Over.OverMorphism.ext hat⟩
    · rintro ⟨a, rfl, rfl⟩
      apply Over.OverMorphism.ext
      exact congrArg (fun b => a.left ≫ b) w
  let Q := NormalQuotient.groupScheme G (SubgroupFunctor.range i) hn q₀ hfib
  let q : G ⟶ Q := NormalQuotient.hom G (SubgroupFunctor.range i) hn q₀ hfib
  refine ⟨Q, q, ?_, hpfin,
    NormalQuotient.isFppfQuotient G (SubgroupFunctor.range i) hn q₀ hfib⟩
  change IsAffineHom r
  infer_instance

/-- An actual affine finite fppf quotient by a specified represented subgroup. -/
structure FiniteNormalSubgroupQuotient {S : Scheme.{u}} {G N : GroupScheme S}
    (i : N ⟶ G) where
  quotient : GroupScheme S
  projection : G ⟶ quotient
  affine : IsAffineHom quotient.X.hom
  finite : IsFinite projection.hom.hom.left
  isFppfQuotient : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) projection

/-- Choose the actual quotient of an affine group by a finite flat normal
subgroup over an affine base. -/
def finiteNormalSubgroupQuotient
    {S : Scheme.{u}} [IsAffine S] {G N : GroupScheme S}
    [IsAffineHom G.X.hom] (i : N ⟶ G) [Mono i.hom.hom]
    [IsFinite N.X.hom] [Flat N.X.hom] [LocallyOfFinitePresentation N.X.hom]
    (hn : (SubgroupFunctor.range i).IsNormal) : FiniteNormalSubgroupQuotient i := by
  let h := exists_affine_quotient_of_finite_flat_normal_subgroup i hn
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.1,
    h.choose_spec.choose_spec.2.1, h.choose_spec.choose_spec.2.2⟩

end Langlands.GroupScheme
