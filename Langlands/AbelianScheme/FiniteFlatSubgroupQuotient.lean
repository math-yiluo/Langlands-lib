import Langlands.GroupScheme.FiniteNormalSubgroupQuotient
import Langlands.GroupScheme.FppfQuotientTargetSmooth
import Langlands.AbelianScheme.FiniteEtaleQuotientPropertyDescent
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation

/-! # Quotients by finite flat subgroups whose cosets lie in affine opens -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

open HomogeneousCosetRelation

/-- A finite flat normal subgroup has an actual finite fppf quotient, provided every right
coset lies in an affine open. The kernel pair of the projection is the coset relation. -/
theorem exists_quotient_of_finite_flat_normal_subgroup_of_affine_cosets
    {S : Scheme.{u}} {G N : GroupScheme S} (i : N ⟶ G) [Mono i.hom.hom]
    [IsFinite N.X.hom] [Flat N.X.hom] [LocallyOfFinitePresentation N.X.hom]
    (hn : (SubgroupFunctor.range i).IsNormal)
    (haff : ∀ x : G.X.left, ∃ U : G.X.left.Opens, IsAffineOpen U ∧
      ∀ r : (arrows i).left, (source i).left r = x → (target i).left r ∈ U) :
    ∃ (Q : GroupScheme S) (q : G ⟶ Q),
      IsFinite q.hom.hom.left ∧ RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q ∧
        IsPullback (source i).left (target i).left q.hom.hom.left q.hom.hom.left := by
  let s := source i
  let t := target i
  have : IsFinite s.left := inferInstanceAs (IsFinite (pullback.fst G.X.hom N.X.hom))
  have : Flat s.left := inferInstanceAs (Flat (pullback.fst G.X.hom N.X.hom))
  have : LocallyOfFinitePresentation s.left :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.fst G.X.hom N.X.hom))
  have : IsIso (translationIso i).hom.left := (Over.forget S).map_isIso (translationIso i).hom
  have ht : t.left = (translationIso i).hom.left ≫ s.left :=
    congrArg (fun e => e.left) (translationIso_hom_source i).symm
  have : IsFinite t.left := by rw [ht]; infer_instance
  have : Flat t.left := by rw [ht]; infer_instance
  have : LocallyOfFinitePresentation t.left := by rw [ht]; infer_instance
  obtain ⟨Y, p, w, hpfin, hpflat, hplfp, hpsurj, hpb, ⟨hc⟩⟩ :=
    AlgebraicGeometry.Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation
      s.left t.left (fun _ _ hs ht => scheme_arrow_unique i hs ht) (scheme_equivalence i) haff
  let : IsFinite p := hpfin
  let : Flat p := hpflat
  let : LocallyOfFinitePresentation p := hplfp
  let : Surjective p := hpsurj
  have hw : s.left ≫ G.X.hom = t.left ≫ G.X.hom := (Over.w s).trans (Over.w t).symm
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
    rw [← exists_arrow_iff]
    constructor
    · intro he
      let a := hpb.lift g.left h.left (congrArg (fun e => e.left) he)
      have has : a ≫ s.left = g.left := hpb.lift_fst _ _ _
      have hat : a ≫ t.left = h.left := hpb.lift_snd _ _ _
      have ha : a ≫ (arrows i).hom = T.hom := by
        rw [← Over.w s, ← Category.assoc, has, Over.w]
      exact ⟨Over.homMk a ha, Over.OverMorphism.ext has, Over.OverMorphism.ext hat⟩
    · rintro ⟨a, rfl, rfl⟩
      apply Over.OverMorphism.ext
      exact congrArg (fun b => a.left ≫ b) w
  exact ⟨NormalQuotient.groupScheme G (SubgroupFunctor.range i) hn q₀ hfib,
    NormalQuotient.hom G (SubgroupFunctor.range i) hn q₀ hfib, hpfin,
    NormalQuotient.isFppfQuotient G (SubgroupFunctor.range i) hn q₀ hfib, hpb⟩

/-- A group-scheme homomorphism whose square is an epimorphism has commutative target when
its source is commutative. -/
theorem isCommMonObj_of_epi_tensorHom {S : Scheme.{u}} {G Q : GroupScheme S} [IsCommMonObj G.X]
    (q : G ⟶ Q) [Epi (q.hom.hom ⊗ₘ q.hom.hom)] : IsCommMonObj Q.X where
  mul_comm := by
    apply (cancel_epi (q.hom.hom ⊗ₘ q.hom.hom)).mp
    rw [← Category.assoc, BraidedCategory.braiding_naturality, Category.assoc,
      ← IsMonHom.mul_hom q.hom.hom, ← Category.assoc, IsCommMonObj.mul_comm,
      IsMonHom.mul_hom q.hom.hom]

/-- The square of a flat surjective quasi-compact morphism in a slice category is an
epimorphism there. -/
theorem epi_tensorHom_of_flat_surjective {S : Scheme.{u}} {X Y : Over S} (q : X ⟶ Y)
    [QuasiCompact q.left] [Flat q.left] [Surjective q.left] : Epi (q ⊗ₘ q) := by
  have hp : (@QuasiCompact ⊓ (@Flat ⊓ @Surjective) : MorphismProperty Scheme.{u}) (q ⊗ₘ q).left :=
    MorphismProperty.pullbackMap (P := @QuasiCompact ⊓ (@Flat ⊓ @Surjective))
      ⟨inferInstance, inferInstance, inferInstance⟩
      ⟨inferInstance, inferInstance, inferInstance⟩
      (Over.w q).symm (Over.w q).symm
  have : Flat (q ⊗ₘ q).left := hp.2.1
  have : Surjective (q ⊗ₘ q).left := hp.2.2
  have : Epi (q ⊗ₘ q).left := Flat.epi_of_flat_of_surjective _
  exact Over.epi_of_epi_left _

end Langlands.GroupScheme

namespace Langlands.AbelianScheme

open Langlands.GroupScheme Langlands.GroupScheme.HomogeneousCosetRelation

variable {K : Type u} [Field K]

/-- Over a field, a finite closed subgroup of an abelian scheme whose right cosets lie in
affine opens has an abelian quotient. The projection is a finite, flat and surjective group
homomorphism with the given subgroup as its scheme-theoretic kernel, and its kernel pair is
the actual coset relation. -/
theorem exists_abelian_quotient_of_finite_subgroup
    (A : AbelianScheme (Spec (CommRingCat.of K))) {N : GroupScheme (Spec (CommRingCat.of K))}
    (i : N ⟶ A.toGrp) [Mono i.hom.hom] [IsFinite N.X.hom]
    (haff : ∀ x : A.X.left, ∃ U : A.X.left.Opens, IsAffineOpen U ∧
      ∀ r : (arrows i).left, (source i).left r = x → (target i).left r ∈ U) :
    ∃ (B : AbelianScheme (Spec (CommRingCat.of K))) (q : A.toGrp ⟶ B.toGrp),
      IsFinite q.hom.hom.left ∧ RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q ∧
        IsPullback (source i).left (target i).left q.hom.hom.left q.hom.hom.left := by
  have : LocallyOfFinitePresentation N.X.hom :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have hn : (SubgroupFunctor.range i).IsNormal := by
    intro T g x _ hx
    rwa [mul_comm g x, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨Q, q, hfin, hq, hpb⟩ :=
    exists_quotient_of_finite_flat_normal_subgroup_of_affine_cosets i hn haff
  have : IsFinite q.hom.hom.left := hfin
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  have : Epi (q.hom.hom ⊗ₘ q.hom.hom) := epi_tensorHom_of_flat_surjective q.hom.hom
  have : IsCommMonObj Q.X := isCommMonObj_of_epi_tensorHom q
  have hw : q.hom.hom.left ≫ Q.X.hom = A.X.hom := Over.w q.hom.hom
  have : Smooth Q.X.hom := hq.smooth_target
  have : IsProper (q.hom.hom.left ≫ Q.X.hom) := by rw [hw]; infer_instance
  have : GeometricallyConnected (q.hom.hom.left ≫ Q.X.hom) := by rw [hw]; infer_instance
  have : UniversallyClosed Q.X.hom := UniversallyClosed.of_comp_surjective q.hom.hom.left Q.X.hom
  have : IsSeparated Q.X.hom :=
    FiniteEtaleQuotientPropertyDescent.isSeparated_of_comp_of_surjective_of_universallyClosed
      q.hom.hom.left Q.X.hom
  have : IsProper Q.X.hom := (isProper_iff Q.X.hom).2 ⟨inferInstance, inferInstance, inferInstance⟩
  have : GeometricallyConnected Q.X.hom :=
    FiniteEtaleQuotientPropertyDescent.geometricallyConnected_of_comp_of_surjective
      q.hom.hom.left Q.X.hom
  let B : AbelianScheme (Spec (CommRingCat.of K)) :=
    { toCommGroupScheme := { toGrp := Q } }
  exact ⟨B, q, hfin, hq, hpb⟩

/-- An abelian quotient of `A` by a finite subgroup: a finite fppf quotient homomorphism to an
abelian scheme, whose kernel pair is the actual coset relation. -/
structure AbelianQuotientData (A : AbelianScheme (Spec (CommRingCat.of K)))
    {N : GroupScheme (Spec (CommRingCat.of K))} (i : N ⟶ A.toGrp) where
  /-- The quotient abelian scheme. -/
  quotient : AbelianScheme (Spec (CommRingCat.of K))
  /-- The quotient homomorphism. -/
  projection : A.toGrp ⟶ quotient.toGrp
  finite : IsFinite projection.hom.hom.left
  isFppfQuotient : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) projection
  isPullback : IsPullback (source i).left (target i).left
    projection.hom.hom.left projection.hom.hom.left

/-- A chosen abelian quotient by a finite subgroup whose cosets lie in affine opens. -/
def abelianQuotientData
    (A : AbelianScheme (Spec (CommRingCat.of K))) {N : GroupScheme (Spec (CommRingCat.of K))}
    (i : N ⟶ A.toGrp) [Mono i.hom.hom] [IsFinite N.X.hom]
    (haff : ∀ x : A.X.left, ∃ U : A.X.left.Opens, IsAffineOpen U ∧
      ∀ r : (arrows i).left, (source i).left r = x → (target i).left r ∈ U) :
    AbelianQuotientData A i :=
  let h := exists_abelian_quotient_of_finite_subgroup A i haff
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.1,
    h.choose_spec.choose_spec.2.1, h.choose_spec.choose_spec.2.2⟩

end Langlands.AbelianScheme
