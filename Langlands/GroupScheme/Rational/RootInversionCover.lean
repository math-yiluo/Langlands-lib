import Langlands.GroupScheme.Rational.RootSubgroupInversion
import Langlands.GroupScheme.Rational.CharacterFpqcProof

/-! # Fpqc inversion points for actual opposite root subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A nonzero character of a split torus takes the value `-1` on an fpqc
cover of the base, without a rational point-lifting assumption. -/
theorem exists_fpqc_character_neg_one (hT : IsSplitTorus T.toGrp)
    {a : characterLattice T} (ha : a ≠ 0) :
    ∃ (U : Over (Spec (CommRingCat.of k)))
      (q : U ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k)))),
      QuasiCompact q.left ∧ Flat q.left ∧ Surjective q.left ∧
      ∃ s : U ⟶ T.X,
        (Gm.pointsEquiv _ U (s ≫ (CommGroupScheme.groupHom a).hom.hom) :
          Γ(U.left, ⊤)) = -1 := by
  let B : Over (Spec (CommRingCat.of k)) := Over.mk (𝟙 _)
  let y : B ⟶ (Gm (Spec (CommRingCat.of k))).X :=
    (Gm.pointsEquiv _ B).symm (-1)
  let c := (CommGroupScheme.groupHom a).hom.hom
  obtain ⟨hqc, hf, hs⟩ := characterFpqc k T hT a ha
  let : QuasiCompact c.left := hqc
  let : Flat c.left := hf
  let : Surjective c.left := hs
  let U : Over (Spec (CommRingCat.of k)) :=
    Over.mk (pullback.fst y.left c.left ≫ B.hom)
  let q : U ⟶ B := Over.homMk (pullback.fst y.left c.left) rfl
  let s : U ⟶ T.X := Over.homMk (pullback.snd y.left c.left) (by
    rw [← Over.w c, ← Category.assoc, ← pullback.condition,
      Category.assoc, Over.w y]
    rfl)
  have hsc : q ≫ y = s ≫ c := Over.OverMorphism.ext pullback.condition
  refine ⟨U, q, ?_, ?_, ?_, s, ?_⟩
  · change QuasiCompact (pullback.fst y.left c.left)
    infer_instance
  · change Flat (pullback.fst y.left c.left)
    infer_instance
  · change Surjective (pullback.fst y.left c.left)
    infer_instance
  · change (Gm.pointsEquiv _ U (s ≫ c) : Γ(U.left, ⊤)) = -1
    rw [← hsc, Gm.pointsEquiv_naturality]
    simp [y]

/-- Character value `-1` is unchanged on replacing the character by its
negative, including in characteristic two. -/
theorem character_neg_eq_neg_one {a : characterLattice T}
    {U : Over (Spec (CommRingCat.of k))} (s : U ⟶ T.X)
    (hs : (Gm.pointsEquiv _ U (s ≫ (CommGroupScheme.groupHom a).hom.hom) :
      Γ(U.left, ⊤)) = -1) :
    (Gm.pointsEquiv _ U (s ≫ (CommGroupScheme.groupHom (-a)).hom.hom) :
      Γ(U.left, ⊤)) = -1 := by
  have he : s ≫ (CommGroupScheme.groupHom (-a)).hom.hom =
      (s ≫ (CommGroupScheme.groupHom a).hom.hom)⁻¹ :=
    congrArg Additive.toMul (map_neg (evalPoint s) a)
  have hu : Gm.pointsEquiv _ U (s ≫ (CommGroupScheme.groupHom a).hom.hom) = -1 :=
    Units.ext hs
  rw [he, map_inv, hu]
  simp

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G)

/-- There is a common fpqc local inversion point for the two actual
opposite root subgroup functors. -/
def HasFpqcInversionPoint (a : characterLattice T) : Prop :=
  ∃ (U : Over (Spec (CommRingCat.of k)))
    (q : U ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k)))),
    QuasiCompact q.left ∧ Flat q.left ∧ Surjective q.left ∧
      ∃ s : U ⟶ T.X, IsInversionPoint i a s ∧ IsInversionPoint i (-a) s

/-- The explicit cyclic structure statements and absence of higher roots
produce a common fpqc inversion point by the actual character map. -/
theorem hasFpqcInversionPoint_of_noHigherRoots
    (hreal : SemigroupRealizationStatement.{u})
    (hcyclic : CyclicRootFunctorComparisonStatement.{u})
    (hfilter : CyclicWeightFiltrationStatement.{u})
    (hG : Smooth G.X.hom) (hT : IsSplitTorus T.toGrp)
    {a : characterLattice T} (ha : a ≠ 0)
    (hpos : ∀ n : ℕ, 2 ≤ n → n • a ∉ relativeRoots i)
    (hneg : ∀ n : ℕ, 2 ≤ n → n • (-a) ∉ relativeRoots i) :
    HasFpqcInversionPoint i a := by
  obtain ⟨U, q, hqc, hf, hsurj, s, hs⟩ := exists_fpqc_character_neg_one hT ha
  refine ⟨U, q, hqc, hf, hsurj, s, ?_, ?_⟩
  · exact isInversionPoint_of_noHigherPositiveRoots
      hreal hcyclic hfilter hG hT i ha hpos s hs
  · exact isInversionPoint_of_noHigherPositiveRoots
      hreal hcyclic hfilter hG hT i (neg_ne_zero.mpr ha) hneg s
      (character_neg_eq_neg_one s hs)

end Langlands.GroupScheme.RelativeRoot
