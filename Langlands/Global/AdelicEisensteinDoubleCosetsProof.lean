import Langlands.Global.AdelicEisensteinDoubleCosetsStatement
import Langlands.Global.AdelicGroupRationalTopology
import Langlands.GroupScheme.GaloisPointRational
import Langlands.GroupScheme.Rational.StandardParabolicPointsProof
import Langlands.GroupScheme.Rational.RelativeWeylCoxeterProof
import Langlands.Group.RelativeWeylMinimalUniqueProof

/-! # Weyl double coset representatives on actual adelic points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints Langlands.GroupScheme.GaloisPointComparison
  Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing
  Langlands.Automorphic.GroupSchemeFunctions

namespace AdelicGroupPoints

section Principal

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- The identity-test rational points as principal adelic points. -/
abbrev principalPoint : rationalPoints G →* AdelicGroupPoints F G :=
  (rational F G).comp (rationalCoeffEquiv F G).toMonoidHom

/-- The principal point homomorphism agrees with the point used for adelic conjugation. -/
theorem principalPoint_eq_innerAdelicPoint (x : rationalPoints G) :
    principalPoint F G x = innerAdelicPoint F G x := by
  rw [innerAdelicPoint_eq_rational]
  apply congrArg (rational F G)
  apply Over.OverMorphism.ext
  change (rationalCoeffEquiv F G x).left = _
  rw [rationalCoeffEquiv_left]
  simp [GroupScheme.constantPoint, algSpec_obj_hom, Algebra.algebraMap_self]
  exact (Category.id_comp x.left).symm

/-- The rational adelic image is the principal image of the identity-test range. -/
theorem rationalImage_eq_map_range {H : GroupScheme (Spec (CommRingCat.of F))}
    (f : H ⟶ G) :
    rationalImage F f =
      ((SubgroupFunctor.range f).carrier (Over.mk (𝟙 _))).map (principalPoint F G) := by
  have h (x : rationalPoints H) :
      map F H G f (rational F H (rationalCoeffEquiv F H x)) =
        principalPoint F G (rationalPoints.map f x) := by
    change _ = rational F G (rationalCoeffEquiv F G (rationalPoints.map f x))
    rw [rationalCoeffEquiv_map]
    exact (DFunLike.congr_fun (rational_naturality F H f) (rationalCoeffEquiv F H x)).symm
  ext y
  constructor
  · rintro ⟨r, rfl⟩
    obtain ⟨x, rfl⟩ := (rationalCoeffEquiv F H).surjective r
    exact ⟨rationalPoints.map f x, SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩, (h x).symm⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hy
    exact ⟨rationalCoeffEquiv F H x, h x⟩

end Principal

end AdelicGroupPoints

/-- Minimal Weyl representatives give the finite family of actual adelic
double coset representatives with positive Levi roots. -/
theorem eisensteinDoubleCosets : EisensteinDoubleCosetsStatement.{u} := by
  intro F _ _ G _ _ hG T i _ hi ν hν P Q
  classical
  obtain ⟨-, -, CM, cs, hcs⟩ := relativeWeylCoxeter F G hG T i hi ν hν
  obtain ⟨e, he⟩ := (standardParabolicPointsStatement_proof F G hG T i hi ν hν).2.2.2
    (rootSet i ν Q) (rootSet i ν P) (rootSet_subset i ν Q) (rootSet_subset i ν P)
  let I := {w : relativeWeylGroup i // IsMinimal cs Q P w}
  have := hG.finite_relativeWeylGroup i hi
  let n (j : I) : normalizerPoints i := (QuotientGroup.mk_surjective j.val).choose
  have hn (j : I) : (QuotientGroup.mk (n j) : relativeWeylGroup i) = j.val :=
    (QuotientGroup.mk_surjective j.val).choose_spec
  let WP := standardRelativeWeylGroup i ν (rootSet i ν P)
  let WQ := standardRelativeWeylGroup i ν (rootSet i ν Q)
  let PP := standardParabolicPoints i ν (rootSet i ν P)
  let PQ := standardParabolicPoints i ν (rootSet i ν Q)
  have he' (j : I) :
      e (DoubleCoset.mk WQ WP j.val) = DoubleCoset.mk PQ PP (n j).val := by
    rw [← hn]
    exact he (n j)
  have hclass (w v : relativeWeylGroup i) :
      DoubleCoset.mk WQ WP w = DoubleCoset.mk WQ WP v ↔ v ∈ doubleCoset cs Q P w := by
    rw [DoubleCoset.eq]
    change (∃ a ∈ WQ, ∃ b ∈ WP, v = a * w * b) ↔ _
    rw [show WQ = standardSubgroup cs Q from (hcs.2.2.2.2 Q).symm,
      show WP = standardSubgroup cs P from (hcs.2.2.2.2 P).symm]
    rfl
  refine ⟨I, inferInstance, n, ?_, ?_⟩
  · intro z hz
    obtain ⟨q, rfl⟩ := hz
    obtain ⟨y, rfl⟩ := (rationalCoeffEquiv F G).surjective q
    change ∃! j : I, ∃ x ∈ rationalImage F (Standard.parabolicHom i ν (rootSet i ν Q)),
      ∃ t ∈ rationalImage F (Standard.parabolicHom i ν (rootSet i ν P)),
        principalPoint F G y = x * innerAdelicPoint F G (n j).val * t
    have hrep (j : I) :
        (∃ x ∈ rationalImage F (Standard.parabolicHom i ν (rootSet i ν Q)),
          ∃ t ∈ rationalImage F (Standard.parabolicHom i ν (rootSet i ν P)),
            principalPoint F G y = x * innerAdelicPoint F G (n j).val * t) ↔
          DoubleCoset.mk PQ PP (n j).val = DoubleCoset.mk PQ PP y := by
      rw [DoubleCoset.eq, rationalImage_eq_map_range, rationalImage_eq_map_range,
        (Standard.isRepresentedBy_parabolicHom i ν (rootSet i ν Q)).2,
        (Standard.isRepresentedBy_parabolicHom i ν (rootSet i ν P)).2,
        ← principalPoint_eq_innerAdelicPoint]
      have hinj : Function.Injective (principalPoint F G) :=
        (rational_injective F G).comp (rationalCoeffEquiv F G).injective
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨t, ht, rfl⟩, hz⟩
        exact ⟨x, hx, t, ht, hinj (by simpa only [map_mul] using hz)⟩
      · rintro ⟨x, hx, t, ht, hz⟩
        refine ⟨_, ⟨x, hx, rfl⟩, _, ⟨t, ht, rfl⟩, ?_⟩
        simp only [hz, map_mul]
    let w := (e.symm (DoubleCoset.mk PQ PP y)).out
    have hw : e (DoubleCoset.mk WQ WP w) = DoubleCoset.mk PQ PP y := by
      rw [DoubleCoset.out_eq', e.apply_symm_apply]
    obtain ⟨v, hv, hvmin⟩ := exists_minimal_in_doubleCoset_unrestricted cs Q P w
    let j : I := ⟨v, hvmin⟩
    refine ⟨j, (hrep j).mpr ?_, ?_⟩
    · rw [← he', ← hw]
      exact congrArg e ((hclass w v).mpr hv).symm
    · intro k hk
      apply Subtype.ext
      have hkClass : DoubleCoset.mk WQ WP w = DoubleCoset.mk WQ WP k.val :=
        e.injective (hw.trans ((he' k).trans ((hrep k).mp hk)).symm)
      exact minimalRepresentativeUnique_proof cs Q P w k.val v
        ((hclass _ _).mp hkClass) hv k.property hvmin
  · intro j
    simp only [hn]
    constructor
    · rintro α ⟨root, hroot, rfl⟩
      exact (hcs.2.2.1 j.val root).mp
        ((((minimalityLengthCriterion_proof cs) Q P j.val).mp j.property).2 root hroot)
    · rintro α ⟨root, hroot, rfl⟩
      exact (hcs.2.2.1 j.val⁻¹ root).mp
        ((((minimalityLengthCriterion_proof cs) P Q j.val⁻¹).mp
          (isMinimal_inv cs j.property)).2 root hroot)

end Langlands.Global
