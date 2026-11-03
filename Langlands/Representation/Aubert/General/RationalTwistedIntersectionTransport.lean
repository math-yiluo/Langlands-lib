import Langlands.Representation.Aubert.General.RationalCoxeterTransport
import Langlands.GroupScheme.Rational.StandardLeviTwistedIntersectionStatement
import Langlands.GroupScheme.Rational.StandardSourceTwistedIntersectionStatement
import Langlands.Representation.Aubert.General.GeometricK0Target

/-! # Twisted-intersection transport to the actual rational-point quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Group.RelativeWeylIndexing

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  (ν : cocharacterLattice T)
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  {C : CoxeterMatrix (SimpleRoot i ν)}
  (cs : CoxeterSystem C (relativeWeylGroup i))

omit [Mono i.hom.hom.left] in
/-- Membership in a standard subgroup transports without relabelling roots. -/
theorem pointCoxeterSystem_mem_standardSubgroup
    (I : Finset (SimpleRoot i ν)) (w : relativeWeylGroup i) :
    weylEquiv i hN hZ w ∈ standardSubgroup (pointCoxeterSystem i ν hN hZ cs) I ↔
      w ∈ standardSubgroup cs I := by
  rw [pointCoxeterSystem_standardSubgroup]
  simp only [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

omit [Mono i.hom.hom.left] in
/-- Minimality in the whole double coset is preserved and reflected. -/
theorem pointCoxeterSystem_isMinimal_iff
    (I J : Finset (SimpleRoot i ν)) (w : relativeWeylGroup i) :
    IsMinimal (pointCoxeterSystem i ν hN hZ cs) I J (weylEquiv i hN hZ w) ↔
      IsMinimal cs I J w := by
  constructor
  · intro hw a ha b hb
    have h := hw (weylEquiv i hN hZ a)
      ((pointCoxeterSystem_mem_standardSubgroup i ν hN hZ cs I a).2 ha)
      (weylEquiv i hN hZ b)
      ((pointCoxeterSystem_mem_standardSubgroup i ν hN hZ cs J b).2 hb)
    simpa only [← map_mul, pointCoxeterSystem_length] using h
  · intro hw a ha b hb
    obtain ⟨a, rfl⟩ := (weylEquiv i hN hZ).surjective a
    obtain ⟨b, rfl⟩ := (weylEquiv i hN hZ).surjective b
    have h := hw a ((pointCoxeterSystem_mem_standardSubgroup i ν hN hZ cs I a).1 ha)
      b ((pointCoxeterSystem_mem_standardSubgroup i ν hN hZ cs J b).1 hb)
    simpa only [← map_mul, pointCoxeterSystem_length] using h

omit [Mono i.hom.hom.left] in
/-- Minimal double-coset representatives correspond through the actual
quotient equivalence, with the original finite simple-root labels. -/
def pointMinimalRepEquiv (I J : Finset (SimpleRoot i ν)) :
    {w : relativeWeylGroup i // IsMinimal cs I J w} ≃
      {w : Group.RelativeWeyl.Weyl (torusPoints i) //
        IsMinimal (pointCoxeterSystem i ν hN hZ cs) I J w} where
  toFun w := ⟨weylEquiv i hN hZ w,
    (pointCoxeterSystem_isMinimal_iff i ν hN hZ cs I J w).2 w.property⟩
  invFun w := ⟨(weylEquiv i hN hZ).symm w,
    (pointCoxeterSystem_isMinimal_iff i ν hN hZ cs I J
      ((weylEquiv i hN hZ).symm w)).1
        (by simpa only [MulEquiv.apply_symm_apply] using w.property)⟩
  left_inv w := Subtype.ext ((weylEquiv i hN hZ).symm_apply_apply w)
  right_inv w := Subtype.ext ((weylEquiv i hN hZ).apply_symm_apply w)

omit [Mono i.hom.hom.left] in
/-- The intrinsic source intersection has exactly the same finite root labels. -/
theorem pointCoxeterSystem_intersectionSubset
    (I J : Finset (SimpleRoot i ν)) (w : relativeWeylGroup i) :
    intersectionSubset (pointCoxeterSystem i ν hN hZ cs) I J (weylEquiv i hN hZ w) =
      intersectionSubset cs I J w := by
  classical
  ext a
  simp only [intersectionSubset, Finset.mem_filter, pointCoxeterSystem_simple,
    ← map_inv, ← map_mul, pointCoxeterSystem_mem_standardSubgroup]

omit [Mono i.hom.hom.left] in
/-- Supplied all-test Levi, parabolic and radical intersection identities give
all three literal point-source identities at every actual normalizer lift.
The finite labels use the transported point Coxeter system itself. -/
theorem point_geometricSourceIntersections
    (hLevi : IsStandardLeviTwistedIntersection i ν cs)
    (hSource : IsStandardSourceTwistedIntersection i ν cs)
    (I J : Finset (SimpleRoot i ν)) (w : Group.RelativeWeyl.Weyl (torusPoints i))
    (hw : IsMinimal (pointCoxeterSystem i ν hN hZ cs) I J w)
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = w) :
    let K := intersectionSubset (pointCoxeterSystem i ν hN hZ cs) I J w
    geometricSourceIntersection (levi i ν I) (levi i ν J) (n : rationalPoints G) =
        levi i ν K ∧
      (geometricSourceIntersection (parabolic i ν I) (levi i ν J)
        (n : rationalPoints G)).subgroupOf (levi i ν J) =
          (parabolic i ν K).subgroupOf (levi i ν J) ∧
      (geometricSourceIntersection (unipotent i ν I) (levi i ν J)
        (n : rationalPoints G)).subgroupOf (levi i ν J) =
          (unipotent i ν K).subgroupOf (levi i ν J) := by
  let w' := (weylEquiv i hN hZ).symm w
  let n' := (normalizerEquiv i hN).symm n
  have hw' : IsMinimal cs I J w' :=
    (pointCoxeterSystem_isMinimal_iff i ν hN hZ cs I J w').1
      (by simpa only [w', MulEquiv.apply_symm_apply] using hw)
  have hn' : QuotientGroup.mk n' = w' := by
    apply (weylEquiv i hN hZ).injective
    rw [weylEquiv_mk]
    simpa only [n', w', MulEquiv.apply_symm_apply] using hn
  have hK : intersectionSubset (pointCoxeterSystem i ν hN hZ cs) I J w =
      intersectionSubset cs I J w' := by
    simpa only [w', MulEquiv.apply_symm_apply] using
      pointCoxeterSystem_intersectionSubset i ν hN hZ cs I J w'
  dsimp only
  rw [hK]
  obtain ⟨hP, hU⟩ := hSource.subgroupOf i ν I J w' hw' n' hn'
  exact ⟨hLevi.rationalPoints i ν I J w' hw' n' hn', hP, hU⟩

end Langlands.Aubert.General.RationalPointFamily
