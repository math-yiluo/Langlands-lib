import Langlands.GroupScheme.Rational.ActionWeightTransport
import Langlands.GroupScheme.Rational.RootProductTransport
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # Semigroup subgroups under equivariant closed inclusions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {B : Scheme.{u}} {G H K : GroupScheme B} {f : G ⟶ H}

/-- Taking the image of a preimage recovers a subgroup contained in the range. -/
theorem map_comap_of_le_range (F : SubgroupFunctor H) (hF : F ≤ range f) :
    (F.comap f).map f = F := by
  rw [map_comap]
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  exact ⟨And.right, fun hx => ⟨hF T hx, hx⟩⟩

/-- Factoring a represented subgroup through a represented inclusion represents
its all-test preimage, whenever the subgroup lies in that inclusion. -/
theorem IsRepresentedBy.factor {V F : SubgroupFunctor H} {j : K ⟶ H}
    (hf : V.IsRepresentedBy f) (hj : F.IsRepresentedBy j) (hF : F ≤ V) :
    (F.comap f).IsRepresentedBy
      (hf.factorHom j (by rw [hj.2]; exact hF)) := by
  let g := hf.factorHom j (by rw [hj.2]; exact hF)
  have hcomp : g ≫ f = j := hf.factorHom_comp _ _
  have hcomp' : g.hom.hom ≫ f.hom.hom = j.hom.hom :=
    congrArg (fun a => a.hom.hom) hcomp
  let : Mono j.hom.hom := hj.1
  refine ⟨mono_of_mono_fac hcomp', ?_⟩
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  constructor
  · rintro ⟨y, rfl⟩
    change T ⟶ K.X at y
    change (y ≫ g.hom.hom) ≫ f.hom.hom ∈ F.carrier T
    rw [Category.assoc, hcomp', ← hj.2]
    exact ⟨y, rfl⟩
  · intro hx
    change x ≫ f.hom.hom ∈ F.carrier T at hx
    rw [← hj.2] at hx
    obtain ⟨y, hy⟩ := hx
    change T ⟶ K.X at y
    change y ≫ j.hom.hom = x ≫ f.hom.hom at hy
    refine ⟨y, ?_⟩
    apply hf.1.right_cancellation
    change (y ≫ g.hom.hom) ≫ f.hom.hom = x ≫ f.hom.hom
    rw [Category.assoc, hcomp']
    exact hy

end SubgroupFunctor

namespace RelativeRoot

section Geometry

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    (f : G ⟶ H) (hfc : IsClosedSubgroup f)

include hfc

/-- A closed inclusion preserves smooth connected closed subgroup functors. -/
theorem IsSmoothConnectedClosed.map {F : SubgroupFunctor G}
    (hF : IsSmoothConnectedClosed F) : IsSmoothConnectedClosed (F.map f) := by
  obtain ⟨K, j, hj, hjc, hKs, hKc⟩ := hF
  have : Mono f.hom.hom.left := hfc.mono
  have hf : (SubgroupFunctor.range f).IsRepresentedBy f :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  exact ⟨K, j ≫ f, hj.comp hf, hjc.comp hfc, hKs, hKc⟩

/-- A smooth connected closed subgroup inside a closed inclusion has the same
smooth connected representative when viewed inside that inclusion. -/
theorem IsSmoothConnectedClosed.comap {F : SubgroupFunctor H}
    (hF : IsSmoothConnectedClosed F) (hFrange : F ≤ SubgroupFunctor.range f) :
    IsSmoothConnectedClosed (F.comap f) := by
  obtain ⟨K, j, hj, hjc, hKs, hKc⟩ := hF
  have : Mono f.hom.hom.left := hfc.mono
  have hf : (SubgroupFunctor.range f).IsRepresentedBy f :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  let g := hf.factorHom j (by rw [hj.2]; exact hFrange)
  have hcomp : g ≫ f = j := hf.factorHom_comp _ _
  refine ⟨K, g, hf.factor hj hFrange, ?_, hKs, hKc⟩
  apply IsClosedSubgroup.of_comp hfc
  rw [hcomp]
  exact hjc

end Geometry

section Semigroups

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (f : G ⟶ H) (hfc : IsClosedSubgroup f)
    (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp H)
    (hbc : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (x : T ⟶ G.X),
      b.act s x ≫ f.hom.hom = c.act s (x ≫ f.hom.hom))

include hfc hbc

/-- Equivariant closed inclusions carry semigroup generators to generators. -/
theorem IsSemigroupGenerator.map {A : AddSubsemigroup (characterLattice S)}
    {F : SubgroupFunctor G} (hF : IsSemigroupGenerator b A F) :
    IsSemigroupGenerator c A (F.map f) := by
  have : Mono f.hom.hom.left := hfc.mono
  have hf : Mono f.hom.hom := Over.mono_of_mono_left _
  refine ⟨hF.1.map f hfc, ?_, ?_⟩
  · rintro T s x ⟨y, hy, rfl⟩
    exact ⟨b.act s y, hF.2.1 T s y hy, hbc T s y⟩
  · rw [actionWeightSupport_map f hf b c hbc]
    exact hF.2.2

/-- Ambient semigroup generators contained in a closed inclusion are also
semigroup generators for its own action. -/
theorem IsSemigroupGenerator.comap {A : AddSubsemigroup (characterLattice S)}
    {F : SubgroupFunctor H} (hF : IsSemigroupGenerator c A F)
    (hFrange : F ≤ SubgroupFunctor.range f) :
    IsSemigroupGenerator b A (F.comap f) := by
  have : Mono f.hom.hom.left := hfc.mono
  have hf : Mono f.hom.hom := Over.mono_of_mono_left _
  refine ⟨hF.1.comap f hfc hFrange, ?_, ?_⟩
  · intro T s x hx
    change b.act s x ≫ f.hom.hom ∈ F.carrier T
    rw [hbc]
    exact hF.2.1 T s (x ≫ f.hom.hom) hx
  · have he := actionWeightSupport_map f hf b c hbc (F.comap f)
    rw [SubgroupFunctor.map_comap_of_le_range F hFrange] at he
    rw [← he]
    exact hF.2.2

/-- The image of the internally generated subgroup lies in the ambient one. -/
theorem semigroupSubgroup_map_le (A : AddSubsemigroup (characterLattice S)) :
    (semigroupSubgroup b A).map f ≤ semigroupSubgroup c A := by
  apply SubgroupFunctor.map_le_iff_le_comap.mpr
  intro T
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨F, hF, hx⟩
  exact generator_le_semigroupSubgroup c A (F.map f)
    (hF.map f hfc b c hbc) T ⟨x, hx, rfl⟩

/-- If the ambient semigroup subgroup lies inside an equivariant closed
inclusion, it equals the image of the subgroup generated internally. -/
theorem semigroupSubgroup_map_eq (A : AddSubsemigroup (characterLattice S))
    (hA : semigroupSubgroup c A ≤ SubgroupFunctor.range f) :
    (semigroupSubgroup b A).map f = semigroupSubgroup c A := by
  apply le_antisymm (semigroupSubgroup_map_le f hfc b c hbc A)
  intro T
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨F, hF, hx⟩
  have hFrange : F ≤ SubgroupFunctor.range f :=
    (generator_le_semigroupSubgroup c A F hF).trans hA
  obtain ⟨y, hyx⟩ := hFrange T hx
  change T ⟶ G.X at y
  change y ≫ f.hom.hom = x at hyx
  refine ⟨y, ?_, hyx⟩
  apply generator_le_semigroupSubgroup b A (F.comap f)
    (hF.comap f hfc b c hbc hFrange) T
  change y ≫ f.hom.hom ∈ F.carrier T
  rw [hyx]
  exact hx

/-- The point homomorphism on the actual generated semigroup subgroups. -/
def semigroupSubgroupPointsMap (A : AddSubsemigroup (characterLattice S))
    (T : Over (Spec (CommRingCat.of k))) :
    (semigroupSubgroup b A).carrier T →* (semigroupSubgroup c A).carrier T where
  toFun x := ⟨x.val ≫ f.hom.hom,
    semigroupSubgroup_map_le f hfc b c hbc A T ⟨x.val, x.property, rfl⟩⟩
  map_one' := Subtype.ext (MonObj.one_comp _)
  map_mul' x y := Subtype.ext (MonObj.mul_comp x.val y.val _)

/-- When the ambient generated subgroup is contained in the inclusion, its
points are canonically the internally generated subgroup points. -/
def semigroupSubgroupPointsEquiv (A : AddSubsemigroup (characterLattice S))
    (hA : semigroupSubgroup c A ≤ SubgroupFunctor.range f)
    (T : Over (Spec (CommRingCat.of k))) :
    (semigroupSubgroup b A).carrier T ≃* (semigroupSubgroup c A).carrier T := by
  have : Mono f.hom.hom.left := hfc.mono
  have hf : Mono f.hom.hom := Over.mono_of_mono_left _
  refine MulEquiv.ofBijective (semigroupSubgroupPointsMap f hfc b c hbc A T) ⟨?_, ?_⟩
  · intro x y h
    apply Subtype.ext
    exact hf.right_cancellation _ _ (congrArg Subtype.val h)
  · intro x
    have hx : x.val ∈ ((semigroupSubgroup b A).map f).carrier T := by
      rw [semigroupSubgroup_map_eq f hfc b c hbc A hA]
      exact x.property
    obtain ⟨y, hy, hyx⟩ := hx
    exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩

end Semigroups

end RelativeRoot

end Langlands.GroupScheme
