import Langlands.Representation.CuspidalSupport.RationalInertia
import Langlands.Representation.Category.SmoothCoproducts
import Langlands.Representation.Category.SubrepresentationSums

/-! # Coproducts in the actual rational inertia block -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.SmoothRep

universe uG uI uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {I : Type uI} [DecidableEq I]
  (A : I → SmoothRep.{0, uG, max uI uV} ℂ G)

/-- The invariant ranges of all summand inclusions span the actual direct sum. -/
theorem iSup_range_directSumι :
    (⨆ i, (hom (directSumι A i)).range) = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  induction x using DirectSum.induction_on with
  | zero => exact Submodule.zero_mem _
  | of i v =>
      exact (le_iSup (fun i => (hom (directSumι A i)).range) i)
        ⟨v, rfl⟩
  | add x y hx hy => exact Submodule.add_mem _ hx hy

/-- Every irreducible actual subquotient of a direct sum occurs in a summand. -/
theorem irreducibleSubquotient_directSum
    {D : SmoothRep.{0, uG, max uI uV} ℂ G} (hD : D.IsIrreducible)
    (h : IsSubquotient D (directSum A)) :
    ∃ i, IsSubquotient D (A i) := by
  let S : Subrepresentation (directSum A).representation :=
    ⨆ i, (hom (directSumι A i)).range
  have hS : IsQuotient (directSum A) (subrepresentation (directSum A) S) := by
    refine ⟨subtype _ S, ?_⟩
    intro v
    refine ⟨⟨v, ?_⟩, rfl⟩
    rw [show S = ⊤ from iSup_range_directSumι A]
    exact Submodule.mem_top
  have h' := smoothSubquotientTransitivity ℂ G _ _ _ h hS.isSubquotient
  obtain ⟨i, hi⟩ := irreducibleSubquotient_iSup hD
    (fun i => (hom (directSumι A i)).range) h'
  let q : A i ⟶ subrepresentation (directSum A) (hom (directSumι A i)).range :=
    ofHom {
      toLinearMap := (hom (directSumι A i)).toLinearMap.rangeRestrict
      isIntertwining' g := by
        ext v
        exact Subtype.ext
          (Representation.IntertwiningMap.isIntertwining _ _ (hom (directSumι A i)) g v) }
  have hq : Function.Surjective (hom q) := by
    intro v
    obtain ⟨w, hw⟩ := v.property
    exact ⟨w, Subtype.ext hw⟩
  exact ⟨i, smoothSubquotientTransitivity ℂ G _ _ _ hi
    (IsQuotient.isSubquotient ⟨q, hq⟩)⟩

end Langlands.SmoothRep

namespace Langlands.CuspidalSupport

universe uF uV uI

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance rationalInertiaCoproductsTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

variable (π : SmoothRep.{0, uF, max uI uV} ℂ (GroupScheme.rationalPoints G))
  {I : Type uI} [DecidableEq I]

/-- Arbitrary direct sums preserve the actual all-subquotients inertia property. -/
theorem rationalInertiaBlockProperty_directSum
    (A : I → SmoothRep.{0, uF, max uI uV} ℂ (GroupScheme.rationalPoints G))
    (hA : ∀ i, rationalInertiaBlockProperty G π (A i)) :
    rationalInertiaBlockProperty G π (SmoothRep.directSum A) := by
  intro D hD h
  obtain ⟨i, hi⟩ := SmoothRep.irreducibleSubquotient_directSum A hD h
  exact hA i D hD hi

/-- The actual direct sum as an object of the full inertia block. -/
def rationalInertiaBlockDirectSum (A : I → RationalInertiaBlock G π) :
    RationalInertiaBlock G π :=
  ⟨SmoothRep.directSum (fun i => (A i).obj),
    rationalInertiaBlockProperty_directSum G π _ (fun i => (A i).property)⟩

/-- The cofan in the full block has the actual summand inclusions. -/
def rationalInertiaBlockDirectSumCofan (A : I → RationalInertiaBlock G π) :
    Cofan A :=
  Cofan.mk (rationalInertiaBlockDirectSum G π A)
    (fun i => ObjectProperty.homMk (SmoothRep.directSumι (fun i => (A i).obj) i))

/-- The direct-sum cofan is a coproduct in the actual full inertia block. -/
def rationalInertiaBlockDirectSumIsColimit (A : I → RationalInertiaBlock G π) :
    IsColimit (rationalInertiaBlockDirectSumCofan G π A) := by
  let h := SmoothRep.directSumIsColimit (fun i => (A i).obj)
  let forgetCofan (s : Cofan A) : Cofan (fun i => (A i).obj) :=
    Cofan.mk s.pt.obj (fun i => (s.inj i).hom)
  refine Cofan.IsColimit.mk _
    (fun s => ObjectProperty.homMk (h.desc (forgetCofan s))) ?_ ?_
  · intro s i
    apply ObjectProperty.hom_ext
    exact h.fac (forgetCofan s) ⟨i⟩
  · intro s m hm
    apply ObjectProperty.hom_ext
    apply h.uniq (forgetCofan s) m.hom
    intro ⟨i⟩
    exact congrArg (fun f => f.hom) (hm i)

omit [DecidableEq I] in
/-- Coproducts exist for every index type whose universe fits the carrier. -/
theorem rationalInertiaBlock_hasColimitsOfShape :
    HasColimitsOfShape (Discrete I) (RationalInertiaBlock G π) := by
  classical
  refine ⟨fun A => ?_⟩
  let B : I → RationalInertiaBlock G π := fun i => A.obj ⟨i⟩
  have : HasColimit (Discrete.functor (A.obj ∘ Discrete.mk)) :=
    ⟨⟨rationalInertiaBlockDirectSumCofan G π B,
      rationalInertiaBlockDirectSumIsColimit G π B⟩⟩
  exact hasColimit_of_iso (Discrete.natIsoFunctor (F := A))

end Langlands.CuspidalSupport
