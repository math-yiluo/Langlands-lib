import Langlands.AlgebraicGeometry.AlgebraicSpace.UnipotentOrbitQuotientStatement
import Mathlib.CategoryTheory.Sites.LocallyInjective

/-! # Points identified by an fppf action quotient are locally in one orbit

Let `π : Z ⟶ Q` be the fppf sheaf quotient of a scheme `Z` by an action `b` of a group
scheme `G`. Two `T`-points of `Z` with the same image in `Q` are, after restriction to the
members of an fppf covering sieve of `T`, translates of each other by points of `G`. Every
member of an fppf covering sieve of `T` is part of a jointly surjective family, so each point
of `T` lies in the image of such a member.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry
open Langlands (GroupScheme)
open Langlands.GroupScheme (SchemeAction)
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace ActionQuotientOrbitRelation

variable {S : Scheme.{u}} {G : GroupScheme S} {Z : Over S} (b : SchemeAction G Z)

/-- Two `T`-points of `Z` are related when the first is the translate of the second by a
`T`-point of `G`. -/
def orbitSetoid (T : Over S) : Setoid (((schemeYoneda S).obj Z).obj (op T)) where
  r x y := ∃ g : T ⟶ G.X, x.down = b.act g y.down
  iseqv :=
    { refl := fun x => ⟨1, (b.act_one x.down).symm⟩
      symm := fun {x y} ⟨g, h⟩ =>
        ⟨g⁻¹, by rw [h, ← b.act_mul, inv_mul_cancel, b.act_one]⟩
      trans := fun {x y z} ⟨g, hg⟩ ⟨k, hk⟩ => ⟨g * k, by rw [hg, hk, b.act_mul]⟩ }

/-- Restriction along a morphism of test schemes preserves the orbit relation. -/
theorem orbitSetoid_map {T T' : Over S} (f : T' ⟶ T)
    {x y : ((schemeYoneda S).obj Z).obj (op T)} (h : (orbitSetoid b T).r x y) :
    (orbitSetoid b T').r (((schemeYoneda S).obj Z).map f.op x)
      (((schemeYoneda S).obj Z).map f.op y) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨f ≫ g, ?_⟩
  change f ≫ x.down = b.act (f ≫ g) (f ≫ y.down)
  rw [hg, b.naturality]

/-- The presheaf of orbits `T ↦ Z(T)/G(T)`. -/
def orbitPresheaf : Presheaf S where
  obj T := Quotient (orbitSetoid b T.unop)
  map f := ↾(Quotient.map (((schemeYoneda S).obj Z).map f)
    (fun _ _ h ↦ orbitSetoid_map b f.unop h))
  map_id T := by
    ext q
    induction q using Quotient.ind with
    | _ x => exact congrArg (Quotient.mk _) (((schemeYoneda S).obj Z).map_id_apply T x)
  map_comp f k := by
    ext q
    induction q using Quotient.ind with
    | _ x =>
      exact congrArg (Quotient.mk _) (((schemeYoneda S).obj Z).map_comp_apply f k x)

/-- The quotient map from the points of `Z` to their orbits. -/
def toOrbitPresheaf : (schemeYoneda S).obj Z ⟶ orbitPresheaf b where
  app T := ↾(Quotient.mk (orbitSetoid b T.unop))
  naturality _ _ _ := rfl

/-- The sieve of morphisms `f : V ⟶ T` after which `x` becomes a translate of `y`. -/
def orbitSieve {T : Over S} (x y : T ⟶ Z) : Sieve T where
  arrows V f := ∃ g : V ⟶ G.X, f ≫ x = b.act g (f ≫ y)
  downward_closed {V W} f := by
    rintro ⟨g, hg⟩ k
    refine ⟨k ≫ g, ?_⟩
    rw [Category.assoc, hg, b.naturality, Category.assoc]

/-- Two points of `Z` with equal images in an fppf action quotient lie in one orbit after
restriction to the members of an fppf covering sieve. -/
theorem orbitSieve_mem {Q : FppfSheaf S} {π : (schemeSheaf S).obj Z ⟶ Q}
    (hπ : IsFppfActionQuotient b π) {T : Over S} (x y : T ⟶ Z)
    (hxy : π.hom.app (op T) ⟨x⟩ = π.hom.app (op T) ⟨y⟩) :
    orbitSieve b x y ∈ fppfTopology S T := by
  obtain ⟨w, ⟨hc⟩⟩ := hπ
  let J := fppfTopology S
  let P := orbitPresheaf b
  let ρ : (schemeSheaf S).obj Z ⟶ (presheafToSheaf J (Type (u + 1))).obj P :=
    ObjectProperty.homMk (toOrbitPresheaf b ≫ toSheafify J P)
  have hρ : (schemeSheaf S).map b.hom ≫ ρ = (schemeSheaf S).map (snd G.X Z) ≫ ρ := by
    apply (sheafToPresheaf J _).map_injective
    change (schemeYoneda S).map b.hom ≫ toOrbitPresheaf b ≫ toSheafify J P =
      (schemeYoneda S).map (snd G.X Z) ≫ toOrbitPresheaf b ≫ toSheafify J P
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    ext V p
    apply Quotient.sound
    refine ⟨p.down ≫ fst G.X Z, ?_⟩
    change p.down ≫ b.hom = lift (p.down ≫ fst G.X Z) (p.down ≫ snd G.X Z) ≫ b.hom
    rw [← comp_lift, lift_fst_snd, Category.comp_id]
  let φ := hc.desc (Cofork.ofπ ρ hρ)
  have hφ : π ≫ φ = ρ := hc.fac (Cofork.ofπ ρ hρ) WalkingParallelPair.one
  have happ : (toSheafify J P).app (op T) ((toOrbitPresheaf b).app (op T) ⟨x⟩) =
      (toSheafify J P).app (op T) ((toOrbitPresheaf b).app (op T) ⟨y⟩) := by
    have h := congrArg (fun k : (schemeSheaf S).obj Z ⟶ _ => k.hom) hφ
    have hx := congrArg (fun k : (schemeYoneda S).obj Z ⟶ _ => k.app (op T) ⟨x⟩) h
    have hy := congrArg (fun k : (schemeYoneda S).obj Z ⟶ _ => k.app (op T) ⟨y⟩) h
    change φ.hom.app (op T) (π.hom.app (op T) ⟨x⟩) =
      (toSheafify J P).app (op T) ((toOrbitPresheaf b).app (op T) ⟨x⟩) at hx
    change φ.hom.app (op T) (π.hom.app (op T) ⟨y⟩) =
      (toSheafify J P).app (op T) ((toOrbitPresheaf b).app (op T) ⟨y⟩) at hy
    rw [← hx, ← hy, hxy]
  refine J.superset_covering ?_
    (CategoryTheory.Presheaf.equalizerSieve_mem J (toSheafify J P) _ _ happ)
  intro V f hf
  have hq : P.map f.op ((toOrbitPresheaf b).app (op T) ⟨x⟩) =
      P.map f.op ((toOrbitPresheaf b).app (op T) ⟨y⟩) := hf
  obtain ⟨g, hg⟩ := Quotient.exact hq
  exact ⟨g, hg⟩

/-- A member of every fppf covering sieve passes through each point of the test scheme. -/
theorem exists_mem_range_of_mem {T : Over S} {J : Sieve T} (hJ : J ∈ fppfTopology S T)
    (t : T.left) : ∃ (V : Over S) (f : V ⟶ T), J f ∧ t ∈ Set.range f.left := by
  rw [GrothendieckTopology.mem_over_iff] at hJ
  have : Precoverage.HasIsos Scheme.fppfPrecoverage.{u} :=
    ⟨fun f _ ↦ f.singleton_mem_fppfPrecoverage⟩
  have : Precoverage.HasPullbacks Scheme.fppfPrecoverage.{u} :=
    inferInstanceAs (Precoverage.HasPullbacks
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)))
  obtain ⟨R, hR, hRJ⟩ :=
    (Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition).1 hJ
  have hjs : R ∈ Scheme.jointlySurjectivePrecoverage T.left := hR.1
  obtain ⟨Y, f, hf, hy⟩ :=
    (Presieve.mem_comap_jointlySurjectivePrecoverage_iff _).1 hjs t
  refine ⟨Over.mk (f ≫ T.hom), Over.homMk f, ?_, hy⟩
  exact (Sieve.overEquiv_iff J f).1 (hRJ _ f hf)

end ActionQuotientOrbitRelation

end Langlands.AlgebraicGeometry.AlgebraicSpace
