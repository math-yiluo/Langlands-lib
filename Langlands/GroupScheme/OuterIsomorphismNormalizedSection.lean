import Langlands.GroupScheme.OuterIsomorphismProduct

/-! # Outer quotients from normalized sections on all tests -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.GroupIsomorphismScheme

variable {S : Scheme.{u}} {G H A : GroupScheme S}
  (I : GroupIsomorphismScheme G H) (a : AutomorphicAction A G)
  {Q : Over S} (s : Q ⟶ I.parameter)

/-- The orbit morphism of a supplied family of normalized isomorphisms. -/
def sectionOrbitMap : A.X ⊗ Q ⟶ I.parameter :=
  lift (fst A.X Q) (snd A.X Q ≫ s) ≫ I.actionHom a

/-- The orbit morphism acts on a test point by the canonical action. -/
theorem sectionOrbitMap_apply {T : Over S} (d : T ⟶ A.X) (q : T ⟶ Q) :
    lift d q ≫ I.sectionOrbitMap a s =
      lift d (q ≫ s) ≫ I.actionHom a := by
  simp only [sectionOrbitMap, ← Category.assoc, comp_lift, lift_fst, lift_snd]

/-- Acting on the orbit morphism multiplies its group coordinate. -/
theorem sectionOrbitMap_equivariant (T : Over S) (d x : T ⟶ A.X)
    (q : T ⟶ Q) :
    lift d (lift x q ≫ I.sectionOrbitMap a s) ≫ I.actionHom a =
      lift (d * x) q ≫ I.sectionOrbitMap a s := by
  let := I.modObj a
  rw [I.sectionOrbitMap_apply, I.sectionOrbitMap_apply]
  change d • (x • (q ≫ s)) = (d * x) • (q ≫ s)
  exact (mul_smul d x (q ≫ s)).symm

variable (h : ∀ (T : Over S), Function.Bijective
  (fun z : (T ⟶ A.X) × (T ⟶ Q) =>
    lift z.1 (z.2 ≫ s) ≫ I.actionHom a))

include h in
/-- Unique normalized decomposition on every test makes the actual orbit
morphism an isomorphism. -/
theorem sectionOrbitMap_isIso : IsIso (I.sectionOrbitMap a s) := by
  refine isIso_of_yoneda_map_bijective _ fun T => ⟨?_, ?_⟩
  · intro f g hfg
    change f ≫ I.sectionOrbitMap a s = g ≫ I.sectionOrbitMap a s at hfg
    have hz : (f ≫ fst A.X Q, f ≫ snd A.X Q) =
        (g ≫ fst A.X Q, g ≫ snd A.X Q) := by
      apply (h T).1
      simpa only [sectionOrbitMap, ← Category.assoc, comp_lift] using hfg
    apply CartesianMonoidalCategory.hom_ext
    · exact congrArg Prod.fst hz
    · exact congrArg Prod.snd hz
  · intro p
    obtain ⟨⟨d, q⟩, hp⟩ := (h T).2 p
    refine ⟨lift d q, ?_⟩
    change lift d q ≫ I.sectionOrbitMap a s = p
    rw [I.sectionOrbitMap_apply]
    exact hp

/-- The product presentation determined by a supplied normalized section and
its unique decomposition on every test. -/
def normalizedProductIso : A.X ⊗ Q ≅ I.parameter :=
  letI := I.sectionOrbitMap_isIso a s h
  asIso (I.sectionOrbitMap a s)

/-- A normalized section with unique all-test decomposition supplies the
actual outer quotient. -/
def outerOfNormalizedSection [Flat A.X.hom] [QuasiCompact A.X.hom] :
    OuterIsomorphismScheme I a :=
  I.outerOfProduct a (I.normalizedProductIso a s h)
    (I.sectionOrbitMap_equivariant a s)

end Langlands.GroupScheme.GroupIsomorphismScheme
