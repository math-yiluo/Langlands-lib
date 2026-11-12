import Langlands.GroupScheme.Reductive.AbsoluteStarAction
import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange

/-! # The actual Tits index of a semisimple field group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]

/-- Restrict an actual absolute root to a split torus over `k`, descending the
restriction by the canonical base-change equivalence of its character lattice. -/
def absoluteRootRestriction (p : GaloisPinningData k (SeparableClosure k) G)
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hS : IsSplitTorus S.toGrp)
    (f : S ⟶ p.torus) (a : p.rootIndex) : characterLattice S :=
  (characterLattice.baseChangeEquiv (algebraBaseMap k (SeparableClosure k)) S hS).symm
    ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map f ≫
      p.rootDatum.root a)

/-- Compatible choices defining the index of an actual semisimple group. The
positivity field concerns every absolute root with nonzero restriction; no
invariance, orbit comparison, rank equality or classification is a field. -/
structure TitsIndexData (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] where
  isSemisimple : IsSemisimple G
  pinning : GaloisPinningData k (SeparableClosure k) G
  maximalTorus : IsMaximalTorus pinning.inclusion
  splitTorus : CommGroupScheme (Spec (CommRingCat.of k))
  splitInclusion : splitTorus.toGrp ⟶ G
  maximalSplit : IsMaximalSplitTorus splitInclusion
  torusMap : splitTorus ⟶ pinning.torus
  square : CommGroupScheme.groupHom torusMap ≫ pinning.inclusion = splitInclusion
  positiveCocharacter : cocharacterLattice splitTorus
  generic : IsGenericCocharacter splitInclusion positiveCocharacter
  compatible : ∀ a : pinning.rootIndex,
    absoluteRootRestriction pinning splitTorus maximalSplit.1.1 torusMap a ≠ 0 →
      (pinning.base.IsPos a ↔
        0 < latticePairing splitTorus
          (absoluteRootRestriction pinning splitTorus maximalSplit.1.1 torusMap a)
          positiveCocharacter)

namespace TitsIndexData

variable (d : TitsIndexData G)

/-- The simple vertices of the actual absolute root datum. -/
abbrev Vertex : Type u := d.pinning.base.support

instance : Finite d.Vertex := inferInstanceAs (Finite d.pinning.base.support)

/-- Actual integral Cartan pairings, encoding the full Dynkin diagram. -/
def cartan (a b : d.Vertex) : ℤ := d.pinning.rootDatum.pairing a.val b.val

/-- The actual restriction of any absolute root to the maximal split torus. -/
def rootRestriction (a : d.pinning.rootIndex) : characterLattice d.splitTorus :=
  absoluteRootRestriction d.pinning d.splitTorus d.maximalSplit.1.1 d.torusMap a

/-- The anisotropic vertices `Δ₀`, defined by actual zero restriction. -/
def zeroVertices : Set d.Vertex := {a | d.rootRestriction a.val = 0}

/-- The distinguished vertices, the complement of `Δ₀`. -/
def distinguishedVertices : Set d.Vertex := d.zeroVerticesᶜ

/-- The full absolute Galois star action on simple vertices, obtained from the
Library action on the based absolute root datum. -/
def star (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) (a : d.Vertex) : d.Vertex :=
  ⟨(d.pinning.starAction σ).val.indexEquiv a.val,
    ((d.pinning.starAction σ).property a.val).mp a.property⟩

@[simp] theorem star_one (a : d.Vertex) : d.star 1 a = a := by
  apply Subtype.ext
  change (d.pinning.starAction 1).val.indexEquiv a.val = a.val
  rw [map_one]
  rfl

theorem star_mul (σ τ : SeparableClosure k ≃ₐ[k] SeparableClosure k) (a : d.Vertex) :
    d.star (σ * τ) a = d.star σ (d.star τ a) := by
  apply Subtype.ext
  change (d.pinning.starAction (σ * τ)).val.indexEquiv a.val =
    (d.pinning.starAction σ).val.indexEquiv ((d.pinning.starAction τ).val.indexEquiv a.val)
  rw [map_mul]
  rfl

/-- The orbit equivalence restricted to distinguished vertices. This restriction
of an equivalence relation makes sense even before star invariance is proved. -/
def distinguishedOrbitSetoid : Setoid d.distinguishedVertices where
  r a b := ∃ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k, d.star σ a.val = b.val
  iseqv := {
    refl := fun a => ⟨1, d.star_one a.val⟩
    symm := by
      rintro a b ⟨σ, h⟩
      refine ⟨σ⁻¹, ?_⟩
      rw [← h, ← d.star_mul, inv_mul_cancel, d.star_one]
    trans := by
      rintro a b c ⟨σ, hσ⟩ ⟨τ, hτ⟩
      refine ⟨τ * σ, ?_⟩
      rw [d.star_mul, hσ, hτ] }

/-- Distinguished star orbits, retaining the original full action in `d`. -/
abbrev DistinguishedOrbit : Type u := Quotient d.distinguishedOrbitSetoid

instance : Finite d.DistinguishedOrbit := inferInstanceAs
  (Finite (Quotient d.distinguishedOrbitSetoid))

/-- The quotient map from distinguished vertices to their actual star orbits. -/
def orbitClass (a : d.distinguishedVertices) : d.DistinguishedOrbit :=
  Quotient.mk d.distinguishedOrbitSetoid a

end TitsIndexData

/-- Equivalence of actual indices: all Cartan pairings, `Δ₀`, and the action of
each element of the same absolute Galois group are preserved. This notion also
compares indices of different groups over the same field. -/
structure TitsIndexEquiv (d : TitsIndexData G) (e : TitsIndexData H) where
  vertices : d.Vertex ≃ e.Vertex
  cartan_eq : ∀ a b, e.cartan (vertices a) (vertices b) = d.cartan a b
  zero_iff : ∀ a, a ∈ d.zeroVertices ↔ vertices a ∈ e.zeroVertices
  star_eq : ∀ (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) a,
    vertices (d.star σ a) = e.star σ (vertices a)

end Langlands.GroupScheme
