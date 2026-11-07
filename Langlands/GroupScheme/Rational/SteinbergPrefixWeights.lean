import Langlands.LinearAlgebra.OrderedReflectionWeights
import Langlands.GroupScheme.Rational.SteinbergCoxeterTorus
import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.AutomorphicAction

/-! # Actual prefix-conjugated additive factors of the Steinberg product -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G}

local instance : Mono p.inclusion.hom.hom.left := p.isMaximalTorus.2.1.mono

namespace NormalizedRootParametrization

variable {a : p.base.support} (x : p.NormalizedRootParametrization a)
    (n : normalizerPoints p.inclusion)

/-- The supplied additive map conjugated by an actual normalizing rational point. -/
def conjugateHom : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G :=
  x.hom ≫ (G.innerIso n).hom

theorem isClosedSubgroup_conjugateHom : IsClosedSubgroup (x.conjugateHom n) :=
  x.isClosedSubgroup.comp_iso (G.innerIso n)

/-- Its scalar values are the actual conjugates on every scheme test. -/
theorem scalarPoint_conjugateHom (T : Over (Spec (CommRingCat.of k)))
    (c : Γ(T.left, ⊤)) :
    VectorGroup.scalarPoint (CommRingCat.of k) T c ≫ (x.conjugateHom n).hom.hom =
      G.constantPoint n T * x.point T c * (G.constantPoint n T)⁻¹ := by
  rw [conjugateHom, Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom]
  rfl

/-- Conjugation changes the torus weight by the actual contravariant Weyl action. -/
theorem conjugateHom_torus_equivariant (T : Over (Spec (CommRingCat.of k)))
    (t : T ⟶ p.torus.X) (c : Γ(T.left, ⊤)) :
    (AutomorphicAction.conjugation p.inclusion).act t
        (VectorGroup.scalarPoint (CommRingCat.of k) T c ≫ (x.conjugateHom n).hom.hom) =
      VectorGroup.scalarPoint (CommRingCat.of k) T
        (VectorGroup.charValue (weylAction p.inclusion n (p.rootDatum.root a)) T t * c) ≫
          (x.conjugateHom n).hom.hom := by
  let σ := normalizingAut p.inclusion n
  let t' : T ⟶ p.torus.X := t ≫ (CommGroupScheme.groupHom σ.inv).hom.hom
  have hn :
      (G.constantPoint n T)⁻¹ * (t ≫ p.inclusion.hom.hom) * G.constantPoint n T =
        t' ≫ p.inclusion.hom.hom := by
    have h := (isNormalizingPoint_normalizingAut p.inclusion n).inv.conj_comp T t
    simpa [t', σ, constantPoint_inv] using h
  have hw :
      VectorGroup.charValue (weylAction p.inclusion n (p.rootDatum.root a)) T t =
        VectorGroup.charValue (p.rootDatum.root a) T t' := by
    rfl
  rw [AutomorphicAction.conjugation_act, scalarPoint_conjugateHom,
    scalarPoint_conjugateHom, hw]
  calc
    _ = G.constantPoint n T *
        (((G.constantPoint n T)⁻¹ * (t ≫ p.inclusion.hom.hom) * G.constantPoint n T) *
          x.point T c *
          ((G.constantPoint n T)⁻¹ * (t ≫ p.inclusion.hom.hom) * G.constantPoint n T)⁻¹) *
        (G.constantPoint n T)⁻¹ := by group
    _ = _ := by
      rw [hn]
      exact congrArg (fun z => G.constantPoint n T * z * (G.constantPoint n T)⁻¹)
        (x.torus_equivariant T t' c)

end NormalizedRootParametrization

variable {r : ℕ} (e : Fin r ≃ p.base.support)
    (x : p.NormalizedSimpleRootParametrizations) (n : p.SimpleReflectionRepresentatives)

/-- Products of the preceding supplied representatives in the actual normalizer. -/
def prefixNormalizer (j : Fin (r + 1)) : normalizerPoints p.inclusion :=
  orderedPrefix r (fun i => (n (e i)).normalizerPoint) j

/-- The actual additive factor obtained by moving preceding representatives to the right. -/
def prefixRootHom (j : Fin r) : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G :=
  (x (e j)).conjugateHom (prefixNormalizer e n j.castSucc)

/-- The full integral character of a prefix-conjugated additive factor. -/
def prefixWeight (j : Fin r) : characterLattice p.torus :=
  weylAction p.inclusion (prefixNormalizer e n j.castSucc) (p.rootDatum.root (e j))

theorem prefixWeight_eq (j : Fin r) :
    prefixWeight e n j =
      orderedPrefix r (fun i => p.rootDatum.reflection (e i)) j.castSucc
        (p.rootDatum.root (e j)) := by
  simp only [prefixWeight, prefixNormalizer, map_orderedPrefix,
    SimpleReflectionRepresentative.weylAction_normalizerPoint]

/-- Independence is in the integral character lattice, over an arbitrary field. -/
theorem prefixWeight_linearIndependent : LinearIndependent ℤ (prefixWeight e n) := by
  change LinearIndependent ℤ (fun j => prefixWeight e n j)
  simp_rw [prefixWeight_eq]
  exact Langlands.LinearAlgebra.prefixSimpleRoots_linearIndependent p.base e

theorem isClosedSubgroup_prefixRootHom (j : Fin r) :
    IsClosedSubgroup (prefixRootHom e x n j) :=
  (x (e j)).isClosedSubgroup_conjugateHom _

theorem prefixRootHom_torus_equivariant (j : Fin r)
    (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ p.torus.X) (c : Γ(T.left, ⊤)) :
    (AutomorphicAction.conjugation p.inclusion).act t
        (VectorGroup.scalarPoint (CommRingCat.of k) T c ≫ (prefixRootHom e x n j).hom.hom) =
      VectorGroup.scalarPoint (CommRingCat.of k) T
        (VectorGroup.charValue (prefixWeight e n j) T t * c) ≫
          (prefixRootHom e x n j).hom.hom :=
  (x (e j)).conjugateHom_torus_equivariant _ T t c

end Langlands.GroupScheme.SplitPinning
