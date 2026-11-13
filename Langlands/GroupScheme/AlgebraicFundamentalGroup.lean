import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.GroupScheme.SimplyConnected.DerivedCoverProof
import Langlands.GroupScheme.SimplyConnected.DerivedCoverMaximalTorusPreimageProof
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.GroupScheme.CocharacterTransportNaturality
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # The algebraic fundamental group from actual maximal tori and derived covers -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AlgebraicFundamentalGroup

variable (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))

/-- The choices in KP Construction 11.3.1: an actual maximal torus and an actual
simply connected cover of the derived subgroup. -/
structure Choice where
  torus : CommGroupScheme (Spec (CommRingCat.of k))
  inclusion : torus.toGrp ⟶ G
  isMaximal : IsMaximalTorus inclusion
  derived : GroupScheme (Spec (CommRingCat.of k))
  cover : GroupScheme (Spec (CommRingCat.of k))
  derivedInclusion : derived ⟶ G
  covering : cover ⟶ derived
  isCover : IsSimplyConnectedDerivedCover derivedInclusion covering

/-- These choices exist over the original field; no maximal-torus or cover witness
is added to the hypotheses of the fundamental group. -/
theorem nonempty_choice (hG : IsConnectedReductive G) : Nonempty (Choice k G) := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨T, i, hi⟩ := maximalTorusExistence k G
  obtain ⟨D, C, d, π, h⟩ := simplyConnectedDerivedCoverExistence k G hG
  exact ⟨⟨T, i, hi, D, C, d, π, h⟩⟩

/-- A fixed choice of maximal torus and derived cover. -/
def chosenChoice (hG : IsConnectedReductive G) : Choice k G :=
  Classical.choice (nonempty_choice k G hG)

namespace Choice

variable {k G} (a : Choice k G)

/-- The full scheme-theoretic preimage of the maximal torus in the derived cover. -/
abbrev scPreimage : GroupScheme (Spec (CommRingCat.of k)) :=
  subgroupIntersection (a.covering ≫ a.derivedInclusion) a.inclusion

/-- The preimage is a torus by the published derived-cover theorem. -/
theorem scPreimage_isTorus : IsTorus a.scPreimage :=
  derivedCoverMaximalTorusPreimage k G a.derived a.cover a.torus
    a.derivedInclusion a.covering a.inclusion a.isCover a.isMaximal

/-- The same actual preimage, with its torus commutativity. -/
def scTorus : CommGroupScheme (Spec (CommRingCat.of k)) :=
  { a.scPreimage with comm := a.scPreimage_isTorus.isCommMonObj }

/-- The actual inclusion of the preimage into the simply connected group. -/
abbrev scInclusion : a.scTorus.toGrp ⟶ a.cover :=
  subgroupIntersectionFst (a.covering ≫ a.derivedInclusion) a.inclusion

/-- The actual homomorphism `T_sc → T`. -/
def scToTorus : a.scTorus ⟶ a.torus :=
  Additive.ofMul (subgroupIntersectionSnd
    (a.covering ≫ a.derivedInclusion) a.inclusion)

variable (E : Type u) [Field E] [Algebra k E]

/-- Cocharacters of the geometric base change of the chosen maximal torus. -/
abbrev lattice :=
  cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus)

/-- Cocharacters of the actual preimage torus after the same base change. -/
abbrev scLattice :=
  cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.scTorus)

/-- The integral map `X_*(T_sc) → X_*(T)` induced by the actual torus morphism. -/
def corootMap : a.scLattice E →ₗ[ℤ] a.lattice E :=
  (AddMonoidHom.mk' (fun ν =>
    ν ≫ (CommGroupScheme.baseChange (algebraBaseMap k E)).map a.scToTorus)
    (fun _ _ => Preadditive.add_comp _ _ _ _ _ _)).toIntLinearMap

/-- The image lattice of `X_*(T_sc)` in `X_*(T)`. -/
def corootImage : Submodule ℤ (a.lattice E) := (a.corootMap E).range

/-- The actual quotient `X_*(T)/X_*(T_sc)` for these choices. -/
abbrev atChoice := a.lattice E ⧸ a.corootImage E

/-- The canonical quotient map. -/
abbrev projection : a.lattice E →ₗ[ℤ] a.atChoice E := (a.corootImage E).mkQ

/-- Galois transport commutes with the actual map from the preimage torus. -/
theorem corootMap_galois (σ : E ≃ₐ[k] E) (ν : a.scLattice E) :
    cocharacterLattice.galoisRepresentation k E a.torus σ (a.corootMap E ν) =
      a.corootMap E (cocharacterLattice.galoisRepresentation k E a.scTorus σ ν) := by
  apply (Additive.ofMul.injective)
  change transportCocharacter (algebraBaseMap k E) (galoisBaseMap k E σ)
      (galoisBaseMap_over k E σ) a.torus.toGrp
      (CommGroupScheme.groupHom ν ≫
        (GroupScheme.baseChange (algebraBaseMap k E)).map
          (CommGroupScheme.groupHom a.scToTorus)) = _
  exact transportCocharacter_naturality (algebraBaseMap k E) (galoisBaseMap k E σ)
    (galoisBaseMap_over k E σ) (CommGroupScheme.groupHom a.scToTorus)
    (CommGroupScheme.groupHom ν)

/-- The coroot image is stable under the ordinary lattice Galois action. -/
theorem corootImage_stable (σ : E ≃ₐ[k] E) :
    a.corootImage E ≤ (a.corootImage E).comap
      (cocharacterLattice.galoisRepresentation k E a.torus σ) := by
  rintro _ ⟨ν, rfl⟩
  exact ⟨cocharacterLattice.galoisRepresentation k E a.scTorus σ ν,
    (a.corootMap_galois E σ ν).symm⟩

/-- The Galois action on the quotient is descended from the actual cocharacter action. -/
def galoisRepresentation : Representation ℤ (E ≃ₐ[k] E) (a.atChoice E) where
  toFun σ := (a.corootImage E).mapQ (a.corootImage E)
    (cocharacterLattice.galoisRepresentation k E a.torus σ) (a.corootImage_stable E σ)
  map_one' := by
    apply LinearMap.ext
    intro x
    obtain ⟨ν, rfl⟩ := (a.corootImage E).mkQ_surjective x
    change a.projection E (cocharacterLattice.galoisRepresentation k E a.torus 1 ν) = _
    rw [map_one]
    rfl
  map_mul' σ τ := by
    apply LinearMap.ext
    intro x
    obtain ⟨ν, rfl⟩ := (a.corootImage E).mkQ_surjective x
    change a.projection E (cocharacterLattice.galoisRepresentation k E a.torus (σ * τ) ν) =
      a.projection E (cocharacterLattice.galoisRepresentation k E a.torus σ
        (cocharacterLattice.galoisRepresentation k E a.torus τ ν))
    rw [map_mul]
    rfl

@[simp] theorem galoisRepresentation_projection (σ : E ≃ₐ[k] E) (ν : a.lattice E) :
    a.galoisRepresentation E σ (a.projection E ν) =
      a.projection E (cocharacterLattice.galoisRepresentation k E a.torus σ ν) := rfl

variable (b : Choice k G)

/-- The torus isomorphism is the restriction of conjugation by the actual point `g`. -/
def IsConjugationComparison
    (g : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k E)).obj G))
    (e : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ≅
      (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus) : Prop :=
  (GroupScheme.baseChange (algebraBaseMap k E)).map a.inclusion ≫
      (((GroupScheme.baseChange (algebraBaseMap k E)).obj G).innerIso g).hom =
    CommGroupScheme.groupHom e.hom ≫
      (GroupScheme.baseChange (algebraBaseMap k E)).map b.inclusion

/-- A comparison is induced on quotient representatives by an actual geometric
conjugation of the maximal tori. This condition includes existence of a conjugator. -/
def IsCanonicalComparison (f : a.atChoice E →ₗ[ℤ] b.atChoice E) : Prop :=
  ∃ (g : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k E)).obj G))
    (e : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ≅
      (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus),
    a.IsConjugationComparison E b g e ∧
      ∀ ν : a.lattice E, f (a.projection E ν) = b.projection E (ν ≫ e.hom)

/-- The candidate canonical comparison, chosen by its geometric conjugation law.
The accompanying unconditional statement supplies existence and uniqueness. -/
def comparison : a.atChoice E →ₗ[ℤ] b.atChoice E :=
  Classical.epsilon (a.IsCanonicalComparison E b)

/-- The epsilon law only requires existence; it does not prove that existence. -/
theorem comparison_spec (h : ∃ f, a.IsCanonicalComparison E b f) :
    a.IsCanonicalComparison E b (a.comparison E b) := Classical.epsilon_spec h

end Choice

variable (E : Type u) [Field E] [Algebra k E]

/-- The chosen presentation of the algebraic fundamental group. Choice independence
is the canonical-comparison assertion of KP Construction 11.3.1. -/
abbrev fundamentalGroup (hG : IsConnectedReductive G) :=
  (chosenChoice k G hG).atChoice E

/-- The actual descended Galois representation on the chosen presentation. -/
abbrev fundamentalGroupGalois (hG : IsConnectedReductive G) :
    Representation ℤ (E ≃ₐ[k] E) (fundamentalGroup k G E hG) :=
  (chosenChoice k G hG).galoisRepresentation E

end Langlands.GroupScheme.AlgebraicFundamentalGroup
