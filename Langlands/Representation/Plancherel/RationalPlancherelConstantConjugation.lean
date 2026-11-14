import Langlands.Representation.Plancherel.RationalPlancherelDensity
import Langlands.Representation.Plancherel.RationalSourceGammaConjugation
import Langlands.GroupScheme.Lie.Functoriality

/-! # Conjugation invariance of the Plancherel constants

Waldspurger 2003, I.1 (printed p.241) defines `c(G|M) = γ(G|M)⁻¹ ∏_{α ∈ Σ_red(P)} γ(M_α|M)`,
and V.2 (printed p.292) the density `μ(ω) = j(ω)⁻¹ ∏_α γ(M_α|M)²`. Lemma V.2.1, third item,
states `μ(sω) = μ(ω)` for `s ∈ W^G`. Besides IV.3 (3) for `j`, this uses that the constants
`γ(M_α|M)` of the Levi `M` and of its conjugate `s·M` agree.

For the Library's constants (module `RationalPlancherelConstant`: the torus `i : T → G`, the
cocharacter `ζ` of `T`, `P = P_G(ζ ≫ i)`, `M = Z_G(ζ ≫ i)` and the compact open `K`), this
module proves that conjugating the torus by a rational point `g`,
`i ↦ innerConjugate i g = i ≫ Int(g)`, and moving
`K` to a compact open `K'` with `gKg⁻¹ = K'` leaves `∏_α γ(M_α|M)`
(`rankOneGammaProduct_eq_of_conjugation`), `c(G|M)` (`plancherelConstant_eq_of_conjugation`)
and the density constant `∏_α γ(M_α|M)²`
(`RationalPlancherelDensity.plancherelDensityConstant_eq_of_conjugation`) unchanged, with the
specializations `K' = gKg⁻¹` and `K' = K` for `g ∈ K`.

The ingredients are: the roots of a torus do not change under an isomorphism of the ambient
group scheme (`roots_comp_iso`), so neither does the index set of the product
(`rankOneCocharacterSet_comp_iso`); conjugation carries the rank-one Levis `M_α` for `i` onto
those for `i ≫ Int(g)` (`mem_cocharacterSubmoduleCentralizer_conj`); and the source constant
`γ^L` is covariant under conjugation (`leviGamma_eq_of_conjugation`, from the Library's
`compactNormalizedSourceGamma_eq_of_transport`).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

/-! ### Roots along group-scheme isomorphisms -/

namespace Langlands.GroupScheme

section InnerConjugate

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- **The conjugate of a homomorphism by a point.** For a homomorphism `f : H → G` of group
schemes over `S` and a point `g ∈ G(S)`, the homomorphism `Int(g) ∘ f`, `h ↦ g f(h) g⁻¹`, that
is, `f` followed by the inner automorphism `G.innerIso g`. For a torus `i : T → G` and a
rational point `g`, `innerConjugate i g` is the conjugate torus `gTg⁻¹`. -/
abbrev innerConjugate (f : H ⟶ G) (g : Over.mk (𝟙 S) ⟶ G.X) : H ⟶ G :=
  f ≫ (G.innerIso g).hom

end InnerConjugate

section RootsIso

variable {R : CommRingCat.{u}} {T : CommGroupScheme (Spec R)} {G G' : GroupScheme (Spec R)}
  [IsAffineHom G.X.hom] [IsAffineHom G'.X.hom]

/-- The roots of a torus are unchanged by composing its embedding with an isomorphism of
group schemes. -/
theorem roots_comp_iso (i : T.toGrp ⟶ G) (e : G ≅ G') : roots (i ≫ e.hom) = roots i := by
  have : IsIso e.hom.hom.hom := (Grp.forget _).map_isIso e.hom
  have : IsIso e.inv.hom.hom := (Grp.forget _).map_isIso e.inv
  apply le_antisymm
  · have h := roots_subset_comp e.inv (i ≫ e.hom)
    rwa [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
  · exact roots_subset_comp e.hom i

end RootsIso

section RelativeRootsIso

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G G' : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [IsAffineHom G'.X.hom]

/-- Relative roots are unchanged by composing with an isomorphism. -/
theorem relativeRoots_comp_iso (i : T.toGrp ⟶ G) (e : G ≅ G') :
    relativeRoots (i ≫ e.hom) = relativeRoots i := by
  rw [relativeRoots_eq_roots, relativeRoots_eq_roots, roots_comp_iso]

/-- Positive relative roots are unchanged by composing with an isomorphism. -/
theorem positiveRelativeRoots_comp_iso (i : T.toGrp ⟶ G) (e : G ≅ G')
    (ν : cocharacterLattice T) :
    positiveRelativeRoots (i ≫ e.hom) ν = positiveRelativeRoots i ν := by
  unfold positiveRelativeRoots
  rw [relativeRoots_comp_iso]

end RelativeRootsIso

end Langlands.GroupScheme

namespace Langlands.Plancherel.RationalDynamicSource

open Aubert.General Haar HarishChandraSchwartz QuotientIntegration
open BruhatTits.DynamicUnipotentContainment

/-! ### The rank-one index set -/

section Algebraic

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G G' : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [IsAffineHom G'.X.hom]
  (i : T.toGrp ⟶ G) (e : G ≅ G') (ζ : cocharacterLattice T)

/-- The roots of the Levi are unchanged by composing with an isomorphism. -/
theorem leviRelativeRoots_comp_iso :
    leviRelativeRoots (i ≫ e.hom) ζ = leviRelativeRoots i ζ := by
  unfold leviRelativeRoots
  rw [relativeRoots_comp_iso]

/-- The submodules `X_*(A_α)` are unchanged by composing with an isomorphism. -/
theorem rankOneCocharacters_comp_iso (β : characterLattice T) :
    rankOneCocharacters (i ≫ e.hom) ζ β = rankOneCocharacters i ζ β := by
  unfold rankOneCocharacters
  rw [leviRelativeRoots_comp_iso]

/-- The index set of `∏_α γ(M_α|M)` is unchanged by composing with an isomorphism. -/
theorem rankOneCocharacterSet_comp_iso :
    rankOneCocharacterSet (i ≫ e.hom) ζ = rankOneCocharacterSet i ζ := by
  unfold rankOneCocharacterSet
  rw [positiveRelativeRoots_comp_iso]
  exact Set.image_congr fun β _ => rankOneCocharacters_comp_iso i e ζ β

end Algebraic

/-! ### Conjugating the rank-one Levis and their constants -/

section Local

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance constantConjugationPointTopology : TopologicalSpace (RationalPoint F G.X) :=
  rationalPointTopology F G.X
local instance constantConjugationPointMeasurable : MeasurableSpace (RationalPoint F G.X) :=
  borel (RationalPoint F G.X)
local instance constantConjugationPointBorel : BorelSpace (RationalPoint F G.X) := ⟨rfl⟩
local instance constantConjugationFieldT2 : T2Space F := BruhatTits.localField_t2Space F
local instance constantConjugationPointTopologicalGroup :
    IsTopologicalGroup (RationalPoint F G.X) := rationalPoint_isTopologicalGroup F G
local instance constantConjugationPointLocallyCompact :
    LocallyCompactSpace (RationalPoint F G.X) := rationalPoint_locallyCompactSpace F G
local instance constantConjugationFieldSecondCountable : SecondCountableTopology F :=
  localField_secondCountableTopology F
local instance constantConjugationPointSecondCountable :
    SecondCountableTopology (RationalPoint F G.X) :=
    AlgebraicGeometry.PointTopology.rationalPoint_secondCountableTopology F G

local notation "X₀" => Over.mk (𝟙 (Spec (CommRingCat.of F)))

section Levi

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (g : RationalPoint F G.X)
  (K K' : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hK' : IsCompact (K' : Set (RationalPoint F G.X)))
  (L L' : Subgroup (RationalPoint F G.X))
  (hL : IsClosed (L : Set (RationalPoint F G.X)))
  (hL' : IsClosed (L' : Set (RationalPoint F G.X)))

/-- **Conjugation covariance of `γ^L`.** If conjugation by `g` carries `K` onto `K'` and `L`
onto `L'`, then the source constant of `L'` for `gχg⁻¹` with `K'` equals that of `L` for `χ`
with `K`. -/
theorem leviGamma_eq_of_conjugation
    (hcompact : ∀ x : RationalPoint F G.X, g * x * g⁻¹ ∈ K' ↔ x ∈ K)
    (hLL : ∀ x : RationalPoint F G.X, g * x * g⁻¹ ∈ L' ↔ x ∈ L) :
    leviGamma (χ ≫ (G.innerIso g).hom) K' hK' L' hL' = leviGamma χ K hK L hL := by
  let e := rationalPointsConjHomeomorph G g
  have hpar : ∀ x : RationalPoint F G.X,
      e x ∈ ((Dynamic.parabolic (χ ≫ (G.innerIso g).hom)).carrier X₀ ⊓ L') ↔
        x ∈ ((Dynamic.parabolic χ).carrier X₀ ⊓ L) := by
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    refine and_congr ?_ ?_
    · simpa only [e, rationalPointsConjHomeomorph_apply, constantPoint_rationalPoint] using
        (Dynamic.mem_parabolic_conj χ g (x := x)).symm
    · simpa only [e, rationalPointsConjHomeomorph_apply] using hLL x
  have hopp : ∀ x : RationalPoint F G.X,
      e x ∈ (unipotentPoints (oppositeCocharacter (χ ≫ (G.innerIso g).hom)) ⊓ L') ↔
        x ∈ (unipotentPoints (oppositeCocharacter χ) ⊓ L) := by
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    refine and_congr ?_ ?_
    · rw [oppositeCocharacter_conjugate]
      simpa only [e, rationalPointsConjHomeomorph_apply, constantPoint_rationalPoint] using
        (Dynamic.mem_unipotent_conj (oppositeCocharacter χ) g (x := x)).symm
    · simpa only [e, rationalPointsConjHomeomorph_apply] using hLL x
  exact compactNormalizedSourceGamma_eq_of_transport e K K' hK hK'
    (isClosed_parabolic_inf χ L hL) (isClosed_oppositeRadical_inf χ L hL)
    (isClosed_parabolic_inf (χ ≫ (G.innerIso g).hom) L' hL')
    (isClosed_oppositeRadical_inf (χ ≫ (G.innerIso g).hom) L' hL')
    hpar hopp hcompact

end Levi

section RankOne

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G)
  (ζ : cocharacterLattice T) (g : RationalPoint F G.X)
  (K K' : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hK' : IsCompact (K' : Set (RationalPoint F G.X)))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] in
/-- Conjugation by `g` carries the rational points of the centralizer `M_N` of the
cocharacters in `N` for `i` onto those for `i ≫ Int(g)`. -/
theorem mem_cocharacterSubmoduleCentralizer_conj (N : Submodule ℤ (cocharacterLattice T))
    (x : RationalPoint F G.X) :
    g * x * g⁻¹ ∈ (cocharacterSubmoduleCentralizer (innerConjugate i g) N).carrier X₀ ↔
      x ∈ (cocharacterSubmoduleCentralizer i N).carrier X₀ := by
  rw [mem_cocharacterSubmoduleCentralizer, mem_cocharacterSubmoduleCentralizer]
  refine forall₂_congr fun ν _ => ?_
  have h := (Dynamic.mem_centralizer_conj (CommGroupScheme.groupHom ν ≫ i) g (x := x)).symm
  rw [constantPoint_rationalPoint, Category.assoc] at h
  exact h

/-- **Conjugation covariance of `γ(M_α|M)`.** -/
theorem rankOneGamma_eq_of_conjugation [IsAffineHom G.X.hom]
    (hcompact : ∀ x : RationalPoint F G.X, g * x * g⁻¹ ∈ K' ↔ x ∈ K)
    (N : Submodule ℤ (cocharacterLattice T)) :
    rankOneGamma (innerConjugate i g) ζ K' hK' N = rankOneGamma i ζ K hK N := by
  unfold rankOneGamma innerConjugate
  have hχ : CommGroupScheme.groupHom ζ ≫ i ≫ (G.innerIso g).hom =
      (CommGroupScheme.groupHom ζ ≫ i) ≫ (G.innerIso g).hom := (Category.assoc _ _ _).symm
  rw [hχ]
  exact leviGamma_eq_of_conjugation (CommGroupScheme.groupHom ζ ≫ i) g K K' hK hK' _ _ _ _
    hcompact (mem_cocharacterSubmoduleCentralizer_conj i g N)

/-- **Conjugation covariance of `∏_α γ(M_α|M)`.** If conjugation by `g` carries `K` onto
`K'`, the rank-one product for the torus `i ≫ Int(g)` with `K'` equals that for `i` with
`K`. -/
theorem rankOneGammaProduct_eq_of_conjugation [IsAffineHom G.X.hom]
    (hcompact : ∀ x : RationalPoint F G.X, g * x * g⁻¹ ∈ K' ↔ x ∈ K) :
    rankOneGammaProduct (innerConjugate i g) ζ K' hK' = rankOneGammaProduct i ζ K hK := by
  unfold rankOneGammaProduct innerConjugate
  rw [rankOneCocharacterSet_comp_iso]
  exact finprod_mem_congr rfl fun N _ =>
    rankOneGamma_eq_of_conjugation i ζ g K K' hK hK' hcompact N

/-- The rank-one product with the conjugate compact `gKg⁻¹`. -/
theorem rankOneGammaProduct_conjugateCompact [IsAffineHom G.X.hom] :
    rankOneGammaProduct (innerConjugate i g) ζ (conjugateCompact g K)
        (conjugateCompact_isCompact g K hK) = rankOneGammaProduct i ζ K hK :=
  rankOneGammaProduct_eq_of_conjugation i ζ g K (conjugateCompact g K) hK
    (conjugateCompact_isCompact g K hK) (fun x => mem_conjugateCompact g x K)

/-- The rank-one product with the same `K` when `g ∈ K`. -/
theorem rankOneGammaProduct_conjugate_of_mem_compact [IsAffineHom G.X.hom] (hg : g ∈ K) :
    rankOneGammaProduct (innerConjugate i g) ζ K hK = rankOneGammaProduct i ζ K hK := by
  apply rankOneGammaProduct_eq_of_conjugation i ζ g K K hK hK
  intro x
  simpa only [conjugateCompact_eq_self g K hg] using mem_conjugateCompact g x K

/-- **Conjugation covariance of `c(G|M)`.** -/
theorem plancherelConstant_eq_of_conjugation [IsAffineHom G.X.hom]
    (hcompact : ∀ x : RationalPoint F G.X, g * x * g⁻¹ ∈ K' ↔ x ∈ K) :
    plancherelConstant (innerConjugate i g) ζ K' hK' = plancherelConstant i ζ K hK := by
  unfold plancherelConstant
  rw [rankOneGammaProduct_eq_of_conjugation i ζ g K K' hK hK' hcompact]
  unfold innerConjugate
  have hχ : CommGroupScheme.groupHom ζ ≫ i ≫ (G.innerIso g).hom =
      (CommGroupScheme.groupHom ζ ≫ i) ≫ (G.innerIso g).hom := (Category.assoc _ _ _).symm
  rw [hχ, gamma_eq_of_compactPreserving_conjugation (CommGroupScheme.groupHom ζ ≫ i) g K K' hK
    hK' hcompact]

/-- `c(G|M)` with the conjugate compact `gKg⁻¹`. -/
theorem plancherelConstant_conjugateCompact [IsAffineHom G.X.hom] :
    plancherelConstant (innerConjugate i g) ζ (conjugateCompact g K)
        (conjugateCompact_isCompact g K hK) = plancherelConstant i ζ K hK :=
  plancherelConstant_eq_of_conjugation i ζ g K (conjugateCompact g K) hK
    (conjugateCompact_isCompact g K hK) (fun x => mem_conjugateCompact g x K)

/-- `c(G|M)` with the same `K` when `g ∈ K`. -/
theorem plancherelConstant_conjugate_of_mem_compact [IsAffineHom G.X.hom] (hg : g ∈ K) :
    plancherelConstant (innerConjugate i g) ζ K hK = plancherelConstant i ζ K hK := by
  apply plancherelConstant_eq_of_conjugation i ζ g K K hK hK
  intro x
  simpa only [conjugateCompact_eq_self g K hg] using mem_conjugateCompact g x K

end RankOne

end Local

end Langlands.Plancherel.RationalDynamicSource

/-! ### The density constant -/

namespace Langlands.Plancherel.RationalPlancherelDensity

open RationalDynamicSource

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G)
  (ζ : cocharacterLattice T) (g : RationalPoint F G.X)
  (K K' : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hK' : IsCompact (K' : Set (RationalPoint F G.X)))

/-- **Conjugation covariance of the density constant `∏_α γ(M_α|M)²`.** -/
theorem plancherelDensityConstant_eq_of_conjugation
    (hcompact : ∀ x : RationalPoint F G.X, g * x * g⁻¹ ∈ K' ↔ x ∈ K) :
    plancherelDensityConstant (innerConjugate i g) ζ K' hK' =
      plancherelDensityConstant i ζ K hK := by
  unfold plancherelDensityConstant
  rw [rankOneGammaProduct_eq_of_conjugation i ζ g K K' hK hK' hcompact]

/-- The density constant with the conjugate compact `gKg⁻¹`. -/
theorem plancherelDensityConstant_conjugateCompact :
    plancherelDensityConstant (innerConjugate i g) ζ (conjugateCompact g K)
        (conjugateCompact_isCompact g K hK) = plancherelDensityConstant i ζ K hK :=
  plancherelDensityConstant_eq_of_conjugation i ζ g K (conjugateCompact g K) hK
    (conjugateCompact_isCompact g K hK) (fun x => mem_conjugateCompact g x K)

/-- The density constant with the same `K` when `g ∈ K`. -/
theorem plancherelDensityConstant_conjugate_of_mem_compact (hg : g ∈ K) :
    plancherelDensityConstant (innerConjugate i g) ζ K hK =
      plancherelDensityConstant i ζ K hK := by
  apply plancherelDensityConstant_eq_of_conjugation i ζ g K K hK hK
  intro x
  simpa only [conjugateCompact_eq_self g K hg] using mem_conjugateCompact g x K

end Langlands.Plancherel.RationalPlancherelDensity
