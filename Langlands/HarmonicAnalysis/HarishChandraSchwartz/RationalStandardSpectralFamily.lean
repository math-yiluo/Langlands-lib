import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalThetaFixedFiniteness
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalFourierOrbitSmoothness
import Langlands.Representation.Plancherel.ProductInducedOrbitBaseChange

/-! # The spectral family `ψ_f` over the standard part of `Θ` on actual points

For a connected reductive group `G` over a nonarchimedean local field, this module indexes
Waldspurger's `Θ` (VI.3) over the standard parabolic subgroups: the pairs `(I, O)` of a set `I`
of simple roots and an orbit `O` of `Im X(M_I)` in `E₂(M_I)` (`RationalStandardTheta`). Each orbit
gets a fixed representative (`rationalOrbitRepresentative`). It defines:

* `RationalStandardThetaSections`: the product of the section spaces of the `(O, P_I)`;
* `rationalStandardThetaSmoothSections`: its subspace of finitely supported families of smooth
  sections, the standard part of `C^∞(Θ) = ⊕_{(O, P)} C^∞(O, P)`;
* `rationalFourierThetaFamily f`: the family `(ψ_f[O, P_I])_{(I, O)}` in the product.

Given the published statement of Theorem VIII.1.2, the family has finite support
(`finite_support_rationalFourierThetaFamily`, Remarque VIII.1.3 (ii)). Given that statement and
the hypotheses of `rationalFourierOrbitSmoothSectionLinear` for every `I`, `f ↦ ψ_f` is a linear
map into the finitely supported smooth families (`rationalFourierThetaLinear`).

The choice of representatives does not matter: for any representative `π'` of `O`, the Library's
base change identifies the section spaces and `C^∞(O, P_I)` built from the chosen representative
with those built from `π'` (`rationalOrbitSectionsBaseEquiv`,
`rationalOrbitSmoothSectionsBaseEquiv`), and sends the component `ψ_f[O, P_I]` of the family to
`ψ_f[O, P_I]` built from `π'` (`rationalOrbitSectionsBaseEquiv_rationalFourierThetaFamily`).
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ComplexConjugate
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

local instance instRationalStandardSpectralFamily1
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (RationalPointFamily.rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (RationalPointFamily.rootSet i ν I)
local instance instRationalStandardSpectralFamily2
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    IsAffine (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (RationalPointFamily.rootSet i ν I)).hom.hom.left
local instance instRationalStandardSpectralFamily3
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    TopologicalSpace
      (rationalPoints (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I))) :=
  rationalPointTopology F (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)).X

-- `M_I(F)` as a subtype of `G(F) = rationalPoints G`, with the membership of `Subgroup G(F)`.
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}

-- The Levi group scheme `L` with `L(F) ≃ M_I(F)`.
set_option hygiene false in
local notation "𝐋" => Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)

-- The root set `J` of `I`.
set_option hygiene false in
local notation "𝐉" => RationalPointFamily.rootSet i ν I

section Index

variable {T : Finset (RationalPointFamily.SimpleRoot i ν) → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ I, (T I).toGrp ⟶ 𝐋) (ha : ∀ I, IsSplitComponent (a I))
  [∀ I, (rationalLeviSplitCenter I (a I)).Normal]
  [∀ I, MeasurableSpace (𝐌 ⧸ rationalLeviSplitCenter I (a I))]
  (mu : ∀ I, Measure (𝐌 ⧸ rationalLeviSplitCenter I (a I))) [∀ I, (mu I).IsHaarMeasure]

/-- The orbits of the unitary unramified characters `Im X(M_I)` in `E₂(M_I)`, the discrete
series of `M_I(F)` modulo `A_{M_I}(F)` (the image of the split component `a I`, with the Haar
measure `mu I`). -/
abbrev RationalLeviOrbitClass (I : Finset (RationalPointFamily.SimpleRoot i ν)) : Type _ :=
  DiscreteSeriesOrbitClass.{u, u, uV} (rationalLeviSplitCenter I (a I))
    (rationalLeviSplitCenter_le_center I (a I) (ha I)) (mu I)
    (RationalPointFamily.leviRationalNormCharacters i ν I)

/-- **The standard part of Waldspurger's `Θ`** (VI.3, printed p. 305): the pairs `(I, O)` of a
finite set `I` of simple roots (the standard parabolic `P_I(F)`) and an orbit `O` of
`Im X(M_I)` in `E₂(M_I)`. -/
abbrev RationalStandardTheta : Type _ :=
  Σ I : Finset (RationalPointFamily.SimpleRoot i ν), RationalLeviOrbitClass a ha mu I

/-- **The chosen representative of an orbit**: an irreducible admissible representation of
`M_I(F)` whose discrete-series class lies in the orbit `O` (a choice of `Quotient.out`, first of
the orbit, then of the isomorphism class). -/
def rationalOrbitRepresentative (I : Finset (RationalPointFamily.SimpleRoot i ν))
    (O : DiscreteSeriesOrbitClass.{u, u, uV} (rationalLeviSplitCenter I (a I))
      (rationalLeviSplitCenter_le_center I (a I) (ha I)) (mu I)
      (RationalPointFamily.leviRationalNormCharacters i ν I)) :
    IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌) :=
  O.out.val.out

/-- The chosen representative is square integrable modulo `A_{M_I}(F)`. -/
theorem rationalOrbitRepresentative_isSquareIntegrable
    (I : Finset (RationalPointFamily.SimpleRoot i ν))
    (O : DiscreteSeriesOrbitClass.{u, u, uV} (rationalLeviSplitCenter I (a I))
      (rationalLeviSplitCenter_le_center I (a I) (ha I)) (mu I)
      (RationalPointFamily.leviRationalNormCharacters i ν I)) :
    IsSquareIntegrableModCentralSubgroup (rationalLeviSplitCenter I (a I))
      (rationalLeviSplitCenter_le_center I (a I) (ha I))
      (rationalOrbitRepresentative a ha mu I O).obj.representation (mu I) := by
  have h := O.out.property
  rw [← Quotient.out_eq O.out.val] at h
  exact h

/-- The orbit of the chosen representative is `O`. -/
theorem mk_discreteSeriesClass_rationalOrbitRepresentative
    (I : Finset (RationalPointFamily.SimpleRoot i ν))
    (O : DiscreteSeriesOrbitClass.{u, u, uV} (rationalLeviSplitCenter I (a I))
      (rationalLeviSplitCenter_le_center I (a I) (ha I)) (mu I)
      (RationalPointFamily.leviRationalNormCharacters i ν I)) :
    (Quotient.mk _ (discreteSeriesClass (rationalLeviSplitCenter I (a I))
        (rationalLeviSplitCenter_le_center I (a I) (ha I)) (mu I)
        (rationalOrbitRepresentative a ha mu I O)
        (rationalOrbitRepresentative_isSquareIntegrable a ha mu I O)) :
      DiscreteSeriesOrbitClass.{u, u, uV} (rationalLeviSplitCenter I (a I))
        (rationalLeviSplitCenter_le_center I (a I) (ha I)) (mu I)
        (RationalPointFamily.leviRationalNormCharacters i ν I)) = O := by
  have h : discreteSeriesClass (rationalLeviSplitCenter I (a I))
      (rationalLeviSplitCenter_le_center I (a I) (ha I)) (mu I)
      (rationalOrbitRepresentative a ha mu I O)
      (rationalOrbitRepresentative_isSquareIntegrable a ha mu I O) = O.out :=
    Subtype.ext (Quotient.out_eq _)
  rw [h]
  exact Quotient.out_eq O

/-- **Any representative of `O` lies in the twist orbit of the chosen one**: an irreducible
admissible `π'`, square integrable modulo `A_{M_I}(F)`, whose discrete-series class has orbit `O`,
as a member of `UnitaryOrbitRepresentative` of the chosen representative. -/
def rationalOrbitRepresentativeMember (I : Finset (RationalPointFamily.SimpleRoot i ν))
    (O : RationalLeviOrbitClass a ha mu I)
    (π' : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
    (hsq' : IsSquareIntegrableModCentralSubgroup (rationalLeviSplitCenter I (a I))
      (rationalLeviSplitCenter_le_center I (a I) (ha I)) π'.obj.representation (mu I))
    (hO : (Quotient.mk _ (discreteSeriesClass (rationalLeviSplitCenter I (a I))
        (rationalLeviSplitCenter_le_center I (a I) (ha I)) (mu I) π' hsq') :
      RationalLeviOrbitClass a ha mu I) = O) :
    UnitaryOrbitRepresentative (RationalPointFamily.leviRationalNormCharacters i ν I)
      (rationalOrbitRepresentative a ha mu I O) :=
  ⟨π', by
    obtain ⟨χ, hχ⟩ := Quotient.exact
      (hO.trans (mk_discreteSeriesClass_rationalOrbitRepresentative a ha mu I O).symm)
    exact ⟨χ, congrArg Subtype.val hχ⟩⟩

theorem rationalOrbitRepresentativeMember_val (I : Finset (RationalPointFamily.SimpleRoot i ν))
    (O : RationalLeviOrbitClass a ha mu I)
    (π' : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
    (hsq' : IsSquareIntegrableModCentralSubgroup (rationalLeviSplitCenter I (a I))
      (rationalLeviSplitCenter_le_center I (a I) (ha I)) π'.obj.representation (mu I))
    (hO : (Quotient.mk _ (discreteSeriesClass (rationalLeviSplitCenter I (a I))
        (rationalLeviSplitCenter_le_center I (a I) (ha I)) (mu I) π' hsq') :
      RationalLeviOrbitClass a ha mu I) = O) :
    (rationalOrbitRepresentativeMember a ha mu I O π' hsq' hO).val = π' :=
  rfl

/-- `π` represents its own orbit: the twist by the trivial character. -/
def selfUnitaryOrbitRepresentative (I : Finset (RationalPointFamily.SimpleRoot i ν))
    (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌)) :
    UnitaryOrbitRepresentative (RationalPointFamily.leviRationalNormCharacters i ν I) π :=
  ⟨π, 1, SmoothDualClass.twist_one _ _⟩

end Index

section Family

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))

variable {T : Finset (RationalPointFamily.SimpleRoot i ν) → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ I, (T I).toGrp ⟶ 𝐋) (ha : ∀ I, IsSplitComponent (a I))
  [∀ I, (rationalLeviSplitCenter I (a I)).Normal]
  [∀ I, MeasurableSpace (𝐌 ⧸ rationalLeviSplitCenter I (a I))]
  (mu : ∀ I, Measure (𝐌 ⧸ rationalLeviSplitCenter I (a I))) [∀ I, (mu I).IsHaarMeasure]

/-- **The product of the section spaces** over the standard part of `Θ`, curried over
`(I, O)`: a family `ψ = (ψ[O, P_I])_{(I, O)}` with `ψ[O, P_I]` a section over the orbit of the
chosen representative (at every representative `ω`, an element of `L(ω, P_I)`). -/
abbrev RationalStandardThetaSections : Type _ :=
  ∀ (I : Finset (RationalPointFamily.SimpleRoot i ν)) (O : RationalLeviOrbitClass a ha mu I),
    ProductInducedOrbitSections (RationalPointFamily.leviRationalNormCharacters i ν I)
      (rationalOrbitRepresentative a ha mu I O) (G := rationalPoints G)
      (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
      (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))

/-- Componentwise smoothness is stable under addition. -/
theorem add_mem_rationalInducedSmoothOrbitSections_of_forall
    {ψ φ : RationalStandardThetaSections hG hi hν a ha mu}
    (hψ : ∀ (I : Finset (RationalPointFamily.SimpleRoot i ν)) (O : RationalLeviOrbitClass a ha mu I),
      ψ I O ∈ rationalInducedSmoothOrbitSections hG hi hν I hKc hPK
        (rationalOrbitRepresentative a ha mu I O))
    (hφ : ∀ (I : Finset (RationalPointFamily.SimpleRoot i ν)) (O : RationalLeviOrbitClass a ha mu I),
      φ I O ∈ rationalInducedSmoothOrbitSections hG hi hν I hKc hPK
        (rationalOrbitRepresentative a ha mu I O))
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) (O : RationalLeviOrbitClass a ha mu I) :
    (ψ + φ) I O ∈ rationalInducedSmoothOrbitSections hG hi hν I hKc hPK
      (rationalOrbitRepresentative a ha mu I O) :=
  Submodule.add_mem _ (hψ I O) (hφ I O)

/-- Finite support is stable under addition. -/
theorem finite_support_add_of_finite {ψ φ : RationalStandardThetaSections hG hi hν a ha mu}
    (hψ : {p : RationalStandardTheta a ha mu | ψ p.1 p.2 ≠ 0}.Finite)
    (hφ : {p : RationalStandardTheta a ha mu | φ p.1 p.2 ≠ 0}.Finite) :
    {p : RationalStandardTheta a ha mu | (ψ + φ) p.1 p.2 ≠ 0}.Finite := by
  refine (hψ.union hφ).subset fun p hp => ?_
  by_contra h
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
  exact hp (by rw [Pi.add_apply, Pi.add_apply, h.1, h.2, add_zero])

/-- Componentwise smoothness of the zero family. -/
theorem zero_mem_rationalInducedSmoothOrbitSections_apply
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) (O : RationalLeviOrbitClass a ha mu I) :
    (0 : RationalStandardThetaSections hG hi hν a ha mu) I O ∈
      rationalInducedSmoothOrbitSections hG hi hν I hKc hPK
        (rationalOrbitRepresentative a ha mu I O) :=
  zero_mem _

/-- The zero family has finite support. -/
theorem finite_support_zero :
    {p : RationalStandardTheta a ha mu |
      (0 : RationalStandardThetaSections hG hi hν a ha mu) p.1 p.2 ≠ 0}.Finite :=
  Set.finite_empty.subset fun p hp => hp (by rw [Pi.zero_apply, Pi.zero_apply])

/-- Componentwise smoothness is stable under scalar multiplication. -/
theorem smul_mem_rationalInducedSmoothOrbitSections_of_forall (c : ℂ)
    {ψ : RationalStandardThetaSections hG hi hν a ha mu}
    (hψ : ∀ (I : Finset (RationalPointFamily.SimpleRoot i ν)) (O : RationalLeviOrbitClass a ha mu I),
      ψ I O ∈ rationalInducedSmoothOrbitSections hG hi hν I hKc hPK
        (rationalOrbitRepresentative a ha mu I O))
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) (O : RationalLeviOrbitClass a ha mu I) :
    (c • ψ) I O ∈ rationalInducedSmoothOrbitSections hG hi hν I hKc hPK
      (rationalOrbitRepresentative a ha mu I O) :=
  Submodule.smul_mem _ c (hψ I O)

/-- Finite support is stable under scalar multiplication. -/
theorem finite_support_smul_of_finite (c : ℂ) {ψ : RationalStandardThetaSections hG hi hν a ha mu}
    (hψ : {p : RationalStandardTheta a ha mu | ψ p.1 p.2 ≠ 0}.Finite) :
    {p : RationalStandardTheta a ha mu | (c • ψ) p.1 p.2 ≠ 0}.Finite :=
  hψ.subset fun p hp h => hp (by rw [Pi.smul_apply, Pi.smul_apply, h, smul_zero])

/-- **The standard part of `C^∞(Θ)`** (VI.3, printed p. 305, `C^∞(Θ) = ⊕_{(O,P) ∈ Θ} C^∞(O, P)`):
the families in `RationalStandardThetaSections` whose components are smooth
(`rationalInducedSmoothOrbitSections`, `C^∞(O, P_I)`) and which have finite support. -/
def rationalStandardThetaSmoothSections :
    Submodule ℂ (RationalStandardThetaSections hG hi hν a ha mu) where
  carrier := {ψ | (∀ (I : Finset (RationalPointFamily.SimpleRoot i ν))
      (O : RationalLeviOrbitClass a ha mu I),
      ψ I O ∈ rationalInducedSmoothOrbitSections hG hi hν I hKc hPK
        (rationalOrbitRepresentative a ha mu I O)) ∧
    {p : RationalStandardTheta a ha mu | ψ p.1 p.2 ≠ 0}.Finite}
  add_mem' := fun hψ hφ =>
    ⟨add_mem_rationalInducedSmoothOrbitSections_of_forall hG hi hν hKc hPK a ha mu hψ.1 hφ.1,
      finite_support_add_of_finite hG hi hν a ha mu hψ.2 hφ.2⟩
  zero_mem' := ⟨zero_mem_rationalInducedSmoothOrbitSections_apply hG hi hν hKc hPK a ha mu,
    finite_support_zero hG hi hν a ha mu⟩
  smul_mem' := fun c _ hψ =>
    ⟨smul_mem_rationalInducedSmoothOrbitSections_of_forall hG hi hν hKc hPK a ha mu c hψ.1,
      finite_support_smul_of_finite hG hi hν a ha mu c hψ.2⟩

theorem mem_rationalStandardThetaSmoothSections
    {ψ : RationalStandardThetaSections hG hi hν a ha mu} :
    ψ ∈ rationalStandardThetaSmoothSections hG hi hν hKc hPK a ha mu ↔
      (∀ (I : Finset (RationalPointFamily.SimpleRoot i ν)) (O : RationalLeviOrbitClass a ha mu I),
        ψ I O ∈ rationalInducedSmoothOrbitSections hG hi hν I hKc hPK
          (rationalOrbitRepresentative a ha mu I O)) ∧
      {p : RationalStandardTheta a ha mu | ψ p.1 p.2 ≠ 0}.Finite :=
  Iff.rfl

/-- **Change of representative for the section spaces**: for a representative `π'` of `O`, the
Library's `productInducedOrbitBaseEquiv` turns sections over the orbit of the chosen
representative into sections over the orbit of `π'`; the two orbits have the same actual
members, and every value at every member is kept. -/
def rationalOrbitSectionsBaseEquiv (I : Finset (RationalPointFamily.SimpleRoot i ν))
    (O : RationalLeviOrbitClass a ha mu I)
    (π' : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
    (hsq' : IsSquareIntegrableModCentralSubgroup (rationalLeviSplitCenter I (a I))
      (rationalLeviSplitCenter_le_center I (a I) (ha I)) π'.obj.representation (mu I))
    (hO : (Quotient.mk _ (discreteSeriesClass (rationalLeviSplitCenter I (a I))
        (rationalLeviSplitCenter_le_center I (a I) (ha I)) (mu I) π' hsq') :
      RationalLeviOrbitClass a ha mu I) = O) :
    ProductInducedOrbitSections (RationalPointFamily.leviRationalNormCharacters i ν I)
        (rationalOrbitRepresentative a ha mu I O) (G := rationalPoints G)
        (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) ≃ₗ[ℂ]
      ProductInducedOrbitSections (RationalPointFamily.leviRationalNormCharacters i ν I) π'
        (G := rationalPoints G)
        (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) :=
  productInducedOrbitBaseEquiv (RationalPointFamily.leviRationalNormCharacters i ν I)
    (rationalOrbitRepresentative a ha mu I O)
    (rationalOrbitRepresentativeMember a ha mu I O π' hsq' hO)
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))

/-- **Independence of `C^∞(O, P_I)` of the representative** (VI.1): the Library's
`productInducedSmoothOrbitBaseEquiv` restricts `rationalOrbitSectionsBaseEquiv` to a linear
equivalence between the smooth sections built from the chosen representative and those built
from `π'`. -/
def rationalOrbitSmoothSectionsBaseEquiv (I : Finset (RationalPointFamily.SimpleRoot i ν))
    (O : RationalLeviOrbitClass a ha mu I)
    (π' : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
    (hsq' : IsSquareIntegrableModCentralSubgroup (rationalLeviSplitCenter I (a I))
      (rationalLeviSplitCenter_le_center I (a I) (ha I)) π'.obj.representation (mu I))
    (hO : (Quotient.mk _ (discreteSeriesClass (rationalLeviSplitCenter I (a I))
        (rationalLeviSplitCenter_le_center I (a I) (ha I)) (mu I) π' hsq') :
      RationalLeviOrbitClass a ha mu I) = O) :
    rationalInducedSmoothOrbitSections hG hi hν I hKc hPK
        (rationalOrbitRepresentative a ha mu I O) ≃ₗ[ℂ]
      rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π' :=
  haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  productInducedSmoothOrbitBaseEquiv (RationalPointFamily.leviRationalNormCharacters i ν I)
    (rationalOrbitRepresentative a ha mu I O)
    (rationalOrbitRepresentativeMember a ha mu I O π' hsq' hO)
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv K
    (isClosed_standardParabolicPoints_rootSet hG hi hν I) hKc
    (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))

/-- The smooth change of representative is the change of representative of the underlying
sections. -/
theorem rationalOrbitSmoothSectionsBaseEquiv_val (I : Finset (RationalPointFamily.SimpleRoot i ν))
    (O : RationalLeviOrbitClass a ha mu I)
    (π' : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
    (hsq' : IsSquareIntegrableModCentralSubgroup (rationalLeviSplitCenter I (a I))
      (rationalLeviSplitCenter_le_center I (a I) (ha I)) π'.obj.representation (mu I))
    (hO : (Quotient.mk _ (discreteSeriesClass (rationalLeviSplitCenter I (a I))
        (rationalLeviSplitCenter_le_center I (a I) (ha I)) (mu I) π' hsq') :
      RationalLeviOrbitClass a ha mu I) = O)
    (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK
      (rationalOrbitRepresentative a ha mu I O)) :
    (rationalOrbitSmoothSectionsBaseEquiv hG hi hν hKc hPK a ha mu I O π' hsq' hO q).val =
      rationalOrbitSectionsBaseEquiv hG hi hν a ha mu I O π' hsq' hO q.val :=
  rfl

variable [∀ I, BorelSpace (𝐌 ⧸ rationalLeviSplitCenter I (a I))] [∀ I, (mu I).IsInvInvariant]
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)) (hρ : IsClosedSubgroup ρ)
  (hKρ : (K : Subgroup (rationalPoints G)) ≤ rationalHeightSubgroup (F := F) ρ)
  (hM : ∀ I : Finset (RationalPointFamily.SimpleRoot i ν), IsIwasawaPair
    ((standardParabolicPoints i ν ∅).subgroupOf
      (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
    ((K : Subgroup (rationalPoints G)).subgroupOf
      (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))))
  {muG : Measure (rationalPoints G)} [muG.IsMulLeftInvariant] [muG.IsMulRightInvariant]
  (hsw : SquareIntegrableWeight muG (rationalXi hKc hPK) (rationalHeight (F := F) ρ))
  (hTA : ∀ (I : Finset (RationalPointFamily.SimpleRoot i ν))
    (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌)),
    IsSquareIntegrableModCentralSubgroup (rationalLeviSplitCenter I (a I))
      (rationalLeviSplitCenter_le_center I (a I) (ha I)) π.obj.representation (mu I) →
    ∀ A : UnitaryOrbitRepresentative (RationalPointFamily.leviRationalNormCharacters i ν I) π,
      IsRationalLeviTempered hKc ρ (hM I) A.val.obj)

/-- **The spectral family `ψ_f`** (VII.1, printed p. 316) over the standard part of `Θ`: for
`f ∈ C(G)`, the family `(ψ_f[O, P_I])_{(I, O)}` in the product of the section spaces, with
`ψ_f[O, P_I] = rationalFourierOrbitSection f` for the chosen representative of `O`. -/
def rationalFourierThetaFamily (f : RationalSchwartzSpace hKc hPK ρ) :
    RationalStandardThetaSections hG hi hν a ha mu := fun I O =>
  rationalFourierOrbitSection hG hi hν I hKc hPK ρ hρ hKρ (hM I)
    (rationalOrbitRepresentative a ha mu I O) (rationalLeviSplitCenter I (a I))
    (rationalLeviSplitCenter_le_center I (a I) (ha I)) (mu I)
    (rationalOrbitRepresentative_isSquareIntegrable a ha mu I O)
    (hTA I _ (rationalOrbitRepresentative_isSquareIntegrable a ha mu I O)) hsw f

/-- **Remarque VIII.1.3 (ii) for the family**: given the published statement of Theorem VIII.1.2,
`ψ_f[O, P_I] ≠ 0` for only finitely many `(I, O)`. -/
theorem finite_support_rationalFourierThetaFamily
    (hVIII : RationalDiscreteSeriesOrbitFinitenessStatement.{u, uV})
    (f : RationalSchwartzSpace hKc hPK ρ) :
    {p : RationalStandardTheta a ha mu |
      rationalFourierThetaFamily hG hi hν hKc hPK a ha mu ρ hρ hKρ hM hsw hTA f p.1 p.2 ≠ 0}.Finite :=
    by
  obtain ⟨T', hT', hmem⟩ := exists_finite_sigma_rationalFourierOrbitSection_ne_zero_of_statement
    hG hi hν hKc hPK a ha mu ρ hρ hKρ hM hsw hVIII f
  refine hT'.subset fun ⟨I, O⟩ hp => ?_
  have h := hmem I (rationalOrbitRepresentative a ha mu I O)
    (rationalOrbitRepresentative_isSquareIntegrable a ha mu I O)
    (hTA I _ (rationalOrbitRepresentative_isSquareIntegrable a ha mu I O)) hp
  rw [mk_discreteSeriesClass_rationalOrbitRepresentative] at h
  exact h

/-- **`ψ_f[O, P_I]` does not depend on the representative**: the change of representative to any
representative `π'` of `O` sends the component of the family to `ψ_f[O, P_I]` built from `π'`. -/
theorem rationalOrbitSectionsBaseEquiv_rationalFourierThetaFamily
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) (O : RationalLeviOrbitClass a ha mu I)
    (π' : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
    (hsq' : IsSquareIntegrableModCentralSubgroup (rationalLeviSplitCenter I (a I))
      (rationalLeviSplitCenter_le_center I (a I) (ha I)) π'.obj.representation (mu I))
    (hO : (Quotient.mk _ (discreteSeriesClass (rationalLeviSplitCenter I (a I))
        (rationalLeviSplitCenter_le_center I (a I) (ha I)) (mu I) π' hsq') :
      RationalLeviOrbitClass a ha mu I) = O)
    (f : RationalSchwartzSpace hKc hPK ρ) :
    rationalOrbitSectionsBaseEquiv hG hi hν a ha mu I O π' hsq' hO
        (rationalFourierThetaFamily hG hi hν hKc hPK a ha mu ρ hρ hKρ hM hsw hTA f I O) =
      rationalFourierOrbitSection hG hi hν I hKc hPK ρ hρ hKρ (hM I) π'
        (rationalLeviSplitCenter I (a I)) (rationalLeviSplitCenter_le_center I (a I) (ha I))
        (mu I) hsq' (hTA I π' hsq') hsw f := by
  funext B
  exact (rationalFourierOrbitSection_apply hG hi hν I hKc hPK ρ hρ hKρ (hM I)
      (rationalOrbitRepresentative a ha mu I O) (rationalLeviSplitCenter I (a I))
      (rationalLeviSplitCenter_le_center I (a I) (ha I)) (mu I)
      (rationalOrbitRepresentative_isSquareIntegrable a ha mu I O)
      (hTA I _ (rationalOrbitRepresentative_isSquareIntegrable a ha mu I O)) hsw f
      ((unitaryOrbitRepresentativeBaseEquiv _ _
        (rationalOrbitRepresentativeMember a ha mu I O π' hsq' hO)).symm B)).trans
    (rationalFourierOrbitSection_apply hG hi hν I hKc hPK ρ hρ hKρ (hM I) π'
      (rationalLeviSplitCenter I (a I)) (rationalLeviSplitCenter_le_center I (a I) (ha I))
      (mu I) hsq' (hTA I π' hsq') hsw f B).symm

/-- The component `ψ_f[O, P_I]` of the family vanishes iff `ψ_f[O, P_I]` built from any
representative `π'` of `O` vanishes: the support of the family does not depend on the chosen
representatives. -/
theorem rationalFourierThetaFamily_eq_zero_iff
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) (O : RationalLeviOrbitClass a ha mu I)
    (π' : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
    (hsq' : IsSquareIntegrableModCentralSubgroup (rationalLeviSplitCenter I (a I))
      (rationalLeviSplitCenter_le_center I (a I) (ha I)) π'.obj.representation (mu I))
    (hO : (Quotient.mk _ (discreteSeriesClass (rationalLeviSplitCenter I (a I))
        (rationalLeviSplitCenter_le_center I (a I) (ha I)) (mu I) π' hsq') :
      RationalLeviOrbitClass a ha mu I) = O)
    (f : RationalSchwartzSpace hKc hPK ρ) :
    rationalFourierThetaFamily hG hi hν hKc hPK a ha mu ρ hρ hKρ hM hsw hTA f I O = 0 ↔
      rationalFourierOrbitSection hG hi hν I hKc hPK ρ hρ hKρ (hM I) π'
        (rationalLeviSplitCenter I (a I)) (rationalLeviSplitCenter_le_center I (a I) (ha I))
        (mu I) hsq' (hTA I π' hsq') hsw f = 0 := by
  rw [← rationalOrbitSectionsBaseEquiv_rationalFourierThetaFamily hG hi hν hKc hPK a ha mu ρ hρ
    hKρ hM hsw hTA I O π' hsq' hO f]
  exact (LinearEquiv.map_eq_zero_iff _).symm

variable [muG.IsInvInvariant] [SigmaFinite muG]
  (hμK : muG (K : Set (rationalPoints G)) = 1)
  {μL : ∀ I : Finset (RationalPointFamily.SimpleRoot i ν), Measure 𝐌}
  [∀ I, (μL I).IsMulLeftInvariant] [∀ I, (μL I).IsMulRightInvariant]
  [∀ I : Finset (RationalPointFamily.SimpleRoot i ν), MeasurableInv 𝐌]
  [∀ I, (μL I).IsInvInvariant] [∀ I, SFinite (μL I)]
  (hswM : ∀ I, SquareIntegrableWeight (μL I) (rationalLeviXi hKc (hM I))
    (fun m => rationalHeight (F := F) ρ m))
  {νU : ∀ I : Finset (RationalPointFamily.SimpleRoot i ν),
    Measure (standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))}
  [∀ I, (νU I).IsHaarMeasure] [∀ I, (νU I).IsMulRightInvariant] [∀ I, SFinite (νU I)]
  (hE : ∀ I, ConstantTermEstimate (νU I)
    (standardUnipotentModulus i ν (RationalPointFamily.rootSet i ν I))
    (rationalXi hKc hPK) (rationalHeight (F := F) ρ) (rationalLeviXi hKc (hM I))
    (fun m => rationalHeight (F := F) ρ m))
  (hPKiw : ∀ (I : Finset (RationalPointFamily.SimpleRoot i ν))
    (m : standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
    (u : standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)),
    (m : rationalPoints G) * u ∈ K ↔ (m : rationalPoints G) ∈ K ∧ (u : rationalPoints G) ∈ K)
  (hMK : ∀ I, μL I {m : 𝐌 | (m : rationalPoints G) ∈ K} = 1)
  (hUK : ∀ I, νU I {u : standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I) |
    (u : rationalPoints G) ∈ K} = 1)
  {Cn : Finset (RationalPointFamily.SimpleRoot i ν) → ℝ}
  (hnσ : ∀ (I : Finset (RationalPointFamily.SimpleRoot i ν))
    (m : standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)),
    ‖rationalValuationCoordinates (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I))
      (isConnectedReductive_leviScheme_rootSet hG hi hν I)
      ((RationalPointFamily.leviRationalPointHomeomorph i ν I).symm m)‖ ≤
      Cn I * (1 + rationalHeight (F := F) ρ m))
  (hint : ∀ (I : Finset (RationalPointFamily.SimpleRoot i ν))
    (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌)),
    IsSquareIntegrableModCentralSubgroup (rationalLeviSplitCenter I (a I))
      (rationalLeviSplitCenter_le_center I (a I) (ha I)) π.obj.representation (mu I) →
    ∀ (f : RationalSchwartzSpace hKc hPK ρ)
    (A : UnitaryOrbitRepresentative (RationalPointFamily.leviRationalNormCharacters i ν I) π)
    (ψ : productInducedCoefficientObject (G := rationalPoints G)
      (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
      (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) A.val.obj),
    Integrable
      (fun x : rationalPoints G × K => conj (CompactInduction.integrand
        (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) A.val.obj K
        x.1 ψ x.2) * f x.1)
      (muG.prod (CompactInduction.measure K hKc)))

/-- **Proposition VII.1.3 for one index** `(I, O)`: the linear map `f ↦ ψ_f[O, P_I]` into
`C^∞(O, P_I)`, `rationalFourierOrbitSmoothSectionLinear` for the chosen representative of `O`
(its own temperedness `hTπ` is `hTA` at the trivial twist). -/
def rationalFourierThetaComponentLinear (I : Finset (RationalPointFamily.SimpleRoot i ν))
    (O : RationalLeviOrbitClass a ha mu I) :
    RationalSchwartzSpace hKc hPK ρ →ₗ[ℂ] rationalInducedSmoothOrbitSections hG hi hν I hKc hPK
      (rationalOrbitRepresentative a ha mu I O) :=
  rationalFourierOrbitSmoothSectionLinear hG hi hν I hKc hPK ρ hρ hKρ (hM I)
    (rationalOrbitRepresentative a ha mu I O) (rationalLeviSplitCenter I (a I))
    (rationalLeviSplitCenter_le_center I (a I) (ha I)) (mu I)
    (rationalOrbitRepresentative_isSquareIntegrable a ha mu I O)
    (hTA I _ (rationalOrbitRepresentative_isSquareIntegrable a ha mu I O)) hsw hμK (hswM I)
    (hTA I _ (rationalOrbitRepresentative_isSquareIntegrable a ha mu I O)
      (selfUnitaryOrbitRepresentative I _))
    (hE I) (hPKiw I) (hMK I) (hUK I) (hnσ I)
    (hint I _ (rationalOrbitRepresentative_isSquareIntegrable a ha mu I O))

/-- The component `ψ_f[O, P_I] ∈ C^∞(O, P_I)` is the family's component. -/
theorem rationalFourierThetaComponentLinear_val (I : Finset (RationalPointFamily.SimpleRoot i ν))
    (O : RationalLeviOrbitClass a ha mu I) (f : RationalSchwartzSpace hKc hPK ρ) :
    (rationalFourierThetaComponentLinear hG hi hν hKc hPK a ha mu ρ hρ hKρ hM hsw hTA hμK hswM
        hE hPKiw hMK hUK hnσ hint I O f).val =
      rationalFourierThetaFamily hG hi hν hKc hPK a ha mu ρ hρ hKρ hM hsw hTA f I O :=
  rationalFourierOrbitSmoothSectionLinear_val hG hi hν I hKc hPK ρ hρ hKρ (hM I)
    (rationalOrbitRepresentative a ha mu I O) (rationalLeviSplitCenter I (a I))
    (rationalLeviSplitCenter_le_center I (a I) (ha I)) (mu I)
    (rationalOrbitRepresentative_isSquareIntegrable a ha mu I O)
    (hTA I _ (rationalOrbitRepresentative_isSquareIntegrable a ha mu I O)) hsw hμK (hswM I)
    (hTA I _ (rationalOrbitRepresentative_isSquareIntegrable a ha mu I O)
      (selfUnitaryOrbitRepresentative I _))
    (hE I) (hPKiw I) (hMK I) (hUK I) (hnσ I)
    (hint I _ (rationalOrbitRepresentative_isSquareIntegrable a ha mu I O)) f

/-- **Proposition VII.1.3 for the family, in the product**: `f ↦ (ψ_f[O, P_I])_{(I, O)}` is a
linear map from `C(G)` into the product of the section spaces. -/
def rationalFourierThetaFamilyLinear :
    RationalSchwartzSpace hKc hPK ρ →ₗ[ℂ] RationalStandardThetaSections hG hi hν a ha mu where
  toFun := rationalFourierThetaFamily hG hi hν hKc hPK a ha mu ρ hρ hKρ hM hsw hTA
  map_add' f g := by
    funext I O
    show rationalFourierThetaFamily hG hi hν hKc hPK a ha mu ρ hρ hKρ hM hsw hTA (f + g) I O =
      rationalFourierThetaFamily hG hi hν hKc hPK a ha mu ρ hρ hKρ hM hsw hTA f I O +
        rationalFourierThetaFamily hG hi hν hKc hPK a ha mu ρ hρ hKρ hM hsw hTA g I O
    rw [← rationalFourierThetaComponentLinear_val hG hi hν hKc hPK a ha mu ρ hρ hKρ hM hsw hTA hμK
        hswM hE hPKiw hMK hUK hnσ hint, ← rationalFourierThetaComponentLinear_val hG hi hν hKc hPK
        a ha mu ρ hρ hKρ hM hsw hTA hμK hswM hE hPKiw hMK hUK hnσ hint,
      ← rationalFourierThetaComponentLinear_val hG hi hν hKc hPK a ha mu ρ hρ hKρ hM hsw hTA hμK
        hswM hE hPKiw hMK hUK hnσ hint, map_add, Submodule.coe_add]
  map_smul' c f := by
    funext I O
    show rationalFourierThetaFamily hG hi hν hKc hPK a ha mu ρ hρ hKρ hM hsw hTA (c • f) I O =
      c • rationalFourierThetaFamily hG hi hν hKc hPK a ha mu ρ hρ hKρ hM hsw hTA f I O
    rw [← rationalFourierThetaComponentLinear_val hG hi hν hKc hPK a ha mu ρ hρ hKρ hM hsw hTA hμK
        hswM hE hPKiw hMK hUK hnσ hint, ← rationalFourierThetaComponentLinear_val hG hi hν hKc hPK
        a ha mu ρ hρ hKρ hM hsw hTA hμK hswM hE hPKiw hMK hUK hnσ hint, map_smul,
      Submodule.coe_smul]

theorem rationalFourierThetaFamilyLinear_apply (f : RationalSchwartzSpace hKc hPK ρ) :
    rationalFourierThetaFamilyLinear hG hi hν hKc hPK a ha mu ρ hρ hKρ hM hsw hTA hμK hswM hE
        hPKiw hMK hUK hnσ hint f =
      rationalFourierThetaFamily hG hi hν hKc hPK a ha mu ρ hρ hKρ hM hsw hTA f :=
  rfl

/-- **`ψ_f ∈ C^∞(Θ)`** (VII.1, with Remarque VIII.1.3 (ii)): given the published statement of
Theorem VIII.1.2, the family `ψ_f` has smooth components and finite support, so `f ↦ ψ_f` is a
linear map from `C(G)` into the standard part of `C^∞(Θ)`. -/
def rationalFourierThetaLinear (hVIII : RationalDiscreteSeriesOrbitFinitenessStatement.{u, uV}) :
    RationalSchwartzSpace hKc hPK ρ →ₗ[ℂ]
      rationalStandardThetaSmoothSections hG hi hν hKc hPK a ha mu :=
  LinearMap.codRestrict (rationalStandardThetaSmoothSections hG hi hν hKc hPK a ha mu)
    (rationalFourierThetaFamilyLinear hG hi hν hKc hPK a ha mu ρ hρ hKρ hM hsw hTA hμK hswM hE
      hPKiw hMK hUK hnσ hint) fun f => by
    rw [rationalFourierThetaFamilyLinear_apply, mem_rationalStandardThetaSmoothSections]
    refine ⟨fun I O => ?_, finite_support_rationalFourierThetaFamily hG hi hν hKc hPK a ha mu ρ
      hρ hKρ hM hsw hTA hVIII f⟩
    have h := (rationalFourierThetaComponentLinear hG hi hν hKc hPK a ha mu ρ hρ hKρ hM hsw
      hTA hμK hswM hE hPKiw hMK hUK hnσ hint I O f).property
    rw [rationalFourierThetaComponentLinear_val] at h
    exact h

/-- The element `ψ_f` of `C^∞(Θ)` is the family `rationalFourierThetaFamily f`. -/
theorem rationalFourierThetaLinear_val
    (hVIII : RationalDiscreteSeriesOrbitFinitenessStatement.{u, uV})
    (f : RationalSchwartzSpace hKc hPK ρ) :
    (rationalFourierThetaLinear hG hi hν hKc hPK a ha mu ρ hρ hKρ hM hsw hTA hμK hswM hE hPKiw
        hMK hUK hnσ hint hVIII f).val =
      rationalFourierThetaFamily hG hi hν hKc hPK a ha mu ρ hρ hKρ hM hsw hTA f :=
  rationalFourierThetaFamilyLinear_apply hG hi hν hKc hPK a ha mu ρ hρ hKρ hM hsw hTA hμK hswM hE
    hPKiw hMK hUK hnσ hint f

end Family

end Langlands.HarishChandraSchwartz
