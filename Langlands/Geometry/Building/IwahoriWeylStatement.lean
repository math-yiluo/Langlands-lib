import Langlands.Geometry.Building.IwahoriWeyl
import Langlands.Geometry.Building.KPApartmentAxioms
import Langlands.GroupScheme.Rational.StandardParabolic
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.RingTheory.Henselian

/-!
# The Iwahori–Weyl group, the Iwasawa decomposition and the corrected KP Theorem 7.8.1

Statements, not proofs, on the actual building data `P : ParahoricBuildingData G` of a
connected reductive group `G` over a nonarchimedean local field `F`, with `N = N_G(S)`,
`Z = Z_G(S)` and `W̃^0 = N(F)/Z(F)^0`:

* KP Theorem 7.8.1(1): the exact sequence `1 → W_aff → W̃^0 → G(F)/G(F)^0 → 1`;
* KP 7.8.2: `W̃^0 = W_aff ⋊ W̃^0_C` for a chamber `C`, and `W̃^0_C ≅ G(F)/G(F)^0`;
* KP Theorem 7.8.1(2): `W̃^0 → I\G(F)/I` is bijective for the Iwahori subgroup `I = P_C`;
* KP Theorem 7.8.1(3): `W^aff_{F₁}\W̃^0/W^aff_{F₂} → P_{F₁}\G(F)/P_{F₂}` is bijective for
  faces `F₁`, `F₂` of a common chamber;
* KP Theorem 5.3.3 (Iwasawa decomposition): `G(F) = U(F) N(F) P_C`;
* KP Lemma 5.3.5 as replaced in the 2024 corrections: `n ∈ U(F) n' P_C ↔ n' n⁻¹ ∈ Z(F)^0`;
* KP Theorem 7.8.1(4), added in the 2024 corrections:
  `W̃^0 → U(F)\G(F)/I = U(F)Z(F)^0\G(F)/I` is bijective.

Here `U` is the unipotent radical of the minimal parabolic subgroup `standardParabolic P.i ν ∅`
of a generic cocharacter `ν` of `S`. The Chapter 7 statements assume the apartment axioms
`P.apartment.SatisfiesApartmentAxioms P.centralizer` (V 6, V 7, AS 2–AS 5, with the AS 5
of the corrected opening of KP Chapter 7). The Chapter 5 statements assume in addition the
standing hypotheses of KP Chapter 5: the valuation ring is Henselian and the residue field is
perfect.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry ValuativeRel
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-! ### Conclusions for fixed data -/

/-- The conclusion of KP Theorem 7.8.1(1): `Z(F)^0` is normal in `N(F)` and `G(F)^0` is normal
in `G(F)`; the action of `N(F) ∩ G(F)^0` on the apartment identifies
`(N(F) ∩ G(F)^0)/Z(F)^0` with the affine Weyl group `W_aff = W(Ψ)` of the affine roots; and
this subgroup of `W̃^0` is the kernel of the surjection `W̃^0 → G(F)/G(F)^0`. -/
def IwahoriWeylExactSequence : Prop :=
  ∃ (_ : P.normalizerZero.Normal) (_ : P.zeroSubgroup.Normal),
    (∃ e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots,
      ∀ n : P.normalizerZeroComponent,
        (e (P.affinePartMk n) : P.Apartment ≃ᵃ[ℝ] P.Apartment) =
          P.apartment.normalizerAffineEquiv (n : normalizerPoints P.i)) ∧
      P.toComponents.ker = P.affinePart ∧ Function.Surjective P.toComponents

/-- The conclusion of KP 7.8.2 for a chamber `C`: the stabilizer `W̃^0_C` of `C` in `W̃^0` is a
complement of the normal subgroup `W_aff = (N(F) ∩ G(F)^0)/Z(F)^0`, so
`W̃^0 = W_aff ⋊ W̃^0_C`, and `W̃^0_C → G(F)/G(F)^0` is bijective. -/
def IwahoriWeylChamberSplitting (C : Set P.Apartment) : Prop :=
  ∃ (_ : P.normalizerZero.Normal) (_ : P.zeroSubgroup.Normal),
    P.affinePart.Normal ∧ P.affinePart.IsComplement' (P.chamberStabilizer C) ∧
      Function.Bijective (P.toComponents.comp (P.chamberStabilizer C).subtype)

/-- The conclusion of KP Theorem 7.8.1(2) for a chamber `C` with Iwahori subgroup
`I = P_C`: there is a bijection `W̃^0 ≃ I\G(F)/I` sending the class of every `n ∈ N(F)` to
`I n I`. -/
def IwahoriDoubleCosetBijection (C : Set P.Apartment) : Prop :=
  ∃ e : P.IwahoriWeylGroup ≃
      DoubleCoset.Quotient (P.parahoric C : Set (rationalPoints G)) (P.parahoric C),
    ∀ n : normalizerPoints P.i,
      e (QuotientGroup.mk n) =
        DoubleCoset.mk (P.parahoric C) (P.parahoric C) (n : rationalPoints G)

/-- The conclusion of KP Theorem 7.8.1(3) for facets `F₁`, `F₂`: `Z(F)^0` is normal in `N(F)`,
and there is a bijection `W^aff_{F₁}\W̃^0/W^aff_{F₂} ≃ P_{F₁}\G(F)/P_{F₂}` sending the class of
every `n ∈ N(F)` to `P_{F₁} n P_{F₂}`. -/
def ParahoricDoubleCosetBijection (F₁ F₂ : Set P.Apartment) : Prop :=
  ∃ (_ : P.normalizerZero.Normal),
    ∃ e : DoubleCoset.Quotient (P.affineFacetStabilizer F₁ : Set P.IwahoriWeylGroup)
          (P.affineFacetStabilizer F₂) ≃
        DoubleCoset.Quotient (P.parahoric F₁ : Set (rationalPoints G)) (P.parahoric F₂),
      ∀ n : normalizerPoints P.i,
        e (DoubleCoset.mk (P.affineFacetStabilizer F₁) (P.affineFacetStabilizer F₂)
            (QuotientGroup.mk n)) =
          DoubleCoset.mk (P.parahoric F₁) (P.parahoric F₂) (n : rationalPoints G)

/-- The conclusion of KP Theorem 5.3.3 (Iwasawa decomposition) for a chamber `C` and the
unipotent radical `U` of the minimal parabolic subgroup of `ν`: `G(F) = U(F) N(F) P_C`. -/
def IwasawaDecomposition (C : Set P.Apartment) (ν : cocharacterLattice P.S) : Prop :=
  ∀ g : rationalPoints G, ∃ u ∈ standardUnipotentPoints P.i ν ∅, ∃ n : normalizerPoints P.i,
    ∃ p ∈ P.parahoric C, g = u * (n : rationalPoints G) * p

/-- The conclusion of KP Lemma 5.3.5 as replaced in the 2024 corrections, for a chamber `C`
and the unipotent radical `U` of the minimal parabolic subgroup of `ν`: for `n, n' ∈ N(F)`,
`n ∈ U(F) n' P_C` if and only if `n' n⁻¹ ∈ Z(F)^0`. -/
def UnipotentNormalizerCoset (C : Set P.Apartment) (ν : cocharacterLattice P.S) : Prop :=
  ∀ n n' : normalizerPoints P.i,
    (∃ u ∈ standardUnipotentPoints P.i ν ∅, ∃ p ∈ P.parahoric C,
        (n : rationalPoints G) = u * (n' : rationalPoints G) * p) ↔
      n' * n⁻¹ ∈ P.normalizerZero

/-- The conclusion of KP Theorem 7.8.1(4), added in the 2024 corrections, for a chamber `C`
with Iwahori subgroup `I = P_C` and the unipotent radical `U` of the minimal parabolic subgroup
of `ν`: there are bijections `W̃^0 ≃ U(F)\G(F)/I` and `W̃^0 ≃ U(F)Z(F)^0\G(F)/I`, each sending
the class of every `n ∈ N(F)` to the double coset of `n`. -/
def UnipotentIwahoriDoubleCosetBijection (C : Set P.Apartment)
    (ν : cocharacterLattice P.S) : Prop :=
  (∃ e : P.IwahoriWeylGroup ≃
      DoubleCoset.Quotient (standardUnipotentPoints P.i ν ∅ : Set (rationalPoints G))
        (P.parahoric C),
    ∀ n : normalizerPoints P.i,
      e (QuotientGroup.mk n) =
        DoubleCoset.mk (standardUnipotentPoints P.i ν ∅) (P.parahoric C)
          (n : rationalPoints G)) ∧
    ∃ e : P.IwahoriWeylGroup ≃
        DoubleCoset.Quotient
          ((standardUnipotentPoints P.i ν ∅ : Set (rationalPoints G)) *
            (P.centralizerZero.map (rationalPoints.map P.centralizer.j) :
              Set (rationalPoints G)))
          (P.parahoric C),
      ∀ n : normalizerPoints P.i,
        e (QuotientGroup.mk n) = Quotient.mk'' (n : rationalPoints G)

end ParahoricBuildingData

/-! ### Statements -/

/-- KP Theorem 7.8.1(1) on the actual building data of a connected reductive group over a
nonarchimedean local field, under the apartment axioms (V 6, V 7, AS 2–AS 5) assumed in the
corrected opening of KP Chapter 7. -/
def IwahoriWeylExactSequenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] (P : ParahoricBuildingData G),
    P.apartment.SatisfiesApartmentAxioms P.centralizer → P.IwahoriWeylExactSequence

/-- KP 7.8.2: for every chamber `C` of the apartment, `W̃^0 = W_aff ⋊ W̃^0_C` and
`W̃^0_C ≅ G(F)/G(F)^0`, under the apartment axioms of KP Chapter 7. -/
def IwahoriWeylChamberSplittingStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] (P : ParahoricBuildingData G),
    P.apartment.SatisfiesApartmentAxioms P.centralizer →
      ∀ C : Set P.Apartment, AffineRootSystem.IsChamber P.affineRoots C →
        P.IwahoriWeylChamberSplitting C

/-- KP Theorem 7.8.1(2), with the injectivity proof of the 2024 corrections: for every chamber
`C` of the apartment, `W̃^0 → P_C\G(F)/P_C` is bijective, under the apartment axioms of KP
Chapter 7. -/
def IwahoriDoubleCosetStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] (P : ParahoricBuildingData G),
    P.apartment.SatisfiesApartmentAxioms P.centralizer →
      ∀ C : Set P.Apartment, AffineRootSystem.IsChamber P.affineRoots C →
        P.IwahoriDoubleCosetBijection C

/-- KP Theorem 7.8.1(3): for facets `F₁`, `F₂` contained in the closure of a common chamber
`C`, `W^aff_{F₁}\W̃^0/W^aff_{F₂} → P_{F₁}\G(F)/P_{F₂}` is bijective, under the apartment
axioms of KP Chapter 7. -/
def ParahoricDoubleCosetStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] (P : ParahoricBuildingData G),
    P.apartment.SatisfiesApartmentAxioms P.centralizer →
      ∀ C F₁ F₂ : Set P.Apartment, AffineRootSystem.IsChamber P.affineRoots C →
        AffineRootSystem.IsFaceOf P.affineRoots F₁ C →
        AffineRootSystem.IsFaceOf P.affineRoots F₂ C →
        P.ParahoricDoubleCosetBijection F₁ F₂

/-- KP Theorem 5.3.3 (Iwasawa decomposition) `G(F) = U(F) N(F) P_C`, for every chamber `C`
of the apartment and the minimal parabolic subgroup of every generic cocharacter `ν` of `S`.
Besides the apartment axioms it assumes the standing hypotheses of KP Chapter 5: `𝒪[F]` is
Henselian and the residue field `𝓀[F]` is perfect. -/
def IwasawaDecompositionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] (P : ParahoricBuildingData G),
    HenselianLocalRing 𝒪[F] → PerfectField 𝓀[F] →
    P.apartment.SatisfiesApartmentAxioms P.centralizer →
      ∀ (C : Set P.Apartment) (ν : cocharacterLattice P.S),
        AffineRootSystem.IsChamber P.affineRoots C → IsGenericCocharacter P.i ν →
          P.IwasawaDecomposition C ν

/-- KP Lemma 5.3.5 as replaced in the 2024 corrections: `n ∈ U(F) n' P_C ↔ n' n⁻¹ ∈ Z(F)^0`
for `n, n' ∈ N(F)`, every chamber `C` of the apartment and the minimal parabolic subgroup of
every generic cocharacter `ν` of `S`, under the hypotheses of KP Chapter 5 and the apartment
axioms. -/
def UnipotentNormalizerCosetStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] (P : ParahoricBuildingData G),
    HenselianLocalRing 𝒪[F] → PerfectField 𝓀[F] →
    P.apartment.SatisfiesApartmentAxioms P.centralizer →
      ∀ (C : Set P.Apartment) (ν : cocharacterLattice P.S),
        AffineRootSystem.IsChamber P.affineRoots C → IsGenericCocharacter P.i ν →
          P.UnipotentNormalizerCoset C ν

/-- KP Theorem 7.8.1(4), added in the 2024 corrections: `W̃^0 → U(F)\G(F)/P_C` and
`W̃^0 → U(F)Z(F)^0\G(F)/P_C` are bijective, for every chamber `C` of the apartment and the
minimal parabolic subgroup of every generic cocharacter `ν` of `S`, under the hypotheses of KP
Chapter 5 and the apartment axioms. -/
def UnipotentIwahoriDoubleCosetStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] (P : ParahoricBuildingData G),
    HenselianLocalRing 𝒪[F] → PerfectField 𝓀[F] →
    P.apartment.SatisfiesApartmentAxioms P.centralizer →
      ∀ (C : Set P.Apartment) (ν : cocharacterLattice P.S),
        AffineRootSystem.IsChamber P.affineRoots C → IsGenericCocharacter P.i ν →
          P.UnipotentIwahoriDoubleCosetBijection C ν

/-- All seven statements of this module together: the corrected KP Theorem 7.8.1(1)–(4),
7.8.2, Theorem 5.3.3 and the replaced Lemma 5.3.5, each with its own hypotheses. -/
def IwahoriWeylBijectionsStatement : Prop :=
  IwahoriWeylExactSequenceStatement.{u} ∧ IwahoriWeylChamberSplittingStatement.{u} ∧
    IwahoriDoubleCosetStatement.{u} ∧ ParahoricDoubleCosetStatement.{u} ∧
    IwasawaDecompositionStatement.{u} ∧ UnipotentNormalizerCosetStatement.{u} ∧
    UnipotentIwahoriDoubleCosetStatement.{u}

end Langlands.Geometry.Building
