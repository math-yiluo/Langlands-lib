import Langlands.Representation.LanglandsClassification.LanglandsTriplet
import Langlands.Representation.Classification.ConstituentRelations
import Langlands.Representation.Category.Twist
import Langlands.GroupScheme.Reductive.Basic

/-! # The Langlands classification (Renard VII.4.2)

For a Langlands triplet `(P = MN, σ, ψ)` relative to a fixed minimal parabolic, the induced
representation `i_P^G(σ ⊗ ψ)` has a unique irreducible quotient `J(P, σ, ψ)`; two triplets
with the same Langlands quotient have the same standard Levi, unramified characters with the
same real part and isomorphic twists `σ ⊗ ψ`; and every irreducible smooth representation of
`G(F)` is a Langlands quotient.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.4.2, Theorem (i): for a Langlands triplet `(P = MN, σ, ψ)` and any unipotent
radical `N` of `P` with `P = MN`, the normalized induced representation `i_P^G(σ ⊗ ψ)` has an
irreducible quotient, and all its irreducible quotient maps have the same kernel. -/
def LanglandsQuotientUniqueStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      [Mono i.hom.hom.left] (ν : cocharacterLattice T) (D : RelativeRootReflectionData i)
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (A : CommGroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (a : A.toGrp ⟶ M)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)) (ha : IsSplitComponent a)
      (J : Set (characterLattice T)) (f : A ⟶ T)
      (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
      (ψ : leviUnramifiedCharacters l hl),
      IsLanglandsTriplet i ν D p l a hp hl ha J f σ ψ →
        letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
        haveI : NonarchimedeanGroup (rationalPoints M) :=
          leviPoints_nonarchimedeanGroup p l hp hl
        ∃ π : SmoothRep.{0, u, max u v} ℂ (rationalPoints G),
          Classification.IsIrreducibleHead
            ((leviInductionFunctor p l r hp hr hl hmul).obj
              (σ.twist ψ.val.toMonoidHom
                (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))).representation
            π.representation

/-- Renard VII.4.2, Theorem (ii): let `(P₁ = M₁N₁, σ₁, ψ₁)` and `(P₂ = M₂N₂, σ₂, ψ₂)` be
Langlands triplets for the same minimal parabolic. If an irreducible smooth representation
`π` of `G(F)` is a quotient of both `i_{P₁}^G(σ₁ ⊗ ψ₁)` and `i_{P₂}^G(σ₂ ⊗ ψ₂)`, then
`M₁ = M₂` (equal simple-root indices), `ψ₂ ψ₁⁻¹` has real part zero (`|ψ₁| = |ψ₂|` on the common
group `M₁(F) = M₂(F)` inside `G(F)`), and `σ₁ ⊗ ψ₁ ≅ σ₂ ⊗ ψ₂` over that common group. -/
def LanglandsQuotientInjectiveStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      [Mono i.hom.hom.left] (ν : cocharacterLattice T) (D : RelativeRootReflectionData i)
      (P₁ M₁ U₁ : GroupScheme (Spec (CommRingCat.of k)))
      (A₁ : CommGroupScheme (Spec (CommRingCat.of k)))
      (p₁ : P₁ ⟶ G) (l₁ : M₁ ⟶ P₁) (r₁ : U₁ ⟶ P₁) (a₁ : A₁.toGrp ⟶ M₁)
      (hp₁ : IsParabolicSubgroup p₁) (hl₁ : IsRationalLeviSubgroup l₁)
      (hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁)
      (hmul₁ : IsIso (subgroupMultiplication l₁ r₁)) (ha₁ : IsSplitComponent a₁)
      (J₁ : Set (characterLattice T)) (f₁ : A₁ ⟶ T)
      (σ₁ : letI := leviPointTopology l₁ hl₁; SmoothRep.{0, u, v} ℂ (rationalPoints M₁))
      (ψ₁ : leviUnramifiedCharacters l₁ hl₁)
      (P₂ M₂ U₂ : GroupScheme (Spec (CommRingCat.of k)))
      (A₂ : CommGroupScheme (Spec (CommRingCat.of k)))
      (p₂ : P₂ ⟶ G) (l₂ : M₂ ⟶ P₂) (r₂ : U₂ ⟶ P₂) (a₂ : A₂.toGrp ⟶ M₂)
      (hp₂ : IsParabolicSubgroup p₂) (hl₂ : IsRationalLeviSubgroup l₂)
      (hr₂ : LeviSubgroup.IsGeometricUnipotentRadical r₂)
      (hmul₂ : IsIso (subgroupMultiplication l₂ r₂)) (ha₂ : IsSplitComponent a₂)
      (J₂ : Set (characterLattice T)) (f₂ : A₂ ⟶ T)
      (σ₂ : letI := leviPointTopology l₂ hl₂; SmoothRep.{0, u, v} ℂ (rationalPoints M₂))
      (ψ₂ : leviUnramifiedCharacters l₂ hl₂),
      IsLanglandsTriplet i ν D p₁ l₁ a₁ hp₁ hl₁ ha₁ J₁ f₁ σ₁ ψ₁ →
      IsLanglandsTriplet i ν D p₂ l₂ a₂ hp₂ hl₂ ha₂ J₂ f₂ σ₂ ψ₂ →
        letI : TopologicalSpace (rationalPoints M₁) := leviPointTopology l₁ hl₁
        haveI : NonarchimedeanGroup (rationalPoints M₁) :=
          leviPoints_nonarchimedeanGroup p₁ l₁ hp₁ hl₁
        letI : TopologicalSpace (rationalPoints M₂) := leviPointTopology l₂ hl₂
        haveI : NonarchimedeanGroup (rationalPoints M₂) :=
          leviPoints_nonarchimedeanGroup p₂ l₂ hp₂ hl₂
        let τ₁ := σ₁.twist ψ₁.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ₁)
        let τ₂ := σ₂.twist ψ₂.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ₂)
        ∀ π : SmoothRep.{0, u, max u v} ℂ (rationalPoints G),
          Classification.IsIrreducibleQuotient
            ((leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj τ₁).representation
            π.representation →
          Classification.IsIrreducibleQuotient
            ((leviInductionFunctor p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂).obj τ₂).representation
            π.representation →
            J₁ = J₂ ∧
            (∀ (m₁ : rationalPoints M₁) (m₂ : rationalPoints M₂),
              rationalPoints.map (l₁ ≫ p₁) m₁ = rationalPoints.map (l₂ ≫ p₂) m₂ →
                ‖(ψ₁.val m₁ : ℂ)‖ = ‖(ψ₂.val m₂ : ℂ)‖) ∧
            ∃ φ : τ₁ ≃ₗ[ℂ] τ₂,
              ∀ (m₁ : rationalPoints M₁) (m₂ : rationalPoints M₂),
                rationalPoints.map (l₁ ≫ p₁) m₁ = rationalPoints.map (l₂ ≫ p₂) m₂ →
                  ∀ x : τ₁, φ (τ₁.representation m₁ x) = τ₂.representation m₂ (φ x)

/-- Renard VII.4.2, Theorem (iii): fix a maximal split torus `i : T → G` and a generic
cocharacter `ν` whose dynamic parabolic is minimal, with reflection data `D`. Every
irreducible smooth representation `π` of `G(F)` is a quotient of `i_P^G(σ ⊗ ψ)` for some
Langlands triplet `(P = MN, σ, ψ)` relative to these choices, with `σ` on a carrier in the
universe of `π`. -/
def LanglandsQuotientExhaustiveStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      [Mono i.hom.hom.left] (ν : cocharacterLattice T) (D : RelativeRootReflectionData i),
      IsMaximalSplitTorus i → IsGenericCocharacter i ν →
      IsMinimalParabolicFunctor (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)) →
      ∀ π : SmoothRep.{0, u, v} ℂ (rationalPoints G), π.IsIrreducible →
        ∃ (P M U : GroupScheme (Spec (CommRingCat.of k)))
          (A : CommGroupScheme (Spec (CommRingCat.of k)))
          (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (a : A.toGrp ⟶ M)
          (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
          (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
          (hmul : IsIso (subgroupMultiplication l r)) (ha : IsSplitComponent a)
          (J : Set (characterLattice T)) (f : A ⟶ T)
          (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
          (ψ : leviUnramifiedCharacters l hl),
          IsLanglandsTriplet i ν D p l a hp hl ha J f σ ψ ∧
            letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
            haveI : NonarchimedeanGroup (rationalPoints M) :=
              leviPoints_nonarchimedeanGroup p l hp hl
            ∃ q : ((leviInductionFunctor p l r hp hr hl hmul).obj
                (σ.twist ψ.val.toMonoidHom
                  (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))).representation.IntertwiningMap
                π.representation,
              Function.Surjective q

/-- Renard VII.4.2, Theorem: the three statements above. -/
def LanglandsClassificationStatement.{u', v'} : Prop :=
  LanglandsQuotientUniqueStatement.{u', v'} ∧ LanglandsQuotientInjectiveStatement.{u', v'} ∧
    LanglandsQuotientExhaustiveStatement.{u', v'}

end Langlands.Aubert.General.RepresentedParabolic
