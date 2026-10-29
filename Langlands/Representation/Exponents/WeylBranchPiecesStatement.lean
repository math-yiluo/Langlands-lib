import Langlands.Representation.Exponents.SupportedRegularMultiplicityBranchObstructionStatement

/-!
# Weyl-piece interfaces for the supported excess-multiplicity branch

Four internal statement boundaries, each a consequence of the normalized
geometric lemma (BZ77, 2.12) together with BZ77, 2.4(d), in the form used by
the branch-selection step of Silberger 1978, Lemma 5.6, printed p.101.
This file states them; it contains no proof of them.
-/

noncomputable section

namespace Langlands

open GeneralLinear Geometric
open RelativeJacquetMultiplicity RelativeRegularComparison

universe uF uV uW uM

namespace WeylBranchPieces

/-- `X` is an actual quotient of an actual subrepresentation of `A`. -/
def IsSubquotient {G : Type*} [Group G] {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : Representation ℂ G V) (X : Representation ℂ G W) : Prop :=
  ∃ U : Subrepresentation A, ∃ q : U.toRepresentation.IntertwiningMap X,
    Function.Surjective q

end WeylBranchPieces

open WeylBranchPieces

/-- Whole-Levi piece of the geometric lemma: for a minimal representative `x`
conjugating the flattened Levi of `S` onto `C`, the transported inner opposite
Jacquet module of `V` along `S` is an actual subquotient of the opposite
Jacquet module along `C` of the normalized induction of `V`. -/
def GLGeometricPieceLiftingStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B C : BlockShape n) (S : BlockRefinement B)
      (x : Equiv.Perm (Fin n)),
      IsMinimalRepresentative B C x →
      ∀ (hx : CuspidalSupport.ConjugatesLevi (F := F.Carrier) (B.flatten S) C x)
        (V : Rep.{uV} ℂ (B.Levi F.Carrier)),
        IsSmooth V.ρ →
        IsSubquotient
          (CuspidalJacquetMultiplicity.oppositeJacquet T C
            (CuspidalJacquetMultiplicity.induced T B V)).ρ
          (CuspidalSupport.transport (B.flatten S) C x hx
            ((innerJacquet T B S V).ρ.comp
              (flattenedLeviEquiv F.Carrier B S).toMonoidHom))

/-- Strict excess of the ambient over the inner Jordan–Hölder multiplicity of
an irreducible cuspidal fine representation is carried by one minimal
representative outside the coarse Weyl group that conjugates a whole flattened
Levi of the coarse Levi onto the fine Levi, and in whose transported inner
opposite Jacquet module the representation is an actual subquotient. -/
def GLGeometricExcessBranchStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n) (S : BlockRefinement B)
      (V : Rep.{uW} ℂ (B.Levi F.Carrier)),
      IsSmooth V.ρ →
      ∀ ρ : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier),
        Representation.IsIrreducible ρ.ρ →
        CuspidalSupport.IsLeviCuspidal (B.flatten S) ρ.ρ →
        let τ : Rep.{uV} ℂ (refinedLevi F.Carrier B S) :=
          Rep.of (ρ.ρ.comp (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom)
        ∀ m_in m_amb : ℕ,
          HasJordanHolderMultiplicity (innerJacquet T B S V) τ m_in →
          HasJordanHolderMultiplicity (ambientJacquet T B S V) τ m_amb →
          m_in < m_amb →
          ∃ (x : Equiv.Perm (Fin n)) (S' : BlockRefinement B)
            (hx : CuspidalSupport.ConjugatesLevi (F := F.Carrier)
              (B.flatten S') (B.flatten S) x),
            IsMinimalRepresentative B (B.flatten S) x ∧ x ∉ blockWeyl B ∧
            IsSubquotient
              (CuspidalSupport.transport (B.flatten S') (B.flatten S) x hx
                ((innerJacquet T B S' V).ρ.comp
                  (flattenedLeviEquiv F.Carrier B S').toMonoidHom))
              ρ.ρ

/-- An irreducible cuspidal subquotient of an inner opposite Jacquet module of
a middle normalized induction inside the coarse Levi comes, through one minimal
representative in the coarse Weyl group, from a transported inner opposite
Jacquet module of the middle representation along a refinement of the middle
shape. -/
def GLProductLeviCuspidalLocalizationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n) (Q : BlockRefinement B),
      let D := B.flatten Q
      ∀ σ : Rep.{uM} ℂ (D.Levi F.Carrier),
        IsSmooth σ.ρ →
        ∀ (S' : BlockRefinement B) (ρ : Rep.{uV} ℂ ((B.flatten S').Levi F.Carrier)),
          Representation.IsIrreducible ρ.ρ →
          CuspidalSupport.IsLeviCuspidal (B.flatten S') ρ.ρ →
          IsSubquotient
            ((innerJacquet T B S' (middleInduced T B Q σ)).ρ.comp
              (flattenedLeviEquiv F.Carrier B S').toMonoidHom)
            ρ.ρ →
          ∃ g ∈ blockWeyl B, ∃ (R' : BlockRefinement D)
            (hg : CuspidalSupport.ConjugatesLevi (F := F.Carrier)
              (D.flatten R') (B.flatten S') g),
            IsMinimalRepresentative D (B.flatten S') g ∧
            IsSubquotient
              (CuspidalSupport.transport (D.flatten R') (B.flatten S') g hg
                ((innerJacquet T D R' σ).ρ.comp
                  (flattenedLeviEquiv F.Carrier D R').toMonoidHom))
              ρ.ρ

/-- An irreducible cuspidal subquotient of an inner opposite Jacquet module of
the inner normalized induction of an irreducible cuspidal representation is
equivalent to a transport of that representation by an element of the Weyl
group of the ambient shape. -/
def GLCuspidalInductionJacquetConstituentStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (D : BlockShape n) (R R' : BlockRefinement D)
      (ω : Rep.{uV} ℂ ((D.flatten R).Levi F.Carrier)),
      Representation.IsIrreducible ω.ρ →
      CuspidalSupport.IsLeviCuspidal (D.flatten R) ω.ρ →
      ∀ ρ : Rep.{uW} ℂ ((D.flatten R').Levi F.Carrier),
        Representation.IsIrreducible ρ.ρ →
        CuspidalSupport.IsLeviCuspidal (D.flatten R') ρ.ρ →
        IsSubquotient
          ((innerJacquet T D R' (innerInduced T D R
              (Rep.of (ω.ρ.comp
                (flattenedLeviEquiv F.Carrier D R).symm.toMonoidHom)))).ρ.comp
            (flattenedLeviEquiv F.Carrier D R').toMonoidHom)
          ρ.ρ →
        ∃ h ∈ blockWeyl D,
          ∃ hh : CuspidalSupport.ConjugatesLevi (F := F.Carrier)
            (D.flatten R) (D.flatten R') h,
            Nonempty (ρ.ρ.Equiv
              (CuspidalSupport.transport (D.flatten R) (D.flatten R') h hh ω.ρ))

end Langlands
