import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Filtration.ObjectDefinitions
import Langlands.Representation.Induction.Parabolic
import Langlands.Representation.Jacquet.Parabolic

/-! BZ77 section 2.13: Jacquet modules of quasicuspidal induction. -/

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric

universe uF uV

/-- The minimal conjugating permutations represent exactly once every coset
of the source block Weyl group acting on the right of `W(M,N)`. -/
def MinimalConjugatingCosetsTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (n : ℕ), 0 < n →
    ∀ (B C : BlockShape n) (w : Equiv.Perm (Fin n)),
      ConjugatesLevi (F := F.Carrier) B C w →
      ∃! v : MinimalConjugatingPermutations (F := F.Carrier) B C,
        ∃ b : blockWeyl B, w = v.val.val * b.val

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData) (n : ℕ)

/-- If no standard subgroup of the target Levi is associated to the source
Levi, the normalized Jacquet module of quasicuspidal induction is zero. -/
def QuasicuspidalJacquetVanishingTheorem : Prop :=
  letI := T.topology
  ∀ (B C : BlockShape n) (ρ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
    IsLeviQuasicuspidal B ρ.representation →
    (¬ ∃ (S : BlockRefinement C) (w : Equiv.Perm (Fin n)),
      (B.leviSubgroup F.Carrier).map
        (MulAut.conj (permutation n F.Carrier w)).toMonoidHom =
        (refinedLevi F.Carrier C S).map (C.leviEmbedding F.Carrier)) →
    Subsingleton ((T.normalizedJacquetFunctor C).obj
      ((T.normalizedParabolicInductionFunctor B).obj ρ))

/-- For nonassociated Levis, the normalized Jacquet module of quasicuspidal
induction has no nonzero quasicuspidal subquotient. -/
def NonassociatedJacquetSubquotientsTheorem : Prop :=
  letI := T.topology
  ∀ (B C : BlockShape n) (ρ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
    IsLeviQuasicuspidal B ρ.representation →
    ¬ LevisAssociated (F := F.Carrier) B C →
    let A := (T.normalizedJacquetFunctor C).obj
      ((T.normalizedParabolicInductionFunctor B).obj ρ)
    ∀ D : SmoothRep.{0, uF, max uF uV} ℂ (C.Levi F.Carrier),
      SmoothRep.IsSubquotient D A → IsLeviQuasicuspidal C D.representation →
      Subsingleton D

/-- For associated Levis, the actual Jacquet module has one successive
quotient for each minimal conjugating permutation, equal up to actual
representation equivalence to the corresponding Weyl transport. -/
def AssociatedJacquetFiltrationTheorem : Prop :=
  letI := T.topology
  ∀ (B C : BlockShape n) (ρ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
    IsLeviQuasicuspidal B ρ.representation →
    LevisAssociated (F := F.Carrier) B C →
    let A := (T.normalizedJacquetFunctor C).obj
      ((T.normalizedParabolicInductionFunctor B).obj ρ)
    IsLeviQuasicuspidal C A.representation ∧
    ∃ (r : ℕ) (e : Fin r ≃ MinimalConjugatingPermutations (F := F.Carrier) B C)
      (s : ObjectRepFiltration (Rep.of A.representation) r),
      ∀ i, Nonempty ((s.gradedRepresentation i).ρ.Equiv
        (transport B C (e i).val.val (e i).property ρ.representation))

/-- The GL_n specialization of all three parts of BZ77 corollary 2.13,
together with the precise coset parametrization used in its part (c). -/
def PadicQuasicuspidalJacquetTheorems : Prop :=
  MinimalConjugatingCosetsTheorem.{uF} ∧
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ), 0 < n →
      QuasicuspidalJacquetVanishingTheorem.{uF, uV} F T n ∧
      NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T n ∧
      AssociatedJacquetFiltrationTheorem.{uF, uV} F T n

end Langlands.CuspidalSupport
