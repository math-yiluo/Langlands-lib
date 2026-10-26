import Langlands.Representation.Induction.NormalCoinvariantMap
import Langlands.Representation.Induction.CompactSurjectivityProof
import Langlands.Representation.Induction.NormalCoinvariantKernelProof
import Langlands.Representation.Smooth.Transfer.SubquotientProof

noncomputable section
open CategoryTheory

namespace Langlands.Induction

universe uG uV

section Assembly

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (H N : Subgroup G) [N.Normal] (hNH : N ≤ H)
variable (σ : Representation ℂ H V)

private theorem comparison_injective
    (hker : ∀ f : CompactFunctions H σ,
      (∀ g : G, eval H σ f.val g ∈
        Representation.Coinvariants.ker (σ.comp (N.subgroupOf H).subtype)) →
      f ∈ Representation.Coinvariants.ker ((compactInduced H σ).comp N.subtype)) :
    Function.Injective (compactNormalCoinvariantsMap H N hNH σ) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro q
  induction q using Representation.Coinvariants.induction_on with
  | h f =>
    intro hf
    apply (Representation.Coinvariants.mk_eq_zero _).mpr
    apply hker f
    intro g
    apply (Representation.Coinvariants.mk_eq_zero _).mp
    exact congrArg (fun F => eval H (σ.toCoinvariants (N.subgroupOf H)) F.val g) hf

private theorem comparison_surjective
    (hsurj : Function.Surjective
      (compactInducedMap H (σ.toCoinvariantsMkQ (N.subgroupOf H)))) :
    Function.Surjective (compactNormalCoinvariantsMap H N hNH σ) := by
  intro f
  obtain ⟨g, hg⟩ := hsurj f
  exact ⟨Representation.Coinvariants.mk _ g, hg⟩

include hNH in
/-- Assemble one natural family from the two bijectivity properties. -/
private theorem comparison_family
    (hsurj : ∀ A : Langlands.SmoothRep.{0, uG, uV} ℂ H,
      Function.Surjective (compactInducedMap H
        (A.representation.toCoinvariantsMkQ (N.subgroupOf H))))
    (hker : ∀ (A : Langlands.SmoothRep.{0, uG, uV} ℂ H)
      (f : CompactFunctions H A.representation),
      (∀ g : G, eval H A.representation f.val g ∈
        Representation.Coinvariants.ker
          (A.representation.comp (N.subgroupOf H).subtype)) →
      f ∈ Representation.Coinvariants.ker
        ((compactInduced H A.representation).comp N.subtype)) :
    ∃ e : ∀ A : Langlands.SmoothRep.{0, uG, uV} ℂ H,
      ((compactInduced H A.representation).toCoinvariants N).Equiv
        (compactInduced H (A.representation.toCoinvariants (N.subgroupOf H))),
      (∀ (A : Langlands.SmoothRep.{0, uG, uV} ℂ H)
          (f : CompactFunctions H A.representation) (g : G),
        eval H (A.representation.toCoinvariants (N.subgroupOf H))
            (e A (Representation.Coinvariants.mk
              ((compactInduced H A.representation).comp N.subtype) f)).val g =
          Representation.Coinvariants.mk
            (A.representation.comp (N.subgroupOf H).subtype)
            (eval H A.representation f.val g)) ∧
      (∀ (A B : Langlands.SmoothRep.{0, uG, uV} ℂ H) (T : A ⟶ B)
          (q : Representation.Coinvariants
            ((compactInduced H A.representation).comp N.subtype)),
        e B (Representation.Coinvariants.map _ _
            (Jacquet.restrictMap
              (compactInducedMap H (Langlands.SmoothRep.hom T)) N) q) =
          compactInducedMap H
            (normalCoinvariantsMap (N.subgroupOf H)
              (Langlands.SmoothRep.hom T)) (e A q)) := by
  let e := fun A : Langlands.SmoothRep.{0, uG, uV} ℂ H =>
    (compactNormalCoinvariantsMap H N hNH A.representation).ofBijective
      ⟨comparison_injective H N hNH A.representation (hker A),
       comparison_surjective H N hNH A.representation (hsurj A)⟩
  refine ⟨e, ?_, ?_⟩
  · intro A f g
    exact compactNormalCoinvariantsMap_eval H N hNH A.representation f g
  · intro A B T q
    exact compactNormalCoinvariantsMap_natural H N hNH A.representation
      B.representation (Langlands.SmoothRep.hom T) q

end Assembly

/-- Compact induction commutes naturally with normal-subgroup coinvariants. -/
theorem compactInductionNormalCoinvariants :
    CompactInductionNormalCoinvariants.{uG,uV} := by
  intro G _ _ _ _ hBasis H N _ hH hN hNH
  have hCofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L.toSubgroup ≤ K.toSubgroup := by
    intro K
    obtain ⟨L, hLc, hLK⟩ := hBasis (K : Set G) K.isOpen K.one_mem
    exact ⟨L, hLc, hLK⟩
  apply comparison_family H N hNH
  · intro A
    let q := A.representation.toCoinvariantsMkQ (N.subgroupOf H)
    have hq : Function.Surjective q := Representation.Coinvariants.mk_surjective _
    have hs : Langlands.IsSmooth
        (A.representation.toCoinvariants (N.subgroupOf H)) :=
      Langlands.isSmooth_of_surjective q hq A.isSmooth
    exact compactInductionSurjectivity G hCofinal H hH A _ A.representation
      (A.representation.toCoinvariants (N.subgroupOf H)) A.isSmooth hs q hq
  · intro A f hf
    exact (compactInductionNormalCoinvariantKernel G hBasis H N hH hN hNH
      A A.representation A.isSmooth f).mpr hf

end Langlands.Induction
