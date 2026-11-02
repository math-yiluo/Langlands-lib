import Langlands.Representation.Filtration.MultiplicityFreeSubmoduleLatticeProof
import Langlands.Representation.Filtration.MultiplicityTransportProof

/-!
# At most one nonzero proper subrepresentation, by support counting

An abstract lattice argument. Let `Φ` be a strictly monotone map from the
subrepresentations of `ρ` to those of a representation `A` with a
multiplicity-free composition series. Suppose that every composition factor of
`A`, except those in a single equivalence class `Bad`, occurs in `Φ X` for every
nonzero `X`, and that `Φ` preserves intersections. Then `ρ` has at most one subrepresentation other than `⊥` and `⊤`.
-/

namespace Langlands.Classification.JuxtaposedShuffle

universe uK uG uH uV uA uB

section Support

variable {k : Type uK} [Field k] {H : Type uH} [Monoid H]

/-- Membership in the composition-factor support depends only on the
equivalence class of the factor. -/
theorem mem_jordanHolderSupport_of_equiv {B : Rep.{uB} k H} {τ τ' : Rep.{uA} k H}
    (h : τ ∈ (jordanHolderSupport B : Set (Rep.{uA} k H))) (e : τ.ρ.Equiv τ'.ρ) :
    τ' ∈ (jordanHolderSupport B : Set (Rep.{uA} k H)) := by
  obtain ⟨m, hm, hpos⟩ := h
  exact ⟨m, (equivJordanHolderMultiplicityTransport k H B B τ τ'
    (Representation.Equiv.refl _) e m).1 hm, hpos⟩

/-- A composition series in which every irreducible representation has
multiplicity at most one is multiplicity free. -/
theorem hasMultiplicityFreeCompositionSeries_of_le_one (B : Rep.{uB} k H) {n : ℕ}
    (s : ObjectRepFiltration B n) (hs : s.HasSimpleFactors)
    (h : ∀ τ : Rep.{uB} k H, Representation.IsIrreducible τ.ρ → ∀ m,
      HasJordanHolderMultiplicity B τ m → m ≤ 1) :
    HasMultiplicityFreeCompositionSeries B := by
  refine ⟨n, s, hs, fun i j hij => ?_⟩
  have hm := h (s.gradedRepresentation i) (hs i) _ ⟨n, s, hs, rfl⟩
  unfold ObjectRepFiltration.factorMultiplicity at hm
  have := Finite.card_le_one_iff_subsingleton.mp hm
  exact congrArg Subtype.val (Subsingleton.elim
    (⟨i, ⟨Representation.Equiv.refl _⟩⟩ : {l : Fin n // Nonempty
      ((s.gradedRepresentation l).ρ.Equiv (s.gradedRepresentation i).ρ)})
    ⟨j, ⟨hij.some.symm⟩⟩)

end Support

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G] {H : Type uH} [Monoid H]
  {V : Type uV} [AddCommGroup V] [Module k V] {ρ : Representation k G V}

/-- If `Φ` is strictly monotone into the subrepresentations of a multiplicity-free
`A`, all `Bad` representations are equivalent, and every factor of `A` that is not
`Bad` occurs in `Φ X` for every nonzero `X`, then two subrepresentations that are
neither `⊥` nor `⊤` are equal. -/
theorem eq_of_ne_bot_of_ne_top (A : Rep.{uA} k H) (hA : HasMultiplicityFreeCompositionSeries A)
    (Φ : Subrepresentation ρ → Subrepresentation A.ρ) (hΦ : StrictMono Φ)
    (hΦinf : ∀ X Y, Φ (X ⊓ Y) = Φ X ⊓ Φ Y)
    (Bad : Rep.{uA} k H → Prop)
    (hbad : ∀ τ τ' : Rep.{uA} k H, Bad τ → Bad τ' → Nonempty (τ.ρ.Equiv τ'.ρ))
    (hcover : ∀ τ ∈ (jordanHolderSupport A : Set (Rep.{uA} k H)), ¬ Bad τ →
      ∀ X : Subrepresentation ρ, X ≠ ⊥ →
        τ ∈ (jordanHolderSupport (Rep.of (Φ X).toRepresentation) : Set (Rep.{uA} k H)))
    {X Y : Subrepresentation ρ} (hX₀ : X ≠ ⊥) (hX₁ : X ≠ ⊤) (hY₀ : Y ≠ ⊥) (hY₁ : Y ≠ ⊤) :
    X = Y := by
  obtain ⟨-, hle, -, -, -, htop⟩ := multiplicityFreeSubmoduleLattice k H A hA
  simp only at hle htop
  have hinj : ∀ X Y : Subrepresentation ρ, Φ X = Φ Y → X ≤ Y := by
    intro X Y h
    by_contra hXY
    have hlt : X ⊓ Y < X := lt_of_le_of_ne inf_le_left (fun h' => hXY (by
      rw [← h']
      exact inf_le_right))
    have := hΦ hlt
    rw [hΦinf, h, inf_idem] at this
    exact lt_irrefl _ this
  have key : ∀ Z : Subrepresentation ρ, Z ≠ ⊥ → Z ≠ ⊤ → ∀ τ : Rep.{uA} k H,
      τ ∈ (jordanHolderSupport (Rep.of (Φ Z).toRepresentation) : Set (Rep.{uA} k H)) ↔
        τ ∈ (jordanHolderSupport A : Set (Rep.{uA} k H)) ∧ ¬ Bad τ := by
    intro Z hZ₀ hZ₁ τ
    constructor
    · intro hτ
      have hτA : τ ∈ (jordanHolderSupport A : Set (Rep.{uA} k H)) := by
        rw [← htop]
        exact (hle _ _).1 le_top hτ
      refine ⟨hτA, fun hb => ?_⟩
      have hsub : (jordanHolderSupport (Rep.of (⊤ : Subrepresentation A.ρ).toRepresentation) :
          Set (Rep.{uA} k H)) ⊆
            jordanHolderSupport (Rep.of (Φ Z).toRepresentation) := by
        rw [htop]
        intro τ' hτ'
        by_cases hb' : Bad τ'
        · exact mem_jordanHolderSupport_of_equiv hτ (hbad τ τ' hb hb').some
        · exact hcover τ' hτ' hb' Z hZ₀
      have htopZ : ⊤ ≤ Φ Z := (hle _ _).2 hsub
      have hlt : Φ Z < Φ ⊤ := hΦ (lt_top_iff_ne_top.2 hZ₁)
      exact absurd (lt_of_le_of_lt htopZ hlt) (not_lt_of_ge le_top)
    · rintro ⟨hτA, hb⟩
      exact hcover τ hτA hb Z hZ₀
  have hΦXY : Φ X = Φ Y := le_antisymm
    ((hle _ _).2 fun τ h => (key Y hY₀ hY₁ τ).2 ((key X hX₀ hX₁ τ).1 h))
    ((hle _ _).2 fun τ h => (key X hX₀ hX₁ τ).2 ((key Y hY₀ hY₁ τ).1 h))
  exact le_antisymm (hinj X Y hΦXY) (hinj Y X hΦXY.symm)

end Langlands.Classification.JuxtaposedShuffle
