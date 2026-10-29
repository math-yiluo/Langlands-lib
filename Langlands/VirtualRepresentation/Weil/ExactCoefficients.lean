import Langlands.VirtualRepresentation.Weil.ExactFiltration
import Langlands.Representation.Filtration.LengthCriterionProof
import Langlands.Representation.Filtration.MultiplicityAdditivityProof
import Langlands.Representation.Filtration.IrreducibleMultiplicityProof

/-!
# Jordan–Hölder coefficients on the exact quotient

Composition-factor multiplicities of actual continuous representations define
an integral left inverse of the canonical exact realization.
-/

noncomputable section

universe uG uV

open scoped MonoidAlgebra

namespace Langlands.VirtualRepresentation.Weil

open FiniteRepresentation

variable {G : Type uG} [Group G] [TopologicalSpace G]

namespace ExactCoefficients

/-- Every continuous finite-dimensional object has an actual composition series. -/
theorem exists_series (A : ContinuousObjects.{uG, uV} G) :
    ∃ n, ∃ s : ObjectRepFiltration A.val.obj n, s.HasSimpleFactors := by
  have : IsNoetherian ℂ[G] A.val.obj.ρ.asModule := isNoetherian_of_tower ℂ inferInstance
  have : IsArtinian ℂ[G] A.val.obj.ρ.asModule := isArtinian_of_tower ℂ inferInstance
  have hfin : IsFiniteLength ℂ[G] A.val.obj.ρ.asModule :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  obtain ⟨s, h₀, h₁⟩ := isFiniteLength_iff_exists_compositionSeries.mp hfin
  exact ⟨s.length, LengthCriterionProof.hasCompositionSeriesLength_of_compositionSeries s h₀ h₁⟩

omit [TopologicalSpace G] in
/-- An irreducible object has positive rank. -/
theorem rank_pos_of_isIrreducible (B : FiniteRepresentation.{0, uG, uV} ℂ G)
    (h : B.IsIrreducible) : 0 < B.rank := by
  have : IsSimpleModule ℂ[G] B.representation.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).mp h
  have : Nontrivial B := IsSimpleModule.nontrivial ℂ[G] B.representation.asModule
  exact Module.finrank_pos

/-- The lattice basis element of an actual continuous irreducible object. -/
def basisOf (B : ContinuousObjects.{uG, uV} G) (h : B.val.IsIrreducible) :
    IrreducibleBasis.{uG, uV} G :=
  basisClass B.val B.property h ⟨B.val.rank, rank_pos_of_isIrreducible B.val h⟩ rfl

/-- A chosen actual representative of a basis class. -/
def representative (b : IrreducibleBasis.{uG, uV} G) : FiniteRepresentation.{0, uG, uV} ℂ G :=
  (Quotient.out b.2.val).val

/-- A basis element is determined by its isomorphism class. -/
theorem basis_ext {b b' : IrreducibleBasis.{uG, uV} G} (h : b.2.val = b'.2.val) : b = b' := by
  obtain ⟨n, c, hc⟩ := b
  obtain ⟨n', c', hc'⟩ := b'
  dsimp only at h
  subst h
  have hn : n = n' := PNat.coe_injective (hc.symm.trans hc')
  subst hn
  rfl

/-- An irreducible object gives the basis element exactly when it is equivalent
to that element's chosen representative. -/
theorem basisOf_eq_iff (B : ContinuousObjects.{uG, uV} G) (h : B.val.IsIrreducible)
    (b : IrreducibleBasis.{uG, uV} G) :
    basisOf B h = b ↔ Nonempty (FiniteRepresentation.Equiv B.val (representative b)) := by
  constructor
  · intro hb
    have hc := congrArg (fun b : IrreducibleBasis.{uG, uV} G => b.2.val) hb
    change Quotient.mk _ _ = b.2.val at hc
    rw [← Quotient.out_eq b.2.val] at hc
    exact Quotient.exact hc
  · intro he
    apply basis_ext
    change Quotient.mk _ _ = b.2.val
    rw [← Quotient.out_eq b.2.val]
    exact Quotient.sound he

/-- The sum of the lattice generators of the graded factors of a series. -/
def seriesSum (A : ContinuousObjects.{uG, uV} G) {n : ℕ}
    (s : ObjectRepFiltration A.val.obj n) (hs : s.HasSimpleFactors) :
    IrreducibleLattice.{uG, uV} G :=
  ∑ i : Fin n, generator (basisOf (continuousFiltrationGraded A s i) (hs i))

/-- Each coefficient of the series sum is the multiplicity of the chosen
representative among the graded factors. -/
theorem seriesSum_apply (A : ContinuousObjects.{uG, uV} G) {n : ℕ}
    (s : ObjectRepFiltration A.val.obj n) (hs : s.HasSimpleFactors)
    (b : IrreducibleBasis.{uG, uV} G) :
    seriesSum A s hs b = (s.factorMultiplicity (representative b).obj : ℤ) := by
  classical
  rw [seriesSum, Finsupp.finsetSum_apply]
  simp only [generator, Finsupp.single_apply]
  rw [Finset.sum_boole, ObjectRepFiltration.factorMultiplicity, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  congr 2
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact basisOf_eq_iff _ _ b

/-- The length of the chosen composition series. -/
def seriesLength (A : ContinuousObjects.{uG, uV} G) : ℕ := (exists_series A).choose

/-- A chosen actual composition series. -/
def series (A : ContinuousObjects.{uG, uV} G) : ObjectRepFiltration A.val.obj (seriesLength A) :=
  (exists_series A).choose_spec.choose

theorem series_hasSimpleFactors (A : ContinuousObjects.{uG, uV} G) :
    (series A).HasSimpleFactors :=
  (exists_series A).choose_spec.choose_spec

/-- The composition-factor coefficients of an actual continuous object. -/
def coefficients (A : ContinuousObjects.{uG, uV} G) : IrreducibleLattice.{uG, uV} G :=
  seriesSum A (series A) (series_hasSimpleFactors A)

theorem hasJordanHolderMultiplicity_series (A : ContinuousObjects.{uG, uV} G)
    (b : IrreducibleBasis.{uG, uV} G) :
    HasJordanHolderMultiplicity A.val.obj (representative b).obj
      ((series A).factorMultiplicity (representative b).obj) :=
  ⟨_, series A, series_hasSimpleFactors A, rfl⟩

/-- Any actual multiplicity witness computes the corresponding coefficient. -/
theorem coefficients_apply (A : ContinuousObjects.{uG, uV} G)
    (b : IrreducibleBasis.{uG, uV} G) {m : ℕ}
    (h : HasJordanHolderMultiplicity A.val.obj (representative b).obj m) :
    coefficients A b = m := by
  rw [coefficients, seriesSum_apply]
  exact congrArg _ ((hasJordanHolderMultiplicity_series A b).unique h)

/-- Equivalent objects have the same coefficients. -/
theorem coefficients_eq_of_equiv {A A' : ContinuousObjects.{uG, uV} G}
    (e : FiniteRepresentation.Equiv A.val A'.val) : coefficients A = coefficients A' := by
  ext b
  rw [coefficients_apply A b (hasJordanHolderMultiplicity_series A b),
    coefficients_apply A' b ((equivJordanHolderMultiplicityTransport ℂ G A.val.obj A'.val.obj
      (representative b).obj (representative b).obj e (Representation.Equiv.refl _) _).mp
        (hasJordanHolderMultiplicity_series A b))]

/-- Coefficients of genuine continuous classes. -/
def classCoefficients : ContinuousClasses.{uG, uV} G → IrreducibleLattice.{uG, uV} G :=
  Quotient.lift coefficients fun _ _ h => by
    obtain ⟨e⟩ := h
    exact coefficients_eq_of_equiv e

/-- Coefficients add along every actual short exact sequence. -/
theorem classCoefficients_isExactAdditive :
    ExactGrothendieckGroup.IsExactAdditive _ (classCoefficients (G := G)) := by
  intro A B C f g h
  change coefficients B = coefficients A + coefficients C
  ext b
  rw [Finsupp.add_apply]
  have hA := hasJordanHolderMultiplicity_series A b
  have hC := hasJordanHolderMultiplicity_series C b
  have hB := jordanHolderShortExactAdditivity ℂ G A.val.obj B.val.obj C.val.obj
    (representative b).obj f g h.1 h.2.1 h.2.2 _ _ hA hC
  rw [coefficients_apply B b hB, coefficients_apply A b hA, coefficients_apply C b hC]
  push_cast
  rfl

/-- An irreducible object has a single coefficient, at its own basis element. -/
theorem coefficients_of_isIrreducible (A : ContinuousObjects.{uG, uV} G)
    (h : A.val.IsIrreducible) : coefficients A = generator (basisOf A h) := by
  ext b
  have hm := (irreducibleMultiplicity.{0, uG, uV, uV}).2 ℂ G A.val.obj (representative b).obj h
  by_cases hb : Nonempty (FiniteRepresentation.Equiv A.val (representative b))
  · rw [coefficients_apply A b ((hm 1).mpr (Or.inl ⟨hb, rfl⟩))]
    obtain rfl := (basisOf_eq_iff A h b).mpr hb
    rw [generator, Finsupp.single_eq_same]
    rfl
  · rw [coefficients_apply A b ((hm 0).mpr (Or.inr ⟨hb, rfl⟩)), generator,
      Finsupp.single_eq_of_ne' (fun hb' => hb ((basisOf_eq_iff A h b).mp hb'))]
    rfl

end ExactCoefficients

open ExactCoefficients

variable (G)

/-- The integral Jordan–Hölder coefficient map on the exact quotient. -/
def exactCoefficients :
    ContinuousExactGroup.{uG, uV} G →ₗ[ℤ] IrreducibleLattice.{uG, uV} G :=
  ExactGrothendieckGroup.lift _ classCoefficients classCoefficients_isExactAdditive

/-- The coefficient map is a left inverse of the canonical realization. -/
theorem exactCoefficients_comp_realizeExact :
    (exactCoefficients.{uG, uV} G).comp (realizeExact.{uG, uV} G) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro b z
  have hs : Finsupp.single b z = z • generator b := by simp [generator]
  rw [hs, LinearMap.map_smul, LinearMap.map_smul]
  congr 1
  change exactCoefficients G (realizeExact G (generator b)) = generator b
  rw [realizeExact_generator, exactCoefficients, ExactGrothendieckGroup.lift_ofClass]
  obtain ⟨n, c, hc⟩ := b
  induction c using Quotient.inductionOn with
  | h A =>
    change coefficients ⟨A.val, A.property.1⟩ = _
    rw [coefficients_of_isIrreducible ⟨A.val, A.property.1⟩ A.property.2]
    congr 1
    exact basis_ext rfl

@[simp]
theorem exactCoefficients_realizeExact (v : IrreducibleLattice.{uG, uV} G) :
    exactCoefficients G (realizeExact G v) = v :=
  LinearMap.congr_fun (exactCoefficients_comp_realizeExact G) v

/-- The canonical exact realization is injective. -/
theorem realizeExact_injective : Function.Injective (realizeExact.{uG, uV} G) :=
  Function.LeftInverse.injective (exactCoefficients_realizeExact G)

end Langlands.VirtualRepresentation.Weil
