import Langlands.JacquetLanglands.Relation

/-!
# The elliptic norm of a square-integrable character, computed on `Dˣ`

The proposition `EllipticNormTransferStatement`, not proved here. Let `F` be a nonarchimedean
local field of characteristic zero and `D` a central division algebra of dimension `n^2` over
`F`. If the character of an irreducible square-integrable representation `π` of `GL_n(F)`
agrees, at corresponding regular elements, with a linear combination `∑ a_j Θ_{τ_j}` of the
characters of pairwise inequivalent irreducible admissible representations `τ_j` of `Dˣ`, then
`∑ |a_j|^2 = 1`. This is the orthogonality relation of elliptic characters on `GL_n(F)`
(norm `1` for square-integrable representations), transported to `Dˣ` by the Weyl integration
formula, together with the orthogonality relations of characters of the group `Dˣ`, compact
modulo its centre (Deligne–Kazhdan–Vignéras, §B.1.f).
-/

noncomputable section

namespace Langlands.JacquetLanglands

universe u uV uW

/-- The elliptic norm of a square-integrable character, computed on `Dˣ` (Deligne–Kazhdan–
Vignéras §B.1.f, characteristic zero). Let `F` be a nonarchimedean local field of characteristic
zero, `D` a finite-dimensional central division algebra over `F` with its module topology and
`n` with `Module.finrank F D = n ^ 2`. Let `π` be an irreducible representation of `GL_n(F)`
(carrier in `Type uV`) that is square-integrable modulo the centre, and let `τ j`, `j ∈ J`, be a
finite family of pairwise inequivalent irreducible admissible representations of `Dˣ` (carriers
in `Type uW`). If `a : J → ℂ` satisfies `Θ_π(g) = ∑ j, a j * Θ_{τ j}(g')` for every regular
elliptic `g` and every regular `g'` that correspond, then `∑ j, ‖a j‖ ^ 2 = 1`. -/
def EllipticNormTransferStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F]
    (D : Type u) [DivisionRing D] [Algebra F D] [FiniteDimensional F D] [Algebra.IsCentral F D]
    [TopologicalSpace D] [IsModuleTopology F D] (n : ℕ),
    Module.finrank F D = n ^ 2 →
    haveI := generalLinear_t2Space F n
    haveI := generalLinear_locallyCompactSpace F n
    haveI := generalLinear_totallyDisconnectedSpace F n
    haveI := units_isTopologicalGroup F D
    haveI := units_t2Space F D
    haveI := units_locallyCompactSpace F D
    haveI := units_totallyDisconnectedSpace F D
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GeneralLinear n F) V)
      (hπ : IsSquareIntegrable π), π.IsIrreducible →
    ∀ (J : Type) [Fintype J] (W : J → Type uW) [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
      (τ : (j : J) → Representation ℂ Dˣ (W j)) (hτ : ∀ j, IsAdmissible (τ j)),
      (∀ j, (τ j).IsIrreducible) →
      Pairwise (fun i j => ¬ Nonempty ((τ i).Equiv (τ j))) →
      ∀ a : J → ℂ,
        (∀ (g : GeneralLinear n F) (g' : Dˣ), Corresponds F D g g' →
          ∃ (c : ℂ) (d : J → ℂ), HasCharacterValue π hπ.isAdmissible g c ∧
            (∀ j, HasCharacterValue (τ j) (hτ j) g' (d j)) ∧ c = ∑ j, a j * d j) →
        ∑ j, ‖a j‖ ^ 2 = 1

end Langlands.JacquetLanglands
