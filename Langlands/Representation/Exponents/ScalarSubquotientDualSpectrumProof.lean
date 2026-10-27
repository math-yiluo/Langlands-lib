import Langlands.Representation.Exponents.ScalarSubquotientDualSpectrumStatement
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section

namespace Langlands

universe uK uA uV uW

namespace ScalarSubquotientDualSpectrum

variable {K : Type uK} [Field K] {A : Type uA} [CommGroup A]
  {V : Type uV} [AddCommGroup V] [Module K V]

/-- Simultaneous maximal generalized weight spaces for distinct characters
are independent in arbitrary dimension. -/
theorem independent_weights (ρ : Representation K A V) :
    iSupIndep (fun χ : A →* Kˣ => ⨅ a, Module.End.maxGenEigenspace (ρ a) (χ a : K)) := by
  have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (fun a : A => ρ a)
    (fun a b c => Module.End.mapsTo_maxGenEigenspace_of_comm
      ((Commute.all b a).map ρ) c)
  apply h.comp
  intro χ ψ he
  apply MonoidHom.ext
  intro a
  apply Units.ext
  exact congrFun he a

/-- A uniform generalized character vector lies in the simultaneous maximal
weight space. -/
theorem generalized_le_weight (ρ : Representation K A V) (χ : A →* Kˣ) :
    (generalizedCommutativeCharacterSpace ρ χ).toSubmodule ≤
      ⨅ a, Module.End.maxGenEigenspace (ρ a) (χ a : K) := by
  intro v hv
  obtain ⟨k, hk⟩ := (mem_generalizedCommutativeCharacterSpace ρ χ v).mp hv
  exact (Module.End.mem_iInf_maxGenEigenspace_iff _ _ _).mpr
    (fun a => ⟨k, hk a⟩)

/-- Restriction of full-dual vectors commutes with the transpose action. -/
theorem dualRestrict_comp (ρ : Representation K A V) (U : Subrepresentation ρ) (a : A) :
    (commutativeTranspose U.toRepresentation a).comp U.toSubmodule.dualRestrict =
      U.toSubmodule.dualRestrict.comp (commutativeTranspose ρ a) := by
  ext φ u
  rfl

/-- Restriction carries uniform generalized dual character vectors into the
same simultaneous maximal weight space on the invariant subspace. -/
theorem restrict_generalized_le (ρ : Representation K A V)
    (U : Subrepresentation ρ) (χ : A →* Kˣ) :
    ((generalizedCommutativeCharacterSpace (commutativeTranspose ρ) χ).toSubmodule.map
      U.toSubmodule.dualRestrict) ≤
        ⨅ a, Module.End.maxGenEigenspace (commutativeTranspose U.toRepresentation a) (χ a : K) := by
  rintro _ ⟨φ, hφ, rfl⟩
  have hm := generalized_le_weight (commutativeTranspose ρ) χ hφ
  simp only [Submodule.mem_iInf] at hm ⊢
  intro a
  exact Module.End.mapsTo_genEigenspace_of_comp U.toSubmodule.dualRestrict
    (dualRestrict_comp ρ U a) (χ a : K) ⊤ (hm a)

/-- Generalized spanning on the full dual forces the scalar character of an
actual nonzero subquotient to belong to the indexing predicate. -/
theorem scalarSubquotient_mem
    (ρ : Representation K A V) (P : (A →* Kˣ) → Prop)
    (hspan : (⨆ (χ : A →* Kˣ) (_ : P χ),
      (generalizedCommutativeCharacterSpace (commutativeTranspose ρ) χ).toSubmodule) = ⊤)
    (χ : A →* Kˣ) (U : Subrepresentation ρ)
    (W : Type uW) [AddCommGroup W] [Module K W] [Nontrivial W]
    (q : U.toSubmodule →ₗ[K] W) (hq : Function.Surjective q)
    (hscalar : ∀ (a : A) (u : U.toSubmodule), q (U.toRepresentation a u) = (χ a : K) • q u) :
    P χ := by
  classical
  let weight (ψ : A →* Kˣ) : Submodule K (Module.Dual K U.toSubmodule) :=
    ⨅ a, Module.End.maxGenEigenspace (commutativeTranspose U.toRepresentation a) (ψ a : K)
  have hspanU : (⨆ (ψ : A →* Kˣ) (_ : P ψ), weight ψ) = ⊤ := by
    apply top_unique
    rw [← LinearMap.range_eq_top.mpr (Subspace.dualRestrict_surjective (W := U.toSubmodule)),
      LinearMap.range_eq_map, ← hspan]
    simp_rw [Submodule.map_iSup]
    exact iSup₂_mono (fun ψ _ => restrict_generalized_le ρ U ψ)
  obtain ⟨ℓ, hℓ⟩ := exists_ne (0 : Module.Dual K W)
  let φ : Module.Dual K U.toSubmodule := ℓ.comp q
  have hφ : φ ≠ 0 := by
    intro he
    apply hℓ
    ext w
    obtain ⟨u, rfl⟩ := hq w
    exact congrArg (fun f : Module.Dual K U.toSubmodule => f u) he
  have hφweight : φ ∈ weight χ := by
    apply (Module.End.mem_iInf_maxGenEigenspace_iff _ _ _).mpr
    intro a
    refine ⟨1, ?_⟩
    have he : commutativeTranspose U.toRepresentation a φ = (χ a : K) • φ := by
      ext u
      simp only [commutativeTranspose_apply, LinearMap.smul_apply]
      change ℓ (q (U.toRepresentation a u)) = (χ a : K) • ℓ (q u)
      rw [hscalar, map_smul]
    simp [he]
  by_contra hχ
  have hd := (independent_weights (commutativeTranspose U.toRepresentation)).disjoint_biSup
    (y := {ψ | P ψ}) hχ
  change Disjoint (weight χ) (⨆ (ψ : A →* Kˣ) (_ : P ψ), weight ψ) at hd
  rw [hspanU, disjoint_top] at hd
  apply hφ
  simpa [hd] using hφweight

end ScalarSubquotientDualSpectrum

/-- Generalized full-dual spanning detects every actual nonzero scalar
subquotient, with four independent universes. -/
theorem scalarSubquotientDualSpectrum :
    ScalarSubquotientDualSpectrumStatement.{uK, uA, uV, uW} := by
  intro K _ A _ V _ _ ρ P hspan χ U W _ _ _ q hq hscalar
  exact ScalarSubquotientDualSpectrum.scalarSubquotient_mem ρ P hspan χ U W q hq hscalar

end Langlands
