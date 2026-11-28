import Langlands.BushnellKutzko.DiagonalSplitTypeRefinement

/-! # Additive characters of lattice quotients from the block trace pairing

For an integral lattice `Λ ⊆ 𝔄` and `N ∈ ℤ`, the quotient `Λ / (Λ ∩ 𝔓^N)` is finite, and for
`w ∈ 𝔓^{1−N}` and `e₁, e₂ ∈ 𝔄` the map `y ↦ ψ_A(e₁ y e₂ w)` descends to an additive character
of this quotient. -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.SplitBlocks

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V

/-- The quotient `Λ / (Λ ∩ 𝔓^N)` of an integral lattice. -/
abbrev latticeQuotient (𝓛 : LatticeChain 𝒪[F] F V) (Λ : Submodule 𝒪[F] A) (N : ℤ) :=
  Λ ⧸ ((𝓛.endFiltration N).comap Λ.subtype)

/-- `Λ / (Λ ∩ 𝔓^N)` is finite for `Λ ⊆ 𝔄`. -/
theorem finite_latticeQuotient (𝓛 : LatticeChain 𝒪[F] F V) {Λ : Submodule 𝒪[F] A}
    (hΛ : Λ ≤ 𝓛.endFiltration 0) {N : ℤ} (hN : 0 ≤ N) :
    Finite (latticeQuotient 𝓛 Λ N) := by
  have : Finite (layerQuotient 𝓛 0 N) := finite_layerQuotient 𝓛 0 N hN
  let f : Λ →ₗ[𝒪[F]] layerQuotient 𝓛 0 N :=
    (Submodule.mkQ _).comp (Submodule.inclusion hΛ)
  have hker : LinearMap.ker f = (𝓛.endFiltration N).comap Λ.subtype := by
    ext y
    simp only [f, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.coe_subtype, Submodule.coe_inclusion]
  let e := (LinearMap.ker f).quotEquivOfEq _ hker
  have hfin : Finite (Λ ⧸ LinearMap.ker f) :=
    Finite.of_equiv _ (f.quotKerEquivRange.toEquiv.symm)
  exact Finite.of_equiv _ e.toEquiv

/-- The character `y ↦ ψ_A(e₁ y e₂ w)` of `Λ / (Λ ∩ 𝔓^N)`, for `e₁, e₂ ∈ 𝔄` and
`w ∈ 𝔓^{1−N}`. -/
def latticeBlockCharacter (𝓛 : LatticeChain 𝒪[F] F V) {ψF : AddChar F ℂ}
    (hψ : IsBKAdditiveCharacter ψF) (Λ : Submodule 𝒪[F] A) (N : ℤ) {e₁ e₂ w : A} (he₁ : e₁ ∈ 𝓛.endFiltration 0)
    (he₂ : e₂ ∈ 𝓛.endFiltration 0) (hw : w ∈ 𝓛.endFiltration (1 - N)) :
    AddChar (latticeQuotient 𝓛 Λ N) ℂ :=
  let ψ := (traceCharacter ψF).compAddMonoidHom
    ((AddMonoidHom.mulRight w).comp ((AddMonoidHom.mulRight e₂).comp
      ((AddMonoidHom.mulLeft e₁).comp Λ.subtype.toAddMonoidHom)))
  AddChar.toAddMonoidHomEquiv.symm <|
    QuotientAddGroup.lift ((𝓛.endFiltration N).comap Λ.subtype).toAddSubgroup
      ψ.toAddMonoidHom (fun y hy => by
        change traceCharacter ψF (e₁ * (y : A) * e₂ * w) = 1
        have hyN : (y : A) ∈ 𝓛.endFiltration N := hy
        exact traceCharacter_eq_one 𝓛 hψ
          (mul_mul_mem_endFiltration 𝓛 (𝓛.mul_mem_endFiltration he₁ hyN) he₂ hw (by ring)))

theorem latticeBlockCharacter_mk (𝓛 : LatticeChain 𝒪[F] F V) {ψF : AddChar F ℂ}
    (hψ : IsBKAdditiveCharacter ψF) (Λ : Submodule 𝒪[F] A) (N : ℤ) {e₁ e₂ w : A} (he₁ : e₁ ∈ 𝓛.endFiltration 0)
    (he₂ : e₂ ∈ 𝓛.endFiltration 0) (hw : w ∈ 𝓛.endFiltration (1 - N)) (y : Λ) :
    latticeBlockCharacter 𝓛 hψ Λ N he₁ he₂ hw (Submodule.Quotient.mk y) =
      traceCharacter ψF (e₁ * (y : A) * e₂ * w) :=
  rfl

end Langlands.BushnellKutzko.SplitBlocks
